package main

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"runtime"
	"sort"
	"strings"
	"sync"
	"time"

	"golang.org/x/text/transform"

	"github.com/gdamore/tcell"
	"github.com/koron/gomigemo/embedict"
	"github.com/koron/gomigemo/migemo"
	"github.com/mattn/go-colorable"
	enc "github.com/mattn/go-encoding"
	"github.com/mattn/go-runewidth"
	"github.com/saracen/walker"
)

const name = "gof"

const version = "0.0.13"

var revision = "HEAD"

type matched struct {
	name     string
	pos1     int
	pos2     int
	selected bool
	index    int
}

type MatchMode = int
const (
	Normal MatchMode = iota
	Fuzzy
	Migemo
)

var (
	input            = []rune{}
	files            []string
	selected         = []string{}
	heading          = false
	current          []matched
	cursorX, cursorY int
	offset           int
	width, height    int
	screen			 tcell.Screen
	mutex            sync.Mutex
	dirty            = false
	duration         = 20 * time.Millisecond
	timer            *time.Timer
	scanning         = 0
	ignorere         *regexp.Regexp
	migemoDict		 migemo.Dict
)

func env(key, def string) string {
	if v := os.Getenv(key); v != "" {
		return v
	}
	return def
}

func tprint(x, y int, st tcell.Style, msg string) {
	for _, c := range []rune(msg) {
		screen.SetContent(x, y, c, nil, st)
		x += runewidth.RuneWidth(c)
	}
}

func tprintf(x, y int, st tcell.Style, format string, args ...interface{}) {
	s := fmt.Sprintf(format, args...)
	tprint(x, y, st, s)
}

func filter(mode MatchMode) {
	mutex.Lock()
	fs := files
	inp := input
	sel := selected
	mutex.Unlock()

	var tmp []matched
	if len(inp) == 0 {
		tmp = make([]matched, len(fs))
		for n, f := range fs {
			prevSelected := false
			for _, s := range sel {
				if f == s {
					prevSelected = true
					break
				}
			}
			tmp[n] = matched{
				name:     f,
				pos1:     -1,
				pos2:     -1,
				selected: prevSelected,
				index:    n,
			}
		}
	} else if mode == Fuzzy || mode == Migemo {
		var pat string
		if mode == Fuzzy {
			pat = "(?i)(?:.*)("
			for _, r := range []rune(inp) {
				pat += regexp.QuoteMeta(string(r)) + ".*?"
			}
			pat += ")"
		} else {
			var err error
			if migemoDict == migemo.Dict(nil) {
				if migemoDict, err = embedict.Load(); err != nil {
					fmt.Fprintln(os.Stderr, "Failed to load migemo dict:", err)
					os.Exit(1)
				}
			}
			if p, err := migemo.Pattern(migemoDict, string(inp)); err != nil {
				fmt.Fprintln(os.Stderr, "Failed to run migemo", string(inp), err)
				return
			} else {
				pat = fmt.Sprintf("(?i)(%s)", p)
			}
		}
		re := regexp.MustCompile(pat)

		tmp = make([]matched, 0, len(fs))
		for _, f := range fs {
			ms := re.FindAllStringSubmatchIndex(f, 1)
			if len(ms) != 1 || len(ms[0]) != 4 {
				continue
			}
			prevSelected := false
			for _, s := range sel {
				if f == s {
					prevSelected = true
					break
				}
			}
			tmp = append(tmp, matched{
				name:     f,
				pos1:     len([]rune(f[0:ms[0][2]])),
				pos2:     len([]rune(f[0:ms[0][3]])),
				selected: prevSelected,
				index:    len(tmp),
			})
		}
	} else {
		tmp = make([]matched, 0, len(fs))
		inpl := strings.ToLower(string(inp))
		for _, f := range fs {
			var pos int
			if lf := strings.ToLower(f); len(f) == len(lf) {
				pos = strings.Index(lf, inpl)
			} else {
				pos = bytes.Index([]byte(f), []byte(string(inp)))
			}
			if pos == -1 {
				continue
			}
			prevSelected := false
			for _, s := range sel {
				if f == s {
					prevSelected = true
					break
				}
			}
			pos1 := len([]rune(f[:pos]))
			tmp = append(tmp, matched{
				name:     f,
				pos1:     pos1,
				pos2:     pos1 + len(inp),
				selected: prevSelected,
				index:    len(tmp),
			})
		}
	}
	if len(inp) > 0 {
		sort.Slice(tmp, func(i, j int) bool {
			li, lj := tmp[i].pos2-tmp[i].pos1, tmp[j].pos2-tmp[j].pos1
			return li < lj || li == lj && tmp[i].index < tmp[j].index
		})
	}

	mutex.Lock()
	defer mutex.Unlock()
	current = tmp
	selected = sel
	if cursorY < 0 {
		cursorY = 0
	}
	if cursorY >= len(current) {
		cursorY = len(current) - 1
	}
	if cursorY >= 0 && height > 0 {
		if cursorY < offset {
			offset = cursorY
		} else if offset < cursorY-(height-3) {
			offset = cursorY - (height - 3)
		}
		if len(current)-(height-3)-1 < offset {
			offset = len(current) - (height - 3) - 1
			if offset < 0 {
				offset = 0
			}
		}
	} else {
		offset = 0
	}
}

func drawLines() {
	defer func() {
		recover()
	}()
	mutex.Lock()
	defer mutex.Unlock()

	width, height = screen.Size()
	screen.Clear()

	pat := ""
	for _, r := range input {
		pat += regexp.QuoteMeta(string(r)) + ".*?"
	}
	for n := offset; n <= height-3+offset; n++ {
		if n >= len(current) {
			break
		}
		x, y, w := 2, height-3-(n-offset), 0
		name := current[n].name
		pos1 := current[n].pos1
		pos2 := current[n].pos2
		selected := current[n].selected
		if pos1 >= 0 {
			pwidth := runewidth.StringWidth(string([]rune(current[n].name)[0:pos1]))
			if !heading && pwidth > width/2 {
				rname := []rune(name)
				wwidth := 0
				for i := 0; i < len(rname); i++ {
					w = runewidth.RuneWidth(rname[i])
					if wwidth+w > width/2 {
						name = "..." + string(rname[i:])
						pos1 -= i - 3
						pos2 -= i - 3
						break
					}
					wwidth += w
				}
			}
		}
		swidth := runewidth.StringWidth(name)
		if swidth+2 > width {
			rname := []rune(name)
			name = string(rname[0:width-5]) + "..."
		}
		for f, c := range []rune(name) {
			w = runewidth.RuneWidth(c)
			if x+w > width {
				break
			}
			if pos1 <= f && f < pos2 {
				if selected {
					screen.SetCell(x, y, tcell.StyleDefault.Foreground(tcell.ColorRed).Bold(true), c)
				} else if cursorY == n {
					screen.SetCell(x, y, tcell.StyleDefault.Foreground(tcell.ColorYellow).Bold(true).Underline(true), c)
				} else {
					screen.SetCell(x, y, tcell.StyleDefault.Foreground(tcell.ColorGreen).Bold(true), c)
				}
			} else {
				if selected {
					screen.SetCell(x, y, tcell.StyleDefault.Foreground(tcell.ColorRed), c)
				} else if cursorY == n {
					screen.SetCell(x, y, tcell.StyleDefault.Foreground(tcell.ColorYellow).Underline(true), c)
				} else {
					screen.SetCell(x, y, tcell.StyleDefault, c)
				}
			}
			x += w
		}
	}
	if cursorY >= 0 {
		tprint(0, height-3-(cursorY-offset), tcell.StyleDefault.Foreground(tcell.ColorRed).Bold(true), "> ")
	}
	if scanning >= 0 {
		tprint(0, height-2, tcell.StyleDefault.Foreground(tcell.ColorGreen), string([]rune("-\\|/")[scanning%4]))
		scanning++
	}
	tprintf(2, height-2, tcell.StyleDefault, "%d/%d(%d)", len(current), len(files), len(selected))
	tprint(0, height-1, tcell.StyleDefault.Foreground(tcell.ColorBlue).Bold(true), "> ")
	tprint(2, height-1, tcell.StyleDefault.Bold(true), string(input))
	screen.ShowCursor(2+runewidth.StringWidth(string(input[0:cursorX])), height-1)
	screen.Show()
}

var actionKeys = []tcell.Key{
	tcell.KeyCtrlA,
	tcell.KeyCtrlB,
	tcell.KeyCtrlC,
	tcell.KeyCtrlD,
	tcell.KeyCtrlE,
	tcell.KeyCtrlF,
	tcell.KeyCtrlG,
	tcell.KeyCtrlH,
	tcell.KeyCtrlI,
	tcell.KeyCtrlJ,
	tcell.KeyCtrlK,
	tcell.KeyCtrlL,
	tcell.KeyCtrlM,
	tcell.KeyCtrlN,
	tcell.KeyCtrlO,
	tcell.KeyCtrlP,
	tcell.KeyCtrlQ,
	tcell.KeyCtrlR,
	tcell.KeyCtrlS,
	tcell.KeyCtrlT,
	tcell.KeyCtrlU,
	tcell.KeyCtrlV,
	tcell.KeyCtrlW,
	tcell.KeyCtrlX,
	tcell.KeyCtrlY,
	tcell.KeyCtrlZ,
}

func readLines(ctx context.Context, wg *sync.WaitGroup, r io.Reader) {
	defer wg.Done()

	var buf *bufio.Reader
	if se := os.Getenv("GOF_STDIN_ENC"); se != "" {
		if e := enc.GetEncoding(se); e != nil {
			buf = bufio.NewReader(transform.NewReader(r, e.NewDecoder().Transformer))
		} else {
			buf = bufio.NewReader(r)
		}
	} else {
		buf = bufio.NewReader(r)
	}
	files = []string{}

	n := 0
	for {
		b, _, err := buf.ReadLine()
		if err != nil {
			break
		}
		mutex.Lock()
		files = append(files, string(b))
		n++
		if n%1000 == 0 {
			dirty = true
			timer.Reset(duration)
		}
		mutex.Unlock()
	}
	mutex.Lock()
	dirty = true
	timer.Reset(duration)
	scanning = -1
	mutex.Unlock()
}

func listFiles(ctx context.Context, wg *sync.WaitGroup, cwd string) {
	defer wg.Done()

	n := 0
	cb := walker.WithErrorCallback(func(pathname string, err error) error {
		return nil
	})
	fn := func(path string, info os.FileInfo) error {
		path = filepath.Clean(path)
		if p, err := filepath.Rel(cwd, path); err == nil {
			path = p
		}
		if path == "." {
			return nil
		}
		base := filepath.Base(path)
		if ignorere != nil && ignorere.MatchString(base) {
			if info.IsDir() {
				return filepath.SkipDir
			}
			return nil
		}
		path = filepath.ToSlash(path)
		mutex.Lock()
		files = append(files, path)
		n++
		if n%1000 == 0 {
			dirty = true
			timer.Reset(duration)
		}
		mutex.Unlock()
		return nil
	}
	walker.WalkWithContext(ctx, cwd, fn, cb)
	mutex.Lock()
	dirty = true
	timer.Reset(duration)
	scanning = -1
	mutex.Unlock()
}

func main() {
	var fuzzy_ bool
	var migemo_ bool
	var root string
	var exit int
	var action string
	var tapi bool
	var tapiFunc string
	var ignore string
	var showVersion bool
	var matchMode MatchMode

	flag.BoolVar(&fuzzy_, "f", false, "Fuzzy match")
	flag.BoolVar(&migemo_, "m", false, "Migemo match")
	flag.StringVar(&root, "d", "", "Root directory")
	flag.IntVar(&exit, "x", 1, "Exit code for cancel")
	flag.StringVar(&action, "a", "", "Action keys")
	flag.BoolVar(&tapi, "t", false, "Open via Vim's Terminal API")
	flag.StringVar(&tapiFunc, "tf", "", "Terminal API's function name")
	flag.StringVar(&ignore, "i", env(`GOF_IGNORE_PATTERN`, `^(\.git|\.hg|\.svn|_darcs|\.bzr)$`), "Ignore pattern")
	flag.BoolVar(&showVersion, "v", false, "Print the version")
	flag.Parse()

	if showVersion {
		fmt.Printf("%s %s (rev: %s/%s)\n", name, version, revision, runtime.Version())
		return
	}

	defer colorable.EnableColorsStdout(nil)()

	var err error

	// Make regular expression pattern to ignore files.
	if ignore != "" {
		ignorere, err = regexp.Compile(ignore)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	}
	if fuzzy_ && migemo_ {
		fmt.Fprintln(os.Stderr, "-f and -m can't be specified at the same time")
		os.Exit(1)
	}
	if fuzzy_ {
		matchMode = Fuzzy
	} else if migemo_ {
		matchMode = Migemo
	} else {
		matchMode = Normal
	}
	if migemo_ {
		if migemoDict, err = embedict.Load(); err != nil {
			fmt.Fprintln(os.Stderr, "Failed to load migemo dict:", err)
			os.Exit(1)
		}
	}

	// Setup terminal API.
	tapi = tapi || tapiFunc != ""
	if tapi {
		if os.Getenv("VIM_TERMINAL") == "" {
			fmt.Fprintln(os.Stderr, "-t,-tf option is only available inside Vim's terminal window")
			os.Exit(1)
		}
	}

	// Make sure current directory.
	cwd := ""
	if root == "" {
		cwd, err = os.Getwd()
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	} else {
		if runtime.GOOS == "windows" && strings.HasPrefix(root, "/") {
			cwd, _ = os.Getwd()
			cwd = filepath.Join(filepath.VolumeName(cwd), root)
		} else {
			cwd, err = filepath.Abs(root)
		}
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		st, err := os.Stat(cwd)
		if err == nil && !st.IsDir() {
			err = fmt.Errorf("Directory not found: %s", cwd)
		}
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
		err = os.Chdir(cwd)
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	}

	redrawFunc := func() {
		mutex.Lock()
		d := dirty
		mutex.Unlock()
		if d {
			filter(matchMode)
			drawLines()

			mutex.Lock()
			dirty = false
			mutex.Unlock()
		} else {
			drawLines()
		}
	}
	timer = time.AfterFunc(0, redrawFunc)
	timer.Stop()

	var wg sync.WaitGroup
	wg.Add(1)

	isTty := isTerminal()
	ctx, cancel := context.WithCancel(context.Background())
	if isTty {
		// Walk and collect files recursively.
		go listFiles(ctx, &wg, cwd)
	} else {
		// Read lines from stdin.
		go readLines(ctx, &wg, os.Stdin)
	}

	if !isTty {
		err = startTerminal()
		if err != nil {
			fmt.Fprintln(os.Stderr, err)
			os.Exit(1)
		}
	}
	if screen, err = tcell.NewScreen(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
	if err = screen.Init(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}

	redrawFunc()
	actionKey := ""

loop:
	for {
		update := false

		// Polling key events
		ev := screen.PollEvent();
		switch ev := ev.(type) {
		case *tcell.EventKey:
			key := ev.Key()
			for _, ka := range strings.Split(action, ",") {
				for i, kv := range actionKeys {
					if key != kv {
						continue
					}
					ak := fmt.Sprintf("ctrl-%c", 'a'+i)
					if ka != ak {
						continue
					}
					if cursorY >= 0 && cursorY < len(current) {
						if len(selected) == 0 {
							selected = append(selected, current[cursorY].name)
						}
						actionKey = ak
						break loop
					}
				}
			}
			switch key {
			case tcell.KeyEsc, tcell.KeyCtrlD, tcell.KeyCtrlC:
				screen.Fini()
				os.Exit(exit)
			case tcell.KeyHome, tcell.KeyCtrlA:
				cursorX = 0
			case tcell.KeyEnd, tcell.KeyCtrlE:
				cursorX = len(input)
			case tcell.KeyEnter:
				if cursorY >= 0 && cursorY < len(current) {
					if len(selected) == 0 {
						selected = append(selected, current[cursorY].name)
					}
					break loop
				}
			case tcell.KeyLeft:
				if cursorX > 0 {
					cursorX--
				}
			case tcell.KeyRight:
				if cursorX < len([]rune(input)) {
					cursorX++
				}
			case tcell.KeyUp, tcell.KeyCtrlK, tcell.KeyCtrlP:
				if cursorY < len(current)-1 {
					cursorY++
					if offset < cursorY-(height-3) {
						offset = cursorY - (height - 3)
					}
				}
			case tcell.KeyDown, tcell.KeyCtrlJ, tcell.KeyCtrlN:
				if cursorY > 0 {
					cursorY--
					if cursorY < offset {
						offset = cursorY
					}
				}
			case tcell.KeyCtrlI:
				heading = !heading
			case tcell.KeyCtrlL:
				update = true
			case tcell.KeyCtrlU:
				cursorX = 0
				input = []rune{}
				update = true
			case tcell.KeyCtrlW:
				part := string(input[0:cursorX])
				rest := input[cursorX:len(input)]
				pos := regexp.MustCompile(`\s+`).FindStringIndex(part)
				if len(pos) > 0 && pos[len(pos)-1] > 0 {
					input = []rune(part[0 : pos[len(pos)-1]-1])
					input = append(input, rest...)
				} else {
					input = []rune{}
				}
				cursorX = len(input)
				update = true
			case tcell.KeyCtrlZ:
				found := -1
				name := current[cursorY].name
				for i, s := range selected {
					if name == s {
						found = i
						break
					}
				}
				if found == -1 {
					selected = append(selected, current[cursorY].name)
				} else {
					selected = append(selected[:found], selected[found+1:]...)
				}
				update = true
			case tcell.KeyBackspace, tcell.KeyBackspace2:
				if cursorX > 0 {
					input = append(input[0:cursorX-1], input[cursorX:len(input)]...)
					cursorX--
					update = true
				}
			case tcell.KeyDelete:
				if cursorX < len([]rune(input)) {
					input = append(input[0:cursorX], input[cursorX+1:len(input)]...)
					update = true
				}
			case tcell.KeyCtrlR:
				switch matchMode {
				case Normal:
					matchMode = Fuzzy
				case Fuzzy:
					matchMode = Migemo
				default:
					matchMode = Normal
				}
				update = true
			default:
				ch := ev.Rune()
				if ch > 0 {
					out := []rune{}
					out = append(out, input[0:cursorX]...)
					out = append(out, ch)
					input = append(out, input[cursorX:len(input)]...)
					cursorX++
					update = true
				}
			}
		case *tcell.EventError:
			update = false
		}

		// If need to update, start timer
		if scanning != -1 {
			if update {
				mutex.Lock()
				dirty = true
				timer.Reset(duration)
				mutex.Unlock()
			} else {
				timer.Reset(1)
			}
		} else {
			if update {
				filter(matchMode)
			}
			drawLines()
		}
	}
	timer.Stop()

	// Request terminating
	cancel()

	screen.Clear()
	screen.Fini()
	stopTerminal()

	wg.Wait()

	if len(selected) == 0 {
		os.Exit(exit)
	}

	if tapi {
		for _, f := range selected {
			command := make([]interface{}, 0, 3)
			if tapiFunc != "" {
				command = append(command, "call", tapiFunc, newVimTapiCall(cwd, f, actionKey))
			} else {
				if !filepath.IsAbs(f) {
					f = filepath.Join(cwd, f)
				}
				command = append(command, "drop", f)
			}
			b, err := json.Marshal(command)
			if err != nil {
				fmt.Fprintln(os.Stderr, err)
				os.Exit(1)
			}
			fmt.Printf("\x1b]51;%s\x07", string(b))
		}
	} else {
		if action != "" {
			fmt.Println(actionKey)
		}
		if root != "" {
			for _, f := range selected {
				fmt.Println(filepath.Join(root, f))
			}
		} else {
			for _, f := range selected {
				fmt.Println(f)
			}

		}
	}
}

type vimTapiCall struct {
	RootDir   string `json:"root_dir"`
	Filename  string `json:"filename"`
	Fullpath  string `json:"fullpath"`
	ActionKey string `json:"action_key"`
}

func newVimTapiCall(rootDir, filename, actionKey string) *vimTapiCall {
	fullpath := filename
	if !filepath.IsAbs(filename) {
		fullpath = filepath.Join(rootDir, filename)
	}
	return &vimTapiCall{RootDir: rootDir, Filename: filename, Fullpath: fullpath, ActionKey: actionKey}
}
