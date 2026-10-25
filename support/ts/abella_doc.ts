// Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
// Copyright (C) 2023  Inria (Institut National de Recherche
//                     en Informatique et en Automatique)
// See LICENSE for licensing details.

const htmlEscapes: Record<string, string> = {
  "&": "&amp;",
  "<": "&lt;",
  ">": "&gt;",
  '"': "&quot;",
  "'": "&#39;",
};

function escapeHtml(txt: string): string {
  return txt.replace(/[&<>"']/g, (ch) => htmlEscapes[ch]);
}

type RexHandler = {
  rex: RegExp;
  cls: string;
};

const rexHandlers: Array<RexHandler> = [
  {
    // op_re
    rex: /(:[:=-]?|=(?:&gt;)?|\|-|-&gt;|\\\/?|\/\\|\{|\})/g,
    cls: "s-op",
  },
  {
    // type_re
    rex: /\b(olist|prop|o)\b/g,
    cls: "s-ty",
  },
  {
    // term_re
    rex: /\b(forall|exists|nabla|pi|sigma)\b/g,
    cls: "s-tm",
  },
];

function fontify(txt: string): string {
  txt = escapeHtml(txt);
  rexHandlers.forEach((hnd) => {
    txt = txt.replaceAll(hnd.rex, `<span class="${hnd.cls}">$1</span>`);
  });
  return txt;
}

type SequentObj = {
  vars: [string, string][];
  hyps: [string, string][];
  goal: string;
  more: number;
  name?: string;
}

function bg(count: number): string {
  return (count & 1) === 0 ? "rl-even" : "rl-odd";
}

function sequentToString(obj: SequentObj, doInsts?: boolean): string {
  let repr = '<div class="rl">';
  if (obj.name)
    repr += `<div><span class="rl-name">Subgoal ${obj.name}</span></div>`;
  let count = 0;
  if (obj.vars && obj.vars.length > 0) {
    const vars: string[] = [];
    const insts: [string, string][] = [];
    obj.vars.forEach((v) => {
      if (v[1]) insts.push(v);
      else vars.push(v[0]);
    });
    if (vars.length)
      repr += `<div class="${bg(count++)}"><code>Variables: ${vars.join(" ")}</code></div>`;
    if (doInsts)
      insts.forEach((v) => {
        repr += `<div class="${bg(count++)}"><code>  ${v[0]} &larr; ${v[1]}</code></div>`;
      });
  }
  obj.hyps.forEach((h) => {
    repr += `<div class="${bg(count++)}"><code><span class="rl-hyp">${h[0]}</span>: ${fontify(h[1])}</code></div>`;
  });
  repr += '<div class="rl-line"></div>';
  repr += `<div>&nbsp;<code>${fontify(obj.goal)}</code></div>`;
  if (obj.more > 0)
    repr += `<div class="rl-more">(+ ${obj.more} more subgoal${obj.more > 1 ? "s" : ""})</div>`;
  repr += '</div>';
  return repr;
}

function isPresent<A>(arg: A | null | undefined): A {
  if (arg === undefined || arg === null) throw new Error("Bug: isPresent()");
  return arg;
}

class Content {
  readonly source: string;
  marks: Array<[number, string]>;
  private dirty: boolean;

  constructor(source: string) {
    this.source = source;
    this.marks = new Array();
    this.dirty = false;
  }

  addMark(pos: number, thing: string) {
    if (pos < 0 || pos > this.source.length) {
      throw new Error(`bug: Content.addMark(${pos}, ${thing}, limit=${this.source.length})`);
      // console.log(`bug: Content.addMark(${pos}, ${thing}, limit=${this.source.length})`);
      // return;
    }
    this.marks.push([pos, thing]);
    this.dirty = true;          // [HACK] optimizable?
  }

  fontify(start: number, stop: number, rex: RegExp, cls: string) {
    if (start < 0 || start > stop || stop > this.source.length) {
      throw new Error(`bug: Content.fontify(${start}, ${stop}, ..., ${cls})`);
      // console.log(`bug: Content.fontify(${start}, ${stop}, ..., ${cls})`);
      // return;
    }
    const extract = this.source.slice(start, stop);
    for (let match of extract.matchAll(rex)) {
      const matchStart = start + isPresent(match.index);
      const matchStop = matchStart + match[0].length;
      if (matchStop > stop) continue;
      this.addMark(matchStart, `<span class="${cls}">`);
      this.addMark(matchStop, `</span>`);
    }
  }

  toString(): string {
    if (this.dirty) {
      this.marks.sort((a, b) => a[0] - b[0]);
      this.dirty = false;
    }
    const marks = this.marks.values();
    let result = "";
    let curPos = 0;
    while (curPos < this.source.length) {
      const next = marks.next();
      if (next.done) break;
      const [nextMarkPos, nextMark] = next.value;
      if (nextMarkPos < curPos)
        throw new Error(`bug: Content.toString(curPos = ${curPos}, nextMarkPos = ${nextMarkPos})`);
      result += escapeHtml(this.source.slice(curPos, nextMarkPos));
      curPos = nextMarkPos;
      result += nextMark;
    }
    if (curPos < this.source.length)
      result += escapeHtml(this.source.slice(curPos, this.source.length));
    return result;
  }
}

const opRex = /(:[:=-]?|=(?:>)?|\|-|->|\\\/?|\/\\|\{|\}|;|\.)/g;
const typeRex = /\b(olist|prop|o)\b/g;
const termRex = /\b(forall|exists|nabla|pi|sigma|sig|module|end)\b/g;
const topBuiltRex = /\b(Import|Specification|Query|Set|Show|Close)\b/g;
const topCmdRex = /\b((?:Co)?Define|Theorem|Split|by|Kind|Type|Suspend)\b/g;
const proofCmdRex = /\b(abbrev|all|apply|assert|backchain|case|clear|(?:co)?induction|compute|cut|inst|intros|keep|left|monotone|on|permute|rename|right|search|split(?:\*)?|to|unabbrev|unfold|with|witness)\b/g;
const proofSpecRex = /\b(skip|undo|abort)\b/g;
const sigRex = /\b(type|kind)\b/g;

const do_expand = "[expand proof]";
const do_collapse = "[collapse proof]";

function getBox(boxId: string): HTMLDivElement {
  const box = document.getElementById(boxId);
  if (!box) throw new Error(`Bug: cannot find #${boxId}`);
  if (box.tagName !== "DIV") throw new Error(`Bug: #${boxId} is a <${box.tagName}>, not a <div>`);
  return box as HTMLDivElement;
}

const xIcon = `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20" fill="currentColor">
  <path d="M6.28 5.22a.75.75 0 00-1.06 1.06L8.94 10l-3.72 3.72a.75.75 0 101.06 1.06L10 11.06l3.72 3.72a.75.75 0 101.06-1.06L11.06 10l3.72-3.72a.75.75 0 00-1.06-1.06L10 8.94 6.28 5.22z" />
</svg>`;

class FocusDialog {
  readonly dialog: HTMLDialogElement;
  readonly content: HTMLDivElement;

  show(html: string) {
    this.content.innerHTML = html;
    if (!this.dialog.open) this.dialog.showModal();
  }

  close() {
    if (this.dialog.open) this.dialog.close();
  }

  constructor() {
    this.dialog = document.createElement("dialog");
    this.dialog.classList.add("focusbox");
    const inner = document.createElement("div");
    inner.classList.add("focusbox-inner");
    const btnClose = document.createElement("button");
    btnClose.type = "button";
    btnClose.classList.add("focusbox-close");
    btnClose.setAttribute("aria-label", "Close");
    btnClose.innerHTML = xIcon;
    btnClose.addEventListener("click", () => this.close());
    this.content = document.createElement("div");
    this.content.classList.add("focusbox-content");
    inner.append(btnClose, this.content);
    this.dialog.append(inner);
    this.dialog.addEventListener("click", (ev) => {
      if (ev.target === this.dialog) this.close();
    });
    this.dialog.addEventListener("close", () => {
      this.content.replaceChildren();
    });
    document.body.append(this.dialog);
  }
}

async function loadModule(boxId: string, thmContents: string, thmJson: any[]) {
  const focusDialog = new FocusDialog();
  const thmBox = getBox(boxId);
  // get data
  const thmText = new Content(thmContents);
  const runData = thmJson;
  // map data to chunks
  const chunkMap = new Map<number, any>();
  runData.forEach((elm) => {
    if (elm.id === undefined) return;
    chunkMap.set(elm.id, elm);
  });
  // markup source into chunk divs
  runData.forEach((elm) => {
    if (elm.type === "top_command" || elm.type === "proof_command") {
      const [start, , , stop, , ] = elm.range;
      thmText.addMark(start, `<div id="chunk-${elm.id}" class="ab-command">`);
      thmText.addMark(stop, '</div>');
      thmText.fontify(start, stop, opRex, "s-op");
      thmText.fontify(start, stop, typeRex, "s-ty");
      thmText.fontify(start, stop, termRex, "s-tm");
      if (elm.type === "top_command") {
        thmText.fontify(start, stop, topBuiltRex, "s-tb");
        thmText.fontify(start, stop, topCmdRex, "s-tc");
      }
      if (elm.type === "proof_command") {
        thmText.fontify(start, stop, proofCmdRex, "s-pc");
        thmText.fontify(start, stop, proofSpecRex, "s-ps");
      }
      elm.command = escapeHtml(thmText.source.slice(start, stop));
    } else if (elm.type === "link") {
      const [start, , , stop, , ] = elm.source;
      thmText.addMark(start + 1, `<a href="/${elm.url}" class="ln">`);
      thmText.addMark(stop - 1, '</a>');
    }
  });
  // insert proof begin/end tokens
  runData.forEach((elm) => {
    if (elm.type === "proof_command") {
      const stop = elm.range[3];
      const thmElm = chunkMap.get(elm.thm_id);
      if (!thmElm) throw new Error(`Bug: can't find ${elm.id} -> ${elm.thm_id}`);
      thmElm.proofStop = Math.max(stop, thmElm.proofStop ?? stop);
    }
  });
  runData.forEach((elm) => {
    if (elm.type === "top_command") {
      if (elm.proofStop) {
        thmText.addMark(elm.range[3], '<div class="ab-proof">');
        thmText.addMark(elm.proofStop, '</div>');
      }
    }
  });
  // render text
  thmBox.innerHTML = thmText.toString();
  // create the buttons
  thmBox.querySelectorAll("div.ab-proof").forEach((el) => {
    const proofEl = el as HTMLElement;
    for (let child = proofEl.firstChild;
         child != null && child.nodeType === Node.TEXT_NODE;
         child = proofEl.firstChild)
      proofEl.before(child);
    const btn = document.createElement("button");
    btn.type = "button";
    btn.classList.add("proof-toggle");
    btn.textContent = do_expand;
    const setExpanded = (expanded: boolean) => {
      btn.dataset.state = expanded ? "E" : "C";
      btn.setAttribute("aria-expanded", String(expanded));
      btn.textContent = expanded ? do_collapse : do_expand;
      proofEl.hidden = !expanded;
    };
    btn.addEventListener("click", () => {
      setExpanded(btn.dataset.state !== "E");
    });
    proofEl.before(btn);
    proofEl.before(document.createElement("br"));
    setExpanded(false);
  });
  // create the floats
  runData.forEach((elm) => {
    elm.float = "";
    if (elm.type === "top_command" || elm.type === "proof_command") {
      if (elm.type === "top_command") {
        // elm.float += `<div class="ab-int"><span class="ab-pr">Abella &lt;</span> <strong>${elm.command}</strong></div>`;
      } else {
        const startSeq = elm.start_state as SequentObj;
        const endSeq = elm.end_state as SequentObj | undefined;
        elm.float += sequentToString(startSeq);
        elm.theorem = escapeHtml(elm.theorem);
        elm.float += `<div class="ab-int"><span class="ab-pr">${elm.theorem} &lt;</span> <strong>${elm.command}</strong></div>`;
        if (endSeq) elm.float += sequentToString(endSeq);
      }
    }
  });
  // add system messages to floats
  let floatDest : any | undefined = undefined;
  runData.forEach((elm) => {
    if (elm.type === "system_message" && floatDest) {
      // [HACK] below, if happens, is possible Abella bug; skip
      if (floatDest.float === undefined) return;
      elm.message = escapeHtml(elm.message);
      floatDest.float += `<div class="ab-sys">${elm.message}</div>`;
    }
    if (elm.type === "top_command" || elm.type === "proof_command")
      floatDest = elm;
  });
  // link the floats
  runData.forEach((elm) => {
    if (elm.float) {
      const targetChunk = document.getElementById(`chunk-${elm.id}`);
      if (!targetChunk) {
        console.log(`Bug: could not find chunk #${elm.id}`);
        return;
      }
      const float = document.createElement("div");
      float.classList.add("float");
      float.innerHTML = `<div class="float-container">${elm.float}</div>`;
      targetChunk.addEventListener("mousemove", () => {
        float.dataset.visible = "true";
        float.style.transform = "";
        const flRect = float.getBoundingClientRect();
        const flWidth = Math.max(flRect.width, 1);
        const flHeight = Math.max(flRect.height, 1);
        const wWidth = window.innerWidth, wHeight = window.innerHeight;
        const proofCommandRect = targetChunk.getBoundingClientRect();
        // Tuck the shared border under the command's opaque tab background
        // so the tab and the float do not show a double edge.
        let yscale = 1;
        if (proofCommandRect.bottom + flHeight <= wHeight) {
          // below command
          targetChunk.dataset.floatSide = "below";
          float.style.top = `${proofCommandRect.bottom - 1}px`;
        } else if (proofCommandRect.top - flHeight >= 0) {
          // above command
          targetChunk.dataset.floatSide = "above";
          float.style.top = `${proofCommandRect.top - flHeight + 1}px`;
        } else if (proofCommandRect.top > wHeight - proofCommandRect.bottom) {
          // above command scaled
          targetChunk.dataset.floatSide = "above";
          const maxHeight = proofCommandRect.top;
          yscale = maxHeight / flHeight;
          float.style.top = "1px";
          float.style.transform = `scale(${yscale})`;
        } else {
          // below command scaled
          targetChunk.dataset.floatSide = "below";
          const maxHeight = Math.max(wHeight - proofCommandRect.bottom, 1);
          yscale = maxHeight / flHeight;
          float.style.top = `${proofCommandRect.bottom - 1}px`;
          float.style.transform = `scale(${yscale})`;
        }
        if (proofCommandRect.left + flWidth * yscale <= wWidth)
          // left-adjusted with command
          float.style.left = `${proofCommandRect.left}px`;
        else
          // flush right
          float.style.left = `${Math.max(wWidth - flWidth * yscale, 0)}px`;
      });
      targetChunk.addEventListener("mouseleave", () => {
        delete float.dataset.visible;
      });
      targetChunk.addEventListener("click", (ev) => {
        if (ev.target instanceof Element && ev.target.closest("a")) return;
        delete float.dataset.visible;
        focusDialog.show(float.innerHTML);
      });
      document.body.append(float);
    }
  });
  const btnExpandAll = document.createElement("button");
  btnExpandAll.type = "button";
  btnExpandAll.classList.add("proof-toggle");
  btnExpandAll.textContent = "[expand all proofs]";
  btnExpandAll.addEventListener("click", () => {
    thmBox.querySelectorAll<HTMLButtonElement>(
      'button.proof-toggle[data-state="C"]')
      .forEach((el) => el.click());
  });
  const btnCollapseAll = document.createElement("button");
  btnCollapseAll.type = "button";
  btnCollapseAll.classList.add("proof-toggle");
  btnCollapseAll.textContent = "[collapse all proofs]";
  btnCollapseAll.addEventListener("click", () => {
    thmBox.querySelectorAll<HTMLButtonElement>(
      'button.proof-toggle[data-state="E"]')
      .forEach((el) => el.click());
  });
  thmBox.insertAdjacentText("afterbegin", "\n");
  thmBox.insertAdjacentElement("afterbegin", btnCollapseAll);
  thmBox.insertAdjacentText("afterbegin", " ");
  thmBox.insertAdjacentElement("afterbegin", btnExpandAll);
}

async function loadLP(sigBoxId: string, sigContents: string, sigJson: any[],
                      modBoxId: string, modContents: string, modJson: any[]) {
  const sigBox = getBox(sigBoxId);
  const modBox = getBox(modBoxId);
  // get data
  const sigText = new Content(sigContents);
  const sigData = sigJson;
  const modText = new Content(modContents);
  const modData = modJson;
  sigData.forEach((annot) => {
    if (annot.kind === "name") {
      sigText.addMark(annot.range[0], '<span class="s-op">');
      sigText.addMark(annot.range[1], '</span>');
    } else if (annot.kind === "accum_sig") {
      const [start, stop] = annot.range;
      const extSig = sigText.source.slice(start, stop);
      sigText.addMark(start, `<a href="./${extSig}.lp.html" class="ln">`);
      sigText.addMark(stop, '</a>');
    } else if (annot.kind === "decl") {
      const [start, stop] = annot.range;
      sigText.addMark(start, '<div class="ab-command">');
      sigText.fontify(start, stop, opRex, "s-op");
      sigText.fontify(start, stop, typeRex, "s-ty");
      sigText.fontify(start, stop, termRex, "s-tm");
      sigText.fontify(start, stop, sigRex, "s-op");
      sigText.addMark(stop, '</div>');
    }
  });
  sigBox.innerHTML = sigText.toString();
  modData.forEach((annot) => {
    if (annot.kind === "name") {
      modText.addMark(annot.range[0], '<span class="s-op">');
      modText.addMark(annot.range[1], '</span>');
    } else if (annot.kind === "accum") {
      const [start, stop] = annot.range;
      const extMod = modText.source.slice(start, stop);
      modText.addMark(start, `<a href="./${extMod}.lp.html" class="ln">`);
      modText.addMark(stop, '</a>');
    } else if (annot.kind === "clause") {
      const [start, stop] = annot.range;
      modText.addMark(start, '<div class="ab-command">');
      modText.fontify(start, stop, opRex, "s-op");
      modText.fontify(start, stop, typeRex, "s-ty");
      modText.fontify(start, stop, termRex, "s-tm");
      modText.fontify(start, stop, sigRex, "s-tc");
      modText.addMark(stop, '</div>');
    }
  });
  modBox.innerHTML = modText.toString();
}

(window as any)["loadModule"] = loadModule;
(window as any)["loadLP"] = loadLP;
