function noop() { }
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert(target, node, anchor) {
    target.insertBefore(node, anchor || null);
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function find_comment(nodes, text, start) {
    for (let i = start; i < nodes.length; i += 1) {
        const node = nodes[i];
        if (node.nodeType === 8 /* comment node */ && node.textContent.trim() === text) {
            return i;
        }
    }
    return nodes.length;
}
function claim_html_tag(nodes, is_svg) {
    // find html opening tag
    const start_index = find_comment(nodes, 'HTML_TAG_START', 0);
    const end_index = find_comment(nodes, 'HTML_TAG_END', start_index);
    if (start_index === end_index) {
        return new HtmlTagHydration(undefined, is_svg);
    }
    init_claim_info(nodes);
    const html_tag_nodes = nodes.splice(start_index, end_index - start_index + 1);
    detach(html_tag_nodes[0]);
    detach(html_tag_nodes[html_tag_nodes.length - 1]);
    const claimed_nodes = html_tag_nodes.slice(1, html_tag_nodes.length - 1);
    for (const n of claimed_nodes) {
        n.claim_order = nodes.claim_info.total_claimed;
        nodes.claim_info.total_claimed += 1;
    }
    return new HtmlTagHydration(claimed_nodes, is_svg);
}
function set_data(text, data) {
    data = '' + data;
    if (text.wholeText !== data)
        text.data = data;
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}
class HtmlTag {
    constructor(is_svg = false) {
        this.is_svg = false;
        this.is_svg = is_svg;
        this.e = this.n = null;
    }
    c(html) {
        this.h(html);
    }
    m(html, target, anchor = null) {
        if (!this.e) {
            if (this.is_svg)
                this.e = svg_element(target.nodeName);
            else
                this.e = element(target.nodeName);
            this.t = target;
            this.c(html);
        }
        this.i(anchor);
    }
    h(html) {
        this.e.innerHTML = html;
        this.n = Array.from(this.e.childNodes);
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert(this.t, this.n[i], anchor);
        }
    }
    p(html) {
        this.d();
        this.h(html);
        this.i(this.a);
    }
    d() {
        this.n.forEach(detach);
    }
}
class HtmlTagHydration extends HtmlTag {
    constructor(claimed_nodes, is_svg = false) {
        super(is_svg);
        this.e = this.n = null;
        this.l = claimed_nodes;
    }
    c(html) {
        if (this.l) {
            this.n = this.l;
        }
        else {
            super.c(html);
        }
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert_hydration(this.t, this.n[i], anchor);
        }
    }
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
const render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.55.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let title_value;
	let meta2;
	let meta3;
	let meta4;
	let meta5;
	let meta6;
	let meta7;
	let meta8;
	let meta9;
	let meta10;
	let meta11;
	let meta12;
	let meta13;
	let link;
	let style;
	let t;
	document.title = title_value = /*seo_title*/ ctx[0];

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			meta2 = element("meta");
			meta3 = element("meta");
			meta4 = element("meta");
			meta5 = element("meta");
			meta6 = element("meta");
			meta7 = element("meta");
			meta8 = element("meta");
			meta9 = element("meta");
			meta10 = element("meta");
			meta11 = element("meta");
			meta12 = element("meta");
			meta13 = element("meta");
			link = element("link");
			style = element("style");
			t = text("@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\n@font-face {\n\tfont-family: 'Bodoni SvtyTwo ITC TT';\n\tsrc: url('https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/fonts/BodoniSvtyTwoITCTTBook.woff2') format('woff2');\n\tfont-weight: normal;\n\tfont-style: normal;\n\tfont-display: swap;\n}\n\n@font-face {\n    font-family: 'Darker Grotesque Regular';\n\tsrc: url('https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/fonts/DarkerGrotesque-Regular.woff2') format('woff2');\n    font-style: normal;\n    font-weight: normal;\n    font-display: swap;\n}\n    \n\n@font-face {\n    font-family: 'Darker Grotesque SemiBold';\n\tsrc: url('https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/fonts/DarkerGrotesque-SemiBold.woff2') format('woff2');\n    font-style: normal;\n    font-weight: normal;\n    font-display: swap;\n}\n\nhtml {\n\n  /* Colors */\n  --color-accent: #ffcc00;\n\n  /* Default property values */\n  --background: white;\n  --color: #222;\n  --padding: 2rem; \n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2); \n  --border-radius: 8px; \n  --max-width: 1400px;\n  --border-color: #CBCACE;\n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color,\n      var(--transition-time) border-color,\n        var(--transition-time) text-decoration-color,\n          var(--transition-time) box-shadow, var(--transtion-time) transform;\n}\n\n#page {\n  font-family: 'Darker Grotesque Regular', sans-serif;\n  color: var(--color);\n  line-height: 1.6; \n  font-size: 1.2rem;\n  background: var(--background);\n}\n\nh1, h2 {\n  font-family: 'Bodoni SvtyTwo ITC TT', serif;\n}\n\n.section .content {\n  max-width: var(--max-width);\n  margin: 0 auto;\n  padding: var(--padding);\n}\n\n.section .content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.section .content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n  }\n\n.section .content a {\n    text-decoration: underline;\n  }\n\n.section .content h1 {\n    font-size: 3rem;\n    font-weight: 700;\n    margin-bottom: 1rem;\n  }\n\n.section .content h2 {\n    font-size: 2.25rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n\n.section .content h3 {\n    font-size: 1.75rem; \n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n\n.section .content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.section .content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.section .content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.section-container {\n  max-width: var(--max-width, 1400px);\n  margin: 0 auto;\n  padding: 3rem var(--padding, 1rem); \n}\n\n.heading {\n  font-size: 3rem;\n  line-height: 1;\n  font-weight: 700;\n  margin: 0;\n}\n\n.button {\n  color: var(--color);\n  cursor: pointer;\n  background: var(--color-accent);\n  border-radius: 5px;\n  padding: 8px 20px;\n  transition: var(--transition);\n}\n\n.button:hover {\n    color: var(--color-accent);\n    background: var(--color);\n  }\n\n.button.inverted {\n    background: transparent; \n    color: var(--color-accent); \n    border: 2px solid var(--color-accent);\n  }\n\narticle p {\n    padding-bottom: 0.5rem;\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1t6wdq2', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			meta2 = claim_element(head_nodes, "META", { name: true, content: true });
			meta3 = claim_element(head_nodes, "META", { name: true, content: true });
			meta4 = claim_element(head_nodes, "META", { name: true, content: true });
			meta5 = claim_element(head_nodes, "META", { name: true, content: true });
			meta6 = claim_element(head_nodes, "META", { name: true, content: true });
			meta7 = claim_element(head_nodes, "META", { name: true, content: true });
			meta8 = claim_element(head_nodes, "META", { property: true, content: true });
			meta9 = claim_element(head_nodes, "META", { property: true, content: true });
			meta10 = claim_element(head_nodes, "META", { property: true, content: true });
			meta11 = claim_element(head_nodes, "META", { property: true, content: true });
			meta12 = claim_element(head_nodes, "META", { property: true, content: true });
			meta13 = claim_element(head_nodes, "META", { property: true, content: true });
			link = claim_element(head_nodes, "LINK", { rel: true, href: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\n@font-face {\n\tfont-family: 'Bodoni SvtyTwo ITC TT';\n\tsrc: url('https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/fonts/BodoniSvtyTwoITCTTBook.woff2') format('woff2');\n\tfont-weight: normal;\n\tfont-style: normal;\n\tfont-display: swap;\n}\n\n@font-face {\n    font-family: 'Darker Grotesque Regular';\n\tsrc: url('https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/fonts/DarkerGrotesque-Regular.woff2') format('woff2');\n    font-style: normal;\n    font-weight: normal;\n    font-display: swap;\n}\n    \n\n@font-face {\n    font-family: 'Darker Grotesque SemiBold';\n\tsrc: url('https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/fonts/DarkerGrotesque-SemiBold.woff2') format('woff2');\n    font-style: normal;\n    font-weight: normal;\n    font-display: swap;\n}\n\nhtml {\n\n  /* Colors */\n  --color-accent: #ffcc00;\n\n  /* Default property values */\n  --background: white;\n  --color: #222;\n  --padding: 2rem; \n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2); \n  --border-radius: 8px; \n  --max-width: 1400px;\n  --border-color: #CBCACE;\n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color,\n      var(--transition-time) border-color,\n        var(--transition-time) text-decoration-color,\n          var(--transition-time) box-shadow, var(--transtion-time) transform;\n}\n\n#page {\n  font-family: 'Darker Grotesque Regular', sans-serif;\n  color: var(--color);\n  line-height: 1.6; \n  font-size: 1.2rem;\n  background: var(--background);\n}\n\nh1, h2 {\n  font-family: 'Bodoni SvtyTwo ITC TT', serif;\n}\n\n.section .content {\n  max-width: var(--max-width);\n  margin: 0 auto;\n  padding: var(--padding);\n}\n\n.section .content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.section .content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n  }\n\n.section .content a {\n    text-decoration: underline;\n  }\n\n.section .content h1 {\n    font-size: 3rem;\n    font-weight: 700;\n    margin-bottom: 1rem;\n  }\n\n.section .content h2 {\n    font-size: 2.25rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n\n.section .content h3 {\n    font-size: 1.75rem; \n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n\n.section .content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.section .content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.section .content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.section-container {\n  max-width: var(--max-width, 1400px);\n  margin: 0 auto;\n  padding: 3rem var(--padding, 1rem); \n}\n\n.heading {\n  font-size: 3rem;\n  line-height: 1;\n  font-weight: 700;\n  margin: 0;\n}\n\n.button {\n  color: var(--color);\n  cursor: pointer;\n  background: var(--color-accent);\n  border-radius: 5px;\n  padding: 8px 20px;\n  transition: var(--transition);\n}\n\n.button:hover {\n    color: var(--color-accent);\n    background: var(--color);\n  }\n\n.button.inverted {\n    background: transparent; \n    color: var(--color-accent); \n    border: 2px solid var(--color-accent);\n  }\n\narticle p {\n    padding-bottom: 0.5rem;\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(meta2, "name", "description");
			attr(meta2, "content", /*seo_description*/ ctx[1]);
			attr(meta3, "name", "twitter:title");
			attr(meta3, "content", /*seo_title*/ ctx[0]);
			attr(meta4, "name", "twitter:site");
			attr(meta4, "content", "@foteini_chalkia");
			attr(meta5, "name", "twitter:handle");
			attr(meta5, "content", "@foteini_chalkia");
			attr(meta6, "name", "twitter:cardType");
			attr(meta6, "content", "summary");
			attr(meta7, "name", "twitter:description");
			attr(meta7, "content", /*seo_description*/ ctx[1]);
			attr(meta8, "property", "og:type");
			attr(meta8, "content", "website");
			attr(meta9, "property", "og:title");
			attr(meta9, "content", /*seo_title*/ ctx[0]);
			attr(meta10, "property", "og:description");
			attr(meta10, "content", /*seo_description*/ ctx[1]);
			attr(meta11, "property", "og:url");
			attr(meta11, "content", "https://www.chalkia.com/");
			attr(meta12, "property", "og:locale");
			attr(meta12, "content", "en");
			attr(meta13, "property", "og:site_name");
			attr(meta13, "content", "Bridal & Haute Coutoure | Foteini Chalkia");
			attr(link, "rel", "icon");
			attr(link, "href", "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/assets/favicon.png");
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, meta2);
			append_hydration(document.head, meta3);
			append_hydration(document.head, meta4);
			append_hydration(document.head, meta5);
			append_hydration(document.head, meta6);
			append_hydration(document.head, meta7);
			append_hydration(document.head, meta8);
			append_hydration(document.head, meta9);
			append_hydration(document.head, meta10);
			append_hydration(document.head, meta11);
			append_hydration(document.head, meta12);
			append_hydration(document.head, meta13);
			append_hydration(document.head, link);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*seo_title*/ 1 && title_value !== (title_value = /*seo_title*/ ctx[0])) {
				document.title = title_value;
			}

			if (dirty & /*seo_description*/ 2) {
				attr(meta2, "content", /*seo_description*/ ctx[1]);
			}

			if (dirty & /*seo_title*/ 1) {
				attr(meta3, "content", /*seo_title*/ ctx[0]);
			}

			if (dirty & /*seo_description*/ 2) {
				attr(meta7, "content", /*seo_description*/ ctx[1]);
			}

			if (dirty & /*seo_title*/ 1) {
				attr(meta9, "content", /*seo_title*/ ctx[0]);
			}

			if (dirty & /*seo_description*/ 2) {
				attr(meta10, "content", /*seo_description*/ ctx[1]);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(meta2);
			detach(meta3);
			detach(meta4);
			detach(meta5);
			detach(meta6);
			detach(meta7);
			detach(meta8);
			detach(meta9);
			detach(meta10);
			detach(meta11);
			detach(meta12);
			detach(meta13);
			detach(link);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { social } = $$props;
	let { na } = $$props;
	let { nav } = $$props;
	let { a } = $$props;
	let { add } = $$props;
	let { addre } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;

	$$self.$$set = $$props => {
		if ('social' in $$props) $$invalidate(2, social = $$props.social);
		if ('na' in $$props) $$invalidate(3, na = $$props.na);
		if ('nav' in $$props) $$invalidate(4, nav = $$props.nav);
		if ('a' in $$props) $$invalidate(5, a = $$props.a);
		if ('add' in $$props) $$invalidate(6, add = $$props.add);
		if ('addre' in $$props) $$invalidate(7, addre = $$props.addre);
		if ('address' in $$props) $$invalidate(8, address = $$props.address);
		if ('phone' in $$props) $$invalidate(9, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(10, email = $$props.email);
		if ('seo_title' in $$props) $$invalidate(0, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(1, seo_description = $$props.seo_description);
	};

	return [
		seo_title,
		seo_description,
		social,
		na,
		nav,
		a,
		add,
		addre,
		address,
		phone,
		email
	];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			social: 2,
			na: 3,
			nav: 4,
			a: 5,
			add: 6,
			addre: 7,
			address: 8,
			phone: 9,
			email: 10,
			seo_title: 0,
			seo_description: 1
		});
	}
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const result = {
    attributes: {
      width: width.toString(),
      height: height.toString(),
      viewBox: box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString()
    },
    body
  };
  return result;
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + "$3");
  });
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToURL(svg) {
  return 'url("data:image/svg+xml,' + encodeSVGforURL(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url,
    width: fixSize(renderAttribs.width),
    height: fixSize(renderAttribs.height),
    ...commonProps,
    ...useMask ? monotoneProps : coloredProps
  };
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.55.0 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.55.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[16] = list[i].link;
	child_ctx[17] = list[i].title;
	child_ctx[18] = list[i].icon;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[16] = list[i].link;
	return child_ctx;
}

// (132:8) {:else}
function create_else_block$1(ctx) {
	let icon;
	let current;

	icon = new Component$1({
			props: { icon: "line-md:menu", height: "32" }
		});

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

// (130:37) 
function create_if_block_1$1(ctx) {
	let icon;
	let current;

	icon = new Component$1({
			props: {
				icon: "line-md:close-to-menu-transition",
				height: "32"
			}
		});

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

// (128:8) {#if mobileMenu===true}
function create_if_block$1(ctx) {
	let icon;
	let current;

	icon = new Component$1({
			props: {
				icon: "line-md:menu-to-close-transition",
				height: "32"
			}
		});

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

// (137:8) {#each nav as {link}}
function create_each_block_1(ctx) {
	let a_1;
	let h3;
	let t_value = /*link*/ ctx[16].label + "";
	let t;
	let a_1_href_value;

	return {
		c() {
			a_1 = element("a");
			h3 = element("h3");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a_1 = claim_element(nodes, "A", { href: true, class: true });
			var a_1_nodes = children(a_1);
			h3 = claim_element(a_1_nodes, "H3", {});
			var h3_nodes = children(h3);
			t = claim_text(h3_nodes, t_value);
			h3_nodes.forEach(detach);
			a_1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a_1, "href", a_1_href_value = /*link*/ ctx[16].url);
			attr(a_1, "class", "svelte-55bh7e");
			toggle_class(a_1, "active", /*link*/ ctx[16].active === true);
		},
		m(target, anchor) {
			insert_hydration(target, a_1, anchor);
			append_hydration(a_1, h3);
			append_hydration(h3, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 2 && t_value !== (t_value = /*link*/ ctx[16].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 2 && a_1_href_value !== (a_1_href_value = /*link*/ ctx[16].url)) {
				attr(a_1, "href", a_1_href_value);
			}

			if (dirty & /*nav*/ 2) {
				toggle_class(a_1, "active", /*link*/ ctx[16].active === true);
			}
		},
		d(detaching) {
			if (detaching) detach(a_1);
		}
	};
}

// (146:6) {#each social as {link, title, icon}}
function create_each_block(ctx) {
	let a_1;
	let icon;
	let t;
	let a_1_href_value;
	let a_1_title_value;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[18] } });

	return {
		c() {
			a_1 = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			a_1 = claim_element(nodes, "A", { href: true, title: true, class: true });
			var a_1_nodes = children(a_1);
			claim_component(icon.$$.fragment, a_1_nodes);
			t = claim_space(a_1_nodes);
			a_1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a_1, "href", a_1_href_value = /*link*/ ctx[16]);
			attr(a_1, "title", a_1_title_value = /*title*/ ctx[17]);
			attr(a_1, "class", "svelte-55bh7e");
		},
		m(target, anchor) {
			insert_hydration(target, a_1, anchor);
			mount_component(icon, a_1, null);
			append_hydration(a_1, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social*/ 1) icon_changes.icon = /*icon*/ ctx[18];
			icon.$set(icon_changes);

			if (!current || dirty & /*social*/ 1 && a_1_href_value !== (a_1_href_value = /*link*/ ctx[16])) {
				attr(a_1, "href", a_1_href_value);
			}

			if (!current || dirty & /*social*/ 1 && a_1_title_value !== (a_1_title_value = /*title*/ ctx[17])) {
				attr(a_1, "title", a_1_title_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a_1);
			destroy_component(icon);
		}
	};
}

function create_fragment$2(ctx) {
	let div7;
	let div6;
	let div5;
	let div4;
	let div1;
	let button;
	let current_block_type_index;
	let if_block;
	let t0;
	let div0;
	let t1;
	let div2;
	let a_1;
	let t2;
	let t3;
	let div3;
	let current;
	let mounted;
	let dispose;
	const if_block_creators = [create_if_block$1, create_if_block_1$1, create_else_block$1];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (/*mobileMenu*/ ctx[2] === true) return 0;
		if (/*mobileMenu*/ ctx[2] === false) return 1;
		return 2;
	}

	current_block_type_index = select_block_type(ctx);
	if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
	let each_value_1 = /*nav*/ ctx[1];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	let each_value = /*social*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div7 = element("div");
			div6 = element("div");
			div5 = element("div");
			div4 = element("div");
			div1 = element("div");
			button = element("button");
			if_block.c();
			t0 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t1 = space();
			div2 = element("div");
			a_1 = element("a");
			t2 = text("CHALKIA");
			t3 = space();
			div3 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div7 = claim_element(nodes, "DIV", { class: true, id: true });
			var div7_nodes = children(div7);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { id: true, class: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div1 = claim_element(div4_nodes, "DIV", { id: true, class: true });
			var div1_nodes = children(div1);
			button = claim_element(div1_nodes, "BUTTON", { title: true, class: true });
			var button_nodes = children(button);
			if_block.l(button_nodes);
			button_nodes.forEach(detach);
			t0 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { id: true, class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t1 = claim_space(div4_nodes);
			div2 = claim_element(div4_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			a_1 = claim_element(div2_nodes, "A", { href: true, class: true });
			var a_1_nodes = children(a_1);
			t2 = claim_text(a_1_nodes, "CHALKIA");
			a_1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t3 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div3_nodes);
			}

			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "title", "Menu");
			attr(button, "class", "svelte-55bh7e");
			toggle_class(button, "active", /*mobileMenu*/ ctx[2] === true);
			attr(div0, "id", "mobileMenuContent");
			attr(div0, "class", "svelte-55bh7e");
			toggle_class(div0, "active", /*mobileMenu*/ ctx[2] === true);
			attr(div1, "id", "mobileMenu");
			attr(div1, "class", "svelte-55bh7e");
			attr(a_1, "href", "/");
			attr(a_1, "class", "svelte-55bh7e");
			attr(div2, "class", "logo svelte-55bh7e");
			attr(div3, "class", "social svelte-55bh7e");
			attr(div4, "class", "container svelte-55bh7e");
			attr(div5, "id", "top-bar");
			attr(div5, "class", "svelte-55bh7e");
			attr(div6, "class", "component");
			attr(div7, "class", "section has-component");
			attr(div7, "id", "lpoea");
		},
		m(target, anchor) {
			insert_hydration(target, div7, anchor);
			append_hydration(div7, div6);
			append_hydration(div6, div5);
			append_hydration(div5, div4);
			append_hydration(div4, div1);
			append_hydration(div1, button);
			if_blocks[current_block_type_index].m(button, null);
			append_hydration(div1, t0);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].m(div0, null);
			}

			append_hydration(div4, t1);
			append_hydration(div4, div2);
			append_hydration(div2, a_1);
			append_hydration(a_1, t2);
			append_hydration(div4, t3);
			append_hydration(div4, div3);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(div3, null);
			}

			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[15]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index !== previous_block_index) {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block = if_blocks[current_block_type_index];

				if (!if_block) {
					if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block.c();
				}

				transition_in(if_block, 1);
				if_block.m(button, null);
			}

			if (!current || dirty & /*mobileMenu*/ 4) {
				toggle_class(button, "active", /*mobileMenu*/ ctx[2] === true);
			}

			if (dirty & /*nav*/ 2) {
				each_value_1 = /*nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_1(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(div0, null);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_1.length;
			}

			if (!current || dirty & /*mobileMenu*/ 4) {
				toggle_class(div0, "active", /*mobileMenu*/ ctx[2] === true);
			}

			if (dirty & /*social*/ 1) {
				each_value = /*social*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div3, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			transition_out(if_block);
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div7);
			if_blocks[current_block_type_index].d();
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { social } = $$props;
	let { na } = $$props;
	let { nav } = $$props;
	let { a } = $$props;
	let { add } = $$props;
	let { addre } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { lpoea } = $$props;
	let { ugrhc } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;
	let { ofaxo } = $$props;
	let mobileMenu;
	const click_handler = () => $$invalidate(2, mobileMenu = !mobileMenu);

	$$self.$$set = $$props => {
		if ('social' in $$props) $$invalidate(0, social = $$props.social);
		if ('na' in $$props) $$invalidate(3, na = $$props.na);
		if ('nav' in $$props) $$invalidate(1, nav = $$props.nav);
		if ('a' in $$props) $$invalidate(4, a = $$props.a);
		if ('add' in $$props) $$invalidate(5, add = $$props.add);
		if ('addre' in $$props) $$invalidate(6, addre = $$props.addre);
		if ('address' in $$props) $$invalidate(7, address = $$props.address);
		if ('phone' in $$props) $$invalidate(8, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(9, email = $$props.email);
		if ('lpoea' in $$props) $$invalidate(10, lpoea = $$props.lpoea);
		if ('ugrhc' in $$props) $$invalidate(11, ugrhc = $$props.ugrhc);
		if ('seo_title' in $$props) $$invalidate(12, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(13, seo_description = $$props.seo_description);
		if ('ofaxo' in $$props) $$invalidate(14, ofaxo = $$props.ofaxo);
	};

	return [
		social,
		nav,
		mobileMenu,
		na,
		a,
		add,
		addre,
		address,
		phone,
		email,
		lpoea,
		ugrhc,
		seo_title,
		seo_description,
		ofaxo,
		click_handler
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			social: 0,
			na: 3,
			nav: 1,
			a: 4,
			add: 5,
			addre: 6,
			address: 7,
			phone: 8,
			email: 9,
			lpoea: 10,
			ugrhc: 11,
			seo_title: 12,
			seo_description: 13,
			ofaxo: 14
		});
	}
}

/* generated by Svelte v3.55.0 */

function create_fragment$3(ctx) {
	let div1;
	let div0;
	let h1;
	let t0;
	let p0;
	let t1;
	let strong0;
	let t2;
	let t3;
	let p1;
	let t4;
	let strong1;
	let t5;
	let t6;
	let h20;
	let t7;
	let p2;
	let em0;
	let t8;
	let strong2;
	let em1;
	let t9;
	let em2;
	let t10;
	let strong3;
	let em3;
	let t11;
	let em4;
	let t12;
	let strong4;
	let em5;
	let t13;
	let em6;
	let t14;
	let strong5;
	let em7;
	let t15;
	let em8;
	let t16;
	let p3;
	let t17;
	let strong6;
	let t18;
	let t19;
	let strong7;
	let t20;
	let t21;
	let strong8;
	let t22;
	let t23;
	let strong9;
	let t24;
	let t25;
	let strong10;
	let t26;
	let t27;
	let strong11;
	let t28;
	let t29;
	let p4;
	let t30;
	let strong12;
	let t31;
	let t32;
	let strong13;
	let t33;
	let t34;
	let strong14;
	let t35;
	let t36;
	let strong15;
	let t37;
	let t38;
	let strong16;
	let t39;
	let t40;
	let strong17;
	let t41;
	let t42;
	let h21;
	let t43;
	let p5;
	let t44;
	let strong18;
	let t45;
	let t46;
	let strong19;
	let t47;
	let t48;
	let strong20;
	let t49;
	let t50;
	let h22;
	let t51;
	let p6;
	let strong21;
	let em9;
	let t52;
	let t53;
	let em10;
	let t54;
	let em11;
	let t55;
	let strong22;
	let em12;
	let t56;
	let em13;
	let t57;
	let p7;
	let t58;
	let strong23;
	let t59;
	let t60;
	let strong24;
	let t61;
	let t62;
	let p8;
	let t63;
	let strong25;
	let t64;
	let t65;
	let strong26;
	let t66;
	let t67;
	let p9;
	let t68;
	let strong27;
	let t69;
	let t70;
	let strong28;
	let t71;
	let t72;
	let strong29;
	let t73;
	let t74;
	let h23;
	let t75;
	let p10;
	let em14;
	let t76;
	let strong30;
	let em15;
	let t77;
	let em16;
	let t78;
	let strong31;
	let em17;
	let t79;
	let em18;
	let t80;
	let strong32;
	let em19;
	let t81;
	let em20;
	let t82;
	let p11;
	let strong33;
	let t83;
	let t84;
	let strong34;
	let t85;
	let t86;
	let strong35;
	let t87;
	let t88;
	let strong36;
	let t89;
	let t90;
	let p12;
	let t91;
	let strong37;
	let t92;
	let t93;
	let strong38;
	let t94;
	let t95;
	let strong39;
	let t96;
	let t97;
	let h24;
	let t98;
	let p13;
	let t99;
	let strong40;
	let t100;
	let t101;
	let strong41;
	let t102;
	let t103;
	let h30;
	let t104;
	let p14;
	let em21;
	let t105;
	let p15;
	let t106;
	let strong42;
	let t107;
	let t108;
	let strong43;
	let t109;
	let t110;
	let strong44;
	let t111;
	let t112;
	let strong45;
	let t113;
	let t114;
	let p16;
	let t115;
	let strong46;
	let t116;
	let t117;
	let strong47;
	let t118;
	let t119;
	let strong48;
	let t120;
	let t121;
	let strong49;
	let t122;
	let t123;
	let h31;
	let t124;
	let p17;
	let em22;
	let t125;
	let p18;
	let t126;
	let h32;
	let t127;
	let p19;
	let em23;
	let t128;
	let p20;
	let t129;
	let strong50;
	let t130;
	let t131;
	let strong51;
	let t132;
	let t133;
	let h25;
	let t134;
	let p21;
	let strong52;
	let t135;
	let t136;
	let strong53;
	let t137;
	let t138;
	let h26;
	let t139;
	let h33;
	let t140;
	let p22;
	let em24;
	let t141;
	let strong54;
	let em25;
	let t142;
	let em26;
	let t143;
	let p23;
	let t144;
	let strong55;
	let t145;
	let t146;
	let strong56;
	let t147;
	let t148;
	let p24;
	let strong57;
	let t149;
	let t150;
	let p25;
	let t151;
	let strong58;
	let t152;
	let t153;
	let p26;
	let t154;
	let strong59;
	let t155;
	let t156;
	let strong60;
	let t157;
	let t158;
	let strong61;
	let t159;
	let t160;
	let p27;
	let t161;
	let strong62;
	let t162;
	let t163;
	let strong63;
	let t164;
	let t165;
	let strong64;
	let t166;
	let t167;
	let strong65;
	let t168;
	let t169;
	let p28;
	let t170;
	let strong66;
	let t171;
	let t172;
	let a_1;
	let t173;
	let t174;
	let h34;
	let t175;
	let p29;
	let em27;
	let t176;
	let p30;
	let t177;
	let p31;
	let t178;
	let h27;
	let t179;
	let h35;
	let t180;
	let p32;
	let em28;
	let t181;
	let p33;
	let strong67;
	let t182;
	let t183;
	let p34;
	let t184;
	let h36;
	let t185;
	let p35;
	let em29;
	let t186;
	let p36;
	let t187;
	let ul;
	let li0;
	let p37;
	let strong68;
	let t188;
	let t189;
	let li1;
	let p38;
	let strong69;
	let t190;
	let t191;
	let li2;
	let p39;
	let strong70;
	let t192;
	let t193;
	let li3;
	let p40;
	let strong71;
	let t194;
	let t195;
	let li4;
	let p41;
	let strong72;
	let t196;
	let t197;
	let li5;
	let p42;
	let strong73;
	let t198;
	let t199;
	let p43;
	let br;
	let t200;
	let strong74;
	let t201;
	let t202;
	let strong75;
	let t203;
	let t204;
	let strong76;
	let t205;
	let t206;
	let p44;
	let t207;
	let h28;
	let t208;
	let h37;
	let t209;
	let p45;
	let em30;
	let t210;
	let p46;
	let t211;
	let strong77;
	let t212;
	let t213;
	let p47;
	let t214;
	let strong78;
	let t215;
	let t216;
	let h38;
	let t217;
	let p48;
	let em31;
	let t218;
	let p49;
	let t219;
	let strong79;
	let t220;
	let t221;
	let strong80;
	let t222;
	let t223;
	let h39;
	let t224;
	let p50;
	let em32;
	let t225;
	let p51;
	let strong81;
	let t226;
	let t227;
	let p52;
	let strong82;
	let t228;
	let t229;

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			h1 = element("h1");
			t0 = text("Privacy Policy");
			p0 = element("p");
			t1 = text("At ");
			strong0 = element("strong");
			t2 = text("“Chalkia”");
			t3 = text(", we’re committed to protecting and respecting your privacy.");
			p1 = element("p");
			t4 = text("This ");
			strong1 = element("strong");
			t5 = text("Privacy Policy");
			t6 = text(" explains when and why we collect personal information, how we use it, the conditions under which we may disclose it to others and what choices you have.");
			h20 = element("h2");
			t7 = text("Introduction");
			p2 = element("p");
			em0 = element("em");
			t8 = text("We are a company that specializes in architectural design. People use our ");
			strong2 = element("strong");
			em1 = element("em");
			t9 = text("Services");
			em2 = element("em");
			t10 = text("to get informed about our services. Our ");
			strong3 = element("strong");
			em3 = element("em");
			t11 = text("Privacy Policy");
			em4 = element("em");
			t12 = text("applies to any ");
			strong4 = element("strong");
			em5 = element("em");
			t13 = text("Visitor");
			em6 = element("em");
			t14 = text("to our ");
			strong5 = element("strong");
			em7 = element("em");
			t15 = text("Services");
			em8 = element("em");
			t16 = text(".");
			p3 = element("p");
			t17 = text("Our non-registered (");
			strong6 = element("strong");
			t18 = text("“Visitors”");
			t19 = text(") users get informed through our ");
			strong7 = element("strong");
			t20 = text("Services");
			t21 = text(". All content and data on our ");
			strong8 = element("strong");
			t22 = text("Services");
			t23 = text(" is viewable to non-registered (");
			strong9 = element("strong");
			t24 = text("“Visitors”");
			t25 = text(") users. You don’t have to be a registered user (");
			strong10 = element("strong");
			t26 = text("“Member”");
			t27 = text(") to use our ");
			strong11 = element("strong");
			t28 = text("Services");
			t29 = text(".");
			p4 = element("p");
			t30 = text("We use the term ");
			strong12 = element("strong");
			t31 = text("“Designated Countries”");
			t32 = text(" to refer to countries in the ");
			strong13 = element("strong");
			t33 = text("European Union");
			t34 = text(" (");
			strong14 = element("strong");
			t35 = text("EU");
			t36 = text("), ");
			strong15 = element("strong");
			t37 = text("European Economic Area");
			t38 = text(" (");
			strong16 = element("strong");
			t39 = text("EEA");
			t40 = text("), and ");
			strong17 = element("strong");
			t41 = text("Switzerland");
			t42 = text(".");
			h21 = element("h2");
			t43 = text("Services");
			p5 = element("p");
			t44 = text("This ");
			strong18 = element("strong");
			t45 = text("Privacy Policy");
			t46 = text(" applies to ");
			strong19 = element("strong");
			t47 = text("www.chalkia.com");
			t48 = text(" (");
			strong20 = element("strong");
			t49 = text("“Services”");
			t50 = text(").");
			h22 = element("h2");
			t51 = text("Data Controllers And Contracting Parties");
			p6 = element("p");
			strong21 = element("strong");
			em9 = element("em");
			t52 = text("“");
			t53 = text("Chalkia");
			em10 = element("em");
			t54 = text("”");
			em11 = element("em");
			t55 = text("is the controller of your personal data in connection with our ");
			strong22 = element("strong");
			em12 = element("em");
			t56 = text("Services");
			em13 = element("em");
			t57 = text("and the company’s electronic data processing system.");
			p7 = element("p");
			t58 = text("If you reside in the ");
			strong23 = element("strong");
			t59 = text("“Designated Countries”");
			t60 = text(": ");
			strong24 = element("strong");
			t61 = text("“Chalkia”");
			t62 = text(" will be the controller of your personal data provided to, or collected by or for, or processed in connection with our Services.");
			p8 = element("p");
			t63 = text("If you reside outside of the ");
			strong25 = element("strong");
			t64 = text("“Designated Countries”");
			t65 = text(": ");
			strong26 = element("strong");
			t66 = text("“Chalkia”");
			t67 = text(" will be the controller of your personal data provided to, or collected by or for, or processed in connection with, our Services.");
			p9 = element("p");
			t68 = text("As a ");
			strong27 = element("strong");
			t69 = text("Visitor");
			t70 = text(" of our ");
			strong28 = element("strong");
			t71 = text("Services");
			t72 = text(", the collection, use and sharing of your personal data is subject to this ");
			strong29 = element("strong");
			t73 = text("Privacy Policy");
			t74 = text(" and updates.");
			h23 = element("h2");
			t75 = text("Change");
			p10 = element("p");
			em14 = element("em");
			t76 = text("Changes to the ");
			strong30 = element("strong");
			em15 = element("em");
			t77 = text("Privacy Policy");
			em16 = element("em");
			t78 = text("apply to your use of our ");
			strong31 = element("strong");
			em17 = element("em");
			t79 = text("Services");
			em18 = element("em");
			t80 = text("after the ");
			strong32 = element("strong");
			em19 = element("em");
			t81 = text("“effective date”");
			em20 = element("em");
			t82 = text(".");
			p11 = element("p");
			strong33 = element("strong");
			t83 = text("“Chalkia”");
			t84 = text(" can modify this ");
			strong34 = element("strong");
			t85 = text("Privacy Policy");
			t86 = text(", and if we make material changes to it, we will provide notice through our ");
			strong35 = element("strong");
			t87 = text("Services");
			t88 = text(", or by other means, to provide you the opportunity to review the changes before they become effective. If you object to any changes, you may stop using our ");
			strong36 = element("strong");
			t89 = text("Services");
			t90 = text(".");
			p12 = element("p");
			t91 = text("You acknowledge that your continued use of our ");
			strong37 = element("strong");
			t92 = text("Services");
			t93 = text(" after we publish or send a notice about our changes to this ");
			strong38 = element("strong");
			t94 = text("Privacy Policy");
			t95 = text(" means that the collection, use and sharing of your personal data is subject to the updated ");
			strong39 = element("strong");
			t96 = text("Privacy Policy");
			t97 = text(".");
			h24 = element("h2");
			t98 = text("1. Data We Collect");
			p13 = element("p");
			t99 = text("In order for the ");
			strong40 = element("strong");
			t100 = text("Visitor");
			t101 = text(" to contact us through our ");
			strong41 = element("strong");
			t102 = text("Services");
			t103 = text(" and get information about our services it is not necessary to give any personal data.");
			h30 = element("h3");
			t104 = text("1.1 Data From Your Device");
			p14 = element("p");
			em21 = element("em");
			t105 = text("We receive data from your devices.");
			p15 = element("p");
			t106 = text("We collect a series of general data and information when users visit and use our ");
			strong42 = element("strong");
			t107 = text("Services");
			t108 = text(". This general data and information are stored in the server log files. Collected may be (1) the browser types and versions used, (2) the operating system used to access our ");
			strong43 = element("strong");
			t109 = text("Services");
			t110 = text(", (3) the website from which you reached our ");
			strong44 = element("strong");
			t111 = text("Services");
			t112 = text(" (so-called referrers), (4) the sub-websites, (5) the date and time of access to our ");
			strong45 = element("strong");
			t113 = text("Services");
			t114 = text(", (6) an Internet protocol address (IP address), (7) the Internet service provider of the accessing system, and (8) any other similar data and information that may be used in the event of attacks on our information technology systems.");
			p16 = element("p");
			t115 = text("When using these general data and information, we do not draw any conclusions about the users. Rather, this information is needed to (1) deliver the content of our ");
			strong46 = element("strong");
			t116 = text("Services");
			t117 = text(" correctly, (2) optimize the content of our ");
			strong47 = element("strong");
			t118 = text("Services");
			t119 = text(", (3) ensure the long-term viability of our information technology systems, and (4) provide law enforcement authorities with the information necessary for criminal prosecution in case of a cyber-attack. Therefore, we analyze anonymously collected data and information statistically, with the aim of increasing the data protection and data security of our enterprise, and to ensure an optimal level of protection for the personal data we process. The anonymous data of the server log files are stored separately from all personal data provided by the ");
			strong48 = element("strong");
			t120 = text("Visitors");
			t121 = text(" of our ");
			strong49 = element("strong");
			t122 = text("Services");
			t123 = text(".");
			h31 = element("h3");
			t124 = text("1.2 Sensitive Data");
			p17 = element("p");
			em22 = element("em");
			t125 = text("We do not gather sensitive personal data.");
			p18 = element("p");
			t126 = text("We do not gather sensitive personal data (e.g. health, genetic, biometric data; racial or ethnic origin, political opinions, religious or philosophical beliefs, trade union membership, sexual orientation, and criminal convictions). We expressly request that you do not provide any such sensitive data to us.");
			h32 = element("h3");
			t127 = text("1.3 Children’s Information");
			p19 = element("p");
			em23 = element("em");
			t128 = text("Only with the consent of their parents or guardians.");
			p20 = element("p");
			t129 = text("Children have access to our ");
			strong50 = element("strong");
			t130 = text("Services");
			t131 = text(" only with the consent of their parents or guardians. If you learn that a child has provided us with personal information without consent, please contact us by sending an email to ");
			strong51 = element("strong");
			t132 = text("info [at] chalkia.com");
			t133 = text(".");
			h25 = element("h2");
			t134 = text("2. How We Use Your Data");
			p21 = element("p");
			strong52 = element("strong");
			t135 = text("“Chalkia”");
			t136 = text(" will not process any ");
			strong53 = element("strong");
			t137 = text("Visitor’s");
			t138 = text(" personal data.");
			h26 = element("h2");
			t139 = text("3. How We Share Your Data");
			h33 = element("h3");
			t140 = text("3.1 Google Analytics (With Anonymization Function)");
			p22 = element("p");
			em24 = element("em");
			t141 = text("We share some of your personal data with ");
			strong54 = element("strong");
			em25 = element("em");
			t142 = text("Google Analytics");
			em26 = element("em");
			t143 = text(".");
			p23 = element("p");
			t144 = text("We have integrated the component of ");
			strong55 = element("strong");
			t145 = text("Google Analytics");
			t146 = text(" (With Anonymization Function) in our ");
			strong56 = element("strong");
			t147 = text("Services");
			t148 = text(".");
			p24 = element("p");
			strong57 = element("strong");
			t149 = text("Google Analytics");
			t150 = text(" is a web analytics service. Web analytics is the collection, gathering, and analysis of data about the behavior of visitors to websites. Web analytics are mainly used for the optimization of a website and in order to carry out a cost-benefit analysis of Internet advertising.");
			p25 = element("p");
			t151 = text("The operator of the ");
			strong58 = element("strong");
			t152 = text("Google Analytics");
			t153 = text(" component is Google Inc., 1600 Amphitheatre Pkwy, Mountain View, CA 94043-1351, United States.");
			p26 = element("p");
			t154 = text("For the web analytics through ");
			strong59 = element("strong");
			t155 = text("Google Analytics");
			t156 = text(" our ");
			strong60 = element("strong");
			t157 = text("Services");
			t158 = text(" use the application “_gat. _anonymizeIp”. By means of this application your IP address of the Internet connection is abridged by ");
			strong61 = element("strong");
			t159 = text("Google");
			t160 = text(" and anonymized.");
			p27 = element("p");
			t161 = text("With each call-up to one of the individual pages into which a component from ");
			strong62 = element("strong");
			t162 = text("Google Analytics");
			t163 = text(" service was integrated, the web browser automatically sends data through the corresponding ");
			strong63 = element("strong");
			t164 = text("Google Analytics");
			t165 = text(" component. During the course of this technical procedure, ");
			strong64 = element("strong");
			t166 = text("Google Maps");
			t167 = text(" and ");
			strong65 = element("strong");
			t168 = text("Google");
			t169 = text(" is made aware of what specific page you visited.");
			p28 = element("p");
			t170 = text("Further information and the applicable data protection provisions of ");
			strong66 = element("strong");
			t171 = text("Google");
			t172 = text(" may be retrieved under ");
			a_1 = element("a");
			t173 = text("https://policies.google.com/privacy");
			t174 = text(".");
			h34 = element("h3");
			t175 = text("3.2 Third Parties");
			p29 = element("p");
			em27 = element("em");
			t176 = text("We do not sell or rent your personal data to third parties.");
			p30 = element("p");
			t177 = text("We do not sell or rent your personal data to third parties.");
			p31 = element("p");
			t178 = text("We do not share your personal data with third parties for marketing purposes.");
			h27 = element("h2");
			t179 = text("4. Your Choices & Obligations");
			h35 = element("h3");
			t180 = text("4.1 Data Retention");
			p32 = element("p");
			em28 = element("em");
			t181 = text("We keep your personal data until you request for their deletion.");
			p33 = element("p");
			strong67 = element("strong");
			t182 = text("“Chalkia”");
			t183 = text(" keeps your personal data until you request for their deletion.");
			p34 = element("p");
			t184 = text("Tax information is exempt from the write-off process and is subject to mandatory tax compliance.");
			h36 = element("h3");
			t185 = text("4.2 Rights To Access And Control Your Personal Data");
			p35 = element("p");
			em29 = element("em");
			t186 = text("You can access or request the deletion of your personal data.");
			p36 = element("p");
			t187 = text("With respect to your personal data, you retain the following rights:");
			ul = element("ul");
			li0 = element("li");
			p37 = element("p");
			strong68 = element("strong");
			t188 = text("Right of Access");
			t189 = text(": You can send us a request in order to be informed about the personal data we keep for you.");
			li1 = element("li");
			p38 = element("p");
			strong69 = element("strong");
			t190 = text("Right to Rectification");
			t191 = text(": You can send us a request in order to ask us to change, update or correct your personal data, particularly if it’s inaccurate.");
			li2 = element("li");
			p39 = element("p");
			strong70 = element("strong");
			t192 = text("Right to Erasure");
			t193 = text(": You can send us a request in order to ask us to delete all or some of your personal data.");
			li3 = element("li");
			p40 = element("p");
			strong71 = element("strong");
			t194 = text("Right to Restrict Processing");
			t195 = text(": You can send us a request in order to ask us to limit the processing of all or some of your personal data.");
			li4 = element("li");
			p41 = element("p");
			strong72 = element("strong");
			t196 = text("Right to Object Processing");
			t197 = text(": You can send us a request in order to ask us to stop the processing of all or some of your personal data.");
			li5 = element("li");
			p42 = element("p");
			strong73 = element("strong");
			t198 = text("Right to Data Portability");
			t199 = text(": You can send us a request in order to ask us to send a copy of your personal data to you or to an organization of your choice.");
			p43 = element("p");
			br = element("br");
			t200 = text("You may contact us to exercise any of the above rights regarding your personal data. ");
			strong74 = element("strong");
			t201 = text("“Chalkia”");
			t202 = text(" will respond to your request free of charge, without delay and in any case within one month of receipt of the request, except in exceptional circumstances, so that the deadline can be extended by another two months if necessary, taking into account the complexity of the request and/or the total number of requests. ");
			strong75 = element("strong");
			t203 = text("“Chalkia”");
			t204 = text(" will inform you of any extension within one month of receipt of the request and of the reasons for the delay. If your request can not be met, ");
			strong76 = element("strong");
			t205 = text("“Chalkia”");
			t206 = text(" will inform you without delay and at the latest within one month of receipt of the request, for the reasons.");
			p44 = element("p");
			t207 = text("The request to satisfy any of the above rights is reviewed each time in accordance with all applicable laws.");
			h28 = element("h2");
			t208 = text("5. Other Important Information");
			h37 = element("h3");
			t209 = text("5.1 Security Breaches");
			p45 = element("p");
			em30 = element("em");
			t210 = text("We monitor for and try to prevent security breaches.");
			p46 = element("p");
			t211 = text("We implement security safeguards designed to protect your data, such as ");
			strong77 = element("strong");
			t212 = text("HTTPS");
			t213 = text(". We regularly monitor our systems for possible vulnerabilities and attacks. However, we cannot warrant the security of any information that you send us. There is no guarantee that data may not be accessed, disclosed, altered, or destroyed by breach of any of our physical, technical, or managerial safeguards.");
			p47 = element("p");
			t214 = text("In case of a security breach, ");
			strong78 = element("strong");
			t215 = text("“Chalkia”");
			t216 = text(" will inform all concerned within 72 hours.");
			h38 = element("h3");
			t217 = text("5.2 Contact Information");
			p48 = element("p");
			em31 = element("em");
			t218 = text("You can contact us for any questions.");
			p49 = element("p");
			t219 = text("You may contact us for any questions about this ");
			strong79 = element("strong");
			t220 = text("Privacy Policy");
			t221 = text(" by sending an email to ");
			strong80 = element("strong");
			t222 = text("info [at] chalkia.com");
			t223 = text(".");
			h39 = element("h3");
			t224 = text("5.3 Institutional Framework For The Protection Of Personal Data");
			p50 = element("p");
			em32 = element("em");
			t225 = text("The legislation governing the present text.");
			p51 = element("p");
			strong81 = element("strong");
			t226 = text("Greece");
			t227 = text(": Law 2472/1997, Law 3471/2006");
			p52 = element("p");
			strong82 = element("strong");
			t228 = text("European Union");
			t229 = text(": Directive 95/46/EC, 2002/58/EC, 2009/136/EC");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h1 = claim_element(div0_nodes, "H1", {});
			var h1_nodes = children(h1);
			t0 = claim_text(h1_nodes, "Privacy Policy");
			h1_nodes.forEach(detach);
			p0 = claim_element(div0_nodes, "P", {});
			var p0_nodes = children(p0);
			t1 = claim_text(p0_nodes, "At ");
			strong0 = claim_element(p0_nodes, "STRONG", {});
			var strong0_nodes = children(strong0);
			t2 = claim_text(strong0_nodes, "“Chalkia”");
			strong0_nodes.forEach(detach);
			t3 = claim_text(p0_nodes, ", we’re committed to protecting and respecting your privacy.");
			p0_nodes.forEach(detach);
			p1 = claim_element(div0_nodes, "P", {});
			var p1_nodes = children(p1);
			t4 = claim_text(p1_nodes, "This ");
			strong1 = claim_element(p1_nodes, "STRONG", {});
			var strong1_nodes = children(strong1);
			t5 = claim_text(strong1_nodes, "Privacy Policy");
			strong1_nodes.forEach(detach);
			t6 = claim_text(p1_nodes, " explains when and why we collect personal information, how we use it, the conditions under which we may disclose it to others and what choices you have.");
			p1_nodes.forEach(detach);
			h20 = claim_element(div0_nodes, "H2", {});
			var h20_nodes = children(h20);
			t7 = claim_text(h20_nodes, "Introduction");
			h20_nodes.forEach(detach);
			p2 = claim_element(div0_nodes, "P", {});
			var p2_nodes = children(p2);
			em0 = claim_element(p2_nodes, "EM", {});
			var em0_nodes = children(em0);
			t8 = claim_text(em0_nodes, "We are a company that specializes in architectural design. People use our ");
			em0_nodes.forEach(detach);
			strong2 = claim_element(p2_nodes, "STRONG", {});
			var strong2_nodes = children(strong2);
			em1 = claim_element(strong2_nodes, "EM", {});
			var em1_nodes = children(em1);
			t9 = claim_text(em1_nodes, "Services");
			em1_nodes.forEach(detach);
			strong2_nodes.forEach(detach);
			em2 = claim_element(p2_nodes, "EM", {});
			var em2_nodes = children(em2);
			t10 = claim_text(em2_nodes, "to get informed about our services. Our ");
			em2_nodes.forEach(detach);
			strong3 = claim_element(p2_nodes, "STRONG", {});
			var strong3_nodes = children(strong3);
			em3 = claim_element(strong3_nodes, "EM", {});
			var em3_nodes = children(em3);
			t11 = claim_text(em3_nodes, "Privacy Policy");
			em3_nodes.forEach(detach);
			strong3_nodes.forEach(detach);
			em4 = claim_element(p2_nodes, "EM", {});
			var em4_nodes = children(em4);
			t12 = claim_text(em4_nodes, "applies to any ");
			em4_nodes.forEach(detach);
			strong4 = claim_element(p2_nodes, "STRONG", {});
			var strong4_nodes = children(strong4);
			em5 = claim_element(strong4_nodes, "EM", {});
			var em5_nodes = children(em5);
			t13 = claim_text(em5_nodes, "Visitor");
			em5_nodes.forEach(detach);
			strong4_nodes.forEach(detach);
			em6 = claim_element(p2_nodes, "EM", {});
			var em6_nodes = children(em6);
			t14 = claim_text(em6_nodes, "to our ");
			em6_nodes.forEach(detach);
			strong5 = claim_element(p2_nodes, "STRONG", {});
			var strong5_nodes = children(strong5);
			em7 = claim_element(strong5_nodes, "EM", {});
			var em7_nodes = children(em7);
			t15 = claim_text(em7_nodes, "Services");
			em7_nodes.forEach(detach);
			strong5_nodes.forEach(detach);
			em8 = claim_element(p2_nodes, "EM", {});
			var em8_nodes = children(em8);
			t16 = claim_text(em8_nodes, ".");
			em8_nodes.forEach(detach);
			p2_nodes.forEach(detach);
			p3 = claim_element(div0_nodes, "P", {});
			var p3_nodes = children(p3);
			t17 = claim_text(p3_nodes, "Our non-registered (");
			strong6 = claim_element(p3_nodes, "STRONG", {});
			var strong6_nodes = children(strong6);
			t18 = claim_text(strong6_nodes, "“Visitors”");
			strong6_nodes.forEach(detach);
			t19 = claim_text(p3_nodes, ") users get informed through our ");
			strong7 = claim_element(p3_nodes, "STRONG", {});
			var strong7_nodes = children(strong7);
			t20 = claim_text(strong7_nodes, "Services");
			strong7_nodes.forEach(detach);
			t21 = claim_text(p3_nodes, ". All content and data on our ");
			strong8 = claim_element(p3_nodes, "STRONG", {});
			var strong8_nodes = children(strong8);
			t22 = claim_text(strong8_nodes, "Services");
			strong8_nodes.forEach(detach);
			t23 = claim_text(p3_nodes, " is viewable to non-registered (");
			strong9 = claim_element(p3_nodes, "STRONG", {});
			var strong9_nodes = children(strong9);
			t24 = claim_text(strong9_nodes, "“Visitors”");
			strong9_nodes.forEach(detach);
			t25 = claim_text(p3_nodes, ") users. You don’t have to be a registered user (");
			strong10 = claim_element(p3_nodes, "STRONG", {});
			var strong10_nodes = children(strong10);
			t26 = claim_text(strong10_nodes, "“Member”");
			strong10_nodes.forEach(detach);
			t27 = claim_text(p3_nodes, ") to use our ");
			strong11 = claim_element(p3_nodes, "STRONG", {});
			var strong11_nodes = children(strong11);
			t28 = claim_text(strong11_nodes, "Services");
			strong11_nodes.forEach(detach);
			t29 = claim_text(p3_nodes, ".");
			p3_nodes.forEach(detach);
			p4 = claim_element(div0_nodes, "P", {});
			var p4_nodes = children(p4);
			t30 = claim_text(p4_nodes, "We use the term ");
			strong12 = claim_element(p4_nodes, "STRONG", {});
			var strong12_nodes = children(strong12);
			t31 = claim_text(strong12_nodes, "“Designated Countries”");
			strong12_nodes.forEach(detach);
			t32 = claim_text(p4_nodes, " to refer to countries in the ");
			strong13 = claim_element(p4_nodes, "STRONG", {});
			var strong13_nodes = children(strong13);
			t33 = claim_text(strong13_nodes, "European Union");
			strong13_nodes.forEach(detach);
			t34 = claim_text(p4_nodes, " (");
			strong14 = claim_element(p4_nodes, "STRONG", {});
			var strong14_nodes = children(strong14);
			t35 = claim_text(strong14_nodes, "EU");
			strong14_nodes.forEach(detach);
			t36 = claim_text(p4_nodes, "), ");
			strong15 = claim_element(p4_nodes, "STRONG", {});
			var strong15_nodes = children(strong15);
			t37 = claim_text(strong15_nodes, "European Economic Area");
			strong15_nodes.forEach(detach);
			t38 = claim_text(p4_nodes, " (");
			strong16 = claim_element(p4_nodes, "STRONG", {});
			var strong16_nodes = children(strong16);
			t39 = claim_text(strong16_nodes, "EEA");
			strong16_nodes.forEach(detach);
			t40 = claim_text(p4_nodes, "), and ");
			strong17 = claim_element(p4_nodes, "STRONG", {});
			var strong17_nodes = children(strong17);
			t41 = claim_text(strong17_nodes, "Switzerland");
			strong17_nodes.forEach(detach);
			t42 = claim_text(p4_nodes, ".");
			p4_nodes.forEach(detach);
			h21 = claim_element(div0_nodes, "H2", {});
			var h21_nodes = children(h21);
			t43 = claim_text(h21_nodes, "Services");
			h21_nodes.forEach(detach);
			p5 = claim_element(div0_nodes, "P", {});
			var p5_nodes = children(p5);
			t44 = claim_text(p5_nodes, "This ");
			strong18 = claim_element(p5_nodes, "STRONG", {});
			var strong18_nodes = children(strong18);
			t45 = claim_text(strong18_nodes, "Privacy Policy");
			strong18_nodes.forEach(detach);
			t46 = claim_text(p5_nodes, " applies to ");
			strong19 = claim_element(p5_nodes, "STRONG", {});
			var strong19_nodes = children(strong19);
			t47 = claim_text(strong19_nodes, "www.chalkia.com");
			strong19_nodes.forEach(detach);
			t48 = claim_text(p5_nodes, " (");
			strong20 = claim_element(p5_nodes, "STRONG", {});
			var strong20_nodes = children(strong20);
			t49 = claim_text(strong20_nodes, "“Services”");
			strong20_nodes.forEach(detach);
			t50 = claim_text(p5_nodes, ").");
			p5_nodes.forEach(detach);
			h22 = claim_element(div0_nodes, "H2", {});
			var h22_nodes = children(h22);
			t51 = claim_text(h22_nodes, "Data Controllers And Contracting Parties");
			h22_nodes.forEach(detach);
			p6 = claim_element(div0_nodes, "P", {});
			var p6_nodes = children(p6);
			strong21 = claim_element(p6_nodes, "STRONG", {});
			var strong21_nodes = children(strong21);
			em9 = claim_element(strong21_nodes, "EM", {});
			var em9_nodes = children(em9);
			t52 = claim_text(em9_nodes, "“");
			em9_nodes.forEach(detach);
			t53 = claim_text(strong21_nodes, "Chalkia");
			em10 = claim_element(strong21_nodes, "EM", {});
			var em10_nodes = children(em10);
			t54 = claim_text(em10_nodes, "”");
			em10_nodes.forEach(detach);
			strong21_nodes.forEach(detach);
			em11 = claim_element(p6_nodes, "EM", {});
			var em11_nodes = children(em11);
			t55 = claim_text(em11_nodes, "is the controller of your personal data in connection with our ");
			em11_nodes.forEach(detach);
			strong22 = claim_element(p6_nodes, "STRONG", {});
			var strong22_nodes = children(strong22);
			em12 = claim_element(strong22_nodes, "EM", {});
			var em12_nodes = children(em12);
			t56 = claim_text(em12_nodes, "Services");
			em12_nodes.forEach(detach);
			strong22_nodes.forEach(detach);
			em13 = claim_element(p6_nodes, "EM", {});
			var em13_nodes = children(em13);
			t57 = claim_text(em13_nodes, "and the company’s electronic data processing system.");
			em13_nodes.forEach(detach);
			p6_nodes.forEach(detach);
			p7 = claim_element(div0_nodes, "P", {});
			var p7_nodes = children(p7);
			t58 = claim_text(p7_nodes, "If you reside in the ");
			strong23 = claim_element(p7_nodes, "STRONG", {});
			var strong23_nodes = children(strong23);
			t59 = claim_text(strong23_nodes, "“Designated Countries”");
			strong23_nodes.forEach(detach);
			t60 = claim_text(p7_nodes, ": ");
			strong24 = claim_element(p7_nodes, "STRONG", {});
			var strong24_nodes = children(strong24);
			t61 = claim_text(strong24_nodes, "“Chalkia”");
			strong24_nodes.forEach(detach);
			t62 = claim_text(p7_nodes, " will be the controller of your personal data provided to, or collected by or for, or processed in connection with our Services.");
			p7_nodes.forEach(detach);
			p8 = claim_element(div0_nodes, "P", {});
			var p8_nodes = children(p8);
			t63 = claim_text(p8_nodes, "If you reside outside of the ");
			strong25 = claim_element(p8_nodes, "STRONG", {});
			var strong25_nodes = children(strong25);
			t64 = claim_text(strong25_nodes, "“Designated Countries”");
			strong25_nodes.forEach(detach);
			t65 = claim_text(p8_nodes, ": ");
			strong26 = claim_element(p8_nodes, "STRONG", {});
			var strong26_nodes = children(strong26);
			t66 = claim_text(strong26_nodes, "“Chalkia”");
			strong26_nodes.forEach(detach);
			t67 = claim_text(p8_nodes, " will be the controller of your personal data provided to, or collected by or for, or processed in connection with, our Services.");
			p8_nodes.forEach(detach);
			p9 = claim_element(div0_nodes, "P", {});
			var p9_nodes = children(p9);
			t68 = claim_text(p9_nodes, "As a ");
			strong27 = claim_element(p9_nodes, "STRONG", {});
			var strong27_nodes = children(strong27);
			t69 = claim_text(strong27_nodes, "Visitor");
			strong27_nodes.forEach(detach);
			t70 = claim_text(p9_nodes, " of our ");
			strong28 = claim_element(p9_nodes, "STRONG", {});
			var strong28_nodes = children(strong28);
			t71 = claim_text(strong28_nodes, "Services");
			strong28_nodes.forEach(detach);
			t72 = claim_text(p9_nodes, ", the collection, use and sharing of your personal data is subject to this ");
			strong29 = claim_element(p9_nodes, "STRONG", {});
			var strong29_nodes = children(strong29);
			t73 = claim_text(strong29_nodes, "Privacy Policy");
			strong29_nodes.forEach(detach);
			t74 = claim_text(p9_nodes, " and updates.");
			p9_nodes.forEach(detach);
			h23 = claim_element(div0_nodes, "H2", {});
			var h23_nodes = children(h23);
			t75 = claim_text(h23_nodes, "Change");
			h23_nodes.forEach(detach);
			p10 = claim_element(div0_nodes, "P", {});
			var p10_nodes = children(p10);
			em14 = claim_element(p10_nodes, "EM", {});
			var em14_nodes = children(em14);
			t76 = claim_text(em14_nodes, "Changes to the ");
			em14_nodes.forEach(detach);
			strong30 = claim_element(p10_nodes, "STRONG", {});
			var strong30_nodes = children(strong30);
			em15 = claim_element(strong30_nodes, "EM", {});
			var em15_nodes = children(em15);
			t77 = claim_text(em15_nodes, "Privacy Policy");
			em15_nodes.forEach(detach);
			strong30_nodes.forEach(detach);
			em16 = claim_element(p10_nodes, "EM", {});
			var em16_nodes = children(em16);
			t78 = claim_text(em16_nodes, "apply to your use of our ");
			em16_nodes.forEach(detach);
			strong31 = claim_element(p10_nodes, "STRONG", {});
			var strong31_nodes = children(strong31);
			em17 = claim_element(strong31_nodes, "EM", {});
			var em17_nodes = children(em17);
			t79 = claim_text(em17_nodes, "Services");
			em17_nodes.forEach(detach);
			strong31_nodes.forEach(detach);
			em18 = claim_element(p10_nodes, "EM", {});
			var em18_nodes = children(em18);
			t80 = claim_text(em18_nodes, "after the ");
			em18_nodes.forEach(detach);
			strong32 = claim_element(p10_nodes, "STRONG", {});
			var strong32_nodes = children(strong32);
			em19 = claim_element(strong32_nodes, "EM", {});
			var em19_nodes = children(em19);
			t81 = claim_text(em19_nodes, "“effective date”");
			em19_nodes.forEach(detach);
			strong32_nodes.forEach(detach);
			em20 = claim_element(p10_nodes, "EM", {});
			var em20_nodes = children(em20);
			t82 = claim_text(em20_nodes, ".");
			em20_nodes.forEach(detach);
			p10_nodes.forEach(detach);
			p11 = claim_element(div0_nodes, "P", {});
			var p11_nodes = children(p11);
			strong33 = claim_element(p11_nodes, "STRONG", {});
			var strong33_nodes = children(strong33);
			t83 = claim_text(strong33_nodes, "“Chalkia”");
			strong33_nodes.forEach(detach);
			t84 = claim_text(p11_nodes, " can modify this ");
			strong34 = claim_element(p11_nodes, "STRONG", {});
			var strong34_nodes = children(strong34);
			t85 = claim_text(strong34_nodes, "Privacy Policy");
			strong34_nodes.forEach(detach);
			t86 = claim_text(p11_nodes, ", and if we make material changes to it, we will provide notice through our ");
			strong35 = claim_element(p11_nodes, "STRONG", {});
			var strong35_nodes = children(strong35);
			t87 = claim_text(strong35_nodes, "Services");
			strong35_nodes.forEach(detach);
			t88 = claim_text(p11_nodes, ", or by other means, to provide you the opportunity to review the changes before they become effective. If you object to any changes, you may stop using our ");
			strong36 = claim_element(p11_nodes, "STRONG", {});
			var strong36_nodes = children(strong36);
			t89 = claim_text(strong36_nodes, "Services");
			strong36_nodes.forEach(detach);
			t90 = claim_text(p11_nodes, ".");
			p11_nodes.forEach(detach);
			p12 = claim_element(div0_nodes, "P", {});
			var p12_nodes = children(p12);
			t91 = claim_text(p12_nodes, "You acknowledge that your continued use of our ");
			strong37 = claim_element(p12_nodes, "STRONG", {});
			var strong37_nodes = children(strong37);
			t92 = claim_text(strong37_nodes, "Services");
			strong37_nodes.forEach(detach);
			t93 = claim_text(p12_nodes, " after we publish or send a notice about our changes to this ");
			strong38 = claim_element(p12_nodes, "STRONG", {});
			var strong38_nodes = children(strong38);
			t94 = claim_text(strong38_nodes, "Privacy Policy");
			strong38_nodes.forEach(detach);
			t95 = claim_text(p12_nodes, " means that the collection, use and sharing of your personal data is subject to the updated ");
			strong39 = claim_element(p12_nodes, "STRONG", {});
			var strong39_nodes = children(strong39);
			t96 = claim_text(strong39_nodes, "Privacy Policy");
			strong39_nodes.forEach(detach);
			t97 = claim_text(p12_nodes, ".");
			p12_nodes.forEach(detach);
			h24 = claim_element(div0_nodes, "H2", {});
			var h24_nodes = children(h24);
			t98 = claim_text(h24_nodes, "1. Data We Collect");
			h24_nodes.forEach(detach);
			p13 = claim_element(div0_nodes, "P", {});
			var p13_nodes = children(p13);
			t99 = claim_text(p13_nodes, "In order for the ");
			strong40 = claim_element(p13_nodes, "STRONG", {});
			var strong40_nodes = children(strong40);
			t100 = claim_text(strong40_nodes, "Visitor");
			strong40_nodes.forEach(detach);
			t101 = claim_text(p13_nodes, " to contact us through our ");
			strong41 = claim_element(p13_nodes, "STRONG", {});
			var strong41_nodes = children(strong41);
			t102 = claim_text(strong41_nodes, "Services");
			strong41_nodes.forEach(detach);
			t103 = claim_text(p13_nodes, " and get information about our services it is not necessary to give any personal data.");
			p13_nodes.forEach(detach);
			h30 = claim_element(div0_nodes, "H3", {});
			var h30_nodes = children(h30);
			t104 = claim_text(h30_nodes, "1.1 Data From Your Device");
			h30_nodes.forEach(detach);
			p14 = claim_element(div0_nodes, "P", {});
			var p14_nodes = children(p14);
			em21 = claim_element(p14_nodes, "EM", {});
			var em21_nodes = children(em21);
			t105 = claim_text(em21_nodes, "We receive data from your devices.");
			em21_nodes.forEach(detach);
			p14_nodes.forEach(detach);
			p15 = claim_element(div0_nodes, "P", {});
			var p15_nodes = children(p15);
			t106 = claim_text(p15_nodes, "We collect a series of general data and information when users visit and use our ");
			strong42 = claim_element(p15_nodes, "STRONG", {});
			var strong42_nodes = children(strong42);
			t107 = claim_text(strong42_nodes, "Services");
			strong42_nodes.forEach(detach);
			t108 = claim_text(p15_nodes, ". This general data and information are stored in the server log files. Collected may be (1) the browser types and versions used, (2) the operating system used to access our ");
			strong43 = claim_element(p15_nodes, "STRONG", {});
			var strong43_nodes = children(strong43);
			t109 = claim_text(strong43_nodes, "Services");
			strong43_nodes.forEach(detach);
			t110 = claim_text(p15_nodes, ", (3) the website from which you reached our ");
			strong44 = claim_element(p15_nodes, "STRONG", {});
			var strong44_nodes = children(strong44);
			t111 = claim_text(strong44_nodes, "Services");
			strong44_nodes.forEach(detach);
			t112 = claim_text(p15_nodes, " (so-called referrers), (4) the sub-websites, (5) the date and time of access to our ");
			strong45 = claim_element(p15_nodes, "STRONG", {});
			var strong45_nodes = children(strong45);
			t113 = claim_text(strong45_nodes, "Services");
			strong45_nodes.forEach(detach);
			t114 = claim_text(p15_nodes, ", (6) an Internet protocol address (IP address), (7) the Internet service provider of the accessing system, and (8) any other similar data and information that may be used in the event of attacks on our information technology systems.");
			p15_nodes.forEach(detach);
			p16 = claim_element(div0_nodes, "P", {});
			var p16_nodes = children(p16);
			t115 = claim_text(p16_nodes, "When using these general data and information, we do not draw any conclusions about the users. Rather, this information is needed to (1) deliver the content of our ");
			strong46 = claim_element(p16_nodes, "STRONG", {});
			var strong46_nodes = children(strong46);
			t116 = claim_text(strong46_nodes, "Services");
			strong46_nodes.forEach(detach);
			t117 = claim_text(p16_nodes, " correctly, (2) optimize the content of our ");
			strong47 = claim_element(p16_nodes, "STRONG", {});
			var strong47_nodes = children(strong47);
			t118 = claim_text(strong47_nodes, "Services");
			strong47_nodes.forEach(detach);
			t119 = claim_text(p16_nodes, ", (3) ensure the long-term viability of our information technology systems, and (4) provide law enforcement authorities with the information necessary for criminal prosecution in case of a cyber-attack. Therefore, we analyze anonymously collected data and information statistically, with the aim of increasing the data protection and data security of our enterprise, and to ensure an optimal level of protection for the personal data we process. The anonymous data of the server log files are stored separately from all personal data provided by the ");
			strong48 = claim_element(p16_nodes, "STRONG", {});
			var strong48_nodes = children(strong48);
			t120 = claim_text(strong48_nodes, "Visitors");
			strong48_nodes.forEach(detach);
			t121 = claim_text(p16_nodes, " of our ");
			strong49 = claim_element(p16_nodes, "STRONG", {});
			var strong49_nodes = children(strong49);
			t122 = claim_text(strong49_nodes, "Services");
			strong49_nodes.forEach(detach);
			t123 = claim_text(p16_nodes, ".");
			p16_nodes.forEach(detach);
			h31 = claim_element(div0_nodes, "H3", {});
			var h31_nodes = children(h31);
			t124 = claim_text(h31_nodes, "1.2 Sensitive Data");
			h31_nodes.forEach(detach);
			p17 = claim_element(div0_nodes, "P", {});
			var p17_nodes = children(p17);
			em22 = claim_element(p17_nodes, "EM", {});
			var em22_nodes = children(em22);
			t125 = claim_text(em22_nodes, "We do not gather sensitive personal data.");
			em22_nodes.forEach(detach);
			p17_nodes.forEach(detach);
			p18 = claim_element(div0_nodes, "P", {});
			var p18_nodes = children(p18);
			t126 = claim_text(p18_nodes, "We do not gather sensitive personal data (e.g. health, genetic, biometric data; racial or ethnic origin, political opinions, religious or philosophical beliefs, trade union membership, sexual orientation, and criminal convictions). We expressly request that you do not provide any such sensitive data to us.");
			p18_nodes.forEach(detach);
			h32 = claim_element(div0_nodes, "H3", {});
			var h32_nodes = children(h32);
			t127 = claim_text(h32_nodes, "1.3 Children’s Information");
			h32_nodes.forEach(detach);
			p19 = claim_element(div0_nodes, "P", {});
			var p19_nodes = children(p19);
			em23 = claim_element(p19_nodes, "EM", {});
			var em23_nodes = children(em23);
			t128 = claim_text(em23_nodes, "Only with the consent of their parents or guardians.");
			em23_nodes.forEach(detach);
			p19_nodes.forEach(detach);
			p20 = claim_element(div0_nodes, "P", {});
			var p20_nodes = children(p20);
			t129 = claim_text(p20_nodes, "Children have access to our ");
			strong50 = claim_element(p20_nodes, "STRONG", {});
			var strong50_nodes = children(strong50);
			t130 = claim_text(strong50_nodes, "Services");
			strong50_nodes.forEach(detach);
			t131 = claim_text(p20_nodes, " only with the consent of their parents or guardians. If you learn that a child has provided us with personal information without consent, please contact us by sending an email to ");
			strong51 = claim_element(p20_nodes, "STRONG", {});
			var strong51_nodes = children(strong51);
			t132 = claim_text(strong51_nodes, "info [at] chalkia.com");
			strong51_nodes.forEach(detach);
			t133 = claim_text(p20_nodes, ".");
			p20_nodes.forEach(detach);
			h25 = claim_element(div0_nodes, "H2", {});
			var h25_nodes = children(h25);
			t134 = claim_text(h25_nodes, "2. How We Use Your Data");
			h25_nodes.forEach(detach);
			p21 = claim_element(div0_nodes, "P", {});
			var p21_nodes = children(p21);
			strong52 = claim_element(p21_nodes, "STRONG", {});
			var strong52_nodes = children(strong52);
			t135 = claim_text(strong52_nodes, "“Chalkia”");
			strong52_nodes.forEach(detach);
			t136 = claim_text(p21_nodes, " will not process any ");
			strong53 = claim_element(p21_nodes, "STRONG", {});
			var strong53_nodes = children(strong53);
			t137 = claim_text(strong53_nodes, "Visitor’s");
			strong53_nodes.forEach(detach);
			t138 = claim_text(p21_nodes, " personal data.");
			p21_nodes.forEach(detach);
			h26 = claim_element(div0_nodes, "H2", {});
			var h26_nodes = children(h26);
			t139 = claim_text(h26_nodes, "3. How We Share Your Data");
			h26_nodes.forEach(detach);
			h33 = claim_element(div0_nodes, "H3", {});
			var h33_nodes = children(h33);
			t140 = claim_text(h33_nodes, "3.1 Google Analytics (With Anonymization Function)");
			h33_nodes.forEach(detach);
			p22 = claim_element(div0_nodes, "P", {});
			var p22_nodes = children(p22);
			em24 = claim_element(p22_nodes, "EM", {});
			var em24_nodes = children(em24);
			t141 = claim_text(em24_nodes, "We share some of your personal data with ");
			em24_nodes.forEach(detach);
			strong54 = claim_element(p22_nodes, "STRONG", {});
			var strong54_nodes = children(strong54);
			em25 = claim_element(strong54_nodes, "EM", {});
			var em25_nodes = children(em25);
			t142 = claim_text(em25_nodes, "Google Analytics");
			em25_nodes.forEach(detach);
			strong54_nodes.forEach(detach);
			em26 = claim_element(p22_nodes, "EM", {});
			var em26_nodes = children(em26);
			t143 = claim_text(em26_nodes, ".");
			em26_nodes.forEach(detach);
			p22_nodes.forEach(detach);
			p23 = claim_element(div0_nodes, "P", {});
			var p23_nodes = children(p23);
			t144 = claim_text(p23_nodes, "We have integrated the component of ");
			strong55 = claim_element(p23_nodes, "STRONG", {});
			var strong55_nodes = children(strong55);
			t145 = claim_text(strong55_nodes, "Google Analytics");
			strong55_nodes.forEach(detach);
			t146 = claim_text(p23_nodes, " (With Anonymization Function) in our ");
			strong56 = claim_element(p23_nodes, "STRONG", {});
			var strong56_nodes = children(strong56);
			t147 = claim_text(strong56_nodes, "Services");
			strong56_nodes.forEach(detach);
			t148 = claim_text(p23_nodes, ".");
			p23_nodes.forEach(detach);
			p24 = claim_element(div0_nodes, "P", {});
			var p24_nodes = children(p24);
			strong57 = claim_element(p24_nodes, "STRONG", {});
			var strong57_nodes = children(strong57);
			t149 = claim_text(strong57_nodes, "Google Analytics");
			strong57_nodes.forEach(detach);
			t150 = claim_text(p24_nodes, " is a web analytics service. Web analytics is the collection, gathering, and analysis of data about the behavior of visitors to websites. Web analytics are mainly used for the optimization of a website and in order to carry out a cost-benefit analysis of Internet advertising.");
			p24_nodes.forEach(detach);
			p25 = claim_element(div0_nodes, "P", {});
			var p25_nodes = children(p25);
			t151 = claim_text(p25_nodes, "The operator of the ");
			strong58 = claim_element(p25_nodes, "STRONG", {});
			var strong58_nodes = children(strong58);
			t152 = claim_text(strong58_nodes, "Google Analytics");
			strong58_nodes.forEach(detach);
			t153 = claim_text(p25_nodes, " component is Google Inc., 1600 Amphitheatre Pkwy, Mountain View, CA 94043-1351, United States.");
			p25_nodes.forEach(detach);
			p26 = claim_element(div0_nodes, "P", {});
			var p26_nodes = children(p26);
			t154 = claim_text(p26_nodes, "For the web analytics through ");
			strong59 = claim_element(p26_nodes, "STRONG", {});
			var strong59_nodes = children(strong59);
			t155 = claim_text(strong59_nodes, "Google Analytics");
			strong59_nodes.forEach(detach);
			t156 = claim_text(p26_nodes, " our ");
			strong60 = claim_element(p26_nodes, "STRONG", {});
			var strong60_nodes = children(strong60);
			t157 = claim_text(strong60_nodes, "Services");
			strong60_nodes.forEach(detach);
			t158 = claim_text(p26_nodes, " use the application “_gat. _anonymizeIp”. By means of this application your IP address of the Internet connection is abridged by ");
			strong61 = claim_element(p26_nodes, "STRONG", {});
			var strong61_nodes = children(strong61);
			t159 = claim_text(strong61_nodes, "Google");
			strong61_nodes.forEach(detach);
			t160 = claim_text(p26_nodes, " and anonymized.");
			p26_nodes.forEach(detach);
			p27 = claim_element(div0_nodes, "P", {});
			var p27_nodes = children(p27);
			t161 = claim_text(p27_nodes, "With each call-up to one of the individual pages into which a component from ");
			strong62 = claim_element(p27_nodes, "STRONG", {});
			var strong62_nodes = children(strong62);
			t162 = claim_text(strong62_nodes, "Google Analytics");
			strong62_nodes.forEach(detach);
			t163 = claim_text(p27_nodes, " service was integrated, the web browser automatically sends data through the corresponding ");
			strong63 = claim_element(p27_nodes, "STRONG", {});
			var strong63_nodes = children(strong63);
			t164 = claim_text(strong63_nodes, "Google Analytics");
			strong63_nodes.forEach(detach);
			t165 = claim_text(p27_nodes, " component. During the course of this technical procedure, ");
			strong64 = claim_element(p27_nodes, "STRONG", {});
			var strong64_nodes = children(strong64);
			t166 = claim_text(strong64_nodes, "Google Maps");
			strong64_nodes.forEach(detach);
			t167 = claim_text(p27_nodes, " and ");
			strong65 = claim_element(p27_nodes, "STRONG", {});
			var strong65_nodes = children(strong65);
			t168 = claim_text(strong65_nodes, "Google");
			strong65_nodes.forEach(detach);
			t169 = claim_text(p27_nodes, " is made aware of what specific page you visited.");
			p27_nodes.forEach(detach);
			p28 = claim_element(div0_nodes, "P", {});
			var p28_nodes = children(p28);
			t170 = claim_text(p28_nodes, "Further information and the applicable data protection provisions of ");
			strong66 = claim_element(p28_nodes, "STRONG", {});
			var strong66_nodes = children(strong66);
			t171 = claim_text(strong66_nodes, "Google");
			strong66_nodes.forEach(detach);
			t172 = claim_text(p28_nodes, " may be retrieved under ");

			a_1 = claim_element(p28_nodes, "A", {
				target: true,
				rel: true,
				class: true,
				href: true
			});

			var a_1_nodes = children(a_1);
			t173 = claim_text(a_1_nodes, "https://policies.google.com/privacy");
			a_1_nodes.forEach(detach);
			t174 = claim_text(p28_nodes, ".");
			p28_nodes.forEach(detach);
			h34 = claim_element(div0_nodes, "H3", {});
			var h34_nodes = children(h34);
			t175 = claim_text(h34_nodes, "3.2 Third Parties");
			h34_nodes.forEach(detach);
			p29 = claim_element(div0_nodes, "P", {});
			var p29_nodes = children(p29);
			em27 = claim_element(p29_nodes, "EM", {});
			var em27_nodes = children(em27);
			t176 = claim_text(em27_nodes, "We do not sell or rent your personal data to third parties.");
			em27_nodes.forEach(detach);
			p29_nodes.forEach(detach);
			p30 = claim_element(div0_nodes, "P", {});
			var p30_nodes = children(p30);
			t177 = claim_text(p30_nodes, "We do not sell or rent your personal data to third parties.");
			p30_nodes.forEach(detach);
			p31 = claim_element(div0_nodes, "P", {});
			var p31_nodes = children(p31);
			t178 = claim_text(p31_nodes, "We do not share your personal data with third parties for marketing purposes.");
			p31_nodes.forEach(detach);
			h27 = claim_element(div0_nodes, "H2", {});
			var h27_nodes = children(h27);
			t179 = claim_text(h27_nodes, "4. Your Choices & Obligations");
			h27_nodes.forEach(detach);
			h35 = claim_element(div0_nodes, "H3", {});
			var h35_nodes = children(h35);
			t180 = claim_text(h35_nodes, "4.1 Data Retention");
			h35_nodes.forEach(detach);
			p32 = claim_element(div0_nodes, "P", {});
			var p32_nodes = children(p32);
			em28 = claim_element(p32_nodes, "EM", {});
			var em28_nodes = children(em28);
			t181 = claim_text(em28_nodes, "We keep your personal data until you request for their deletion.");
			em28_nodes.forEach(detach);
			p32_nodes.forEach(detach);
			p33 = claim_element(div0_nodes, "P", {});
			var p33_nodes = children(p33);
			strong67 = claim_element(p33_nodes, "STRONG", {});
			var strong67_nodes = children(strong67);
			t182 = claim_text(strong67_nodes, "“Chalkia”");
			strong67_nodes.forEach(detach);
			t183 = claim_text(p33_nodes, " keeps your personal data until you request for their deletion.");
			p33_nodes.forEach(detach);
			p34 = claim_element(div0_nodes, "P", {});
			var p34_nodes = children(p34);
			t184 = claim_text(p34_nodes, "Tax information is exempt from the write-off process and is subject to mandatory tax compliance.");
			p34_nodes.forEach(detach);
			h36 = claim_element(div0_nodes, "H3", {});
			var h36_nodes = children(h36);
			t185 = claim_text(h36_nodes, "4.2 Rights To Access And Control Your Personal Data");
			h36_nodes.forEach(detach);
			p35 = claim_element(div0_nodes, "P", {});
			var p35_nodes = children(p35);
			em29 = claim_element(p35_nodes, "EM", {});
			var em29_nodes = children(em29);
			t186 = claim_text(em29_nodes, "You can access or request the deletion of your personal data.");
			em29_nodes.forEach(detach);
			p35_nodes.forEach(detach);
			p36 = claim_element(div0_nodes, "P", {});
			var p36_nodes = children(p36);
			t187 = claim_text(p36_nodes, "With respect to your personal data, you retain the following rights:");
			p36_nodes.forEach(detach);
			ul = claim_element(div0_nodes, "UL", {});
			var ul_nodes = children(ul);
			li0 = claim_element(ul_nodes, "LI", {});
			var li0_nodes = children(li0);
			p37 = claim_element(li0_nodes, "P", {});
			var p37_nodes = children(p37);
			strong68 = claim_element(p37_nodes, "STRONG", {});
			var strong68_nodes = children(strong68);
			t188 = claim_text(strong68_nodes, "Right of Access");
			strong68_nodes.forEach(detach);
			t189 = claim_text(p37_nodes, ": You can send us a request in order to be informed about the personal data we keep for you.");
			p37_nodes.forEach(detach);
			li0_nodes.forEach(detach);
			li1 = claim_element(ul_nodes, "LI", {});
			var li1_nodes = children(li1);
			p38 = claim_element(li1_nodes, "P", {});
			var p38_nodes = children(p38);
			strong69 = claim_element(p38_nodes, "STRONG", {});
			var strong69_nodes = children(strong69);
			t190 = claim_text(strong69_nodes, "Right to Rectification");
			strong69_nodes.forEach(detach);
			t191 = claim_text(p38_nodes, ": You can send us a request in order to ask us to change, update or correct your personal data, particularly if it’s inaccurate.");
			p38_nodes.forEach(detach);
			li1_nodes.forEach(detach);
			li2 = claim_element(ul_nodes, "LI", {});
			var li2_nodes = children(li2);
			p39 = claim_element(li2_nodes, "P", {});
			var p39_nodes = children(p39);
			strong70 = claim_element(p39_nodes, "STRONG", {});
			var strong70_nodes = children(strong70);
			t192 = claim_text(strong70_nodes, "Right to Erasure");
			strong70_nodes.forEach(detach);
			t193 = claim_text(p39_nodes, ": You can send us a request in order to ask us to delete all or some of your personal data.");
			p39_nodes.forEach(detach);
			li2_nodes.forEach(detach);
			li3 = claim_element(ul_nodes, "LI", {});
			var li3_nodes = children(li3);
			p40 = claim_element(li3_nodes, "P", {});
			var p40_nodes = children(p40);
			strong71 = claim_element(p40_nodes, "STRONG", {});
			var strong71_nodes = children(strong71);
			t194 = claim_text(strong71_nodes, "Right to Restrict Processing");
			strong71_nodes.forEach(detach);
			t195 = claim_text(p40_nodes, ": You can send us a request in order to ask us to limit the processing of all or some of your personal data.");
			p40_nodes.forEach(detach);
			li3_nodes.forEach(detach);
			li4 = claim_element(ul_nodes, "LI", {});
			var li4_nodes = children(li4);
			p41 = claim_element(li4_nodes, "P", {});
			var p41_nodes = children(p41);
			strong72 = claim_element(p41_nodes, "STRONG", {});
			var strong72_nodes = children(strong72);
			t196 = claim_text(strong72_nodes, "Right to Object Processing");
			strong72_nodes.forEach(detach);
			t197 = claim_text(p41_nodes, ": You can send us a request in order to ask us to stop the processing of all or some of your personal data.");
			p41_nodes.forEach(detach);
			li4_nodes.forEach(detach);
			li5 = claim_element(ul_nodes, "LI", {});
			var li5_nodes = children(li5);
			p42 = claim_element(li5_nodes, "P", {});
			var p42_nodes = children(p42);
			strong73 = claim_element(p42_nodes, "STRONG", {});
			var strong73_nodes = children(strong73);
			t198 = claim_text(strong73_nodes, "Right to Data Portability");
			strong73_nodes.forEach(detach);
			t199 = claim_text(p42_nodes, ": You can send us a request in order to ask us to send a copy of your personal data to you or to an organization of your choice.");
			p42_nodes.forEach(detach);
			li5_nodes.forEach(detach);
			ul_nodes.forEach(detach);
			p43 = claim_element(div0_nodes, "P", {});
			var p43_nodes = children(p43);
			br = claim_element(p43_nodes, "BR", {});
			t200 = claim_text(p43_nodes, "You may contact us to exercise any of the above rights regarding your personal data. ");
			strong74 = claim_element(p43_nodes, "STRONG", {});
			var strong74_nodes = children(strong74);
			t201 = claim_text(strong74_nodes, "“Chalkia”");
			strong74_nodes.forEach(detach);
			t202 = claim_text(p43_nodes, " will respond to your request free of charge, without delay and in any case within one month of receipt of the request, except in exceptional circumstances, so that the deadline can be extended by another two months if necessary, taking into account the complexity of the request and/or the total number of requests. ");
			strong75 = claim_element(p43_nodes, "STRONG", {});
			var strong75_nodes = children(strong75);
			t203 = claim_text(strong75_nodes, "“Chalkia”");
			strong75_nodes.forEach(detach);
			t204 = claim_text(p43_nodes, " will inform you of any extension within one month of receipt of the request and of the reasons for the delay. If your request can not be met, ");
			strong76 = claim_element(p43_nodes, "STRONG", {});
			var strong76_nodes = children(strong76);
			t205 = claim_text(strong76_nodes, "“Chalkia”");
			strong76_nodes.forEach(detach);
			t206 = claim_text(p43_nodes, " will inform you without delay and at the latest within one month of receipt of the request, for the reasons.");
			p43_nodes.forEach(detach);
			p44 = claim_element(div0_nodes, "P", {});
			var p44_nodes = children(p44);
			t207 = claim_text(p44_nodes, "The request to satisfy any of the above rights is reviewed each time in accordance with all applicable laws.");
			p44_nodes.forEach(detach);
			h28 = claim_element(div0_nodes, "H2", {});
			var h28_nodes = children(h28);
			t208 = claim_text(h28_nodes, "5. Other Important Information");
			h28_nodes.forEach(detach);
			h37 = claim_element(div0_nodes, "H3", {});
			var h37_nodes = children(h37);
			t209 = claim_text(h37_nodes, "5.1 Security Breaches");
			h37_nodes.forEach(detach);
			p45 = claim_element(div0_nodes, "P", {});
			var p45_nodes = children(p45);
			em30 = claim_element(p45_nodes, "EM", {});
			var em30_nodes = children(em30);
			t210 = claim_text(em30_nodes, "We monitor for and try to prevent security breaches.");
			em30_nodes.forEach(detach);
			p45_nodes.forEach(detach);
			p46 = claim_element(div0_nodes, "P", {});
			var p46_nodes = children(p46);
			t211 = claim_text(p46_nodes, "We implement security safeguards designed to protect your data, such as ");
			strong77 = claim_element(p46_nodes, "STRONG", {});
			var strong77_nodes = children(strong77);
			t212 = claim_text(strong77_nodes, "HTTPS");
			strong77_nodes.forEach(detach);
			t213 = claim_text(p46_nodes, ". We regularly monitor our systems for possible vulnerabilities and attacks. However, we cannot warrant the security of any information that you send us. There is no guarantee that data may not be accessed, disclosed, altered, or destroyed by breach of any of our physical, technical, or managerial safeguards.");
			p46_nodes.forEach(detach);
			p47 = claim_element(div0_nodes, "P", {});
			var p47_nodes = children(p47);
			t214 = claim_text(p47_nodes, "In case of a security breach, ");
			strong78 = claim_element(p47_nodes, "STRONG", {});
			var strong78_nodes = children(strong78);
			t215 = claim_text(strong78_nodes, "“Chalkia”");
			strong78_nodes.forEach(detach);
			t216 = claim_text(p47_nodes, " will inform all concerned within 72 hours.");
			p47_nodes.forEach(detach);
			h38 = claim_element(div0_nodes, "H3", {});
			var h38_nodes = children(h38);
			t217 = claim_text(h38_nodes, "5.2 Contact Information");
			h38_nodes.forEach(detach);
			p48 = claim_element(div0_nodes, "P", {});
			var p48_nodes = children(p48);
			em31 = claim_element(p48_nodes, "EM", {});
			var em31_nodes = children(em31);
			t218 = claim_text(em31_nodes, "You can contact us for any questions.");
			em31_nodes.forEach(detach);
			p48_nodes.forEach(detach);
			p49 = claim_element(div0_nodes, "P", {});
			var p49_nodes = children(p49);
			t219 = claim_text(p49_nodes, "You may contact us for any questions about this ");
			strong79 = claim_element(p49_nodes, "STRONG", {});
			var strong79_nodes = children(strong79);
			t220 = claim_text(strong79_nodes, "Privacy Policy");
			strong79_nodes.forEach(detach);
			t221 = claim_text(p49_nodes, " by sending an email to ");
			strong80 = claim_element(p49_nodes, "STRONG", {});
			var strong80_nodes = children(strong80);
			t222 = claim_text(strong80_nodes, "info [at] chalkia.com");
			strong80_nodes.forEach(detach);
			t223 = claim_text(p49_nodes, ".");
			p49_nodes.forEach(detach);
			h39 = claim_element(div0_nodes, "H3", {});
			var h39_nodes = children(h39);
			t224 = claim_text(h39_nodes, "5.3 Institutional Framework For The Protection Of Personal Data");
			h39_nodes.forEach(detach);
			p50 = claim_element(div0_nodes, "P", {});
			var p50_nodes = children(p50);
			em32 = claim_element(p50_nodes, "EM", {});
			var em32_nodes = children(em32);
			t225 = claim_text(em32_nodes, "The legislation governing the present text.");
			em32_nodes.forEach(detach);
			p50_nodes.forEach(detach);
			p51 = claim_element(div0_nodes, "P", {});
			var p51_nodes = children(p51);
			strong81 = claim_element(p51_nodes, "STRONG", {});
			var strong81_nodes = children(strong81);
			t226 = claim_text(strong81_nodes, "Greece");
			strong81_nodes.forEach(detach);
			t227 = claim_text(p51_nodes, ": Law 2472/1997, Law 3471/2006");
			p51_nodes.forEach(detach);
			p52 = claim_element(div0_nodes, "P", {});
			var p52_nodes = children(p52);
			strong82 = claim_element(p52_nodes, "STRONG", {});
			var strong82_nodes = children(strong82);
			t228 = claim_text(strong82_nodes, "European Union");
			strong82_nodes.forEach(detach);
			t229 = claim_text(p52_nodes, ": Directive 95/46/EC, 2002/58/EC, 2009/136/EC");
			p52_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a_1, "target", "_blank");
			attr(a_1, "rel", "noopener noreferrer nofollow");
			attr(a_1, "class", "link link");
			attr(a_1, "href", "https://policies.google.com/privacy");
			attr(div0, "class", "content");
			attr(div1, "class", "section has-content");
			attr(div1, "id", "ofaxo");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, h1);
			append_hydration(h1, t0);
			append_hydration(div0, p0);
			append_hydration(p0, t1);
			append_hydration(p0, strong0);
			append_hydration(strong0, t2);
			append_hydration(p0, t3);
			append_hydration(div0, p1);
			append_hydration(p1, t4);
			append_hydration(p1, strong1);
			append_hydration(strong1, t5);
			append_hydration(p1, t6);
			append_hydration(div0, h20);
			append_hydration(h20, t7);
			append_hydration(div0, p2);
			append_hydration(p2, em0);
			append_hydration(em0, t8);
			append_hydration(p2, strong2);
			append_hydration(strong2, em1);
			append_hydration(em1, t9);
			append_hydration(p2, em2);
			append_hydration(em2, t10);
			append_hydration(p2, strong3);
			append_hydration(strong3, em3);
			append_hydration(em3, t11);
			append_hydration(p2, em4);
			append_hydration(em4, t12);
			append_hydration(p2, strong4);
			append_hydration(strong4, em5);
			append_hydration(em5, t13);
			append_hydration(p2, em6);
			append_hydration(em6, t14);
			append_hydration(p2, strong5);
			append_hydration(strong5, em7);
			append_hydration(em7, t15);
			append_hydration(p2, em8);
			append_hydration(em8, t16);
			append_hydration(div0, p3);
			append_hydration(p3, t17);
			append_hydration(p3, strong6);
			append_hydration(strong6, t18);
			append_hydration(p3, t19);
			append_hydration(p3, strong7);
			append_hydration(strong7, t20);
			append_hydration(p3, t21);
			append_hydration(p3, strong8);
			append_hydration(strong8, t22);
			append_hydration(p3, t23);
			append_hydration(p3, strong9);
			append_hydration(strong9, t24);
			append_hydration(p3, t25);
			append_hydration(p3, strong10);
			append_hydration(strong10, t26);
			append_hydration(p3, t27);
			append_hydration(p3, strong11);
			append_hydration(strong11, t28);
			append_hydration(p3, t29);
			append_hydration(div0, p4);
			append_hydration(p4, t30);
			append_hydration(p4, strong12);
			append_hydration(strong12, t31);
			append_hydration(p4, t32);
			append_hydration(p4, strong13);
			append_hydration(strong13, t33);
			append_hydration(p4, t34);
			append_hydration(p4, strong14);
			append_hydration(strong14, t35);
			append_hydration(p4, t36);
			append_hydration(p4, strong15);
			append_hydration(strong15, t37);
			append_hydration(p4, t38);
			append_hydration(p4, strong16);
			append_hydration(strong16, t39);
			append_hydration(p4, t40);
			append_hydration(p4, strong17);
			append_hydration(strong17, t41);
			append_hydration(p4, t42);
			append_hydration(div0, h21);
			append_hydration(h21, t43);
			append_hydration(div0, p5);
			append_hydration(p5, t44);
			append_hydration(p5, strong18);
			append_hydration(strong18, t45);
			append_hydration(p5, t46);
			append_hydration(p5, strong19);
			append_hydration(strong19, t47);
			append_hydration(p5, t48);
			append_hydration(p5, strong20);
			append_hydration(strong20, t49);
			append_hydration(p5, t50);
			append_hydration(div0, h22);
			append_hydration(h22, t51);
			append_hydration(div0, p6);
			append_hydration(p6, strong21);
			append_hydration(strong21, em9);
			append_hydration(em9, t52);
			append_hydration(strong21, t53);
			append_hydration(strong21, em10);
			append_hydration(em10, t54);
			append_hydration(p6, em11);
			append_hydration(em11, t55);
			append_hydration(p6, strong22);
			append_hydration(strong22, em12);
			append_hydration(em12, t56);
			append_hydration(p6, em13);
			append_hydration(em13, t57);
			append_hydration(div0, p7);
			append_hydration(p7, t58);
			append_hydration(p7, strong23);
			append_hydration(strong23, t59);
			append_hydration(p7, t60);
			append_hydration(p7, strong24);
			append_hydration(strong24, t61);
			append_hydration(p7, t62);
			append_hydration(div0, p8);
			append_hydration(p8, t63);
			append_hydration(p8, strong25);
			append_hydration(strong25, t64);
			append_hydration(p8, t65);
			append_hydration(p8, strong26);
			append_hydration(strong26, t66);
			append_hydration(p8, t67);
			append_hydration(div0, p9);
			append_hydration(p9, t68);
			append_hydration(p9, strong27);
			append_hydration(strong27, t69);
			append_hydration(p9, t70);
			append_hydration(p9, strong28);
			append_hydration(strong28, t71);
			append_hydration(p9, t72);
			append_hydration(p9, strong29);
			append_hydration(strong29, t73);
			append_hydration(p9, t74);
			append_hydration(div0, h23);
			append_hydration(h23, t75);
			append_hydration(div0, p10);
			append_hydration(p10, em14);
			append_hydration(em14, t76);
			append_hydration(p10, strong30);
			append_hydration(strong30, em15);
			append_hydration(em15, t77);
			append_hydration(p10, em16);
			append_hydration(em16, t78);
			append_hydration(p10, strong31);
			append_hydration(strong31, em17);
			append_hydration(em17, t79);
			append_hydration(p10, em18);
			append_hydration(em18, t80);
			append_hydration(p10, strong32);
			append_hydration(strong32, em19);
			append_hydration(em19, t81);
			append_hydration(p10, em20);
			append_hydration(em20, t82);
			append_hydration(div0, p11);
			append_hydration(p11, strong33);
			append_hydration(strong33, t83);
			append_hydration(p11, t84);
			append_hydration(p11, strong34);
			append_hydration(strong34, t85);
			append_hydration(p11, t86);
			append_hydration(p11, strong35);
			append_hydration(strong35, t87);
			append_hydration(p11, t88);
			append_hydration(p11, strong36);
			append_hydration(strong36, t89);
			append_hydration(p11, t90);
			append_hydration(div0, p12);
			append_hydration(p12, t91);
			append_hydration(p12, strong37);
			append_hydration(strong37, t92);
			append_hydration(p12, t93);
			append_hydration(p12, strong38);
			append_hydration(strong38, t94);
			append_hydration(p12, t95);
			append_hydration(p12, strong39);
			append_hydration(strong39, t96);
			append_hydration(p12, t97);
			append_hydration(div0, h24);
			append_hydration(h24, t98);
			append_hydration(div0, p13);
			append_hydration(p13, t99);
			append_hydration(p13, strong40);
			append_hydration(strong40, t100);
			append_hydration(p13, t101);
			append_hydration(p13, strong41);
			append_hydration(strong41, t102);
			append_hydration(p13, t103);
			append_hydration(div0, h30);
			append_hydration(h30, t104);
			append_hydration(div0, p14);
			append_hydration(p14, em21);
			append_hydration(em21, t105);
			append_hydration(div0, p15);
			append_hydration(p15, t106);
			append_hydration(p15, strong42);
			append_hydration(strong42, t107);
			append_hydration(p15, t108);
			append_hydration(p15, strong43);
			append_hydration(strong43, t109);
			append_hydration(p15, t110);
			append_hydration(p15, strong44);
			append_hydration(strong44, t111);
			append_hydration(p15, t112);
			append_hydration(p15, strong45);
			append_hydration(strong45, t113);
			append_hydration(p15, t114);
			append_hydration(div0, p16);
			append_hydration(p16, t115);
			append_hydration(p16, strong46);
			append_hydration(strong46, t116);
			append_hydration(p16, t117);
			append_hydration(p16, strong47);
			append_hydration(strong47, t118);
			append_hydration(p16, t119);
			append_hydration(p16, strong48);
			append_hydration(strong48, t120);
			append_hydration(p16, t121);
			append_hydration(p16, strong49);
			append_hydration(strong49, t122);
			append_hydration(p16, t123);
			append_hydration(div0, h31);
			append_hydration(h31, t124);
			append_hydration(div0, p17);
			append_hydration(p17, em22);
			append_hydration(em22, t125);
			append_hydration(div0, p18);
			append_hydration(p18, t126);
			append_hydration(div0, h32);
			append_hydration(h32, t127);
			append_hydration(div0, p19);
			append_hydration(p19, em23);
			append_hydration(em23, t128);
			append_hydration(div0, p20);
			append_hydration(p20, t129);
			append_hydration(p20, strong50);
			append_hydration(strong50, t130);
			append_hydration(p20, t131);
			append_hydration(p20, strong51);
			append_hydration(strong51, t132);
			append_hydration(p20, t133);
			append_hydration(div0, h25);
			append_hydration(h25, t134);
			append_hydration(div0, p21);
			append_hydration(p21, strong52);
			append_hydration(strong52, t135);
			append_hydration(p21, t136);
			append_hydration(p21, strong53);
			append_hydration(strong53, t137);
			append_hydration(p21, t138);
			append_hydration(div0, h26);
			append_hydration(h26, t139);
			append_hydration(div0, h33);
			append_hydration(h33, t140);
			append_hydration(div0, p22);
			append_hydration(p22, em24);
			append_hydration(em24, t141);
			append_hydration(p22, strong54);
			append_hydration(strong54, em25);
			append_hydration(em25, t142);
			append_hydration(p22, em26);
			append_hydration(em26, t143);
			append_hydration(div0, p23);
			append_hydration(p23, t144);
			append_hydration(p23, strong55);
			append_hydration(strong55, t145);
			append_hydration(p23, t146);
			append_hydration(p23, strong56);
			append_hydration(strong56, t147);
			append_hydration(p23, t148);
			append_hydration(div0, p24);
			append_hydration(p24, strong57);
			append_hydration(strong57, t149);
			append_hydration(p24, t150);
			append_hydration(div0, p25);
			append_hydration(p25, t151);
			append_hydration(p25, strong58);
			append_hydration(strong58, t152);
			append_hydration(p25, t153);
			append_hydration(div0, p26);
			append_hydration(p26, t154);
			append_hydration(p26, strong59);
			append_hydration(strong59, t155);
			append_hydration(p26, t156);
			append_hydration(p26, strong60);
			append_hydration(strong60, t157);
			append_hydration(p26, t158);
			append_hydration(p26, strong61);
			append_hydration(strong61, t159);
			append_hydration(p26, t160);
			append_hydration(div0, p27);
			append_hydration(p27, t161);
			append_hydration(p27, strong62);
			append_hydration(strong62, t162);
			append_hydration(p27, t163);
			append_hydration(p27, strong63);
			append_hydration(strong63, t164);
			append_hydration(p27, t165);
			append_hydration(p27, strong64);
			append_hydration(strong64, t166);
			append_hydration(p27, t167);
			append_hydration(p27, strong65);
			append_hydration(strong65, t168);
			append_hydration(p27, t169);
			append_hydration(div0, p28);
			append_hydration(p28, t170);
			append_hydration(p28, strong66);
			append_hydration(strong66, t171);
			append_hydration(p28, t172);
			append_hydration(p28, a_1);
			append_hydration(a_1, t173);
			append_hydration(p28, t174);
			append_hydration(div0, h34);
			append_hydration(h34, t175);
			append_hydration(div0, p29);
			append_hydration(p29, em27);
			append_hydration(em27, t176);
			append_hydration(div0, p30);
			append_hydration(p30, t177);
			append_hydration(div0, p31);
			append_hydration(p31, t178);
			append_hydration(div0, h27);
			append_hydration(h27, t179);
			append_hydration(div0, h35);
			append_hydration(h35, t180);
			append_hydration(div0, p32);
			append_hydration(p32, em28);
			append_hydration(em28, t181);
			append_hydration(div0, p33);
			append_hydration(p33, strong67);
			append_hydration(strong67, t182);
			append_hydration(p33, t183);
			append_hydration(div0, p34);
			append_hydration(p34, t184);
			append_hydration(div0, h36);
			append_hydration(h36, t185);
			append_hydration(div0, p35);
			append_hydration(p35, em29);
			append_hydration(em29, t186);
			append_hydration(div0, p36);
			append_hydration(p36, t187);
			append_hydration(div0, ul);
			append_hydration(ul, li0);
			append_hydration(li0, p37);
			append_hydration(p37, strong68);
			append_hydration(strong68, t188);
			append_hydration(p37, t189);
			append_hydration(ul, li1);
			append_hydration(li1, p38);
			append_hydration(p38, strong69);
			append_hydration(strong69, t190);
			append_hydration(p38, t191);
			append_hydration(ul, li2);
			append_hydration(li2, p39);
			append_hydration(p39, strong70);
			append_hydration(strong70, t192);
			append_hydration(p39, t193);
			append_hydration(ul, li3);
			append_hydration(li3, p40);
			append_hydration(p40, strong71);
			append_hydration(strong71, t194);
			append_hydration(p40, t195);
			append_hydration(ul, li4);
			append_hydration(li4, p41);
			append_hydration(p41, strong72);
			append_hydration(strong72, t196);
			append_hydration(p41, t197);
			append_hydration(ul, li5);
			append_hydration(li5, p42);
			append_hydration(p42, strong73);
			append_hydration(strong73, t198);
			append_hydration(p42, t199);
			append_hydration(div0, p43);
			append_hydration(p43, br);
			append_hydration(p43, t200);
			append_hydration(p43, strong74);
			append_hydration(strong74, t201);
			append_hydration(p43, t202);
			append_hydration(p43, strong75);
			append_hydration(strong75, t203);
			append_hydration(p43, t204);
			append_hydration(p43, strong76);
			append_hydration(strong76, t205);
			append_hydration(p43, t206);
			append_hydration(div0, p44);
			append_hydration(p44, t207);
			append_hydration(div0, h28);
			append_hydration(h28, t208);
			append_hydration(div0, h37);
			append_hydration(h37, t209);
			append_hydration(div0, p45);
			append_hydration(p45, em30);
			append_hydration(em30, t210);
			append_hydration(div0, p46);
			append_hydration(p46, t211);
			append_hydration(p46, strong77);
			append_hydration(strong77, t212);
			append_hydration(p46, t213);
			append_hydration(div0, p47);
			append_hydration(p47, t214);
			append_hydration(p47, strong78);
			append_hydration(strong78, t215);
			append_hydration(p47, t216);
			append_hydration(div0, h38);
			append_hydration(h38, t217);
			append_hydration(div0, p48);
			append_hydration(p48, em31);
			append_hydration(em31, t218);
			append_hydration(div0, p49);
			append_hydration(p49, t219);
			append_hydration(p49, strong79);
			append_hydration(strong79, t220);
			append_hydration(p49, t221);
			append_hydration(p49, strong80);
			append_hydration(strong80, t222);
			append_hydration(p49, t223);
			append_hydration(div0, h39);
			append_hydration(h39, t224);
			append_hydration(div0, p50);
			append_hydration(p50, em32);
			append_hydration(em32, t225);
			append_hydration(div0, p51);
			append_hydration(p51, strong81);
			append_hydration(strong81, t226);
			append_hydration(p51, t227);
			append_hydration(div0, p52);
			append_hydration(p52, strong82);
			append_hydration(strong82, t228);
			append_hydration(p52, t229);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { social } = $$props;
	let { na } = $$props;
	let { nav } = $$props;
	let { a } = $$props;
	let { add } = $$props;
	let { addre } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;

	$$self.$$set = $$props => {
		if ('social' in $$props) $$invalidate(0, social = $$props.social);
		if ('na' in $$props) $$invalidate(1, na = $$props.na);
		if ('nav' in $$props) $$invalidate(2, nav = $$props.nav);
		if ('a' in $$props) $$invalidate(3, a = $$props.a);
		if ('add' in $$props) $$invalidate(4, add = $$props.add);
		if ('addre' in $$props) $$invalidate(5, addre = $$props.addre);
		if ('address' in $$props) $$invalidate(6, address = $$props.address);
		if ('phone' in $$props) $$invalidate(7, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(8, email = $$props.email);
		if ('seo_title' in $$props) $$invalidate(9, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(10, seo_description = $$props.seo_description);
	};

	return [
		social,
		na,
		nav,
		a,
		add,
		addre,
		address,
		phone,
		email,
		seo_title,
		seo_description
	];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			social: 0,
			na: 1,
			nav: 2,
			a: 3,
			add: 4,
			addre: 5,
			address: 6,
			phone: 7,
			email: 8,
			seo_title: 9,
			seo_description: 10
		});
	}
}

/* generated by Svelte v3.55.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[16] = list[i].link;
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[16] = list[i].link;
	child_ctx[19] = list[i].title;
	child_ctx[20] = list[i].icon;
	return child_ctx;
}

// (96:8) {#each social as {link, title, icon}}
function create_each_block_1$1(ctx) {
	let a_1;
	let icon;
	let t;
	let a_1_href_value;
	let a_1_title_value;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[20] } });

	return {
		c() {
			a_1 = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			a_1 = claim_element(nodes, "A", { href: true, title: true, class: true });
			var a_1_nodes = children(a_1);
			claim_component(icon.$$.fragment, a_1_nodes);
			t = claim_space(a_1_nodes);
			a_1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a_1, "href", a_1_href_value = /*link*/ ctx[16]);
			attr(a_1, "title", a_1_title_value = /*title*/ ctx[19]);
			attr(a_1, "class", "svelte-ujoeq8");
		},
		m(target, anchor) {
			insert_hydration(target, a_1, anchor);
			mount_component(icon, a_1, null);
			append_hydration(a_1, t);
			current = true;
		},
		p(ctx, dirty) {
			const icon_changes = {};
			if (dirty & /*social*/ 1) icon_changes.icon = /*icon*/ ctx[20];
			icon.$set(icon_changes);

			if (!current || dirty & /*social*/ 1 && a_1_href_value !== (a_1_href_value = /*link*/ ctx[16])) {
				attr(a_1, "href", a_1_href_value);
			}

			if (!current || dirty & /*social*/ 1 && a_1_title_value !== (a_1_title_value = /*title*/ ctx[19])) {
				attr(a_1, "title", a_1_title_value);
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a_1);
			destroy_component(icon);
		}
	};
}

// (105:6) {#each nav as {link}}
function create_each_block$1(ctx) {
	let a_1;
	let h3;
	let t_value = /*link*/ ctx[16].label + "";
	let t;
	let a_1_href_value;

	return {
		c() {
			a_1 = element("a");
			h3 = element("h3");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a_1 = claim_element(nodes, "A", { href: true, class: true });
			var a_1_nodes = children(a_1);
			h3 = claim_element(a_1_nodes, "H3", {});
			var h3_nodes = children(h3);
			t = claim_text(h3_nodes, t_value);
			h3_nodes.forEach(detach);
			a_1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a_1, "href", a_1_href_value = /*link*/ ctx[16].url);
			attr(a_1, "class", "svelte-ujoeq8");
			toggle_class(a_1, "active", /*link*/ ctx[16].active === true);
		},
		m(target, anchor) {
			insert_hydration(target, a_1, anchor);
			append_hydration(a_1, h3);
			append_hydration(h3, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 2 && t_value !== (t_value = /*link*/ ctx[16].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 2 && a_1_href_value !== (a_1_href_value = /*link*/ ctx[16].url)) {
				attr(a_1, "href", a_1_href_value);
			}

			if (dirty & /*nav*/ 2) {
				toggle_class(a_1, "active", /*link*/ ctx[16].active === true);
			}
		},
		d(detaching) {
			if (detaching) detach(a_1);
		}
	};
}

function create_fragment$4(ctx) {
	let div7;
	let div6;
	let footer;
	let div4;
	let div1;
	let h20;
	let t0;
	let t1;
	let html_tag;
	let t2;
	let a_1;
	let t3;
	let a_1_href_value;
	let t4;
	let div0;
	let t5;
	let div2;
	let h21;
	let t6;
	let t7;
	let t8;
	let div3;
	let img;
	let img_src_value;
	let img_alt_value;
	let t9;
	let div5;
	let t10;
	let t11;
	let t12;
	let current;
	let each_value_1 = /*social*/ ctx[0];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	const out = i => transition_out(each_blocks_1[i], 1, 1, () => {
		each_blocks_1[i] = null;
	});

	let each_value = /*nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div7 = element("div");
			div6 = element("div");
			footer = element("footer");
			div4 = element("div");
			div1 = element("div");
			h20 = element("h2");
			t0 = text("CHALKIA");
			t1 = space();
			html_tag = new HtmlTagHydration(false);
			t2 = space();
			a_1 = element("a");
			t3 = text(/*phone*/ ctx[3]);
			t4 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t5 = space();
			div2 = element("div");
			h21 = element("h2");
			t6 = text("MENU");
			t7 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t8 = space();
			div3 = element("div");
			img = element("img");
			t9 = space();
			div5 = element("div");
			t10 = text("© 2022");
			t11 = text(/*cp*/ ctx[5]);
			t12 = text(" Foteini Chalkia - All rights reserved");
			this.h();
		},
		l(nodes) {
			div7 = claim_element(nodes, "DIV", { class: true, id: true });
			var div7_nodes = children(div7);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			footer = claim_element(div6_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			div4 = claim_element(footer_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div1 = claim_element(div4_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			h20 = claim_element(div1_nodes, "H2", { class: true });
			var h20_nodes = children(h20);
			t0 = claim_text(h20_nodes, "CHALKIA");
			h20_nodes.forEach(detach);
			t1 = claim_space(div1_nodes);
			html_tag = claim_html_tag(div1_nodes, false);
			t2 = claim_space(div1_nodes);
			a_1 = claim_element(div1_nodes, "A", { href: true, title: true, class: true });
			var a_1_nodes = children(a_1);
			t3 = claim_text(a_1_nodes, /*phone*/ ctx[3]);
			a_1_nodes.forEach(detach);
			t4 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(div0_nodes);
			}

			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t5 = claim_space(div4_nodes);
			div2 = claim_element(div4_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			h21 = claim_element(div2_nodes, "H2", { class: true });
			var h21_nodes = children(h21);
			t6 = claim_text(h21_nodes, "MENU");
			h21_nodes.forEach(detach);
			t7 = claim_space(div2_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div2_nodes);
			}

			div2_nodes.forEach(detach);
			t8 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			img = claim_element(div3_nodes, "IMG", { src: true, alt: true, class: true });
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			t9 = claim_space(footer_nodes);
			div5 = claim_element(footer_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			t10 = claim_text(div5_nodes, "© 2022");
			t11 = claim_text(div5_nodes, /*cp*/ ctx[5]);
			t12 = claim_text(div5_nodes, " Foteini Chalkia - All rights reserved");
			div5_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h20, "class", "svelte-ujoeq8");
			html_tag.a = t2;
			attr(a_1, "href", a_1_href_value = "tel:" + /*phone*/ ctx[3].replace('+', '00').split(' ').join(''));
			attr(a_1, "title", "Call us");
			attr(a_1, "class", "svelte-ujoeq8");
			attr(div0, "class", "social svelte-ujoeq8");
			attr(div1, "class", "svelte-ujoeq8");
			attr(h21, "class", "svelte-ujoeq8");
			attr(div2, "class", "svelte-ujoeq8");
			if (!src_url_equal(img.src, img_src_value = /*badges*/ ctx[4].url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*badges*/ ctx[4].alt);
			attr(img, "class", "svelte-ujoeq8");
			attr(div3, "class", "badges svelte-ujoeq8");
			attr(div4, "class", "section-container svelte-ujoeq8");
			attr(div5, "class", "copyright svelte-ujoeq8");
			attr(footer, "class", "svelte-ujoeq8");
			attr(div6, "class", "component");
			attr(div7, "class", "section has-component");
			attr(div7, "id", "ugrhc");
		},
		m(target, anchor) {
			insert_hydration(target, div7, anchor);
			append_hydration(div7, div6);
			append_hydration(div6, footer);
			append_hydration(footer, div4);
			append_hydration(div4, div1);
			append_hydration(div1, h20);
			append_hydration(h20, t0);
			append_hydration(div1, t1);
			html_tag.m(/*address*/ ctx[2], div1);
			append_hydration(div1, t2);
			append_hydration(div1, a_1);
			append_hydration(a_1, t3);
			append_hydration(div1, t4);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].m(div0, null);
			}

			append_hydration(div4, t5);
			append_hydration(div4, div2);
			append_hydration(div2, h21);
			append_hydration(h21, t6);
			append_hydration(div2, t7);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].m(div2, null);
			}

			append_hydration(div4, t8);
			append_hydration(div4, div3);
			append_hydration(div3, img);
			append_hydration(footer, t9);
			append_hydration(footer, div5);
			append_hydration(div5, t10);
			append_hydration(div5, t11);
			append_hydration(div5, t12);
			current = true;
		},
		p(ctx, [dirty]) {
			if (!current || dirty & /*address*/ 4) html_tag.p(/*address*/ ctx[2]);
			if (!current || dirty & /*phone*/ 8) set_data(t3, /*phone*/ ctx[3]);

			if (!current || dirty & /*phone*/ 8 && a_1_href_value !== (a_1_href_value = "tel:" + /*phone*/ ctx[3].replace('+', '00').split(' ').join(''))) {
				attr(a_1, "href", a_1_href_value);
			}

			if (dirty & /*social*/ 1) {
				each_value_1 = /*social*/ ctx[0];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
						transition_in(each_blocks_1[i], 1);
					} else {
						each_blocks_1[i] = create_each_block_1$1(child_ctx);
						each_blocks_1[i].c();
						transition_in(each_blocks_1[i], 1);
						each_blocks_1[i].m(div0, null);
					}
				}

				group_outros();

				for (i = each_value_1.length; i < each_blocks_1.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (dirty & /*nav*/ 2) {
				each_value = /*nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div2, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (!current || dirty & /*badges*/ 16 && !src_url_equal(img.src, img_src_value = /*badges*/ ctx[4].url)) {
				attr(img, "src", img_src_value);
			}

			if (!current || dirty & /*badges*/ 16 && img_alt_value !== (img_alt_value = /*badges*/ ctx[4].alt)) {
				attr(img, "alt", img_alt_value);
			}

			if (!current || dirty & /*cp*/ 32) set_data(t11, /*cp*/ ctx[5]);
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value_1.length; i += 1) {
				transition_in(each_blocks_1[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks_1 = each_blocks_1.filter(Boolean);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				transition_out(each_blocks_1[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div7);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { social } = $$props;
	let { na } = $$props;
	let { nav } = $$props;
	let { a } = $$props;
	let { add } = $$props;
	let { addre } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { lpoea } = $$props;
	let { ugrhc } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;
	let { ofaxo } = $$props;
	let { badges } = $$props;
	let cp = '';

	onMount(async () => {
		let y = new Date().getFullYear();
		if (y > 2022) $$invalidate(5, cp = `-${y}`);
	});

	$$self.$$set = $$props => {
		if ('social' in $$props) $$invalidate(0, social = $$props.social);
		if ('na' in $$props) $$invalidate(6, na = $$props.na);
		if ('nav' in $$props) $$invalidate(1, nav = $$props.nav);
		if ('a' in $$props) $$invalidate(7, a = $$props.a);
		if ('add' in $$props) $$invalidate(8, add = $$props.add);
		if ('addre' in $$props) $$invalidate(9, addre = $$props.addre);
		if ('address' in $$props) $$invalidate(2, address = $$props.address);
		if ('phone' in $$props) $$invalidate(3, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(10, email = $$props.email);
		if ('lpoea' in $$props) $$invalidate(11, lpoea = $$props.lpoea);
		if ('ugrhc' in $$props) $$invalidate(12, ugrhc = $$props.ugrhc);
		if ('seo_title' in $$props) $$invalidate(13, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(14, seo_description = $$props.seo_description);
		if ('ofaxo' in $$props) $$invalidate(15, ofaxo = $$props.ofaxo);
		if ('badges' in $$props) $$invalidate(4, badges = $$props.badges);
	};

	return [
		social,
		nav,
		address,
		phone,
		badges,
		cp,
		na,
		a,
		add,
		addre,
		email,
		lpoea,
		ugrhc,
		seo_title,
		seo_description,
		ofaxo
	];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			social: 0,
			na: 6,
			nav: 1,
			a: 7,
			add: 8,
			addre: 9,
			address: 2,
			phone: 3,
			email: 10,
			lpoea: 11,
			ugrhc: 12,
			seo_title: 13,
			seo_description: 14,
			ofaxo: 15,
			badges: 4
		});
	}
}

/* generated by Svelte v3.55.0 */

function instance$5($$self, $$props, $$invalidate) {
	let { social } = $$props;
	let { na } = $$props;
	let { nav } = $$props;
	let { a } = $$props;
	let { add } = $$props;
	let { addre } = $$props;
	let { address } = $$props;
	let { phone } = $$props;
	let { email } = $$props;
	let { seo_title } = $$props;
	let { seo_description } = $$props;

	$$self.$$set = $$props => {
		if ('social' in $$props) $$invalidate(0, social = $$props.social);
		if ('na' in $$props) $$invalidate(1, na = $$props.na);
		if ('nav' in $$props) $$invalidate(2, nav = $$props.nav);
		if ('a' in $$props) $$invalidate(3, a = $$props.a);
		if ('add' in $$props) $$invalidate(4, add = $$props.add);
		if ('addre' in $$props) $$invalidate(5, addre = $$props.addre);
		if ('address' in $$props) $$invalidate(6, address = $$props.address);
		if ('phone' in $$props) $$invalidate(7, phone = $$props.phone);
		if ('email' in $$props) $$invalidate(8, email = $$props.email);
		if ('seo_title' in $$props) $$invalidate(9, seo_title = $$props.seo_title);
		if ('seo_description' in $$props) $$invalidate(10, seo_description = $$props.seo_description);
	};

	return [
		social,
		na,
		nav,
		a,
		add,
		addre,
		address,
		phone,
		email,
		seo_title,
		seo_description
	];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, null, safe_not_equal, {
			social: 0,
			na: 1,
			nav: 2,
			a: 3,
			add: 4,
			addre: 5,
			address: 6,
			phone: 7,
			email: 8,
			seo_title: 9,
			seo_description: 10
		});
	}
}

/* generated by Svelte v3.55.0 */

function create_fragment$5(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let current;

	component_0 = new Component({
			props: {
				social: [
					{
						"title": "Follow us on facebook",
						"link": "https://www.facebook.com/chalkia.official",
						"icon": "fa6-brands:square-facebook"
					},
					{
						"title": "Follow us on twitter",
						"link": "https://twitter.com/foteini_chalkia",
						"icon": "fa6-brands:square-twitter"
					},
					{
						"title": "Follow us on instagram",
						"link": "https://www.instagram.com/foteinichalkia_/",
						"icon": "fa6-brands:square-instagram"
					},
					{
						"title": "Follow us on pinterest",
						"link": "https://pinterest.com/Foteini_Chalkia/",
						"icon": "fa6-brands:square-pinterest"
					}
				],
				na: [{}, {}],
				nav: [
					{
						"link": {
							"label": "Bridal",
							"url": "/bridal",
							"active": false
						}
					},
					{
						"link": {
							"label": "Haute Couture",
							"url": "/haute-couture",
							"active": false
						}
					},
					{
						"link": { "label": "About", "url": "/about" }
					},
					{
						"link": {
							"label": "Editorials",
							"url": "/editorials"
						}
					},
					{
						"link": { "label": "Press", "url": "/press" }
					},
					{
						"link": { "label": "Contact", "url": "/contact" }
					}
				],
				a: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				add: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				addre: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				address: "<p>36 Damareos Str.</p>\n<p>11633 Athens, Greece</p>",
				phone: "+30 210 220 4390",
				email: "info@chalkia.com",
				seo_title: "About | Foteini Chalkia",
				seo_description: "She is inspired by silhouettes, fabrics, sounds and stories. The modern fearless woman is her muse."
			}
		});

	component_1 = new Component$2({
			props: {
				social: [
					{
						"title": "Follow us on facebook",
						"link": "https://www.facebook.com/chalkia.official",
						"icon": "fa6-brands:square-facebook"
					},
					{
						"title": "Follow us on twitter",
						"link": "https://twitter.com/foteini_chalkia",
						"icon": "fa6-brands:square-twitter"
					},
					{
						"title": "Follow us on instagram",
						"link": "https://www.instagram.com/foteinichalkia_/",
						"icon": "fa6-brands:square-instagram"
					},
					{
						"title": "Follow us on pinterest",
						"link": "https://pinterest.com/Foteini_Chalkia/",
						"icon": "fa6-brands:square-pinterest"
					}
				],
				na: [{}, {}],
				nav: [
					{
						"link": {
							"label": "Bridal",
							"url": "/bridal",
							"active": false
						}
					},
					{
						"link": {
							"label": "Haute Couture",
							"url": "/haute-couture",
							"active": false
						}
					},
					{
						"link": { "label": "About", "url": "/about" }
					},
					{
						"link": {
							"label": "Editorials",
							"url": "/editorials"
						}
					},
					{
						"link": { "label": "Press", "url": "/press" }
					},
					{
						"link": { "label": "Contact", "url": "/contact" }
					}
				],
				a: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				add: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				addre: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				address: "<p>36 Damareos Str.</p>\n<p>11633 Athens, Greece</p>",
				phone: "+30 210 220 4390",
				email: "info@chalkia.com",
				lpoea: {},
				ugrhc: {
					"badges": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/assets/sustainable.png",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/assets/sustainable.png",
						"alt": "Sustainable Materials",
						"size": null
					}
				},
				seo_title: "About | Foteini Chalkia",
				seo_description: "She is inspired by silhouettes, fabrics, sounds and stories. The modern fearless woman is her muse.",
				ofaxo: "<h1>Privacy Policy</h1><p>At <strong>“Chalkia”</strong>, we’re committed to protecting and respecting your privacy.</p><p>This <strong>Privacy Policy</strong> explains when and why we collect personal information, how we use it, the conditions under which we may disclose it to others and what choices you have.</p><h2>Introduction</h2><p><em>We are a company that specializes in architectural design. People use our </em><strong><em>Services</em></strong><em> to get informed about our services. Our </em><strong><em>Privacy Policy</em></strong><em> applies to any </em><strong><em>Visitor</em></strong><em> to our </em><strong><em>Services</em></strong><em>.</em></p><p>Our non-registered (<strong>“Visitors”</strong>) users get informed through our <strong>Services</strong>. All content and data on our <strong>Services</strong> is viewable to non-registered (<strong>“Visitors”</strong>) users. You don’t have to be a registered user (<strong>“Member”</strong>) to use our <strong>Services</strong>.</p><p>We use the term <strong>“Designated Countries”</strong> to refer to countries in the <strong>European Union</strong> (<strong>EU</strong>), <strong>European Economic Area</strong> (<strong>EEA</strong>), and <strong>Switzerland</strong>.</p><h2>Services</h2><p>This <strong>Privacy Policy</strong> applies to <strong>www.chalkia.com</strong> (<strong>“Services”</strong>).</p><h2>Data Controllers And Contracting Parties</h2><p><strong><em>“</em>Chalkia<em>”</em></strong><em> is the controller of your personal data in connection with our </em><strong><em>Services</em></strong><em> and the company’s electronic data processing system.</em></p><p>If you reside in the <strong>“Designated Countries”</strong>: <strong>“Chalkia”</strong> will be the controller of your personal data provided to, or collected by or for, or processed in connection with our Services.</p><p>If you reside outside of the <strong>“Designated Countries”</strong>: <strong>“Chalkia”</strong> will be the controller of your personal data provided to, or collected by or for, or processed in connection with, our Services.</p><p>As a <strong>Visitor</strong> of our <strong>Services</strong>, the collection, use and sharing of your personal data is subject to this <strong>Privacy Policy</strong> and updates.</p><h2>Change</h2><p><em>Changes to the </em><strong><em>Privacy Policy</em></strong><em> apply to your use of our </em><strong><em>Services</em></strong><em> after the </em><strong><em>“effective date”</em></strong><em>.</em></p><p><strong>“Chalkia”</strong> can modify this <strong>Privacy Policy</strong>, and if we make material changes to it, we will provide notice through our <strong>Services</strong>, or by other means, to provide you the opportunity to review the changes before they become effective. If you object to any changes, you may stop using our <strong>Services</strong>.</p><p>You acknowledge that your continued use of our <strong>Services</strong> after we publish or send a notice about our changes to this <strong>Privacy Policy</strong> means that the collection, use and sharing of your personal data is subject to the updated <strong>Privacy Policy</strong>.</p><h2>1. Data We Collect</h2><p>In order for the <strong>Visitor</strong> to contact us through our <strong>Services</strong> and get information about our services it is not necessary to give any personal data.</p><h3>1.1 Data From Your Device</h3><p><em>We receive data from your devices.</em></p><p>We collect a series of general data and information when users visit and use our <strong>Services</strong>. This general data and information are stored in the server log files. Collected may be (1) the browser types and versions used, (2) the operating system used to access our <strong>Services</strong>, (3) the website from which you reached our <strong>Services</strong> (so-called referrers), (4) the sub-websites, (5) the date and time of access to our <strong>Services</strong>, (6) an Internet protocol address (IP address), (7) the Internet service provider of the accessing system, and (8) any other similar data and information that may be used in the event of attacks on our information technology systems.</p><p>When using these general data and information, we do not draw any conclusions about the users. Rather, this information is needed to (1) deliver the content of our <strong>Services</strong> correctly, (2) optimize the content of our <strong>Services</strong>, (3) ensure the long-term viability of our information technology systems, and (4) provide law enforcement authorities with the information necessary for criminal prosecution in case of a cyber-attack. Therefore, we analyze anonymously collected data and information statistically, with the aim of increasing the data protection and data security of our enterprise, and to ensure an optimal level of protection for the personal data we process. The anonymous data of the server log files are stored separately from all personal data provided by the <strong>Visitors</strong> of our <strong>Services</strong>.</p><h3>1.2 Sensitive Data</h3><p><em>We do not gather sensitive personal data.</em></p><p>We do not gather sensitive personal data (e.g. health, genetic, biometric data; racial or ethnic origin, political opinions, religious or philosophical beliefs, trade union membership, sexual orientation, and criminal convictions). We expressly request that you do not provide any such sensitive data to us.</p><h3>1.3 Children’s Information</h3><p><em>Only with the consent of their parents or guardians.</em></p><p>Children have access to our <strong>Services</strong> only with the consent of their parents or guardians. If you learn that a child has provided us with personal information without consent, please contact us by sending an email to <strong>info [at] chalkia.com</strong>.</p><h2>2. How We Use Your Data</h2><p><strong>“Chalkia”</strong> will not process any <strong>Visitor’s</strong> personal data.</p><h2>3. How We Share Your Data</h2><h3>3.1 Google Analytics (With Anonymization Function)</h3><p><em>We share some of your personal data with </em><strong><em>Google Analytics</em></strong><em>.</em></p><p>We have integrated the component of <strong>Google Analytics</strong> (With Anonymization Function) in our <strong>Services</strong>.</p><p><strong>Google Analytics</strong> is a web analytics service. Web analytics is the collection, gathering, and analysis of data about the behavior of visitors to websites. Web analytics are mainly used for the optimization of a website and in order to carry out a cost-benefit analysis of Internet advertising.</p><p>The operator of the <strong>Google Analytics</strong> component is Google Inc., 1600 Amphitheatre Pkwy, Mountain View, CA 94043-1351, United States.</p><p>For the web analytics through <strong>Google Analytics</strong> our <strong>Services</strong> use the application “_gat. _anonymizeIp”. By means of this application your IP address of the Internet connection is abridged by <strong>Google</strong> and anonymized.</p><p>With each call-up to one of the individual pages into which a component from <strong>Google Analytics</strong> service was integrated, the web browser automatically sends data through the corresponding <strong>Google Analytics</strong> component. During the course of this technical procedure, <strong>Google Maps</strong> and <strong>Google</strong> is made aware of what specific page you visited.</p><p>Further information and the applicable data protection provisions of <strong>Google</strong> may be retrieved under <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link\" href=\"https://policies.google.com/privacy\">https://policies.google.com/privacy</a>.</p><h3>3.2 Third Parties</h3><p><em>We do not sell or rent your personal data to third parties.</em></p><p>We do not sell or rent your personal data to third parties.</p><p>We do not share your personal data with third parties for marketing purposes.</p><h2>4. Your Choices &amp; Obligations</h2><h3>4.1 Data Retention</h3><p><em>We keep your personal data until you request for their deletion.</em></p><p><strong>“Chalkia”</strong> keeps your personal data until you request for their deletion.</p><p>Tax information is exempt from the write-off process and is subject to mandatory tax compliance.</p><h3>4.2 Rights To Access And Control Your Personal Data</h3><p><em>You can access or request the deletion of your personal data.</em></p><p>With respect to your personal data, you retain the following rights:</p><ul><li><p><strong>Right of Access</strong>: You can send us a request in order to be informed about the personal data we keep for you.</p></li><li><p><strong>Right to Rectification</strong>: You can send us a request in order to ask us to change, update or correct your personal data, particularly if it’s inaccurate.</p></li><li><p><strong>Right to Erasure</strong>: You can send us a request in order to ask us to delete all or some of your personal data.</p></li><li><p><strong>Right to Restrict Processing</strong>: You can send us a request in order to ask us to limit the processing of all or some of your personal data.</p></li><li><p><strong>Right to Object Processing</strong>: You can send us a request in order to ask us to stop the processing of all or some of your personal data.</p></li><li><p><strong>Right to Data Portability</strong>: You can send us a request in order to ask us to send a copy of your personal data to you or to an organization of your choice.</p></li></ul><p><br>You may contact us to exercise any of the above rights regarding your personal data. <strong>“Chalkia”</strong> will respond to your request free of charge, without delay and in any case within one month of receipt of the request, except in exceptional circumstances, so that the deadline can be extended by another two months if necessary, taking into account the complexity of the request and/or the total number of requests. <strong>“Chalkia”</strong> will inform you of any extension within one month of receipt of the request and of the reasons for the delay. If your request can not be met, <strong>“Chalkia”</strong> will inform you without delay and at the latest within one month of receipt of the request, for the reasons.</p><p>The request to satisfy any of the above rights is reviewed each time in accordance with all applicable laws.</p><h2>5. Other Important Information</h2><h3>5.1 Security Breaches</h3><p><em>We monitor for and try to prevent security breaches.</em></p><p>We implement security safeguards designed to protect your data, such as <strong>HTTPS</strong>. We regularly monitor our systems for possible vulnerabilities and attacks. However, we cannot warrant the security of any information that you send us. There is no guarantee that data may not be accessed, disclosed, altered, or destroyed by breach of any of our physical, technical, or managerial safeguards.</p><p>In case of a security breach, <strong>“Chalkia”</strong> will inform all concerned within 72 hours.</p><h3>5.2 Contact Information</h3><p><em>You can contact us for any questions.</em></p><p>You may contact us for any questions about this <strong>Privacy Policy</strong> by sending an email to <strong>info [at] chalkia.com</strong>.</p><h3>5.3 Institutional Framework For The Protection Of Personal Data</h3><p><em>The legislation governing the present text.</em></p><p><strong>Greece</strong>: Law 2472/1997, Law 3471/2006</p><p><strong>European Union</strong>: Directive 95/46/EC, 2002/58/EC, 2009/136/EC</p>"
			}
		});

	component_2 = new Component$3({
			props: {
				social: [
					{
						"title": "Follow us on facebook",
						"link": "https://www.facebook.com/chalkia.official",
						"icon": "fa6-brands:square-facebook"
					},
					{
						"title": "Follow us on twitter",
						"link": "https://twitter.com/foteini_chalkia",
						"icon": "fa6-brands:square-twitter"
					},
					{
						"title": "Follow us on instagram",
						"link": "https://www.instagram.com/foteinichalkia_/",
						"icon": "fa6-brands:square-instagram"
					},
					{
						"title": "Follow us on pinterest",
						"link": "https://pinterest.com/Foteini_Chalkia/",
						"icon": "fa6-brands:square-pinterest"
					}
				],
				na: [{}, {}],
				nav: [
					{
						"link": {
							"label": "Bridal",
							"url": "/bridal",
							"active": false
						}
					},
					{
						"link": {
							"label": "Haute Couture",
							"url": "/haute-couture",
							"active": false
						}
					},
					{
						"link": { "label": "About", "url": "/about" }
					},
					{
						"link": {
							"label": "Editorials",
							"url": "/editorials"
						}
					},
					{
						"link": { "label": "Press", "url": "/press" }
					},
					{
						"link": { "label": "Contact", "url": "/contact" }
					}
				],
				a: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				add: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				addre: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				address: "<p>36 Damareos Str.</p>\n<p>11633 Athens, Greece</p>",
				phone: "+30 210 220 4390",
				email: "info@chalkia.com",
				seo_title: "About | Foteini Chalkia",
				seo_description: "She is inspired by silhouettes, fabrics, sounds and stories. The modern fearless woman is her muse."
			}
		});

	component_3 = new Component$4({
			props: {
				social: [
					{
						"title": "Follow us on facebook",
						"link": "https://www.facebook.com/chalkia.official",
						"icon": "fa6-brands:square-facebook"
					},
					{
						"title": "Follow us on twitter",
						"link": "https://twitter.com/foteini_chalkia",
						"icon": "fa6-brands:square-twitter"
					},
					{
						"title": "Follow us on instagram",
						"link": "https://www.instagram.com/foteinichalkia_/",
						"icon": "fa6-brands:square-instagram"
					},
					{
						"title": "Follow us on pinterest",
						"link": "https://pinterest.com/Foteini_Chalkia/",
						"icon": "fa6-brands:square-pinterest"
					}
				],
				na: [{}, {}],
				nav: [
					{
						"link": {
							"label": "Bridal",
							"url": "/bridal",
							"active": false
						}
					},
					{
						"link": {
							"label": "Haute Couture",
							"url": "/haute-couture",
							"active": false
						}
					},
					{
						"link": { "label": "About", "url": "/about" }
					},
					{
						"link": {
							"label": "Editorials",
							"url": "/editorials"
						}
					},
					{
						"link": { "label": "Press", "url": "/press" }
					},
					{
						"link": { "label": "Contact", "url": "/contact" }
					}
				],
				a: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				add: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				addre: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				address: "<p>36 Damareos Str.</p>\n<p>11633 Athens, Greece</p>",
				phone: "+30 210 220 4390",
				email: "info@chalkia.com",
				lpoea: {},
				ugrhc: {
					"badges": {
						"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/assets/sustainable.png",
						"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/assets/sustainable.png",
						"alt": "Sustainable Materials",
						"size": null
					}
				},
				seo_title: "About | Foteini Chalkia",
				seo_description: "She is inspired by silhouettes, fabrics, sounds and stories. The modern fearless woman is her muse.",
				ofaxo: "<h1>Privacy Policy</h1><p>At <strong>“Chalkia”</strong>, we’re committed to protecting and respecting your privacy.</p><p>This <strong>Privacy Policy</strong> explains when and why we collect personal information, how we use it, the conditions under which we may disclose it to others and what choices you have.</p><h2>Introduction</h2><p><em>We are a company that specializes in architectural design. People use our </em><strong><em>Services</em></strong><em> to get informed about our services. Our </em><strong><em>Privacy Policy</em></strong><em> applies to any </em><strong><em>Visitor</em></strong><em> to our </em><strong><em>Services</em></strong><em>.</em></p><p>Our non-registered (<strong>“Visitors”</strong>) users get informed through our <strong>Services</strong>. All content and data on our <strong>Services</strong> is viewable to non-registered (<strong>“Visitors”</strong>) users. You don’t have to be a registered user (<strong>“Member”</strong>) to use our <strong>Services</strong>.</p><p>We use the term <strong>“Designated Countries”</strong> to refer to countries in the <strong>European Union</strong> (<strong>EU</strong>), <strong>European Economic Area</strong> (<strong>EEA</strong>), and <strong>Switzerland</strong>.</p><h2>Services</h2><p>This <strong>Privacy Policy</strong> applies to <strong>www.chalkia.com</strong> (<strong>“Services”</strong>).</p><h2>Data Controllers And Contracting Parties</h2><p><strong><em>“</em>Chalkia<em>”</em></strong><em> is the controller of your personal data in connection with our </em><strong><em>Services</em></strong><em> and the company’s electronic data processing system.</em></p><p>If you reside in the <strong>“Designated Countries”</strong>: <strong>“Chalkia”</strong> will be the controller of your personal data provided to, or collected by or for, or processed in connection with our Services.</p><p>If you reside outside of the <strong>“Designated Countries”</strong>: <strong>“Chalkia”</strong> will be the controller of your personal data provided to, or collected by or for, or processed in connection with, our Services.</p><p>As a <strong>Visitor</strong> of our <strong>Services</strong>, the collection, use and sharing of your personal data is subject to this <strong>Privacy Policy</strong> and updates.</p><h2>Change</h2><p><em>Changes to the </em><strong><em>Privacy Policy</em></strong><em> apply to your use of our </em><strong><em>Services</em></strong><em> after the </em><strong><em>“effective date”</em></strong><em>.</em></p><p><strong>“Chalkia”</strong> can modify this <strong>Privacy Policy</strong>, and if we make material changes to it, we will provide notice through our <strong>Services</strong>, or by other means, to provide you the opportunity to review the changes before they become effective. If you object to any changes, you may stop using our <strong>Services</strong>.</p><p>You acknowledge that your continued use of our <strong>Services</strong> after we publish or send a notice about our changes to this <strong>Privacy Policy</strong> means that the collection, use and sharing of your personal data is subject to the updated <strong>Privacy Policy</strong>.</p><h2>1. Data We Collect</h2><p>In order for the <strong>Visitor</strong> to contact us through our <strong>Services</strong> and get information about our services it is not necessary to give any personal data.</p><h3>1.1 Data From Your Device</h3><p><em>We receive data from your devices.</em></p><p>We collect a series of general data and information when users visit and use our <strong>Services</strong>. This general data and information are stored in the server log files. Collected may be (1) the browser types and versions used, (2) the operating system used to access our <strong>Services</strong>, (3) the website from which you reached our <strong>Services</strong> (so-called referrers), (4) the sub-websites, (5) the date and time of access to our <strong>Services</strong>, (6) an Internet protocol address (IP address), (7) the Internet service provider of the accessing system, and (8) any other similar data and information that may be used in the event of attacks on our information technology systems.</p><p>When using these general data and information, we do not draw any conclusions about the users. Rather, this information is needed to (1) deliver the content of our <strong>Services</strong> correctly, (2) optimize the content of our <strong>Services</strong>, (3) ensure the long-term viability of our information technology systems, and (4) provide law enforcement authorities with the information necessary for criminal prosecution in case of a cyber-attack. Therefore, we analyze anonymously collected data and information statistically, with the aim of increasing the data protection and data security of our enterprise, and to ensure an optimal level of protection for the personal data we process. The anonymous data of the server log files are stored separately from all personal data provided by the <strong>Visitors</strong> of our <strong>Services</strong>.</p><h3>1.2 Sensitive Data</h3><p><em>We do not gather sensitive personal data.</em></p><p>We do not gather sensitive personal data (e.g. health, genetic, biometric data; racial or ethnic origin, political opinions, religious or philosophical beliefs, trade union membership, sexual orientation, and criminal convictions). We expressly request that you do not provide any such sensitive data to us.</p><h3>1.3 Children’s Information</h3><p><em>Only with the consent of their parents or guardians.</em></p><p>Children have access to our <strong>Services</strong> only with the consent of their parents or guardians. If you learn that a child has provided us with personal information without consent, please contact us by sending an email to <strong>info [at] chalkia.com</strong>.</p><h2>2. How We Use Your Data</h2><p><strong>“Chalkia”</strong> will not process any <strong>Visitor’s</strong> personal data.</p><h2>3. How We Share Your Data</h2><h3>3.1 Google Analytics (With Anonymization Function)</h3><p><em>We share some of your personal data with </em><strong><em>Google Analytics</em></strong><em>.</em></p><p>We have integrated the component of <strong>Google Analytics</strong> (With Anonymization Function) in our <strong>Services</strong>.</p><p><strong>Google Analytics</strong> is a web analytics service. Web analytics is the collection, gathering, and analysis of data about the behavior of visitors to websites. Web analytics are mainly used for the optimization of a website and in order to carry out a cost-benefit analysis of Internet advertising.</p><p>The operator of the <strong>Google Analytics</strong> component is Google Inc., 1600 Amphitheatre Pkwy, Mountain View, CA 94043-1351, United States.</p><p>For the web analytics through <strong>Google Analytics</strong> our <strong>Services</strong> use the application “_gat. _anonymizeIp”. By means of this application your IP address of the Internet connection is abridged by <strong>Google</strong> and anonymized.</p><p>With each call-up to one of the individual pages into which a component from <strong>Google Analytics</strong> service was integrated, the web browser automatically sends data through the corresponding <strong>Google Analytics</strong> component. During the course of this technical procedure, <strong>Google Maps</strong> and <strong>Google</strong> is made aware of what specific page you visited.</p><p>Further information and the applicable data protection provisions of <strong>Google</strong> may be retrieved under <a target=\"_blank\" rel=\"noopener noreferrer nofollow\" class=\"link link\" href=\"https://policies.google.com/privacy\">https://policies.google.com/privacy</a>.</p><h3>3.2 Third Parties</h3><p><em>We do not sell or rent your personal data to third parties.</em></p><p>We do not sell or rent your personal data to third parties.</p><p>We do not share your personal data with third parties for marketing purposes.</p><h2>4. Your Choices &amp; Obligations</h2><h3>4.1 Data Retention</h3><p><em>We keep your personal data until you request for their deletion.</em></p><p><strong>“Chalkia”</strong> keeps your personal data until you request for their deletion.</p><p>Tax information is exempt from the write-off process and is subject to mandatory tax compliance.</p><h3>4.2 Rights To Access And Control Your Personal Data</h3><p><em>You can access or request the deletion of your personal data.</em></p><p>With respect to your personal data, you retain the following rights:</p><ul><li><p><strong>Right of Access</strong>: You can send us a request in order to be informed about the personal data we keep for you.</p></li><li><p><strong>Right to Rectification</strong>: You can send us a request in order to ask us to change, update or correct your personal data, particularly if it’s inaccurate.</p></li><li><p><strong>Right to Erasure</strong>: You can send us a request in order to ask us to delete all or some of your personal data.</p></li><li><p><strong>Right to Restrict Processing</strong>: You can send us a request in order to ask us to limit the processing of all or some of your personal data.</p></li><li><p><strong>Right to Object Processing</strong>: You can send us a request in order to ask us to stop the processing of all or some of your personal data.</p></li><li><p><strong>Right to Data Portability</strong>: You can send us a request in order to ask us to send a copy of your personal data to you or to an organization of your choice.</p></li></ul><p><br>You may contact us to exercise any of the above rights regarding your personal data. <strong>“Chalkia”</strong> will respond to your request free of charge, without delay and in any case within one month of receipt of the request, except in exceptional circumstances, so that the deadline can be extended by another two months if necessary, taking into account the complexity of the request and/or the total number of requests. <strong>“Chalkia”</strong> will inform you of any extension within one month of receipt of the request and of the reasons for the delay. If your request can not be met, <strong>“Chalkia”</strong> will inform you without delay and at the latest within one month of receipt of the request, for the reasons.</p><p>The request to satisfy any of the above rights is reviewed each time in accordance with all applicable laws.</p><h2>5. Other Important Information</h2><h3>5.1 Security Breaches</h3><p><em>We monitor for and try to prevent security breaches.</em></p><p>We implement security safeguards designed to protect your data, such as <strong>HTTPS</strong>. We regularly monitor our systems for possible vulnerabilities and attacks. However, we cannot warrant the security of any information that you send us. There is no guarantee that data may not be accessed, disclosed, altered, or destroyed by breach of any of our physical, technical, or managerial safeguards.</p><p>In case of a security breach, <strong>“Chalkia”</strong> will inform all concerned within 72 hours.</p><h3>5.2 Contact Information</h3><p><em>You can contact us for any questions.</em></p><p>You may contact us for any questions about this <strong>Privacy Policy</strong> by sending an email to <strong>info [at] chalkia.com</strong>.</p><h3>5.3 Institutional Framework For The Protection Of Personal Data</h3><p><em>The legislation governing the present text.</em></p><p><strong>Greece</strong>: Law 2472/1997, Law 3471/2006</p><p><strong>European Union</strong>: Directive 95/46/EC, 2002/58/EC, 2009/136/EC</p>",
				badges: {
					"url": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/assets/sustainable.png",
					"src": "https://zzyumdkmbkvyfpswmpyz.supabase.co/storage/v1/object/public/sites/chalkia/assets/sustainable.png",
					"alt": "Sustainable Materials",
					"size": null
				}
			}
		});

	component_4 = new Component$5({
			props: {
				social: [
					{
						"title": "Follow us on facebook",
						"link": "https://www.facebook.com/chalkia.official",
						"icon": "fa6-brands:square-facebook"
					},
					{
						"title": "Follow us on twitter",
						"link": "https://twitter.com/foteini_chalkia",
						"icon": "fa6-brands:square-twitter"
					},
					{
						"title": "Follow us on instagram",
						"link": "https://www.instagram.com/foteinichalkia_/",
						"icon": "fa6-brands:square-instagram"
					},
					{
						"title": "Follow us on pinterest",
						"link": "https://pinterest.com/Foteini_Chalkia/",
						"icon": "fa6-brands:square-pinterest"
					}
				],
				na: [{}, {}],
				nav: [
					{
						"link": {
							"label": "Bridal",
							"url": "/bridal",
							"active": false
						}
					},
					{
						"link": {
							"label": "Haute Couture",
							"url": "/haute-couture",
							"active": false
						}
					},
					{
						"link": { "label": "About", "url": "/about" }
					},
					{
						"link": {
							"label": "Editorials",
							"url": "/editorials"
						}
					},
					{
						"link": { "label": "Press", "url": "/press" }
					},
					{
						"link": { "label": "Contact", "url": "/contact" }
					}
				],
				a: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				add: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				addre: "Cillum aute id tempor aute. Laborum fugiat tempor laboris sunt reprehenderit.",
				address: "<p>36 Damareos Str.</p>\n<p>11633 Athens, Greece</p>",
				phone: "+30 210 220 4390",
				email: "info@chalkia.com",
				seo_title: "About | Foteini Chalkia",
				seo_description: "She is inspired by silhouettes, fabrics, sounds and stories. The modern fearless woman is her muse."
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
		}
	};
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$5, safe_not_equal, {});
	}
}

export default Component$6;
