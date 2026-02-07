# Expansion Algorithm

1. Parse file to `Syntax`.
2. Traverse top-down.
3. If list head `(foo ...)` is a macro binding `foo`:
   a. Invoke `foo` with arguments.
   b. Replace node with result.
   c. Comparison mark logic (hygiene) applied to result.
   d. Continue expansion on the *result* (until fixpoint/atom).
4. If not macro, descend into children.
