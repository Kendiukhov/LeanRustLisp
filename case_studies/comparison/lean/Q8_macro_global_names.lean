/-!
Q8 (limit probe). Hygiene for GLOBAL names referenced by a macro template.

`call_helper!` is defined inside `namespace Lib`; its template mentions `helper`.
Lean's quotation records which global `helper` that identifier denotes where the macro
is defined (`Lib.helper`), so the expansion refers to `Lib.helper` at every use site,
even where another global `helper` is in scope (`User.helper`, `_root_.helper`) or a
local variable named `helper` shadows it. Each result prints "definition site". (The
unused-variable warning that `lean` prints for the local `helper` confirms that the
expansion does not refer to it.)
-/
namespace Lib
def helper : String := "Lib.helper (definition site)"
macro "call_helper!" : term => `(helper)
end Lib

namespace User
def helper : String := "User.helper (use site)"
def inUserNamespace : String := call_helper!
end User

def helper : String := "_root_.helper (use site)"
def atRoot : String := call_helper!
def underLocal : String := let helper := "local helper (use site)"; call_helper!

def main : IO Unit := do
  IO.println s!"call_helper! in namespace User (User.helper in scope): {User.inUserNamespace}"
  IO.println s!"call_helper! at the root (_root_.helper in scope):    {atRoot}"
  IO.println s!"call_helper! under `let helper := ...`:               {underLocal}"
