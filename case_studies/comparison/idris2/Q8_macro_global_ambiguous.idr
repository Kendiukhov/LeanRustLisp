-- Q8 (limit probe, companion of Q8_macro_global_names.idr). The macro `callHelper`
-- (template: unqualified `helper`, defined next to `Lib.helper`) is used inside a
-- namespace that defines its own global `helper`. The name in the template is resolved
-- at the use site, where both globals are visible, and elaboration reports an ambiguity.
module Main

import Language.Reflection

%language ElabReflection

namespace Lib
  export
  helper : String
  helper = "Lib.helper (definition site)"

  export %macro
  callHelper : Elab String
  callHelper = check `(helper)

namespace User
  export
  helper : String
  helper = "User.helper (use site)"

  export
  inUserNamespace : String
  inUserNamespace = callHelper
