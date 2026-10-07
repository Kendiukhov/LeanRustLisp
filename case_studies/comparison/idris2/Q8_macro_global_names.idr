-- Q8 (limit probe). Name resolution for GLOBAL names referenced by a macro template.
--
-- `callHelper` is a `%macro` defined in namespace `Lib`; its quoted template mentions
-- `helper`. An Idris 2 quote is unresolved syntax (`TTImp`), so `helper` is resolved
-- where the macro is USED: under a local `let helper = ...` the expansion picks the
-- local variable (result "use site"). Writing the qualified name `Lib.helper` in the
-- template pins it to the definition site. In a namespace that defines another global
-- `helper`, the unqualified template is ambiguous (Q8_macro_global_ambiguous.idr).
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

  export %macro
  callHelperQualified : Elab String
  callHelperQualified = check `(Lib.helper)

underLocal : String
underLocal = let helper : String = "local helper (use site)" in callHelper

underLocalQualified : String
underLocalQualified = let helper : String = "local helper (use site)" in callHelperQualified

main : IO ()
main = do
  putStrLn ("callHelper under `let helper = ...`:          " ++ underLocal)
  putStrLn ("callHelperQualified under `let helper = ...`: " ++ underLocalQualified)
