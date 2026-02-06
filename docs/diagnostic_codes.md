# Diagnostic Codes

This registry lists the stable diagnostic codes emitted by the compiler. Messages are printed as
`[CODE] message` in CLI/REPL output.

If you add or change a code, update this file and keep the mapping stable.

## Frontend: Parser (`F000x`)

- `F0001`: `ParseError::UnexpectedEof`
- `F0002`: `ParseError::UnexpectedChar`
- `F0003`: `ParseError::UnmatchedParen`

## Frontend: Macro Expander (`F010x`)

- `F0100`: `ExpansionError::TransformationError`
- `F0101`: `ExpansionError::ArgumentCountMismatch`
- `F0102`: `ExpansionError::InvalidSyntax`
- `F0103`: `ExpansionError::UnknownForm`
- `F0104`: `ExpansionError::MacroBoundaryDenied`
- `F0105`: Macro allowlist redefinition warning (driver-pushed diagnostic)
- `F0106`: `ExpansionError::ExpansionStepLimitExceeded` / `ExpansionError::ExpansionDepthLimitExceeded`

## Frontend: Elaborator (`F020x`)

- `F0200`: `ElabError::UnboundVariable`
- `F0201`: `ElabError::UnknownInductive`
- `F0202`: `ElabError::AmbiguousConstructor`
- `F0203`: `ElabError::NotImplemented`
- `F0205`: `ElabError::TypeMismatch`
- `F0206`: `ElabError::FunctionKindMismatch`
- `F0207`: `ElabError::FunctionKindAnnotationTooSmall`
- `F0208`: `ElabError::AmbiguousRefLifetime`
- `F0209`: `ElabError::ImplicitNonCopyUse`
- `F0210`: `ElabError::EvalInType`
- `F0211`: `ElabError::NonExhaustiveMatch`
- `F0212`: `ElabError::DuplicateMatchCase`
- `F0213`: `ElabError::UnknownMatchCase`
- `F0214`: `ElabError::UnificationError`
- `F0215`: `ElabError::OccursCheck`
- `F0216`: `ElabError::SolutionContainsFreeVariables`
- `F0217`: `ElabError::UnsolvedConstraints`
- `F0218`: `ElabError::RecursorNeedsMotive`
- `F0219`: `ElabError::UnknownTypeMarker`
- `F0220`: `ElabError::ConflictingTypeMarkers`
- `F0221`: `ElabError::MissingInteriorMutabilityKind`

## Kernel: Type Checker (`K000x`)

- `K0001`: `TypeError::UnknownVariable`
- `K0002`: `TypeError::TypeMismatch`
- `K0003`: `TypeError::ExpectedFunction`
- `K0004`: `TypeError::ExpectedSort`
- `K0005`: `TypeError::UnknownInductive`
- `K0006`: `TypeError::UnknownConstructor`
- `K0007`: `TypeError::UnknownConst`
- `K0008`: `TypeError::ReservedPrimitiveName`
- `K0009`: `TypeError::ReservedPrimitiveSignature`
- `K0010`: `TypeError::ReservedMarkerName`
- `K0011`: `TypeError::ReservedMarkerSignature`
- `K0012`: `TypeError::ReservedCoreName`
- `K0013`: `TypeError::DefinitionAlreadyExists`
- `K0014`: `TypeError::InductiveAlreadyExists`
- `K0015`: `TypeError::NonPositiveOccurrence`
- `K0016`: `TypeError::NestedInductive`
- `K0017`: `TypeError::UniverseLevelTooSmall`
- `K0018`: `TypeError::NonTerminating`
- `K0019`: `TypeError::TerminationError`
- `K0020`: `TypeError::PartialInType`
- `K0021`: `TypeError::OwnershipError`
- `K0022`: `TypeError::EffectError`
- `K0023`: `TypeError::AxiomDependencyRequiresNoncomputable`
- `K0024`: `TypeError::PartialReturnType`
- `K0025`: `TypeError::MissingWellFoundedInfo`
- `K0026`: `TypeError::InvalidWellFoundedDecreasingArg`
- `K0027`: `TypeError::LargeElimination`
- `K0028`: `TypeError::PropFieldInData`
- `K0029`: `TypeError::CopyDeriveFailure`
- `K0030`: `TypeError::ExplicitCopyInstanceRequiresUnsafe`
- `K0031`: `TypeError::ExplicitCopyInstanceInteriorMutable`
- `K0032`: `TypeError::MissingTypeMarkerDefinition`
- `K0033`: `TypeError::UnknownCaptureAnnotation`
- `K0034`: `TypeError::InvalidCaptureAnnotation`
- `K0035`: `TypeError::InvalidTypeMarkerDefinition`
- `K0036`: `TypeError::MarkerRegistryUninitialized`
- `K0037`: `TypeError::MarkerRegistryAlreadyInitialized`
- `K0038`: `TypeError::UnknownMarkerId`
- `K0039`: `TypeError::MissingRecursorLevel`
- `K0040`: `TypeError::RecursorLevelCount`
- `K0041`: `TypeError::CtorNotReturningInductive`
- `K0042`: `TypeError::CtorArityMismatch`
- `K0043`: `TypeError::FunctionKindTooSmall`
- `K0044`: `TypeError::InvalidRefLifetimeLabel`
- `K0045`: `TypeError::AmbiguousRefLifetime`
- `K0046`: `TypeError::RefLifetimeLabelMismatch`
- `K0047`: `TypeError::UnresolvedMeta`
- `K0048`: `TypeError::DefEqFuelExhausted`
- `K0049`: `TypeError::DefEqFixUnfold`
- `K0050`: `TypeError::NbeNonFunctionApplication`
- `K0051`: `TypeError::NotImplemented`

## MIR: Ownership/Borrow/Typing (`M1xx`/`M2xx`/`M3xx`)

- `M100`: `OwnershipError::UseAfterMove`
- `M101`: `OwnershipError::CopyOfNonCopy`
- `M102`: `OwnershipError::DoubleMoveInArgs`
- `M103`: `OwnershipError::OverwriteWithoutDrop`
- `M104`: `OwnershipError::LinearNotConsumed`
- `M105`: `OwnershipError::UninitializedReturn`
- `M106`: `OwnershipError::UseUninitialized`
- `M200`: `BorrowError::ConflictingBorrow`
- `M201`: `BorrowError::UseWhileBorrowed`
- `M202`: `BorrowError::MoveOutOfRef`
- `M203`: `BorrowError::DanglingReference`
- `M204`: `BorrowError::EscapingReference`
- `M205`: `BorrowError::MutateSharedRef`
- `M206`: `BorrowError::AssignWhileBorrowed`
- `M207`: `BorrowError::InternalInvariant`
- `M300`: MIR typing errors (`TypingChecker`)

## CLI Driver (`C000x`)

- `C0001`: Macro import not found
- `C0002`: Macro import cycle detected
- `C0003`: Macro import read failure
- `C0004`: Evaluation blocked due to axiom dependencies
- `C0005`: Interior mutability gated in safe code
- `C0006`: Panic-free lint error
- `C0007`: Invalid `import-macros` form (expects string paths)
