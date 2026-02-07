# Modules and Packages

## Files as Modules

Every `.lrl` file is a module. The module name is derived from the filename.

## Packages

(Future Specification)
Packages will be managed by a package manager (likely integrated into the CLI), defining dependencies and workspaces.

## Visibility

Currently, top-level definitions in a module are visible to any module that imports it.
(Future: `private` / `pub` visibility modifiers).
