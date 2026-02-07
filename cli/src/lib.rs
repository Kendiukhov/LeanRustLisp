pub mod compiler;
pub mod driver;
pub mod expand;
pub mod package_manager;
pub mod repl;

use frontend::macro_expander::Expander;

/// Macros in the prelude that are allowed to expand into macro-boundary forms.
pub const PRELUDE_MACRO_BOUNDARY_ALLOWLIST: &[&str] = &[];

pub fn set_prelude_macro_boundary_allowlist(expander: &mut Expander, module_id: &str) {
    expander
        .set_macro_boundary_allowlist(module_id, PRELUDE_MACRO_BOUNDARY_ALLOWLIST.iter().copied());
}

pub fn configure_defeq_fuel(
    defeq_fuel: Option<usize>,
) -> Result<(), kernel::nbe::DefEqFuelOverrideError> {
    if let Some(fuel) = defeq_fuel {
        return kernel::nbe::set_def_eq_fuel_policy(fuel, kernel::nbe::DefEqFuelSource::Override);
    }

    if let Ok(value) = std::env::var("LRL_DEFEQ_FUEL") {
        if let Ok(fuel) = value.parse::<usize>() {
            if fuel > 0 {
                return kernel::nbe::set_def_eq_fuel_policy(
                    fuel,
                    kernel::nbe::DefEqFuelSource::Env,
                );
            }
        }
    }

    Ok(())
}
