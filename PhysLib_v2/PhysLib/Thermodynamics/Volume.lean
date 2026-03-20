import Mathlib.Tactic
import PhysLib.Foundations.SI
import Mathlib.Algebra.Group.MinimalAxioms

namespace SI.Thermodynamics
open UnitsSystem SI
unseal Rat.add Rat.mul Rat.sub Rat.inv

abbrev area_unit := 2 • length_unit
abbrev Area := Scalar area_unit

abbrev volume_unit := 3 • length_unit
abbrev Volume := Scalar volume_unit
-- @[simp] def cubic_meter : Volume := 1 • meter**3

abbrev heat_capacity_unit := energy_unit - temperature_unit - mass_unit
abbrev HeatCapacity := Scalar heat_capacity_unit

abbrev thermal_conductivity_unit := energy_unit - time_unit - length_unit - temperature_unit
abbrev ThermalConductivity := Scalar thermal_conductivity_unit

abbrev heat_of_fusion_unit := energy_unit - mass_unit
abbrev HeatOfFusion := Scalar heat_of_fusion_unit

end SI.Thermodynamics
