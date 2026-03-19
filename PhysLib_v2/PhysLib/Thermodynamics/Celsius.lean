import Mathlib.Tactic
import PhysLib.Foundations.SI
import Mathlib.Algebra.Group.MinimalAxioms

namespace SI.Thermodynamics
open UnitsSystem SI
unseal Rat.add Rat.mul Rat.sub Rat.inv

/-- Conversion between Celsius (°C) and Kelvin (K):
`T(°C) = T(K) - 273.15`. -/
noncomputable abbrev celsius : Temperature :=
  kelvin - (27315/100 : ℚ) • kelvin

end SI.Thermodynamics
