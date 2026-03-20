import Mathlib.Tactic
import PHYSlib.Foundations.SI
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace SI
open UnitsSystem

/- This is needed to keep dimensions such as `Length` and `Speed * Time` defeq to each other -/
unseal Rat.add Rat.mul Rat.sub Rat.inv



variable (m:Mass) (v v_0:Speed) (F:Force) (p:Momentum) (E:Energy) (h h_0 h_1:Length) (t:Time) (a:Acceleration)


#check h = (2.3:ℚ) • (-a * t**2) / 1 + v * t

#check F = m * a
#check p = m * v
#check h = - a * t**2 / 2 + v * t
#check h = - a * t**2 / 2 + v * t /2
#check h = - a * t**2 / 2 + v * t /2 + a * t**2
#check h = - a * t**2 / 2 +a * t**2 + v * t /2
#check h = - a * t**2 / 2 +(a * t**2 + v * t /2)
-- #check meter.in h = meter.in(- a * t**2 / 2 + v * t + a * t**2)
-- #check h = - a * t**2 / 2 + a * t**2 + v * t
-- #check h = a * t**2 - a * t**2 / 2 + v * t
-- #check h = a * t**2 + v * t - a * t**2 / 2
-- #check h = (v * t : Formal) - a * t**2 / 2 + a * t**2
-- #check h = ((v * t + a * t**2 : Formal )- a * t**2 / 2 : Formal)
#check h_1 = - a * t**2 +a * t**2 / 2
#check h_0 =  v * t
#check h = h_1 + h_0
-- #check h = - a * t**2 +a * t**2 / 2 + v * t
#check h = - a * t**2 / 2 + v * t - a * t**2 / 2
#check h = - a * t**2 / 2 + v * t - a * t**2 / 2 + v * t
#check E = 1 • kilogram * c**2
#check E = m * v**2 / 2 + m * g * h
#check v = v_0 - a * t / 2
#check v_0 = - a * t / 2 + v
#check v_0 = - a * t + v / 2
-- #check v_0 = - a * t + v
-- #check E = m * c**3  -- fails to typecheck
-- #check m + v -- fails to typecheck



example (hv : v = 60 • kilo meter / hour) : (StandardUnit _).in v = 50/(3:ℝ) := by
  simp [←Scalar.val_inj, hour, minute, kilo, meter, second, hv]
  norm_num

example (first_law : F = m * a) (hm : m = 2 • kilogram) (ha : a = 3 • meter / second**2) : F = 6 • newton := by
  simp [←Scalar.val_inj, first_law, hm, ha, kilogram, meter, second, newton]
  norm_num

example (kinetic: E = m * v**2 / 2) (hm : m = 2 • kilogram) (hv : v = 3 • meter / second) : joule.in E = 9 := by
  simp [←Scalar.val_inj, kinetic, hm, hv, kilogram, meter, second, joule]
  norm_num

example (ht : t = 3 • hour) : minute.in t = 180 := by
  simp [←Scalar.val_inj, hour, minute, ht]
  norm_num

-- An example of how to use fractional units

abbrev half_frequency_unit := (1/2:ℚ) • frequency_unit
abbrev SqrtFrequency := Scalar half_frequency_unit
abbrev sqrt_hertz:SqrtFrequency := StandardUnit _

example : sqrt_hertz**2 = hertz := by
  simp [←Scalar.val_inj, half_frequency_unit, frequency_unit, sqrt_hertz]

example {w : SqrtFrequency} (hw : w = 2 • sqrt_hertz) : hertz.in (w**2) = 4 := by
  simp [←Scalar.val_inj, half_frequency_unit, frequency_unit, hw]
  norm_num

/-- An example of a non-negative scalar type -/
abbrev NNTemperature := { T:Temperature // T ≥ 0 }

end SI
