import Mathlib.Tactic
import PhysLib.Foundations.SI

namespace SI.Mechanics
open UnitsSystem SI
unseal Rat.add Rat.mul Rat.sub Rat.inv

-- Displacement
@[simp] def displacement_end_x_init_x (x2  : Length) (x1 : Length) : Length := x2 - x1
@[simp] lemma displacement_end_x_init_x_eq (x2 x1 : Length) :
  displacement_end_x_init_x x2 x1 = x2 - x1 := rfl
theorem displacement_init_x_to_end_x
  (x2 x1 dx: Length)
  (hΔx : dx = displacement_end_x_init_x x2 x1):
  x2 = x1 + dx := by
    -- From dx = (x2 - x1), obtain (x2 - x1) = dx
  have hx : x2 - x1 = dx := by
    simpa [displacement_end_x_init_x_eq] using hΔx.symm
  -- Use the general lemma: x - y = z ⇒ x = z + y
  have hx' : x2 = dx + x1 := eq_add_of_sub_eq hx
  -- Swap order of summands to get target form
  simpa [add_comm] using hx'

-- Constant Speed Motion
@[simp] def displacement_delta_t_const_v (v : Speed) (t : Time) : Length := v * t
@[simp] lemma displacement_delta_t_const_v_eq (v : Speed) (t : Time) :
  displacement_delta_t_const_v v t = v * t := rfl

theorem displacement_eq
  (x2 x1 dx1 dx2: Length) (v : Speed) (t : Time)
  (hΔx1 : dx1 = displacement_end_x_init_x x2 x1)
  (hΔx2 : dx2 = displacement_delta_t_const_v v t)
  (hΔx : dx1 = dx2):
  x2 - x1 = v * t := by
  have h' : displacement_end_x_init_x x2 x1 = displacement_delta_t_const_v v t := by
    simpa [hΔx1, hΔx2] using hΔx
  simpa [displacement_end_x_init_x_eq, displacement_delta_t_const_v_eq] using h'

theorem delta_t_const_v_init_x_to_end_x_version0
  (x2 x1 dx1 dx2: Length) (v : Speed) (t : Time)
  (hΔx1 : dx1 = displacement_end_x_init_x x2 x1 )
  (hΔx2 : dx2 = (displacement_delta_t_const_v v t )/1)
  (hΔx : dx1 = dx2):
  x2 = v*t/1 + x1:= by
  -- dx1 = dx2
  have h' :
      displacement_end_x_init_x x2 x1
    = (displacement_delta_t_const_v v t) / (1 : ℕ ) := by
    simpa [hΔx1, hΔx2] using hΔx
  -- x2 - x1 = v * t / 1
  have hx : x2 - x1 = v * t / (1 : ℕ ) := by
    simpa [displacement_end_x_init_x_eq, displacement_delta_t_const_v_eq] using h'
  -- x - y = z ⇒ x = z + y
  exact eq_add_of_sub_eq hx

theorem delta_t_const_v_init_x_to_end_x_version1
  (x2 x1 dx1 dx2 : Length) (v : Speed) (t : Time)
  (hΔx1 : dx1 = displacement_end_x_init_x x2 x1)
  (hΔx2 : dx2 = displacement_delta_t_const_v v t)
  (hΔx  : dx1 = dx2) :
  x2 = x1 + displacement_delta_t_const_v v t := by
  -- dx1 = dx2
  have h' :
    displacement_end_x_init_x x2 x1 = displacement_delta_t_const_v v t := by
    simpa [hΔx1, hΔx2] using hΔx
  -- x2 - x1 = displacement_delta_t_const_v v t
  have hx : x2 - x1 = displacement_delta_t_const_v v t := by
    simpa [displacement_end_x_init_x_eq] using h'
  -- x − y = z ⇒ x = y + z
  exact (eq_add_of_sub_eq hx).trans (by simp [add_comm])

-- Non-constant Speed
@[simp] def delta_v_end_v_init_v (v2 : Speed) (v1 : Speed) : Speed := v2 - v1
@[simp] lemma delta_v_end_v_init_v_eq (v2 v1 : Speed) :
  delta_v_end_v_init_v v2 v1 = v2 - v1 := rfl

-- Constant Acceleration
@[simp] def delta_v_delta_t_const_a (a : Acceleration) (t : Time) : Speed := a * t
@[simp] lemma delta_v_delta_t_const_a_eq (a : Acceleration) (t : Time) :
  delta_v_delta_t_const_a a t = a * t := rfl

theorem delta_v_eq
  (v2 v1 dv1 dv2: Speed) (a : Acceleration) (t : Time)
  (hΔv1 : dv1 = delta_v_end_v_init_v v2 v1)
  (hΔv2 : dv2 = delta_v_delta_t_const_a a t)
  (hΔv : dv1 = dv2):
  v2 - v1 = a * t := by
  have h' : delta_v_end_v_init_v v2 v1 = delta_v_delta_t_const_a a t := by
    simpa [hΔv1, hΔv2] using hΔv
  -- Expand both sides using the @[simp] lemmas to reach the goal
  simpa [delta_v_end_v_init_v_eq, delta_v_delta_t_const_a_eq] using h'

theorem delta_v_const_a_init_v_to_end_v_version0
  (v2 v1 dv1 dv2: Speed) (a : Acceleration) (t : Time)
  (hΔv1 : dv1 = delta_v_end_v_init_v v2 v1)
  (hΔv2 : dv2 = (delta_v_delta_t_const_a a t)/1)
  (hΔv : dv1 = dv2):
  v2 = a*t/1 + v1:= by
  -- dv1 = dv2
  have h' :
      delta_v_end_v_init_v v2 v1
    = (delta_v_delta_t_const_a a t) / (1 : ℕ ) := by
    simpa [hΔv1, hΔv2] using hΔv
  -- v2 - v1 = a * t / 1
  have hv : v2 - v1 = a * t / (1 : ℕ ) := by
    simpa [delta_v_end_v_init_v_eq, delta_v_delta_t_const_a_eq] using h'
  -- x - y = z ⇒ x = z + y
  exact eq_add_of_sub_eq hv

theorem delta_v_const_a_init_v_to_end_v_version1
  (v2 v1 dv1 dv2: Speed) (a : Acceleration) (t : Time)
  (hΔv1 : dv1 = delta_v_end_v_init_v v2 v1)
  (hΔv2 : dv2 = delta_v_delta_t_const_a a t)
  (hΔv : dv1 = dv2):
  v2 = v1 + delta_v_delta_t_const_a a t := by
  -- dv1 = dv2
  have h' :
      delta_v_end_v_init_v v2 v1
    = delta_v_delta_t_const_a a t := by
    simpa [hΔv1, hΔv2] using hΔv
  -- v2 - v1 = delta_v_delta_t_const_a a t
  have hv : v2 - v1 = delta_v_delta_t_const_a a t := by
    simpa [delta_v_end_v_init_v_eq] using h'
  -- x − y = z ⇒ x = y + z
  exact (eq_add_of_sub_eq hv).trans (by simp [add_comm])

/-- Under constant acceleration, the two displacement formulas are equivalent:
    `v0 * t + (a * t^2)/2 = ((v + v0)/2) * t`.
    This uses only the velocity increment relation `v - v0 = a * t`. -/
theorem disp_const_a_forms_eq
  (v2 v1 : Speed) (a : Acceleration) (t : Time)
  (hv : delta_v_end_v_init_v v2 v1 = delta_v_delta_t_const_a a t) :
  v1 * t + a * t ** 2 / 2 = (v2 + v1) / (2 : ℝ ) * t := by
sorry

/-- Under constant acceleration, the two displacement formulas are equivalent:
    `v1 * t + (a * t^2)/2 = ((v2 + v1)/2) * t`,
    using only `v2 - v1 = a * t`.
    This avoids having `a * t` appear directly inside addition. -/
theorem disp_const_a_forms_eq0
  (v2 v1 : Speed) (a : Acceleration) (t : Time)
  (hv : delta_v_end_v_init_v v2 v1 = delta_v_delta_t_const_a a t) :
  v1 * t + (a * (t ** 2)) / 2 = ((v2 + v1) / (2 : ℝ)) * t := by sorry

end SI.Mechanics

namespace SI.Mechanics.Testfield
open UnitsSystem SI SI.Mechanics
unseal Rat.add Rat.mul Rat.sub Rat.inv

theorem delta_t_const_v_init_x_to_end_x_origin0
  (x2 x1 dx1 dx2 : Length) (v : Speed) (t : Time)
  (hΔx1 : dx1 = displacement_end_x_init_x x2 x1)
  (hΔx2 : dx2 = displacement_delta_t_const_v v t)
  (hΔx  : dx1 = dx2) :
  x2 = x1 + displacement_delta_t_const_v v t := by
  -- From dx1 = dx2, get equivalence of the two displacement expressions
  have h' :
    displacement_end_x_init_x x2 x1 = displacement_delta_t_const_v v t := by
    simpa [hΔx1, hΔx2] using hΔx
  -- Expand left-hand displacement: x2 - x1 = displacement_delta_t_const_v v t
  have hx : x2 - x1 = displacement_delta_t_const_v v t := by
    simpa [displacement_end_x_init_x_eq] using h'
  have := (eq_add_of_sub_eq hx)
  -- Now this : x2 = displacement_delta_t_const_v v t + x1
  -- Swap order + expand
  simpa [displacement_delta_t_const_v_eq, add_comm] using this

end SI.Mechanics.Testfield
