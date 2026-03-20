import Mathlib
import Aesop
import Mathlib.Tactic
import PHYSlib.Foundations.SI
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace SI
open BigOperators Real Nat Topology Filter Rat UnitsSystem
unseal Rat.add Rat.mul Rat.sub Rat.inv


-- Construct an instance of NormedAddCommGroup for scalar type Scalar d
-- Normed additive group requires defining norm and basic properties related to distance
instance{d:Dimensions}:NormedAddCommGroup (Scalar d):={
  norm:=fun t=>abs t.val  -- Define norm: the norm of a scalar is the absolute value of its value
  dist_self:=by simp     -- Distance reflexivity: distance from any element to itself is 0 (proved by simplification)
  dist_comm:=by          -- Distance commutativity: distance from x to y equals distance from y to x
    simp
    exact fun x y => abs_sub_comm x.val y.val  -- Using commutativity of real absolute value difference
  dist_triangle:=by      -- Triangle inequality: distance from x to z ≤ distance from x to y + distance from y to z
    simp
    exact fun x y z => abs_sub_le x.val y.val z.val  -- Using triangle inequality of real absolute value
  eq_of_dist_eq_zero:=by -- Zero distance implies equality: if distance from x to y is 0, then x=y
    intro x y hxy        -- Introduce variables x,y and hypothesis hxy that distance is 0
    simp at hxy          -- Simplify the hypothesis
    refine Scalar.ext_iff.mpr ?_  -- Use scalar equivalence condition
    contrapose! hxy;    -- Proof by contradiction: if x≠y then distance is not 0
    exact sub_ne_zero_of_ne hxy  -- Using the property that real difference is non-zero for unequal elements
}

-- Distance definition theorem: distance between two points in Scalar d equals absolute value of difference of their values
theorem dist_def{d:Dimensions}(a1 a2:Scalar d):Dist.dist a1 a2=|a1.val-a2.val|:=rfl

-- Norm definition theorem: norm of an element in Scalar d equals absolute value of its value
theorem norm_def{d:Dimensions}(t:(Scalar d)):‖t‖=abs t.val:=rfl

-- Construct an instance of NormedSpace ℝ over real field for scalar type Scalar d
-- Normed space requires compatibility of scalar multiplication with norm and other properties
instance{d:Dimensions}:NormedSpace ℝ (Scalar d):={
  norm_smul_le:=by       -- Scalar multiplication norm inequality: ‖a·b‖ ≤ |a|·‖b‖
    intro a b
    rw[norm_def,norm_def];simp  -- Simplify using norm definition
    rw[abs_mul]         -- Using real absolute value multiplication property
  smul_zero:=fun a => MulActionWithZero.smul_zero a  -- Scalar multiplication of zero element yields zero element
  smul_add:=fun a x y => DistribSMul.smul_add a x y  -- Distributivity of scalar multiplication over addition
  add_smul:=fun r s x => Module.add_smul r s x       -- Distributivity of addition over scalar multiplication
  zero_smul:=fun x => zero_smul ℝ x                  -- Zero scalar multiplied by any element yields zero element
}

-- Open set equivalence theorem: set S on Scalar d is open if and only if the corresponding real set {x:ℝ|⟨x⟩ ∈ S} is open
theorem open_set_iff{d:Dimensions}(S:Set (Scalar d)):IsOpen S↔ IsOpen {x:ℝ|⟨x⟩ ∈ S}:=by
  constructor  -- Prove equivalence in two directions
  -- Forward: if S is open, then the corresponding real set is open
  intro h
  apply Metric.isOpen_iff.mp at h  -- Use metric space open set equivalence condition
  refine Metric.isOpen_iff.mpr ?_  -- Prove real set satisfies open set condition
  intro x hx
  simp at hx
  have hoe:=h (⟨x⟩:Scalar d) hx  -- Use open set property of S to get ball neighborhood
  obtain ⟨e,he1,he2⟩:=hoe        -- Extract neighborhood radius and containment relation
  use e
  split_ands
  exact he1
  rw[Set.subset_def]
  intro x1 hx1
  simp
  exact he2 hx1

  -- Reverse: if the corresponding real set is open, then S is open
  intro h
  apply Metric.isOpen_iff.mp at h
  refine Metric.isOpen_iff.mpr ?_
  intro x hx
  have hoe:=h (x.val) hx  -- Use open set property of real set to get ball neighborhood
  obtain ⟨e,he1,he2⟩:=hoe
  use e
  split_ands
  exact he1
  rw[Set.subset_def]
  intro x1 hx1
  suffices x1.val∈ {(x:ℝ)|(⟨x⟩:Scalar d)∈ S} by
    simp at this
    exact this
  simp at hx1
  exact he2 hx1

-- Differentiability theorem: mapping from Scalar d to its real value is differentiable over ℝ
theorem differentiable_real_cast{d:Dimensions}:Differentiable ℝ (fun (t:(Scalar d))=>t.val):=by
  rw[Differentiable]  -- Expand differentiability definition
  intro x
  rw[DifferentiableAt]  -- Expand differentiability at a point definition

  -- Construct a bounded linear map f as the derivative
  let f: (Scalar d) →L[ℝ] ℝ:={
    toFun:=(fun t=>t.val)  -- Mapping function: take scalar's value
    map_add':=by           -- Verify linearity: preserves addition
      intro x y
      exact rfl
    map_smul':=by          -- Verify linearity: preserves scalar multiplication
      intro m x
      simp
    cont:={                -- Continuity: preimage of open set is open
      isOpen_preimage:=by
        intro s hs
        refine (open_set_iff ((fun t => t.val) ⁻¹' s)).mpr ?_
        simp
        exact hs
    }
  }

  -- Prove that image of f equals scalar's value
  have hf:∀x:(Scalar d) , f x=x.val:=by
    intro x;exact rfl

  use f  -- Specify f as derivative
  rw[HasFDerivAt]  -- Expand Fréchet derivative definition
  refine { isLittleOTVS := ?_ }  -- Prove remainder is little-o
  -- Prove remainder is identically zero (thus satisfying little-o condition)
  have hsimp:(fun x' => x'.val - x.val - f (x' - x))=0:=by
    refine funext ?_
    intro x'
    rw[hf]
    simp
  rw[hsimp]
  exact Asymptotics.IsLittleOTVS.zero (fun x' => x' - x) (𝓝 x)

-- Theorem: Mapping from real numbers to scalar type (physical lift) is differentiable over ℝ
-- Mapping defined as t ↦ ⟨t⟩ (wrap real number t as Scalar d type)
theorem isdifferentiable_phys_lift{d:Dimensions}:
  Differentiable ℝ (fun (t:ℝ)=>(⟨t⟩:(Scalar d))):=by
  rw[Differentiable]  -- Expand differentiability definition: differentiable at every point
  intro x  -- Take any point x, prove differentiability at x
  rw[DifferentiableAt]  -- Expand differentiability at a point definition

  -- Construct derivative: a bounded linear map f from ℝ to Scalar d
  let f: ℝ →L[ℝ] (Scalar d) :={
    toFun:=(fun t=>(⟨t⟩:(Scalar d)))  -- Mapping function: wrap real number t as Scalar d
    map_add':=by  -- Verify linearity: preserves addition (f(x+y) = f(x)+f(y))
      intro x y
      exact rfl  -- Directly holds by Scalar addition definition
    map_smul':=by  -- Verify linearity: preserves scalar multiplication (f(m·x) = m·f(x))
      intro m x1
      simp  -- Simplify expression
      exact rfl  -- Directly holds by Scalar scalar multiplication definition
    cont:={  -- Verify continuity: preimage of open set is open
      isOpen_preimage:=by
        intro s hs  -- Take any open set s and its open set property hs
        apply (open_set_iff s).mp at hs  -- Use previously proved open set equivalence
        exact hs  -- Get that preimage is also open
    }
  }

  -- Prove that mapping f at any point x equals ⟨x⟩
  have hf:∀x:ℝ , f x=(⟨x⟩:(Scalar d)):=by
    intro x;exact rfl  -- Directly holds by f's definition

  use f  -- Specify f as derivative
  rw[HasFDerivAt]  -- Expand Fréchet derivative definition
  refine { isLittleOTVS := ?_ }  -- Prove remainder is little-o

  -- Prove remainder is identically zero (thus satisfying little-o condition)
  have hsimp:(fun (x':ℝ) => ((⟨x'⟩:(Scalar d)) - (⟨x⟩:(Scalar d)) - f (x' - x)))=0:=by
    refine funext ?_  -- Prove function equality using function extensionality
    intro x'  -- Take any x'
    rw[hf]  -- Replace f(x'-x) with ⟨x'-x⟩
    simp  -- Simplify expression
    exact sub_self ((⟨x'⟩:(Scalar d)) - (⟨x⟩:(Scalar d)))  -- Any element minus itself is zero

  rw[hsimp]  -- Replace remainder with zero function
  -- Zero function satisfies little-o condition
  exact Asymptotics.IsLittleOTVS.zero (fun x' => x' - x) (𝓝 x)


-- Define variable K: a normed additive commutative group and normed space over ℝ
variable (K:Type*)[NormedAddCommGroup K][NormedSpace ℝ K]

-- Theorem: Composition of two differentiable functions is still differentiable
-- f:ℝ→ℝ differentiable, g:ℝ→K differentiable, then g∘f is differentiable
theorem differ3(f:ℝ → ℝ)(g:ℝ → K)(h1:Differentiable ℝ f)(h2:Differentiable ℝ g):
  Differentiable ℝ (g∘ f):=by
  exact Differentiable.comp h2 h1  -- Directly apply differentiability composition property


-- Define physical lift function: "lift" real function f to mapping between scalars
-- Effect: Scalar d1 → Scalar d2, by first taking scalar's real value, then applying f, finally wrapping as new scalar
def physlift(d1 d2:Dimensions)(f:ℝ→ ℝ):Scalar d1→ Scalar d2:=(fun t => ⟨f t.val⟩)

-- Define mathematical conversion function: "convert" mapping between scalars f to real function
-- Effect: ℝ → ℝ, by first wrapping real number as Scalar d1, applying f, then taking real value
def mathcast{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2):ℝ → ℝ:= (fun t=> (f ⟨t⟩).val)


-- Physical lift definition theorem: explicitly state specific form of physlift
theorem physlift_def(d1 d2:Dimensions)(f:ℝ→ ℝ):
  physlift d1 d2 f=(fun t => ⟨f t.val⟩):=rfl  -- Directly holds by definition

-- Mathematical conversion definition theorem: explicitly state specific form of mathcast
theorem mathcast_def(d1 d2:Dimensions)(f:Scalar d1→ Scalar d2):
  mathcast f=(fun t=> (f ⟨t⟩).val):=rfl  -- Directly holds by definition

-- Two physical functions are equal if and only if they are equal as mathematical functions
theorem physfunc_eq_iff{d1 d2:Dimensions}(f1 f2:Scalar d1→ Scalar d2):f1=f2 ↔ mathcast f1=mathcast f2:=by
  constructor
  intro h
  exact congrArg mathcast h
  intro h
  refine funext ?_
  intro x
  refine Scalar.ext_iff.mpr ?_
  have h1:(f1 x).val=(mathcast f1) x.val:=rfl
  have h2:(f2 x).val=(mathcast f2) x.val:=rfl
  rw[h1,h2,h]

-- Lift and conversion inverse property 1: for real function f, lift then convert equals f itself
theorem lift_cast_inverse(d1 d2:Dimensions)(f:ℝ→ ℝ):
  mathcast (physlift d1 d2 f)=f:=by
  refine funext ?_  -- Prove using function extensionality
  intro x  -- Take any real number x
  rw[physlift_def,mathcast_def]  -- Obviously holds after expanding definitions

-- Lift and conversion inverse property 2: for scalar function f, convert then lift equals f itself
theorem cast_lift_inverse{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2):
  physlift d1 d2 (mathcast f)=f:=by
  refine funext ?_  -- Prove using function extensionality
  intro x  -- Take any scalar x
  rw[physlift_def,mathcast_def]  -- Obviously holds after expanding definitions

-- Differentiability of physical lift: if real function f is differentiable, then its lifted scalar function is also differentiable
theorem physlift_dif(f:ℝ → ℝ)(d1 d2:Dimensions)(h:Differentiable ℝ f):
  Differentiable ℝ (physlift d1 d2 f):=by
  -- Prove physlift can be expressed as composition of three functions:
  -- Scalar→real (take val)→real (apply f)→scalar (wrap)
  have hcomp:(physlift d1 d2 f)=(fun (t:ℝ)=>(⟨t⟩:Scalar d2))∘ f ∘ (fun t=>t.val):=by
    rw[physlift_def]  -- Expand physlift definition
    refine funext ?_  -- Prove using function extensionality
    intro x  -- Take any scalar x
    simp  -- Equality holds after simplification

  rw[hcomp]  -- Replace physlift with composition form
  -- Prove composite function is differentiable: by differentiability composition property
  refine Differentiable.comp ?_ ?_
  exact isdifferentiable_phys_lift  -- Outer layer (real→scalar) differentiable
  refine Differentiable.comp h ?_   -- Middle layer f differentiable, composed with inner layer
  exact differentiable_real_cast    -- Innermost layer (scalar→real) differentiable


-- Differentiability of mathematical conversion: if scalar function f is differentiable, then its converted real function is also differentiable
theorem mathcast_dif{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2)(h:Differentiable ℝ f):
  Differentiable ℝ (mathcast f):=by
  -- Prove mathcast can be expressed as composition of three functions:
  -- Real→scalar (wrap)→scalar (apply f)→real (take val)
  have hcomp:(mathcast f)=(fun t=>t.val)∘ f ∘ (fun t=>(⟨t⟩:(Scalar d1))):=by
    rw[mathcast_def]  -- Expand mathcast definition
    refine funext ?_  -- Prove using function extensionality
    intro x  -- Take any real number x
    simp  -- Equality holds after simplification

  rw[hcomp]  -- Replace mathcast with composition form
  -- Prove composite function is differentiable: by differentiability composition property
  refine Differentiable.comp ?_ ?_
  exact differentiable_real_cast    -- Outer layer (scalar→real) differentiable
  refine Differentiable.comp h ?_   -- Middle layer f differentiable, composed with inner layer
  exact isdifferentiable_phys_lift  -- Innermost layer (real→scalar) differentiable

-- Define physical derivative function: differentiate scalar function with dimensions, ensuring dimensional correctness
-- Parameter: f is function from scalar of dimension d1 to scalar of dimension d2
-- Output: function from scalar of dimension d1 to scalar of dimension (d2-d1) (derivative dimension is difference of original function dimensions)
-- Implementation: convert physical quantity function to mathematical quantity (mathcast), differentiate with respect to input scalar's value (x.val), then wrap as physical scalar
noncomputable def physderiv{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2):Scalar d1→ Scalar (d2-d1):=
  (fun x=>⟨deriv (mathcast f) x.val⟩)

-- Physical derivative definition theorem: verify correctness of physderiv definition (equality by definition)
theorem physderiv_def{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2):
  physderiv f=(fun x=>⟨deriv (mathcast f) x.val⟩):=rfl

-- Relationship theorem between physical derivative and mathematical derivative: mathematical conversion of physical derivative equals derivative of original function's mathematical conversion
-- Establish consistency between physical operations and mathematical operations
theorem deriv_mathphys{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2):
  mathcast (physderiv f)=deriv (mathcast f):=rfl

-- Define physical mapping multiplication: multiply two scalar functions with same input dimension, dimensions follow addition rule
-- Parameters: f1 (output dimension d2), f2 (output dimension d3) are both functions from d1 to corresponding dimensions
-- Output: product function, output dimension is d2+d3 (physical quantity multiplication adds dimensions)
def physmapmul{d1 d2 d3:Dimensions}(f1:Scalar d1→ Scalar d2)(f2:Scalar d1→ Scalar d3):Scalar d1→ Scalar (d2+d3):=
  fun x=>(f1 x)*(f2 x)

-- Physical mapping multiplication definition theorem: verify correctness of physmapmul definition
theorem phymapmul_def{d1 d2 d3:Dimensions}(f1:Scalar d1→ Scalar d2)(f2:Scalar d1→ Scalar d3):
  physmapmul f1 f2=fun x=>(f1 x)*(f2 x):=rfl

-- Define physical mapping division: divide two scalar functions with same input dimension, dimensions follow subtraction rule
-- Parameters: f1 (output dimension d2), f2 (output dimension d3) are both functions from d1 to corresponding dimensions
-- Output: quotient function, output dimension is d2-d3 (physical quantity division subtracts dimensions)
noncomputable def physmapdiv{d1 d2 d3:Dimensions}(f1:Scalar d1→ Scalar d2)(f2:Scalar d1→ Scalar d3):Scalar d1→ Scalar (d2-d3):=
  fun x=>((f1 x)/(f2 x))

-- Physical mapping division definition theorem: verify correctness of physmapdiv definition
theorem phymapmdiv_def{d1 d2 d3:Dimensions}(f1:Scalar d1→ Scalar d2)(f2:Scalar d1→ Scalar d3):
  physmapdiv f1 f2=fun x=>((f1 x)/(f2 x)):=rfl

-- Define physical mapping scalar multiplication: multiplication of scalar and function, dimensions follow addition rule
-- Parameters: f (output dimension d3) is function from d1 to d3; a is scalar of dimension d2
-- Output: product function, output dimension is d2+d3 (scalar multiplied by physical quantity adds dimensions)
def physmapsmul{d1 d2 d3:Dimensions}(f:Scalar d1→ Scalar d3)(a: Scalar d2):Scalar d1→ Scalar (d2+d3):=
  fun x=>a*(f x)

-- Physical mapping scalar multiplication definition theorem: verify correctness of physmapsmul definition
theorem phymapsmul_def{d1 d2 d3:Dimensions}(f:Scalar d1→ Scalar d2)(a: Scalar d3):
  physmapsmul f a=fun x=>a*(f x):=rfl

-- Scalar multiplication mathematical conversion theorem: mathematical conversion of physical scalar multiplication equals scalar value multiplied by function's mathematical conversion
-- Ensure mathematical conversion of physical operations conforms to scalar multiplication rules
theorem smul_cast{d1 d2 d3:Dimensions}(f:Scalar d1→ Scalar d3)(a: Scalar d2):
  mathcast (physmapsmul f a)=a.val • (mathcast f):=rfl

-- Define physical mapping dimension conversion: convert function's input and output dimensions through dimension equivalence relations
-- Parameters: f is function from d1 to d2; h1 proves d1=d3, h2 proves d2=d4 (dimension equivalences)
-- Implementation: convert input scalar dimension according to h1 then pass to f, convert result according to h2's symmetric relation
def physmapcast{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2)(d3 d4:Dimensions)(h1:d1=d3)(h2:d2=d4):Scalar d3→ Scalar d4:=
  fun a=>((f (a.cast h1)).cast h2.symm)

-- Physical mapping dimension conversion definition theorem: verify correctness of physmapcast definition
theorem phymapcast_def{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2)(d3 d4:Dimensions)(h1:d1=d3)(h2:d2=d4):
  physmapcast f d3 d4 h1 h2=fun (a:(Scalar d3))=> ((f (a.cast h1)).cast h2.symm):=rfl

-- Dimension conversion mathematical equivalence theorem: after dimension conversion, function's mathematical conversion equals original function's mathematical conversion
-- Shows dimension conversion doesn't affect function's mathematical essence
theorem map_cast_matheq{d1 d2:Dimensions}(f:Scalar d1→ Scalar d2)(d3 d4:Dimensions)(h1:d1=d3)(h2:d2=d4):
  mathcast f=mathcast (physmapcast f d3 d4 h1 h2):=rfl

-- Define a structure named hom with parameters d1 and d2 (dimensions)
structure hom (d1 d2:Dimensions) where
  -- map: mapping from scalar of dimension d1 to scalar of dimension d2
  map:Scalar d1→ Scalar d2
  -- math: function from real to real, defined as converting scalar ⟨t⟩ through map then taking its value (stripping dimension information)
  math:ℝ → ℝ :=fun t=>(map ⟨t⟩).val
  -- deriv: mapping from scalar of dimension d1 to scalar of dimension (d2-d1) (derivative, dimensions satisfy subtraction relation)
  deriv:Scalar d1→ Scalar (d2-d1)
  -- Note: int might be field related to integration, not yet implemented
  --int:ℝ×ℝ → ℝ
  -- h: proves math equals mathematical conversion (mathcast) of map
  h: math=mathcast map
  -- h': proves deriv equals physical derivative (physderiv) of map
  h':deriv=physderiv map

-- Theorem: Conversion rule 1, for any t, value of map applied to ⟨t⟩ equals math applied to t
theorem convert_1{d1 d2:Dimensions}(f:hom d1 d2): ∀t, (f.map ⟨t⟩).val=f.math t:=by
  rw[f.h]  -- Use h hypothesis to replace f.math with mathcast f.map
  unfold mathcast  -- Expand mathcast definition
  exact fun t => rfl  -- Obviously holds since mathcast definition is taking scalar's value

-- Theorem: mathcast check, proves mathcast applied to f.map equals f.math
theorem mathcast_check(d1 d2:Dimensions)(f:hom d1 d2):mathcast f.map=f.math:=by
  exact Eq.symm f.h  -- Use symmetry of h (h is math=mathcast map, converse holds)

-- Theorem: physlift check, proves f.map equals physical lift (physlift) applied to f.math
theorem physlift_check(d1 d2:Dimensions)(f:hom d1 d2):f.map=physlift _ _ f.math:=by
  unfold physlift  -- Expand physlift definition
  refine funext ?_  -- Prove function equality extensionally (equal for all inputs)
  intro x  -- Introduce arbitrary input x
  refine Scalar.ext_iff.mpr ?_  -- Use scalar extensionality (equal values imply equal scalars)
  simp  -- Simplify expression
  rw[f.h]  -- Replace f.math using h hypothesis
  unfold mathcast  -- Expand mathcast
  exact rfl  -- Obviously holds

-- Non-computable definition: physical homomorphism lift, wrap scalar mapping f' as hom structure
noncomputable def phys_homlift{d1 d2:Dimensions}(f':Scalar d1→ Scalar d2):hom d1 d2:={
  map:=f'  -- Map field is f'
  math:=mathcast f'  -- Mathematical function is mathcast of f'
  h:=rfl  -- h field is obviously true equality (math=mathcast map)
  deriv:=physderiv f'  -- Derivative field is physical derivative of f'
  h':=rfl  -- h' field is obviously true equality (deriv=physderiv map)
}

-- Theorem: Lift homomorphism mapping equality, proves f' equals map field of phys_homlift f'
theorem lifthom_eq{d1 d2:Dimensions}(f':Scalar d1→ Scalar d2):f'=(phys_homlift f').map:=by
  unfold phys_homlift  -- Expand phys_homlift definition
  exact rfl  -- Obviously holds since map field is f'

-- Theorem: Lift homomorphism mathematical function equality, proves mathcast f' equals math field of phys_homlift f'
theorem lifthom_matheq{d1 d2:Dimensions}(f':Scalar d1→ Scalar d2):mathcast f'=(phys_homlift f').math:=by
  unfold phys_homlift  -- Expand phys_homlift definition
  exact rfl  -- Obviously holds since math field is mathcast f'

-- Non-computable definition: mathematical homomorphism lift, wrap real function f' as hom structure
noncomputable def math_homlift(d1 d2:Dimensions)(f':ℝ→ ℝ ):hom d1 d2:={
  map:=physlift _ _ f'  -- Map field is physical lift of f'
  math:=f'  -- Mathematical function is f'
  h:=rfl  -- h field is obviously true equality
  deriv:=physderiv (physlift _ _ f')  -- Derivative field is physical derivative of physical lift
  h':=rfl  -- h' field is obviously true equality
}
