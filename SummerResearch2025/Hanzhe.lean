import mathlib
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LocalExtr
open Metric Set Asymptotics Filter Real
open scoped Topology NNReal
open Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


--y₀will be equilibrium point
--f' will= v(t,f(t)) ∀ t∈[a,b)
--f will= [y₁,y₂,....]
variable {v : ℝ → E → E}{y₀: E}{r:ℝ}{local_region:Set E}{K : ℝ≥0}{f : ℝ → E}{f' : ℝ →L[ℝ] E}
--{f' : ℝ → E}


{a b t₀ : ℝ}{s : ℝ → Set E}
--V is lya. function
variable{V:E→ℝ}{V':E →L[ℝ] ℝ}
--{V':E → ℝ}


def new_stable(f: ℝ→E)(eq:E): Prop:=
 ∀ ε > 0, ∃ δ>0, ∀ p, ‖p - eq‖ < δ → ∀ t: ℝ, 0 ≤ t → ‖f t - eq‖ < ε
def new_asymptotically_stable (f: ℝ→E)(eq:E):
Prop :=
 (∀ ε > 0, ∃ δ>0, ∀ p, ‖p-eq‖<δ → ∀ t: ℝ, 0 ≤ t → ‖ f t - eq‖ <ε)∧
 (∃ δ₀ > 0, ∀ p, ‖p - eq‖ < δ₀ → ∀ ε₀ > 0,∃ N >0,∀t,t >N →‖f t - eq‖ < ε₀)
theorem lya
 --(hv : ∀ t ∈ Ico a b, LipschitzOnWith K (v t) (s t))
 (hf : ContinuousOn f (Icc a b))
 (hf' : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)--forces f' to be deriv. of f
 (f_bound : ∀ t ∈ Ico a b, dist (f' t) (v t (f t)) ≤ 0)--forces f to be soln to the ode
 (hy₀:∀ t: ℝ, v t y₀ = 0)--forces y₀ to be an equi. pt
 (loc:y₀∈ local_region)--forces locall_region to contain equi. pt.
 --??need to set arbitrary radius for locall_region ??? doesn't feel like it
 (VE: ∃ V, (ContinuousOn V local_regin)--Vcont
