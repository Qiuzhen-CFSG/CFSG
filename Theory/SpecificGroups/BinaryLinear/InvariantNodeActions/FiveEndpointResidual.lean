module
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators
public import Theory.GroupTheory.PResidual.PerfectCover
/-!
# A nontrivial sixth power in the degree-five endpoint residual

The roots 0←2 and 2←4 lie in the two-residuals of the first and last
minimal parabolics. Their product belongs to the endpoint two-residual,
and its sixth power sends the last basis vector to that vector plus the
first. This obstructs a central product of A₃ blocks, whose exponent
divides six. The witness is symbolic in the original flag basis.

Source: Aschbacher--Smith 15.1.22(3), printed p.1100.
-/
public section
open Subgroup Theory.GroupTheory

namespace BinaryLinear.InvariantNodeActions
open OuterCyclic OrderedResidualConjugators
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

/-- The actual endpoint residual has an element with nonidentity sixth power. -/
theorem five_endpoint_residual_not_exponent_six (b : Basis 4) :
    ∃ x : cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3}ᶜ,
      x ∈ pResidual 2 (cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3}ᶜ) ∧ x ^ 6 ≠ 1 := by
  let E := cutStabilizer b {i : Fin 4 | i.val=0 ∨ i.val=3}ᶜ
  have hn (i : Fin 4) (hi : i=0 ∨ i=3) : minimalParabolic b i ≤ E := by
    apply (cutStabilizer_le_iff b _ _).mpr
    intro j hj he
    change j=i at he
    subst j
    apply hj
    rcases hi with rfl | rfl <;> decide
  have hr (i : Fin 4) (hi : i=0 ∨ i=3) : nodeResidual b i ≤ (pResidual 2 E).map E.subtype :=
    embedded_pResidual_mono 2 (hn i hi)
  let x := root b (0 : Fin 5) 2 (by decide)
  let y := root b (2 : Fin 5) 4 (by decide)
  have hx : x ∈ (pResidual 2 E).map E.subtype := hr 0 (.inl rfl)
    (incident_root_mem_nodeResidual b 0 0 2 (by decide) (Or.inr ⟨Or.inl rfl,by decide⟩))
  have hy : y ∈ (pResidual 2 E).map E.subtype := hr 3 (.inr rfl)
    (incident_root_mem_nodeResidual b 3 2 4 (by decide) (Or.inl ⟨by decide,Or.inr rfl⟩))
  obtain ⟨g,hg,he⟩ := ((pResidual 2 E).map E.subtype).mul_mem hx hy
  change (g : LinearGroup 5) = x*y at he
  refine ⟨g,hg,?_⟩
  intro h6
  have hv : ((x*y)^6) (b 4) = b 4 := by
    have hh := congrArg (fun a : E => (a : LinearGroup 5) (b 4)) h6
    simpa only [coe_pow,coe_one,he,LinearEquiv.coe_one,id_eq] using hh
  have hv' : ((x*y)^6) (b 4) = b 4 + b 0 := by
    simp [x,y,pow_succ,LinearEquiv.mul_apply,root_basis,map_add]
    funext j
    simp only [Pi.add_apply]
    ring_nf
    simp only [show (6 : ZMod 2) = 0 from by decide,
      show (21 : ZMod 2) = 1 from by decide,mul_zero,add_zero,mul_one]
  rw [hv'] at hv
  exact b.ne_zero 0 (add_eq_left.mp hv)
end BinaryLinear.InvariantNodeActions
