module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Marked

/-!
# Conjugation on the literal G.2.5 sections

The compatible comparison identifies I/O₂(I) with the specified starred
image of L. On the upper elementary section inner conjugation is trivial.
On the lower section the proved bound [S,S₃]≤S₂ kills that same kernel.
Thus both representations descend through the actual comparison, retaining
the original quotient maps as their binary coordinates.

Full I-invariance of S₃ remains an explicit input to these constructors;
it is the root-group obligation of the recognition argument. No module
recognition, decomposition or equivariant coordinate witness is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(6–7), printed pp.335–336.
-/

@[expose] public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
variable {G : Type*} [Group G]

/-- The earlier structural comparison, with its literal restriction to L.
This is an input from G.2.5(1–3), not an assertion of recognition. -/
structure StarComparison (D : Setup G) (g h : G) (hLI : D.L ≤ I D g h) where
  equivalence : ((I D g h) ⧸ pCore 2 (I D g h)) ≃* D.star D.L
  agrees (l : D.L) :
    equivalence (QuotientGroup.mk' (pCore 2 (I D g h)) (inclusion hLI l)) = starProjection D l

namespace StarComparison
variable {D : Setup G} {g h : G} {hLI : D.L ≤ I D g h}

/-- The projection through the actual core quotient and comparison. -/
def projection (e : StarComparison D g h hLI) : I D g h →* D.star D.L :=
  e.equivalence.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (I D g h)))

theorem projection_surjective (e : StarComparison D g h hLI) :
    Function.Surjective e.projection :=
  e.equivalence.surjective.comp (QuotientGroup.mk'_surjective _)

theorem projection_ker (e : StarComparison D g h hLI) :
    e.projection.ker = (S D g h).subgroupOf (I D g h) := by
  have hk : e.projection.ker = pCore 2 (I D g h) := by
    ext x
    change e.equivalence (QuotientGroup.mk' _ x) = 1 ↔ x ∈ pCore 2 (I D g h)
    rw [e.equivalence.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  rw [hk]
  exact ((pCore 2 (I D g h)).comap_map_eq_self_of_injective (I D g h).subtype_injective).symm

theorem projection_on_L (e : StarComparison D g h hLI) (l : D.L) :
    e.projection (inclusion hLI l) = starProjection D l := e.agrees l

end StarComparison

private def representationOfBinaryAut
    {K Q : Type*} [Group K] [Group Q] [IsElementaryAbelian 2 Q]
    (β : K →* MulAut Q) : Representation (ZMod 2) K (Additive Q) where
  toFun a := (β a).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext v
    change β 1 v.toMul = v.toMul
    rw [map_one]
    rfl
  map_mul' a b := by
    ext v
    change β (a * b) v.toMul = β a (β b v.toMul)
    rw [map_mul]
    rfl

private theorem exists_descended_section
    {K : Type*} [Group K] (H A E C : Subgroup G)
    (hAH : A ≤ H) (hEA : E ≤ A)
    (hNA : H ≤ normalizer (A : Set G)) (hNE : H ≤ normalizer (E : Set G))
    [(E.subgroupOf A).Normal] [IsElementaryAbelian 2 (A ⧸ E.subgroupOf A)]
    (π : H →* K) (hπ : Function.Surjective π) (hk : π.ker = C.subgroupOf H)
    (hcomm : ⁅A, C⁆ ≤ E) :
    ∃ (σ : Representation (ZMod 2) K (Additive (A ⧸ E.subgroupOf A)))
      (s : Representation.BinaryConjugationSection H A E (σ.comp π)),
      ∀ a : A, (s.coordinates a).toAdd =
        Additive.ofMul (QuotientGroup.mk' (E.subgroupOf A) a) := by
  let Q := A ⧸ E.subgroupOf A
  let q := QuotientGroup.mk' (E.subgroupOf A)
  obtain ⟨α, hα⟩ := exists_quotient_conjugation_action H A E hNA hNE inferInstance
  have hkill : π.ker ≤ α.ker := by
    rw [hk]
    exact quotient_conjugation_action_kills_commutator_layer H A E C
      inferInstance hNA hcomm α hα
  let β : K →* MulAut Q := π.liftOfSurjective hπ ⟨α, hkill⟩
  have hβ (x : H) : β (π x) = α x :=
    π.liftOfRightInverse_comp_apply (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨α, hkill⟩ x
  let σ := representationOfBinaryAut β
  let c : A →* Multiplicative (Additive Q) := {
    toFun := fun a => Multiplicative.ofAdd (Additive.ofMul (q a))
    map_one' := q.map_one
    map_mul' := q.map_mul }
  let s : Representation.BinaryConjugationSection H A E (σ.comp π) := {
    section_le := hAH
    kernel_le := hEA
    normalized := hNA
    coordinates := c
    onto := by
      intro v
      obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective (E.subgroupOf A) v.toAdd.toMul
      exact ⟨a, ha⟩
    kernel_eq := by
      ext a
      exact QuotientGroup.eq_one_iff a
    equivariant := by
      intro x a
      change q _ = β (π x) (q a)
      rw [hβ]
      exact (hα x a).symm }
  exact ⟨σ, s, fun _ => rfl⟩

namespace Hypothesis
open Setup
variable [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
include d

/-- Relative normality of the lower denominator uses the already proved
I-normality of S₂ and the series inclusions. -/
theorem lower_normal (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h) :
    ((S₂ D g h).subgroupOf (S₃ D g h)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (((d.series_inclusions hUT hf hLI).2.2.trans (pCoreIn_le 2 (I D g h))).trans
      (le_normalizer_iff_commutator_le_left.mpr
        ((d.intersection hUT hf).2.2.2.1.trans (d.intersection hUT hf).1)))

/-- Construct the literal lower action, factoring through L* rather than
assuming a representation or a module isomorphism. -/
theorem lower_action (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (hgen : S D g h = (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h)
    (hN : I D g h ≤ normalizer (S₃ D g h : Set G))
    (e : StarComparison D g h hLI) :
    letI := lower_normal d hUT hf hLI
    letI := lower_elementary d hUT hf hLI
    ∃ (σ : Representation (ZMod 2) (D.star D.L) (Additive (LowerQuotient D g h)))
      (s : Representation.BinaryConjugationSection (I D g h) (S₃ D g h) (S₂ D g h)
        (σ.comp e.projection)),
      ∀ a : S₃ D g h, (s.coordinates a).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) a) := by
  let := lower_normal d hUT hf hLI
  let := lower_elementary d hUT hf hLI
  have hEN : I D g h ≤ normalizer (S₂ D g h : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((d.intersection hUT hf).2.2.2.1.trans (d.intersection hUT hf).1)
  apply exists_descended_section (I D g h) (S₃ D g h) (S₂ D g h) (S D g h)
    ((d.series_inclusions hUT hf hLI).2.2.trans (pCoreIn_le 2 (I D g h)))
    (d.series_inclusions hUT hf hLI).2.1 hN hEN e.projection e.projection_surjective e.projection_ker
  rw [commutator_comm]
  exact core_centralizes_lower d hUT hf hLI hU hUg hUh hgen

/-- Construct the actual upper quotient action through the same starred
comparison. Its coordinates are the original quotient projection. -/
theorem upper_action (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (hprod : (S D g h : Set G) = (W D g h : Set G) *
      (conjugate (W D g h) g : Set G) * (conjugate (W D g h) h : Set G))
    (hN : I D g h ≤ normalizer (S₃ D g h : Set G))
    (e : StarComparison D g h hLI) :
    letI : ((S₃ D g h).subgroupOf (S D g h)).Normal :=
      normal_subgroupOf_of_le_normalizer (core_normalizes_third d hLI hU hUg hUh)
    letI := upper_elementary d hUT hf hLI hU hUg hUh hprod
    ∃ (σ : Representation (ZMod 2) (D.star D.L) (Additive (UpperQuotient D g h)))
      (s : Representation.BinaryConjugationSection (I D g h) (S D g h) (S₃ D g h)
        (σ.comp e.projection)),
      ∀ a : S D g h, (s.coordinates a).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₃ D g h).subgroupOf (S D g h)) a) := by
  let : ((S₃ D g h).subgroupOf (S D g h)).Normal :=
    normal_subgroupOf_of_le_normalizer (core_normalizes_third d hLI hU hUg hUh)
  let := upper_elementary d hUT hf hLI hU hUg hUh hprod
  exact Representation.BinaryConjugationSection.exists_canonical
    (I D g h) (S D g h) (S₃ D g h) (pCoreIn_le 2 (I D g h))
    (d.series_inclusions hUT hf hLI).2.2 (I_normalizes_core D g h) hN
    e.projection e.projection_surjective e.projection_ker

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
