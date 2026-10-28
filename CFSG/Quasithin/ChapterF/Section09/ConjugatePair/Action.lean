module
public import CFSG.Quasithin.ChapterF.Section09.ConjugatePair.Kernel
public import Theory.GroupTheory.ConjugatePairSeed.OrthogonalAction
public import Theory.GroupTheory.ConjugatePairSeed.Generators

/-!
# The original pair in the binary plus orthogonal group

The action on the constructed quaternion seed has the original two-core
kernel. Thus its range is canonically isomorphic to the original pair image
in H/O₂(H). Its two module generators are involutions with singular
displacements. These are exactly the finite orthogonal recognition inputs.
Source: Aschbacher–Smith F.9.5(6.i), printed p.319.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} (h : D.Hypothesis)
include h

omit h [Finite G] in
/-- The marked quotient map on an original pair inside H. -/
@[expose] def pairProjection (I : Subgroup G) (hIH : I ≤ D.H) :
    I →* (D.H ⧸ pCore 2 D.H) :=
  (QuotientGroup.mk' (pCore 2 D.H)).comp (inclusion hIH)

omit h [Finite G] in
theorem pairProjection_ker (I : Subgroup G) (hIH : I ≤ D.H) :
    (pairProjection I hIH).ker = D.QH.subgroupOf I := by
  ext x
  change QuotientGroup.mk' (pCore 2 D.H) ⟨x,hIH x.property⟩ = 1 ↔ _
  have hh := QuotientGroup.eq_one_iff (N := pCore 2 D.H) (⟨x,hIH x.property⟩ : D.H)
  change QuotientGroup.mk' (pCore 2 D.H) ⟨x,hIH x.property⟩ = 1 ↔
    (⟨x,hIH x.property⟩ : D.H) ∈ pCore 2 D.H at hh
  rw [hh]
  change (⟨(x:G),hIH x.property⟩ : D.H) ∈ pCore 2 D.H ↔ (x:G) ∈ D.QH
  exact (show D.QH.subgroupOf D.H = pCore 2 D.H from
    comap_map_eq_self_of_injective D.H.subtype_injective _).symm ▸ Iff.rfl

omit h [Finite G] in
theorem pairProjection_range (I : Subgroup G) (hIH : I ≤ D.H) :
    (pairProjection I hIH).range =
      (I.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)) := by
  rw [pairProjection,MonoidHom.range_comp]
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact i.property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

/-- The original pair image is the exact range of its quaternion square action. -/
theorem pair_orthogonal_range
    (hi : D.Vplus.relIndex D.V = 2) (hcard : Nat.card D.V = 16)
    (hp : ∀ g ∈ D.H, D.V₁ < D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom →
      IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (hc : ⁅D.V,D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (g : G) (hg : g ∈ D.H)
    (hn : ¬ IsPGroup 2 (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (q : QuaternionCentralProductData
      (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let I := D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom
    let P := D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom
    Nonempty (((I.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) ≃*
      (seedOrthogonalAction I P (h.pair_normalizes_seed_join hi g hg hn) q).range) := by
  dsimp only
  let I := D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom
  let P := D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom
  have hIH : I ≤ D.H := sup_le h.V_le_H (by
    rintro _ ⟨a,ha,rfl⟩
    exact D.H.mul_mem (D.H.mul_mem hg (h.V_le_H ha)) (D.H.inv_mem hg))
  let α := seedOrthogonalAction I P (h.pair_normalizes_seed_join hi g hg hn) q
  have hk : α.ker = D.QH.subgroupOf I := by
    rw [seedOrthogonalAction_ker I P D.V₁ _ q (h.pair_seed_center hp hc g hg hn)
      (hIH.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))),
      h.pair_seed_kernel hi hcard hp hc g hg hn]
    ext x
    exact and_iff_right x.property
  exact ⟨(MulEquiv.subgroupCongr (pairProjection_range I hIH).symm).trans
    (rangeEquivOfKerEq (pairProjection I hIH) α
      ((pairProjection_ker I hIH).trans hk.symm))⟩
end CFSG.Quasithin.ChapterF.Section09.Setup.Hypothesis
