module

public import CFSG.Quasithin.ChapterE.Section04.GenerationBound.LocalControl.CoreSpace
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.PCoreSurjective

/-!
# The quasisimple local factor lies in the kernel image

Put U = C_V(W_m(O₂(H))) and K = C_H(U). The corank-intersection argument
places W_j(T) in K when j + i(H) ≤ m ≤ k. If H does not normalize W_j(T),
its image in H/O₂(H) is a nontrivial two-subgroup. The quotient has trivial
two-core, so the Chapter B component commutator theorem makes this image
generate F*(H/O₂(H)) by commutators. Normality of K inside H then places
that quasisimple factor in the image of K.

This proves factor containment without an assumption on the outer quotient.
It does not identify O²(H) with that factor or prove normality of KT.
The corank witness's containing member A is allowed to lie outside H.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.4.2,
printed p.241 (PDF p.252); component commutation as in B.1.5(8).
-/

public section

open Subgroup Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValueBound.LocalControl

private theorem quotient_core_bot {X : Type*} [Group X] [Finite X] :
    pCore 2 (X ⧸ pCore 2 X) = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q := QuotientGroup.mk' (pCore 2 X)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he := q.comap_pCore_of_ker_isPGroup hq hk
  have hm := congrArg (map q) he
  rw [map_comap_eq_self_of_surjective hq] at hm
  exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The quasisimple generalized Fitting subgroup of H/O₂(H) lies in the image
of the pointwise kernel on the local invariant space. -/
theorem coreFixedSpace_kernel_image_contains_factor (ρ : Representation (ZMod 2) G V) (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) {k j m : ℕ}
    (hjm : j + primeRank 2 (H ⧸ pCore 2 H) ≤ m) (hmk : m ≤ k)
    (hn : ¬ H ≤ normalizer (weakSubgroup (fixedSpaceFamily ρ (k + 1)) j T : Set G))
    [IsQuasisimple (generalizedFitting (H ⧸ pCore 2 H))] :
    generalizedFitting (H ⧸ pCore 2 H) ≤
      ((subspaceKernel ρ (coreFixedSpace ρ k m H) H).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)) := by
  let K := subspaceKernel ρ (coreFixedSpace ρ k m H) H
  let W := weakSubgroup (fixedSpaceFamily ρ (k + 1)) j T
  let q := QuotientGroup.mk' (pCore 2 H)
  have hWT : W ≤ T := weakSubgroup_le _ _ _
  have hWH : W ≤ H := hWT.trans hTH
  have hWK : W ≤ K := (SubgroupFamily.span_mono _ hTH).trans
    (weakSubgroup_le_coreFixedSpace_kernel ρ H hjm hmk)
  have hWQ : ¬ W.subgroupOf H ≤ pCore 2 H := by
    intro h
    apply hn
    apply weakSubgroup_normalized_of_le_core ρ T H
    have hh := map_mono (f := H.subtype) h
    rwa [map_subgroupOf_eq_of_le hWH] at hh
  have hWne : (W.subgroupOf H).map q ≠ ⊥ := by
    intro he
    apply hWQ
    have hh := (Subgroup.map_eq_bot_iff (W.subgroupOf H)).mp he
    simpa only [q, QuotientGroup.ker_mk'] using hh
  let : (K.subgroupOf H).Normal := coreFixedSpace_kernel_normal ρ k m H
  let : ((K.subgroupOf H).map q).Normal :=
    Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hc := CFSG.Quasithin.ChapterB.QuasisimpleSections.commutator_fitting_eq
    (G := H ⧸ pCore 2 H) quotient_core_bot inferInstance hWne
    (((T.isPGroup'.to_le hWT).comap_subtype).map q)
  rw [← hc]
  exact (commutator_mono le_rfl (map_mono (comap_mono hWK))).trans
    (commutator_le_right _ ((K.subgroupOf H).map q))

end CFSG.Quasithin.ChapterE.ValueBound.LocalControl
