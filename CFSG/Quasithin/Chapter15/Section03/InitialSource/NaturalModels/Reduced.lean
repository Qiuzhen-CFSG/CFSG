module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.NaturalModels.Intersections
public import Theory.Representation.SmallBinaryNaturalSimplicity
public import Theory.GroupTheory.PGroup.CharacteristicPairReduction
public import Theory.GroupTheory.ReducedNormal.Basic

/-!
# The original reduced module in 14.1.7

The join of the given reduced module U with V(M) is reduced. The original
source action dichotomy applies to this same join, whose actual natural
SL₂(2) or orthogonal four-dimensional action is simple. Both U and V(M)
are nonzero normal subgroups of the join, so they coincide. Nontriviality
of V(M) follows from the nontrivial central omega subgroup of T.

This identifies the arbitrary source U with the actual localModule and
transports the full natural-action and central-intersection alternatives.
No irreducibility, model, central-line or module-equality premise is added.
The genuine universal earlier Theorems A and C remain explicit.

Source: Aschbacher–Smith 14.1.7, printed p.977, using B.2.11 reduced joins.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
universe u
variable {G : Type u} [Group G] [Finite G]

theorem reduced_eq_localModule_from_source
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (U : Subgroup M) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype hM.2 : Sylow 2 M) : Subgroup M) ≤
      centralizer (U : Set M)) : U = (localModule T M).subgroupOf M := by
  let := hU.normal
  let := hU.elementary
  let V := (localModule T M).subgroupOf M
  have hV := localModule_reduced_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1, hM.2⟩
  let := hV.normal
  let W := U ⊔ V
  have hW : IsPReduced 2 W := hU.sup hV
  let := hW.normal
  let := hW.elementary
  have hUn : U ≠ ⊥ := by
    intro h
    apply hJ
    intro x _ u hu
    have hu1 : u = 1 := mem_bot.mp (h ▸ hu)
    simp only [hu1, one_mul, mul_one]
  have hUS : U ≤ ((T.subtype hM.2 : Sylow 2 M) : Subgroup M) :=
    (IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal (T.subtype hM.2)
  have hTn : (T : Subgroup G) ≠ ⊥ := by
    intro h
    apply hUn
    apply bot_unique
    intro u hu
    have ht : (u : G) ∈ (T : Subgroup G) := hUS hu
    rw [h, mem_bot] at ht
    exact Subtype.ext ht
  have hZn : centralInvolutions T ≠ ⊥ := by
    let : Nontrivial (T : Subgroup G) := (nontrivial_iff_ne_bot _).mpr hTn
    have h := Subgroup.omega_center_ne_bot T.isPGroup'
    intro hz
    apply h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (T : Subgroup G).subtype_injective).mp hz
  have hVn : V ≠ ⊥ := by
    intro h
    apply hZn
    have hVM : localModule T M ≤ M := localModule_le T hM.2
    have he : V.map M.subtype = localModule T M := map_subgroupOf_eq_of_le hVM
    have hbot : localModule T M = ⊥ := by rw [← he, h, Subgroup.map_bot]
    exact bot_unique ((le_conjugateSpanBy _ _).trans_eq hbot)
  have hJW : ¬ elementaryAbelianMaxJ ((T.subtype hM.2 : Sylow 2 M) : Subgroup M) ≤
      centralizer (W : Set M) := fun h => hJ (h.trans (centralizer_le (show U ≤ W from le_sup_left)))
  have hmodel := reduced_natural_models_from_source hA hC hG T hempty hM hunique hcase W hW hJW
  have hsimple (A : Subgroup M) [A.Normal] (hAW : A ≤ W) : A = ⊥ ∨ A = W := by
    apply NormalElementaryQuotient.normal_subgroup_eq_bot_or_eq W ?_ A hAW
    let ρ := NormalElementaryQuotient.representation W
      (QuotientGroup.mk' (centralizer (W : Set M)))
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    rcases hmodel with h | h
    · obtain ⟨c, e, hc⟩ := h
      exact subspace_simple_of_coordinates ρ (fun g v => specialLinearNatural 2 g v) c e hc
        binarySL2_subspace_eq_bot_or_top
    · obtain ⟨c, e, hc⟩ := h
      exact subspace_simple_of_coordinates ρ (fun g v => g.val v) c e hc
        OrthogonalFourBinary.subspace_eq_bot_or_top
  have hUW : U = W := (hsimple U le_sup_left).resolve_left hUn
  have hVW : V = W := (hsimple V le_sup_right).resolve_left hVn
  exact hUW.trans hVW.symm


theorem reduced_14_1_7_from_source
    {G : Type u} [Group G] [Finite G]
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (U : Subgroup M) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype hM.2 : Sylow 2 M) : Subgroup M) ≤
      centralizer (U : Set M)) :
    letI := hU.normal
    letI := hU.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (∃ (c : Additive U ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (e : (M ⧸ centralizer (U : Set M)) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      (∀ g v, c (ρ g v) = Representation.specialLinearNatural 2 (e g) (c v)) ∧
      Nat.card (U.map M.subtype) = 4 ∧
      ChapterB.thompsonAlpha (T : Subgroup G) ⊓ U.map M.subtype = centralInvolutions T ∧
      Nat.card (centralInvolutions T) = 2) ∨
    (Nonempty (NaturalOrthogonalAction M (U.map M.subtype)) ∧
      Nat.card (U.map M.subtype) = 16 ∧
      Nat.card ↥(ChapterB.thompsonAlpha (T : Subgroup G) ⊓ U.map M.subtype) = 4 ∧
      Nat.card (centralInvolutions T) = 2 ∧
      centralInvolutions T ≤ (ChapterB.thompsonAlpha (T : Subgroup G) ⊓ U.map M.subtype)) := by
  have hUeq := reduced_eq_localModule_from_source hA hC hG T hempty hM hunique hcase U hU hJ
  subst U
  have hVM : localModule T M ≤ M := localModule_le T hM.2
  have hJambient : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (localModule T M : Set G) := by
    intro h
    apply hJ
    have he : (elementaryAbelianMaxJ ((T.subtype hM.2 : Sylow 2 M) : Subgroup M)).map M.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [← elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective]
      simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hM.2]
    intro x hx v hv
    have hxm : (x : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) :=
      he ▸ mem_map_of_mem M.subtype hx
    exact Subtype.ext (h hxm v hv)
  have h := local_14_1_7_from_source hA hC hG T hempty hM hunique hcase hJambient
  simpa only [map_subgroupOf_eq_of_le hVM] using h

end CFSG.Quasithin.Chapter15.Section03.InitialSource
