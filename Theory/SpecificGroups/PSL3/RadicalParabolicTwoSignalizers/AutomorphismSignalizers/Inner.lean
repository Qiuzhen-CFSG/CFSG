module

public import Theory.SpecificGroups.PSL3.RadicalParabolicTwoSignalizers.Centralizers
public import Theory.Representation.RankThreeAbelianAutomizer
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Inner two-signalizers of PSL₃(5) parabolic radicals

A normalized two-subgroup has characteristic abelian center. In the faithful
three-dimensional representation its automizer embeds in S₃, so the radical
of order 25 centralizes this center. The self-centralizer calculation and
coprimality kill it; a nontrivial two-group has nontrivial center.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, proof 1.3.8, printed p.513.
-/

public section

open scoped MatrixGroups IsMulCommutative
open Subgroup Matrix.PSL3.RootPlaneGeometry
namespace Matrix.PSL3.RadicalParabolicTwoSignalizers
local notation "F" => ZMod 5

private theorem five_action_perm_three {A : Type*} [Group A]
    (hA : IsPGroup 5 A) (f : A →* Equiv.Perm (Fin 3)) (a : A) : f a = 1 := by
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hr := hA.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hb : f.range = ⊥ := by
    apply card_eq_one.mp
    rcases hr.card_eq_or_dvd with h | h
    · exact h
    · have hd := h.trans f.range.card_subgroup_dvd_card
      rw [hc] at hd
      norm_num at hd
  exact mem_bot.mp (hb ▸ (show f a ∈ f.range from ⟨a,rfl⟩))

private theorem five_normalizes_abelian_two_centralizes
    (A Q : Subgroup (GL (Fin 3) F)) (hA : IsPGroup 5 A) (hQ : IsPGroup 2 Q)
    [IsMulCommutative Q] (hn : A ≤ normalizer (Q : Set (GL (Fin 3) F))) :
    A ≤ centralizer (Q : Set (GL (Fin 3) F)) := by
  obtain ⟨j, hj⟩ := Representation.rankThree_abelian_automizer_embeds_perm
    5 2 (by decide) Q hQ
  let i : A →* normalizer (Q : Set (GL (Fin 3) F)) := inclusion hn
  let f := (j.comp Q.normalizerMonoidHom.rangeRestrict).comp i
  intro a ha
  have he : Q.normalizerMonoidHom (i ⟨a,ha⟩) = 1 := by
    have hh : Q.normalizerMonoidHom.rangeRestrict (i ⟨a,ha⟩) = 1 := by
      apply hj
      change f ⟨a,ha⟩ = j 1
      rw [map_one]
      exact five_action_perm_three hA f ⟨a,ha⟩
    exact congrArg Subtype.val hh
  have hk : i ⟨a,ha⟩ ∈ Q.normalizerMonoidHom.ker := he
  rw [normalizerMonoidHom_ker] at hk
  exact hk

/-- A two-subgroup of the model normalized by either radical is trivial. -/
theorem normalized_twoSubgroup_eq_bot (point : Bool) (S : Subgroup Model)
    (hS : IsPGroup 2 S)
    (hn : rootPlane F point ≤ normalizer (S : Set Model)) : S = ⊥ := by
  let f : Model →* GL (Fin 3) F :=
    Matrix.SpecialLinearGroup.toGL.comp projectionEquiv.symm.toMonoidHom
  have hf : Function.Injective f :=
    Matrix.SpecialLinearGroup.toGL_injective.comp projectionEquiv.symm.injective
  let Z : Subgroup Model := (center S).map S.subtype
  have hZ : IsPGroup 2 Z := (hS.to_subgroup (center S)).map S.subtype
  have hnZ : rootPlane F point ≤ normalizer (Z : Set Model) :=
    hn.trans (normalizer_le_normalizer_characteristic_image S (center S))
  let : IsMulCommutative Z := Subgroup.map_isMulCommutative (center S) S.subtype
  let : IsMulCommutative (Z.map f) := Subgroup.map_isMulCommutative Z f
  have hcen := five_normalizes_abelian_two_centralizes
    ((rootPlane F point).map f) (Z.map f)
    ((IsPGroup.of_card (p := 5) (n := 2) (card_rootPlane point)).map f) (hZ.map f)
    ((Subgroup.map_mono hnZ).trans ((Z.le_normalizer_map f)))
  have hzcen : Z ≤ centralizer (rootPlane F point : Set Model) := by
    intro z hz a ha
    apply hf
    simpa only [map_mul] using ((hcen (mem_map_of_mem f ha)) _ (mem_map_of_mem f hz)).symm
  have hzbot := centralizing_twoSubgroup_eq_bot point Z hZ hzcen
  by_contra hne
  have : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hne
  have : Nontrivial (center S) := hS.center_nontrivial
  have hz : center S = ⊥ := (map_eq_bot_iff_of_injective (center S) S.subtype_injective).mp hzbot
  exact ((Subgroup.nontrivial_iff_ne_bot (center S)).mp inferInstance) hz

end Matrix.PSL3.RadicalParabolicTwoSignalizers
