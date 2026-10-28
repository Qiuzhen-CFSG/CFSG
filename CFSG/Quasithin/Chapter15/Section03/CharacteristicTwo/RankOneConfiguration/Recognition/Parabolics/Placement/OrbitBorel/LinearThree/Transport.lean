module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Reduction
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.GroupTheory.SylowCoprimeEquivalence

/-!
# Sylow transport for the binary linear-three orbit

The concrete Borel calculation makes the Sylow two-subgroups of every actual
PSL₃(2) model self-normalizing. This property restricts to overgroups and
forces a normal image of the Sylow subgroup under a surjection to be the
whole image. The latter is the Frattini step needed for the product argument.

The Sylow three-order is preserved on restriction to an overgroup and under
any homomorphism with two-group kernel. Restriction to the actual subgroup
and the coprime-kernel Sylow equivalence justify the quotient passage; no
solvability, central kernel, or model-recognition certificate is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the L₃(2)
exclusion in the proof of 15.3.27, printed p.1130 (PDF p.1147).
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree
universe u v
variable {A : Type u} {B : Type v} [Group A] [Finite A] [Group B]

/-- Transport binary Borel self-normalization through the actual model isomorphism. -/
theorem model_sylow_self_normalizing (hA : ClassicalGroup.IsPSL A 3 2)
    (P : Sylow 2 A) : normalizer (P : Set A) = (P : Subgroup A) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hA
  have he := Matrix.PSL3.LinearThree.BorelStructure.normalizer_eq_self_of_card_two
    F hcard (P.mapSurjective (f := e.toMonoidHom) e.surjective)
  change normalizer ((P : Subgroup A).map e.toMonoidHom : Set PSL(3,F)) =
    (P : Subgroup A).map e.toMonoidHom at he
  rw [← map_equiv_normalizer_eq] at he
  exact (map_injective e.injective) he

/-- A two-group kernel preserves the Sylow three-order of every subgroup image. -/
theorem sylow_three_card_image (f : A →* B) (hk : IsPGroup 2 f.ker)
    (Y : Subgroup A) (hY : ∀ P : Sylow 3 Y, Nat.card P = 3)
    (Q : Sylow 3 (Y.map f)) : Nat.card Q = 3 := by
  let g := f.subgroupMap Y
  have hg : Function.Surjective g := f.subgroupMap_surjective Y
  have hkg : IsPGroup 2 g.ker := by
    dsimp [g]
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  have hcop : Nat.Coprime 3 (Nat.card g.ker) := by
    obtain ⟨n, hn⟩ := hkg.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  let P : Sylow 3 Y := Sylow.nonempty.some
  exact (Nat.card_congr (P.equivOfSurjectiveCoprime g hg hcop Q).toEquiv).symm.trans (hY P)

omit [Finite A] in
/-- Self-normalization restricts to every overgroup of the supplied Sylow subgroup. -/
theorem self_normalizing_sylow_subtype (P : Sylow 2 A)
    (hP : normalizer (P : Set A) = (P : Subgroup A))
    (H : Subgroup A) (hPH : (P : Subgroup A) ≤ H) :
    normalizer (P.subtype hPH : Set H) = (P.subtype hPH : Subgroup H) := by
  change normalizer ((P : Subgroup A).subgroupOf H : Set H) = _
  rw [← subgroupOf_normalizer_eq hPH]
  change (normalizer (P : Set A)).subgroupOf H = _
  rw [hP]
  rfl

/-- Frattini: a normal overgroup of a self-normalizing Sylow subgroup is the whole group. -/
theorem normal_overgroup_eq_top (P : Sylow 2 A)
    (hP : normalizer (P : Set A) = (P : Subgroup A))
    (N : Subgroup A) [N.Normal] (hPN : (P : Subgroup A) ≤ N) : N = ⊤ := by
  have h := P.normalizer_sup_eq_top' hPN
  rwa [hP, sup_of_le_right hPN] at h


/-- Passing to a containing subgroup preserves the intrinsic Sylow three-order. -/
theorem sylow_three_card_subgroupOf (Y H : Subgroup A) (hYH : Y ≤ H)
    (hY : ∀ P : Sylow 3 Y, Nat.card P = 3)
    (Q : Sylow 3 (Y.subgroupOf H)) : Nat.card Q = 3 := by
  let e := subgroupOfEquivOfLe hYH
  let P := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card P = Nat.card Q := by
    change Nat.card ((Q : Subgroup (Y.subgroupOf H)).map e.toMonoidHom) = Nat.card Q
    exact card_map_of_injective e.injective
  exact hcard.symm.trans (hY P)

/-- If the image of a self-normalizing Sylow two-subgroup becomes normal,
it is the whole image group. -/
theorem image_isTwoGroup_of_normal_sylow (P : Sylow 2 A)
    (hP : normalizer (P : Set A) = (P : Subgroup A))
    (f : A →* B) (hf : Function.Surjective f)
    (hn : ((P : Subgroup A).map f).Normal) : IsPGroup 2 B := by
  let _ := hn
  have ht : (P : Subgroup A).map f = ⊤ := by
    rw [← hP, P.normalizer_map_surjective f hf, normalizer_eq_top]
  apply (P.isPGroup'.map f).of_surjective
    (topEquiv.toMonoidHom.comp (MulEquiv.subgroupCongr ht).toMonoidHom)
  exact topEquiv.surjective.comp (MulEquiv.subgroupCongr ht).surjective

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree
