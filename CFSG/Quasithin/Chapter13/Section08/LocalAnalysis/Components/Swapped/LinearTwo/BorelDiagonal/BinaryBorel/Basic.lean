module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SL2.EvenBorelResidual

/-!
# Binary product Borels and their marked coordinates

A Sylow two-subgroup of Q × Q is the product of its actual Sylow images.
Its normalizer is therefore the product of the two factor normalizers.
The coordinates below retain the ambient first and second projections.
Self-normalization and the ambient two-core calculation hold for every
Sylow normalizer. For an actual PSL₂(2ⁿ) model, field and Sylow transport
give solvability, two-perfectness, the cyclic torus quotient and its order.

Source: Aschbacher–Smith, proof of 13.8.16(1), printed p.952/PDF p.969.
The Sylow-product argument also occurs in Chapter1,
Embeddings/Swapped/BenderNormalizers; the concrete matrix calculations are
those of ChapterF/Section01/RankOneBorels/Linear and EvenBorelResidual.
This is intrinsic input for the chapter proof, with no ambient classification
or diagonal placement assumed.
-/

@[expose] public section

open Subgroup
open Matrix.ProjectiveSpecialLinearGroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.BinaryBorel
variable {Q : Type*} [Group Q] [Finite Q]

/-- The genuine normalizer of the specified Sylow subgroup. -/
abbrev borel (S : Sylow 2 Q) : Subgroup Q := normalizer (S : Set Q)

/-- The first ambient projection of the chosen product Sylow. -/
noncomputable def firstSylow (S : Sylow 2 (Q × Q)) : Sylow 2 Q :=
  S.mapSurjective (show Function.Surjective (MonoidHom.fst Q Q) from
    fun x => ⟨(x, 1), rfl⟩)

/-- The second ambient projection of the chosen product Sylow. -/
noncomputable def secondSylow (S : Sylow 2 (Q × Q)) : Sylow 2 Q :=
  S.mapSurjective (show Function.Surjective (MonoidHom.snd Q Q) from
    fun x => ⟨(1, x), rfl⟩)

/-- The product Sylow is exactly the product of its two projected Sylows. -/
theorem sylow_eq_prod (S : Sylow 2 (Q × Q)) :
    (S : Subgroup (Q × Q)) =
      (firstSylow S : Subgroup Q).prod (secondSylow S : Subgroup Q) := by
  apply Eq.symm
  apply S.is_maximal'
  · obtain ⟨a, ha⟩ := (firstSylow S).isPGroup'.exists_card_eq
    obtain ⟨b, hb⟩ := (secondSylow S).isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a + b)
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, ha, hb, pow_add]
  · intro x hx
    exact ⟨mem_map_of_mem _ hx, mem_map_of_mem _ hx⟩

/-- The normalizer retains both coordinate normalizers. -/
theorem borel_eq_prod (S : Sylow 2 (Q × Q)) :
    borel S = (borel (firstSylow S)).prod (borel (secondSylow S)) := by
  change normalizer ((S : Subgroup (Q × Q)) : Set (Q × Q)) = _
  rw [sylow_eq_prod S]
  ext x
  constructor
  · intro hx
    constructor
    · apply mem_normalizer_iff.mpr
      intro y
      have h := mem_normalizer_iff.mp hx (y, 1)
      simpa only [mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
        mul_one, mul_inv_cancel, one_mem, and_true] using h
    · apply mem_normalizer_iff.mpr
      intro y
      have h := mem_normalizer_iff.mp hx (1, y)
      simpa only [mem_prod, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv,
        mul_one, mul_inv_cancel, one_mem, true_and] using h
  · intro hx
    apply mem_normalizer_iff.mpr
    intro y
    exact and_congr (mem_normalizer_iff.mp hx.1 y.1) (mem_normalizer_iff.mp hx.2 y.2)

/-- Product coordinates whose underlying maps are the ambient projections. -/
noncomputable def coordinates (S : Sylow 2 (Q × Q)) :
    borel S ≃* borel (firstSylow S) × borel (secondSylow S) :=
  (MulEquiv.subgroupCongr (borel_eq_prod S)).trans (Subgroup.prodEquiv _ _)

theorem coordinates_fst (S : Sylow 2 (Q × Q)) (x : borel S) :
    ((coordinates S x).1 : Q) = (x : Q × Q).1 := rfl

theorem coordinates_snd (S : Sylow 2 (Q × Q)) (x : borel S) :
    ((coordinates S x).2 : Q) = (x : Q × Q).2 := rfl

/-- The inverse coordinates multiply the two genuine ambient factor inclusions. -/
theorem coordinates_symm (S : Sylow 2 (Q × Q))
    (x : borel (firstSylow S)) (y : borel (secondSylow S)) :
    (coordinates S |>.symm (x, y) : Q × Q) = ((x : Q), 1) * (1, (y : Q)) := by
  change ((x : Q), (y : Q)) = ((x : Q), 1) * (1, (y : Q))
  simp

/-- A Sylow normalizer is self-normalizing in its ambient group. -/
theorem self_normalizing (S : Sylow 2 Q) : normalizer (borel S : Set Q) = borel S :=
  S.normalizer_normalizer

omit [Finite Q] in
/-- The ambient image of the intrinsic two-core is the specified Sylow. -/
theorem ambient_twoCore (S : Sylow 2 Q) :
    (pCore 2 (borel S)).map (borel S).subtype = (S : Subgroup Q) :=
  ChapterF.Source.twoCore_sylow_normalizer S

omit [Finite Q] in
theorem twoCore (S : Sylow 2 Q) :
    pCore 2 (borel S) = (S : Subgroup Q).subgroupOf (borel S) := by
  apply Subgroup.map_injective (borel S).subtype_injective
  rw [ambient_twoCore]
  exact (map_subgroupOf_eq_of_le (show (S : Subgroup Q) ≤ borel S from le_normalizer)).symm

/-- Transport the concrete matrix Borel facts through the actual PSL₂ model. -/
theorem factor_facts {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (S : Sylow 2 Q) :
    Group.IsSolvable (borel S) ∧ IsPPerfect 2 (borel S) ∧
      IsCyclic (borel S ⧸ pCore 2 (borel S)) ∧
      Nat.card (borel S ⧸ pCore 2 (borel S)) = 2 ^ n - 1 ∧
      Nat.card (borel S) = 2 ^ n * (2 ^ n - 1) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hm : (borel S).map e.toMonoidHom = borel T :=
    Subgroup.map_normalizer_eq_of_bijective _ e.bijective
  let eB : borel S ≃* OddBorel.borel F :=
    ((e.subgroupMap (borel S)).trans (MulEquiv.subgroupCongr hm)).trans
      (EvenBorelResidual.sylowNormalizerEquiv F T)
  let eT : (borel S ⧸ pCore 2 (borel S)) ≃* Fˣ :=
    (QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).trans
      (EvenBorelResidual.quotientTorusEquiv F hF)
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hn
  have hs := (ChapterF.Source.rankOneSylowFacts_psl2 F n (by omega) hF T).solvable
  have hsolv : Group.IsSolvable (borel S) := by
    let _ := hs
    let eN := (e.subgroupMap (borel S)).trans (MulEquiv.subgroupCongr hm)
    exact Group.isSolvable_of_surjective (f := eN.symm.toMonoidHom) eN.symm.surjective
  refine ⟨hsolv, (EvenBorelResidual.borel_isPPerfect F hq).of_surjective
    eB.symm.toMonoidHom eB.symm.surjective, eT.isCyclic.mpr inferInstance, ?_, ?_⟩
  · rw [Nat.card_congr eT.toEquiv, Nat.card_units, hF]
  · rw [Nat.card_congr eB.toEquiv, EvenBorelResidual.card_borel, hF]

/-- The binary product Borel is solvable. -/
theorem solvable {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (S : Sylow 2 (Q × Q)) : Group.IsSolvable (borel S) := by
  let _ := (factor_facts hn hmodel (firstSylow S)).1
  let _ := (factor_facts hn hmodel (secondSylow S)).1
  exact Group.isSolvable_of_surjective (f := (coordinates S).symm.toMonoidHom) (coordinates S).symm.surjective


end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.BinaryBorel

end
