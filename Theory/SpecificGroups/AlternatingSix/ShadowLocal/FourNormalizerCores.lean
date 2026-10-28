module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryPair
public import Theory.GroupTheory.SymmetricFourModelCoreData
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Two-cores of four-group normalizers in Aut(A₆)

The compatible S₄ × C₂ normalizer model has an elementary two-core of
order eight. The inner four-group is normal in its own normalizer and
lies in that core, so the core centralizes it. The relative normalizer
inside a containing Sylow subgroup has order sixteen, hence is Sylow
in the order-48 normalizer. Its core therefore belongs to the chosen
Sylow subgroup. The relative centralizer also has order eight by the
marked holomorph calculation, proving equality of the actual subgroups.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, the local
cores in the proof of 2.5.24, printed p.568. All normality is relative
to the specified four-group normalizer.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace AlternatingSix.ShadowLocal.FourNormalizerCores

private theorem model_centralizer_zero :
    centralizer (Holomorph.kleinZero : Set Holomorph.Model) = Holomorph.ElementaryPair.zero := by
  ext x
  simp only [mem_centralizer_iff, SetLike.mem_coe, Holomorph.mem_kleinZero,
    Holomorph.ElementaryPair.zero, MonoidHom.mem_range]
  revert x
  decide +kernel

private theorem model_centralizer_one :
    centralizer (Holomorph.kleinOne : Set Holomorph.Model) = Holomorph.ElementaryPair.one := by
  ext x
  simp only [mem_centralizer_iff, SetLike.mem_coe, Holomorph.mem_kleinOne,
    Holomorph.ElementaryPair.one, MonoidHom.mem_range]
  revert x
  decide +kernel

private theorem map_centralizer {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (U : Subgroup A) :
    (centralizer (U : Set A)).map e.toMonoidHom = centralizer (U.map e.toMonoidHom : Set B) := by
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  simp only [mem_map_equiv, MulEquiv.symm_apply_apply, mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · intro hx y hy
    obtain ⟨y, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (hx y (by simpa using hy))
  · intro hx y hy
    apply e.injective
    simpa only [map_mul] using hx (e y) (by simpa using hy)

private theorem sylow_centralizer_card (P : Sylow 2 AutA6) (E : Subgroup P)
    [IsKleinFour E] (hE : E ≤ sylowInner P) :
    Nat.card (centralizer (E : Set P)) = 8 := by
  rcases SylowGeometry.kleinFour_subgroups_inner P E hE with rfl | rfl
  · rw [SylowGeometry.kleinZero, ← map_centralizer, model_centralizer_zero,
      card_map_of_injective (Identification.sylowEquiv P).injective]
    exact Holomorph.ElementaryPair.card_zero
  · rw [SylowGeometry.kleinOne, ← map_centralizer, model_centralizer_one,
      card_map_of_injective (Identification.sylowEquiv P).injective]
    exact Holomorph.ElementaryPair.card_one

private def swapSubgroupOf {A : Type*} [Group A] (B C : Subgroup A) :
    B.subgroupOf C ≃* C.subgroupOf B where
  toFun a := ⟨⟨a.val, a.property⟩, a.val.property⟩
  invFun a := ⟨⟨a.val, a.property⟩, a.val.property⟩
  map_mul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private def centralizerEquiv {A : Type*} [Group A] (P J : Subgroup A) (hJP : J ≤ P) :
    centralizer (J.subgroupOf P : Set P) ≃* (P ⊓ centralizer (J : Set A) : Subgroup A) where
  toFun a := ⟨a.val, a.val.property, fun j hj =>
    congrArg Subtype.val (a.property ⟨j, hJP hj⟩ hj)⟩
  invFun a := ⟨⟨a.val, a.property.1⟩, fun j hj => Subtype.ext (a.property.2 j hj)⟩
  map_mul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual relative two-core is elementary of order eight. -/
theorem core_data (F : Subgroup A6) [IsKleinFour F] :
    IsElementaryAbelian 2 (pCore 2
      (normalizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6))) ∧
    Nat.card (pCore 2 (normalizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6))) = 8 := by
  obtain ⟨e⟩ := four_aut_normalizer_equiv_symmetric_prod F
  obtain ⟨hel, hc⟩ := symmetric_four_model_twoCore_data
    (Or.inr ⟨e.trans MulEquiv.prodComm⟩)
  refine ⟨hel, ?_⟩
  have hn := four_aut_normalizer_card F
  rcases hc with hc | hc
  · omega
  · exact hc.1

/-- In any Sylow subgroup containing the four, the core of its full
automorphism normalizer is exactly its relative centralizer. -/
theorem core_eq_sylow_centralizer (P : Sylow 2 AutA6) (F : Subgroup A6)
    [IsKleinFour F] (hFP : F.map (MulAut.conj : A6 →* AutA6) ≤ P) :
    (normalizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6)).pCoreIn 2 =
      (P : Subgroup AutA6) ⊓ centralizer (F.map (MulAut.conj : A6 →* AutA6) : Set AutA6) := by
  let J := F.map (MulAut.conj : A6 →* AutA6)
  let N := normalizer (J : Set AutA6)
  let Q := N.pCoreIn 2
  let E := J.subgroupOf (P : Subgroup AutA6)
  let eJ := F.equivMapOfInjective (MulAut.conj : A6 →* AutA6) inner_injective
  let : IsKleinFour J := {
    card_four := (Nat.card_congr eJ.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eJ).symm.trans IsKleinFour.exponent_two }
  let eE := subgroupOfEquivOfLe hFP
  let : IsKleinFour E := {
    card_four := (Nat.card_congr eE.toEquiv).trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eE).trans IsKleinFour.exponent_two }
  have hEi : E ≤ sylowInner P := by
    intro a ha
    obtain ⟨f, _, hf⟩ := ha
    exact ⟨f, hf⟩
  have hN : Nat.card N = 48 := four_aut_normalizer_card F
  obtain ⟨hel, hQcard⟩ := core_data F
  let : IsElementaryAbelian 2 (pCore 2 N) := hel
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.map _
  have hQc : Nat.card Q = 8 := by
    change Nat.card ((pCore 2 N).map N.subtype) = 8
    rw [card_map_of_injective N.subtype_injective]
    exact hQcard
  have hJp : IsPGroup 2 J := by
    apply IsPGroup.of_card (n := 2)
    exact IsKleinFour.card_four
  have hJQ : J ≤ Q := le_pCoreIn_of_normalizes hJp J.le_normalizer le_rfl
  have hQC : Q ≤ centralizer (J : Set AutA6) :=
    (le_centralizer Q).trans (centralizer_le hJQ)
  let B := (P : Subgroup AutA6).subgroupOf N
  have hBc : Nat.card B = 16 := by
    rw [Nat.card_congr (swapSubgroupOf (P : Subgroup AutA6) N).toEquiv]
    change Nat.card ((normalizer (J : Set AutA6)).subgroupOf (P : Subgroup AutA6)) = _
    rw [subgroupOf_normalizer_eq hFP]
    exact SylowGeometry.card_normalizer_kleinFour P E hEi
  have hBp : IsPGroup 2 B := P.isPGroup'.comap_subtype
  obtain ⟨T, hBT⟩ := hBp.exists_le_sylow
  have hTc : Nat.card T = 16 := by
    rw [T.card_eq_multiplicity, hN]
    rw [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have heBT : B = (T : Subgroup N) := eq_of_le_of_card_ge hBT (by rw [hTc, hBc])
  have hQP : Q ≤ P := by
    rintro _ ⟨q, hq, rfl⟩
    have ht := (pCore_isPGroup (p := 2) (G := N)).le_sylow_of_normal T hq
    rw [← heBT] at ht
    exact ht
  apply eq_of_le_of_card_ge (le_inf hQP hQC)
  rw [← Nat.card_congr (centralizerEquiv (P : Subgroup AutA6) J hFP).toEquiv,
    sylow_centralizer_card P E hEi, hQc]

end AlternatingSix.ShadowLocal.FourNormalizerCores
