module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.BinaryBorel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.BenderNormalizers

/-!
# Choosing the Borel in the actual component product

For a subgroup K with actual coordinates K ≃ Q × Q, the Borel is the
ambient image of the normalizer of a specified Sylow two-subgroup of K.
Solvability puts J in this normalizer. If the Sylow image is T ∩ K and T
normalizes K, then T normalizes that same Borel. Thus J T normalizes it,
without assuming the Borel containment or normalization conclusions.

For Q ≅ PSL₂(2ⁿ), the coordinates retain the actual ambient inclusion.
The Borel order detects even n, and the product calculation gives three-rank
two. These are intrinsic steps in Aschbacher–Smith, proof of 13.8.16(1),
printed p.952/PDF p.969 (combined manuscript of 1 March 2004).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SylowBorel
variable {D Q : Type*} [Group D] [Group Q]

def relativeBorel (K : Subgroup D) (S : Sylow 2 K) : Subgroup D :=
  (normalizer (S : Set K)).map K.subtype

theorem relativeBorel_le (K : Subgroup D) (S : Sylow 2 K) : relativeBorel K S ≤ K :=
  map_subtype_le _

theorem relativeBorel_eq (K : Subgroup D) (S : Sylow 2 K) :
    relativeBorel K S = normalizer (((S : Subgroup K).map K.subtype) : Set D) ⊓ K := by
  have he : ((S : Subgroup K).map K.subtype).subgroupOf K = (S : Subgroup K) := by
    exact comap_map_eq_self_of_injective K.subtype_injective _
  have hn := subgroupOf_normalizer_eq (map_subtype_le (S : Subgroup K))
  rw [he] at hn
  change (normalizer (((S : Subgroup K).map K.subtype) : Set D)).subgroupOf K =
    normalizer (S : Set K) at hn
  rw [relativeBorel, ← hn, subgroupOf_map_subtype]

theorem sylow_le (K : Subgroup D) (S : Sylow 2 K) :
    (S : Subgroup K).map K.subtype ≤ relativeBorel K S :=
  map_mono le_normalizer

private theorem normalizes_normalizer (A : Subgroup D) {t : D}
    (ht : t ∈ normalizer (A : Set D)) :
    t ∈ normalizer (normalizer (A : Set D) : Set D) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_normalizer_eq_of_bijective _ (MulAut.conj t).bijective,
    mem_normalizer_iff_map_conj_eq.mp ht]

theorem normalized (K T : Subgroup D) (S : Sylow 2 K)
    (hTK : T ≤ normalizer (K : Set D))
    (hS : (S : Subgroup K).map K.subtype = T ⊓ K) :
    T ≤ normalizer (relativeBorel K S : Set D) := by
  have hTS : T ≤ normalizer (((S : Subgroup K).map K.subtype) : Set D) := by
    rw [hS]
    exact (le_inf T.le_normalizer hTK).trans inf_normalizer_le_normalizer_inf
  rw [relativeBorel_eq]
  exact (le_inf (fun _ ht => normalizes_normalizer _ (hTS ht)) hTK).trans
    inf_normalizer_le_normalizer_inf

variable [Finite D] [Finite Q]

noncomputable def productSylow (K : Subgroup D) (e : K ≃* Q × Q)
    (S : Sylow 2 K) : Sylow 2 (Q × Q) := S.mapSurjective (f := e.toMonoidHom) e.surjective

noncomputable def coordinates (K : Subgroup D) (e : K ≃* Q × Q)
    (S : Sylow 2 K) : relativeBorel K S ≃* BinaryBorel.borel (productSylow K e S) :=
  ((normalizer (S : Set K)).equivMapOfInjective K.subtype K.subtype_injective).symm.trans
    ((e.subgroupMap (normalizer (S : Set K))).trans
      (MulEquiv.subgroupCongr (map_normalizer_eq_of_bijective _ e.bijective)))

omit [Finite Q] in
theorem coordinates_apply (K : Subgroup D) (e : K ≃* Q × Q)
    (S : Sylow 2 K) (x : relativeBorel K S) :
    (coordinates K e S x : Q × Q) = e ⟨x, relativeBorel_le K S x.property⟩ := by
  let c := (normalizer (S : Set K)).equivMapOfInjective K.subtype K.subtype_injective
  have hc := congrArg Subtype.val (c.apply_symm_apply x)
  change ((c.symm x : normalizer (S : Set K)) : K).val = (x : D) at hc
  apply congrArg e
  exact Subtype.ext hc


theorem solvable (K : Subgroup D) (e : K ≃* Q × Q) (S : Sylow 2 K)
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n)) :
    Group.IsSolvable (relativeBorel K S) := by
  let _ := BinaryBorel.solvable hn hmodel (productSylow K e S)
  exact Group.isSolvable_of_surjective (f := (coordinates K e S).symm.toMonoidHom)
    (coordinates K e S).symm.surjective

theorem contains_marked (K J T : Subgroup D) (e : K ≃* Q × Q)
    (S : Sylow 2 K) {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n)) (hJK : J ≤ K)
    (hS : (S : Subgroup K).map K.subtype ≤ T)
    [Group.IsSolvable (J ⊔ T : Subgroup D)] : J ≤ relativeBorel K S := by
  let A := (J.subgroupOf K).map e.toMonoidHom
  let S' := productSylow K e S
  let W := J.subgroupOf K ⊔ (S : Subgroup K)
  have hW : W ≤ (J ⊔ T).subgroupOf K := by
    apply sup_le
    · exact fun _ hx => (show J ≤ J ⊔ T from le_sup_left) hx
    · intro x hx
      exact (show T ≤ J ⊔ T from le_sup_right) (hS (mem_map_of_mem K.subtype hx))
  let f : W →* (J ⊔ T : Subgroup D) :=
    (K.subtype.comp W.subtype).codRestrict _ (fun x => hW x.property)
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : (J ⊔ T : Subgroup D) => (z : D)) h))
  let _ : Group.IsSolvable W := Group.isSolvable_of_isSolvable_injective hf
  have hmap : W.map e.toMonoidHom = A ⊔ (S' : Subgroup (Q × Q)) := Subgroup.map_sup _ _ _
  let _ : Group.IsSolvable (A ⊔ (S' : Subgroup (Q × Q)) : Subgroup (Q × Q)) := by
    rw [← hmap]
    exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective W)
  have hA := Chapter1.XiEmbedding.SwappedSylow.binary_model_prod_le_normalizer hn hmodel S' A
  intro x hx
  refine ⟨⟨x, hJK hx⟩, ?_, rfl⟩
  have hex : e ⟨x, hJK hx⟩ ∈ normalizer (S' : Set (Q × Q)) :=
    hA (mem_map_of_mem e.toMonoidHom (show (⟨x, hJK hx⟩ : K) ∈ J.subgroupOf K from hx))
  have hm : (normalizer (S : Set K)).map e.toMonoidHom = normalizer (S' : Set (Q × Q)) :=
    map_normalizer_eq_of_bijective _ e.bijective
  rw [← hm] at hex
  obtain ⟨y, hy, hey⟩ := hex
  have hexy : y = ⟨x, hJK hx⟩ := e.injective hey
  subst y
  exact hy

theorem contains_and_normalized (K J T : Subgroup D) (e : K ≃* Q × Q)
    (S : Sylow 2 K) {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n)) (hJK : J ≤ K)
    (hTK : T ≤ normalizer (K : Set D))
    (hS : (S : Subgroup K).map K.subtype = T ⊓ K)
    [Group.IsSolvable (J ⊔ T : Subgroup D)] :
    J ≤ relativeBorel K S ∧ J ⊔ T ≤ normalizer (relativeBorel K S : Set D) := by
  have hJ := contains_marked K J T e S hn hmodel hJK (hS.le.trans inf_le_left)
  exact ⟨hJ, sup_le (hJ.trans (relativeBorel K S).le_normalizer) (normalized K T S hTK hS)⟩

/-- The order calculation is only for the Borel, not the ambient simple group. -/
theorem card (K : Subgroup D) (e : K ≃* Q × Q) (S : Sylow 2 K)
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n)) :
    Nat.card (relativeBorel K S) = (2 ^ n * (2 ^ n - 1)) ^ 2 := by
  rw [Nat.card_congr ((coordinates K e S).trans
    (BinaryBorel.coordinates (productSylow K e S))).toEquiv, Nat.card_prod,
    (BinaryBorel.factor_facts hn hmodel _).2.2.2.2,
    (BinaryBorel.factor_facts hn hmodel _).2.2.2.2, pow_two]

theorem even_of_three_dvd (K : Subgroup D) (e : K ≃* Q × Q) (S : Sylow 2 K)
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (hthree : 3 ∣ Nat.card (relativeBorel K S)) : Even n := by
  rw [card K e S hn hmodel] at hthree
  have h := Nat.prime_three.dvd_of_dvd_pow hthree
  have hodd : ¬ 3 ∣ 2 ^ n := fun h =>
    (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h)
  exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp
    ((Nat.prime_three.dvd_mul.mp h).resolve_left hodd)

theorem threeRank (K : Subgroup D) (e : K ≃* Q × Q) (S : Sylow 2 K)
    {n : ℕ} (hn : 2 ≤ n) (hmodel : ClassicalGroup.IsPSL Q 2 (2 ^ n))
    (heven : Even n) : primeRank 3 (relativeBorel K S) = 2 := by
  rw [Theory.GroupTheory.primeRank_equiv 3 (coordinates K e S)]
  exact BinaryBorel.threeRank hn hmodel heven _

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.SylowBorel

end
