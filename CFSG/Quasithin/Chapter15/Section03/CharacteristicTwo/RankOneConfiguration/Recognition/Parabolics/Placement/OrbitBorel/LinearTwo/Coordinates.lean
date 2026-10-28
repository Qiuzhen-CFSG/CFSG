module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Reduction
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.GroupTheory.PrimeRankProduct

/-!
# Matrix coordinates for the nonnormal linear-two orbit

The source candidate is the literal subgroup L₀ ∩ N_G(S ∩ L₀).
Coordinates records an actual surjection from L₀ onto two projective matrix
factors, with kernel O₂(L₀), taking the full preimage of the standard root
product to S ∩ L₀. Constructing these coordinates is a separate obligation.
No Borel placement, invariance, parity or rank assertion is a record field.

The normalizer-preimage identity constructs a surjection from the candidate
Borel onto the product of the actual matrix Borels. Its kernel is precisely
the restriction of O₂(L₀), hence a two-group. The torus quotient proves
solvability. Divisibility of the Borel order by three forces even field degree;
each of its two quotient factors then contributes positive three-rank.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.27(1), printed p.1130 (PDF p.1147).
-/

@[expose] public section

open Subgroup
open Matrix.ProjectiveSpecialLinearGroup OddBorel EvenBorelResidual
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearTwo

variable {G : Type*} [Group G]

def canonicalBorel (L S : Subgroup G) : Subgroup G :=
  L ⊓ normalizer (S ⊓ L : Set G)

structure Coordinates (L S : Subgroup G) (F : Type*) [Field F] where
  quotient : L →* (PSL(2,F) × PSL(2,F))
  onto : Function.Surjective quotient
  kernel_eq : quotient.ker = pCore 2 L
  root_preimage : ((kernel F).prod (kernel F)).comap quotient = S.subgroupOf L

theorem Coordinates.kernel_two {L S : Subgroup G} {F : Type*} [Field F]
    (a : Coordinates L S F) : IsPGroup 2 a.quotient.ker := by
  rw [a.kernel_eq]
  exact pCore_isPGroup

private theorem normalizer_prod {A B : Type*} [Group A] [Group B]
    (U : Subgroup A) (V : Subgroup B) :
    normalizer (U.prod V : Set (A × B)) =
      (normalizer (U : Set A)).prod (normalizer (V : Set B)) := by
  ext g
  constructor
  · intro h
    constructor
    · apply mem_normalizer_iff.mpr
      intro x
      have he := mem_normalizer_iff.mp h (x, 1)
      simpa only [Prod.mul_def, Prod.fst_inv, Prod.snd_inv, mul_one, mul_inv_cancel,
        mem_prod, one_mem, and_true] using he
    · apply mem_normalizer_iff.mpr
      intro x
      have he := mem_normalizer_iff.mp h (1, x)
      simpa only [Prod.mul_def, Prod.fst_inv, Prod.snd_inv, mul_one, mul_inv_cancel,
        mem_prod, one_mem, true_and] using he
  · rintro ⟨hU, hV⟩
    apply mem_normalizer_iff.mpr
    intro x
    exact and_congr (mem_normalizer_iff.mp hU x.1) (mem_normalizer_iff.mp hV x.2)

variable {L S : Subgroup G} {F : Type*} [Field F] [CharP F 2]

theorem Coordinates.borel_preimage (a : Coordinates L S F) :
    ((borel F).prod (borel F)).comap a.quotient =
      (canonicalBorel L S).subgroupOf L := by
  have he := comap_normalizer_eq_of_surjective ((kernel F).prod (kernel F)) a.onto
  rw [normalizer_prod, normalizer_kernel, a.root_preimage] at he
  rw [he]
  have hs : S.subgroupOf L = (S ⊓ L).subgroupOf L := by
    ext x
    exact (and_iff_left x.property).symm
  rw [hs, ← subgroupOf_normalizer_eq (show S ⊓ L ≤ L from inf_le_right)]
  ext x
  exact (and_iff_right x.property).symm

def Coordinates.borelMap (a : Coordinates L S F) :
    canonicalBorel L S →* (borel F × borel F) where
  toFun x :=
    let y : L := ⟨x, x.property.1⟩
    let hy : a.quotient y ∈ (borel F).prod (borel F) :=
      a.borel_preimage.ge (show y ∈ (canonicalBorel L S).subgroupOf L from x.property)
    (⟨(a.quotient y).1, hy.1⟩, ⟨(a.quotient y).2, hy.2⟩)
  map_one' := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst a.quotient.map_one
    · exact congrArg Prod.snd a.quotient.map_one
  map_mul' x y := by
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg Prod.fst (a.quotient.map_mul ⟨x, x.property.1⟩ ⟨y, y.property.1⟩)
    · exact congrArg Prod.snd (a.quotient.map_mul ⟨x, x.property.1⟩ ⟨y, y.property.1⟩)

theorem Coordinates.borelMap_surjective (a : Coordinates L S F) :
    Function.Surjective a.borelMap := by
  rintro ⟨b, c⟩
  obtain ⟨x, hx⟩ := a.onto ((b : PSL(2,F)), (c : PSL(2,F)))
  have hm : x ∈ ((borel F).prod (borel F)).comap a.quotient := by
    change a.quotient x ∈ (borel F).prod (borel F)
    rw [hx]
    exact ⟨b.property, c.property⟩
  rw [a.borel_preimage] at hm
  refine ⟨⟨x, hm⟩, ?_⟩
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hx))
    (Subtype.ext (congrArg Prod.snd hx))

theorem Coordinates.borelMap_kernel_two (a : Coordinates L S F) :
    IsPGroup 2 a.borelMap.ker := by
  let f : a.borelMap.ker →* a.quotient.ker :=
    { toFun := fun x => ⟨⟨x.val, x.val.property.1⟩, by
        have hx := x.property
        exact Prod.ext
          (congrArg (fun z : borel F × borel F => (z.1 : PSL(2,F))) hx)
          (congrArg (fun z : borel F × borel F => (z.2 : PSL(2,F))) hx)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply a.kernel_two.of_injective f
  intro x y hxy
  exact Subtype.ext (Subtype.ext
    (congrArg (fun z : a.quotient.ker => (z.val : G)) hxy))

theorem Coordinates.borelMap_kernel_eq (a : Coordinates L S F) :
    a.borelMap.ker = (pCore 2 L).comap
      (inclusion (show canonicalBorel L S ≤ L from inf_le_left)) := by
  rw [← a.kernel_eq]
  ext x
  change a.borelMap x = 1 ↔ a.quotient ⟨x, x.property.1⟩ = 1
  constructor
  · intro hx
    exact Prod.ext
      (congrArg (fun z : borel F × borel F => (z.1 : PSL(2,F))) hx)
      (congrArg (fun z : borel F × borel F => (z.2 : PSL(2,F))) hx)
  · intro hx
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hx))
      (Subtype.ext (congrArg Prod.snd hx))

noncomputable def Coordinates.borelQuotientEquiv (a : Coordinates L S F) :
    canonicalBorel L S ⧸ a.borelMap.ker ≃* (borel F × borel F) :=
  QuotientGroup.quotientKerEquivOfSurjective a.borelMap a.borelMap_surjective

variable [Finite G] [Finite F]

private theorem matrix_borel_solvable {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Group.IsSolvable (borel F) := by
  let : Group.IsNilpotent (pCore 2 (borel F)) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (borel F ⧸ pCore 2 (borel F)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (quotientTorusEquiv F hF).toMonoidHom) (quotientTorusEquiv F hF).injective
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (borel F))).mpr
    ⟨inferInstance, inferInstance⟩

theorem Coordinates.borel_solvable (a : Coordinates L S F)
    {n : ℕ} (hF : Nat.card F = 2 ^ n) : Group.IsSolvable (canonicalBorel L S) := by
  let := matrix_borel_solvable hF
  let : Group.IsNilpotent a.borelMap.ker := a.borelMap_kernel_two.isNilpotent
  exact Group.isSolvable_of_ker_le_range a.borelMap.ker.subtype a.borelMap
    (by rw [range_subtype])

theorem Coordinates.borel_even_and_rank (a : Coordinates L S F)
    {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hthree : 3 ∣ Nat.card (canonicalBorel L S)) :
    Even n ∧ 1 < primeRank 3 (canonicalBorel L S) := by
  have hk : Nat.Coprime 3 (Nat.card a.borelMap.ker) := by
    obtain ⟨k, hk⟩ := a.borelMap_kernel_two.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right k).coprime_dvd_right hk
  have hd : 3 ∣ Nat.card (borel F) := by
    rw [card_eq_card_quotient_mul_card_subgroup a.borelMap.ker,
      Nat.card_congr a.borelQuotientEquiv.toEquiv, Nat.card_prod] at hthree
    have hp := (Nat.prime_three.dvd_mul.mp hthree).resolve_right
      (Nat.prime_three.coprime_iff_not_dvd.mp hk)
    exact (Nat.prime_three.dvd_mul.mp hp).elim id id
  have he : Even n := by
    by_contra hn
    have ho : Odd n := Nat.not_even_iff_odd.mp hn
    exact (Nat.prime_three.coprime_iff_not_dvd.mp (borel_threePrime_of_odd F hF ho)) hd
  have hr : 1 ≤ primeRank 3 (borel F) := by
    have hn : primeRank 3 (borel F) ≠ 0 := fun hz =>
      (PrimeRank.eq_zero_iff_not_dvd_card.mp hz) hd
    omega
  have hb := primeRank_le_of_surjective_of_coprime
    3 a.borelMap a.borelMap_surjective hk
  rw [primeRank_prod_eq_add] at hb
  exact ⟨he, by omega⟩

omit [CharP F 2] [Finite F] [Finite G] in
theorem canonicalBorel_le (L S : Subgroup G) : canonicalBorel L S ≤ L := inf_le_left

omit [CharP F 2] [Finite F] [Finite G] in
theorem sylow_intersection_le_canonicalBorel (L S : Subgroup G) :
    S ⊓ L ≤ canonicalBorel L S := le_inf inf_le_right (S ⊓ L).le_normalizer

omit [CharP F 2] [Finite F] [Finite G] in
theorem sylow_normalizes_orbit_root (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) :
    d.S ≤ normalizer (d.S ⊓ localSpan c.L d.S : Set G) :=
  (le_inf d.S.le_normalizer (le_normalizer_conjugateSpanBy c.L d.S)).trans
    inf_normalizer_le_normalizer_inf

omit [CharP F 2] [Finite F] [Finite G] in
theorem canonicalBorel_normalized {A : Subgroup G}
    (hL : A ≤ normalizer (L : Set G))
    (hU : A ≤ normalizer (S ⊓ L : Set G)) :
    A ≤ normalizer (canonicalBorel L S : Set G) :=
  (le_inf hL (hU.trans (normalizer (S ⊓ L : Set G)).le_normalizer)).trans
    inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearTwo
