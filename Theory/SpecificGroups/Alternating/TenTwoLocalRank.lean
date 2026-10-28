module

public import Theory.GroupTheory.PrimeRankWitness
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# A four-group in A₁₀ whose normalizer has 3-rank at least three

Embed the usual normal Klein four subgroup of A₄ on the letters 0, 1, 2, 3.
The disjoint block action of A₄ × C₃ × C₃ on 4 + 3 + 3 letters is faithful
and normalizes this four-group. Its three-cycles (0 1 2), (4 5 6), (7 8 9)
generate an elementary abelian subgroup of order 27 in the actual A₁₀
normalizer. The elementary-abelian embedding bound then gives 3-rank ≥ 3.

This explicit two-local calculation uses no simplicity, order or recognition
hypothesis on A₁₀. The public existential theorem supplies the obstruction
needed to exclude the A₁₀ alternative in a quasithin recognition argument.

Sources: the standard normal four-group of A₄, formalized in
`Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour`, and the elementary
rank bound in `Theory.GroupTheory.PrimeRankWitness`. The permutation formulas
are proved directly below; finite checks range over the three cyclic
coordinates and ten letters, never over all permutations of ten letters.
-/

namespace alternatingGroup.TenTwoLocalRank

private abbrev C := Multiplicative (ZMod 3)
private abbrev H := alternatingGroup (Fin 4) × (C × C)
private abbrev E := C × (C × C)

private def cycle3 : C →* Equiv.Perm (Fin 3) where
  toFun a := (Equiv.swap 0 1 * Equiv.swap 1 2) ^ a.toAdd.val
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem cycle3_injective : Function.Injective cycle3 := by decide +kernel

private def cycle4 : C →* alternatingGroup (Fin 4) where
  toFun a := ⟨(Equiv.swap 0 1 * Equiv.swap 1 2) ^ a.toAdd.val, by
    rw [Equiv.Perm.mem_alternatingGroup]
    have : ∀ b : C, Equiv.Perm.sign
        ((Equiv.swap 0 1 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) ^ b.toAdd.val) = 1 :=
      by decide +kernel
    exact this a⟩
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private theorem cycle4_injective : Function.Injective cycle4 := by decide +kernel

private def points : (Fin 4 ⊕ (Fin 3 ⊕ Fin 3)) ≃ Fin 10 :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

private def blockPerm : H →* Equiv.Perm (Fin 4 ⊕ (Fin 3 ⊕ Fin 3)) :=
  (Equiv.Perm.sumCongrHom _ _).comp
    ((alternatingGroup (Fin 4)).subtype.prodMap
      ((Equiv.Perm.sumCongrHom _ _).comp (cycle3.prodMap cycle3)))

private def embedding : H →* alternatingGroup (Fin 10) :=
  ((points.permCongrHom.toMonoidHom).comp blockPerm).codRestrict _ (by
    intro a
    rw [Equiv.Perm.mem_alternatingGroup]
    change Equiv.Perm.sign (points.permCongr (blockPerm a)) = 1
    rw [Equiv.Perm.sign_permCongr]
    change Equiv.Perm.sign (Equiv.sumCongr a.1.val
      (Equiv.sumCongr (cycle3 a.2.1) (cycle3 a.2.2))) = 1
    rw [Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_sumCongr,
      Equiv.Perm.mem_alternatingGroup.mp a.1.property]
    have hc : ∀ b : C, Equiv.Perm.sign (cycle3 b) = 1 := by decide +kernel
    rw [hc, hc, one_mul, one_mul])

private theorem embedding_injective : Function.Injective embedding := by
  intro a b hab
  have h := points.permCongrHom.injective (congrArg Subtype.val hab)
  have h' := Equiv.Perm.sumCongrHom_injective h
  change (a.1.val, Equiv.sumCongr (cycle3 a.2.1) (cycle3 a.2.2)) =
    (b.1.val, Equiv.sumCongr (cycle3 b.2.1) (cycle3 b.2.2)) at h'
  have hs : (Equiv.Perm.sumCongrHom (Fin 3) (Fin 3))
      (cycle3 a.2.1, cycle3 a.2.2) =
      (Equiv.Perm.sumCongrHom (Fin 3) (Fin 3)) (cycle3 b.2.1, cycle3 b.2.2) :=
    congrArg Prod.snd h'
  have h'' := Equiv.Perm.sumCongrHom_injective hs
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h'))
    (Prod.ext (cycle3_injective (congrArg Prod.fst h''))
      (cycle3_injective (congrArg Prod.snd h'')))

/-- Extend an even permutation of the first four letters by the identity. -/
public def firstFour : alternatingGroup (Fin 4) →* alternatingGroup (Fin 10) :=
  embedding.comp (MonoidHom.inl _ _)

public theorem firstFour_injective : Function.Injective firstFour := by
  intro a b h
  exact congrArg Prod.fst (embedding_injective h)

public theorem firstFour_apply_first (a : alternatingGroup (Fin 4)) (i : Fin 4) :
    (firstFour a : Equiv.Perm (Fin 10)) (Fin.castAdd 6 i) = Fin.castAdd 6 (a.val i) := by
  change points (blockPerm (a, 1) (points.symm (points (Sum.inl i)))) = _
  rw [points.symm_apply_apply]
  rfl

public theorem firstFour_apply_last (a : alternatingGroup (Fin 4)) (i : Fin 6) :
    (firstFour a : Equiv.Perm (Fin 10)) (Fin.natAdd 4 i) = Fin.natAdd 4 i := by
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin 6).surjective i
  change points (blockPerm (a, 1) (points.symm (points (Sum.inr j)))) = _
  rw [points.symm_apply_apply]
  cases j <;> rfl

private def Q : Subgroup H := (alternatingGroup.kleinFour (Fin 4)).prod ⊥
/-- The usual Klein four subgroup on the first four letters of A₁₀. -/
public def R : Subgroup (alternatingGroup (Fin 10)) := Q.map embedding

/-- Identification with the standard four-group under the first-four-letters embedding. -/
public theorem R_eq_map : R = (alternatingGroup.kleinFour (Fin 4)).map firstFour := by
  ext x
  constructor
  · rintro ⟨⟨a, b⟩, hab, rfl⟩
    have hb : b = 1 := hab.2
    subst b
    exact ⟨a, hab.1, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(a, 1), ⟨ha, rfl⟩, rfl⟩

public theorem R_card : Nat.card R = 4 := by
  rw [R_eq_map, ← Nat.card_congr
    (Subgroup.equivMapOfInjective _ firstFour firstFour_injective).toEquiv]
  exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)

public theorem R_isKleinFour : IsKleinFour R where
  card_four := R_card
  exponent_two := by
    rw [R_eq_map, ← Monoid.exponent_eq_of_mulEquiv
      (Subgroup.equivMapOfInjective _ firstFour firstFour_injective)]
    exact alternatingGroup.exponent_kleinFour_of_card_eq_four (by simp)

public theorem R_ne_bot : R ≠ ⊥ := by
  intro h
  have hc := R_card
  rw [h, Subgroup.card_bot] at hc
  contradiction

public theorem R_isPGroup : IsPGroup 2 R := IsPGroup.of_card (n := 2) R_card

private theorem embedding_mem_normalizer (a : H) :
    embedding a ∈ Subgroup.normalizer (R : Set (alternatingGroup (Fin 10))) := by
  let : (alternatingGroup.kleinFour (Fin 4)).Normal :=
    alternatingGroup.normal_kleinFour (by simp)
  have : Q.Normal := inferInstanceAs
    ((alternatingGroup.kleinFour (Fin 4)).prod (⊥ : Subgroup (C × C))).Normal
  apply Subgroup.le_normalizer_map embedding
  exact ⟨a, by rw [Q.normalizer_eq_top]; trivial, rfl⟩

private def normalizerEmbedding :
    H →* Subgroup.normalizer (R : Set (alternatingGroup (Fin 10))) :=
  embedding.codRestrict _ embedding_mem_normalizer

/-- Three independent cyclic coordinates acting inside the four-group normalizer. -/
public def elementaryEmbedding :
    (Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) →*
      Subgroup.normalizer (R : Set (alternatingGroup (Fin 10))) :=
  normalizerEmbedding.comp (cycle4.prodMap (MonoidHom.id (C × C)))

public theorem elementaryEmbedding_injective : Function.Injective elementaryEmbedding := by
  intro a b h
  have h' := embedding_injective (congrArg Subtype.val h)
  change (cycle4 a.1, a.2) = (cycle4 b.1, b.2) at h'
  exact Prod.ext (cycle4_injective (congrArg Prod.fst h')) (congrArg (fun x : H => x.2) h')

private theorem E_cube (a : E) : a ^ 3 = 1 := by
  have hc (b : C) : b ^ 3 = 1 := by
    change Multiplicative.ofAdd (3 • b.toAdd) = Multiplicative.ofAdd 0
    congr 1
    simp only [nsmul_eq_mul]
    exact zero_mul _
  exact Prod.ext (hc a.1) (Prod.ext (hc a.2.1) (hc a.2.2))

private theorem E_card : Nat.card E = 3 ^ 3 := by
  simp [E, C]

/-- The elementary abelian subgroup of order 27 inside the actual ambient normalizer. -/
public def elementarySubgroup :
    Subgroup (Subgroup.normalizer (R : Set (alternatingGroup (Fin 10)))) :=
  elementaryEmbedding.range

public theorem elementarySubgroup_card : Nat.card elementarySubgroup = 27 := by
  change Nat.card elementaryEmbedding.range = 27
  rw [← Nat.card_congr (MonoidHom.ofInjective elementaryEmbedding_injective).toEquiv]
  exact E_card

public theorem elementarySubgroup_isElementaryAbelian : IsElementaryAbelian 3 elementarySubgroup where
  toIsMulCommutative := inferInstanceAs (IsMulCommutative elementaryEmbedding.range)
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    rintro ⟨x, a, rfl⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, E_cube, map_one]

private def basis : Fin 3 → E :=
  ![(Multiplicative.ofAdd 1, 1, 1), (1, Multiplicative.ofAdd 1, 1),
    (1, 1, Multiplicative.ofAdd 1)]

/-- The three disjoint three-cycles, regarded as elements of A₁₀. -/
public def generators (i : Fin 3) : alternatingGroup (Fin 10) :=
  (elementaryEmbedding (basis i) : alternatingGroup (Fin 10))

public theorem generators_val : ∀ i : Fin 3, (generators i : Equiv.Perm (Fin 10)) =
    ![Equiv.swap 0 1 * Equiv.swap 1 2,
      Equiv.swap 4 5 * Equiv.swap 5 6,
      Equiv.swap 7 8 * Equiv.swap 8 9] i := by decide +kernel

public theorem generators_mem_normalizer (i : Fin 3) :
    generators i ∈ Subgroup.normalizer (R : Set (alternatingGroup (Fin 10))) :=
  (elementaryEmbedding (basis i)).property

public theorem generators_commute (i j : Fin 3) : Commute (generators i) (generators j) := by
  exact ((Commute.all (basis i) (basis j)).map elementaryEmbedding).map
    (Subgroup.normalizer (R : Set (alternatingGroup (Fin 10)))).subtype

public theorem generators_cube (i : Fin 3) : generators i ^ 3 = 1 := by
  change ((Subgroup.normalizer (R : Set (alternatingGroup (Fin 10)))).subtype
    (elementaryEmbedding (basis i))) ^ 3 = 1
  rw [← map_pow, ← map_pow, E_cube, map_one, map_one]

public theorem generators_order (i : Fin 3) : orderOf (generators i) = 3 := by
  apply orderOf_eq_prime (generators_cube i)
  have h : ∀ j : Fin 3, generators j ≠ 1 := by decide +kernel
  exact h i

/-- No nontrivial product of the three cyclic coordinates is the identity. -/
public theorem generators_independent : ∀ a b c : Fin 3,
    generators 0 ^ a.val * generators 1 ^ b.val * generators 2 ^ c.val = 1 →
      a = 0 ∧ b = 0 ∧ c = 0 := by decide +kernel

/-- The normalizer of the explicit nontrivial two-subgroup has 3-rank at least three. -/
public theorem three_le_primeRank_normalizer :
    3 ≤ primeRank 3 (Subgroup.normalizer (R : Set (alternatingGroup (Fin 10)))) :=
  primeRank_ge_of_elementary_embedding E_cube E_card
    elementaryEmbedding elementaryEmbedding_injective

/-- A concrete two-local normalizer in A₁₀ violates the quasithin 3-rank bound. -/
public theorem exists_two_subgroup_normalizer_rank_ge_three :
    ∃ U : Subgroup (alternatingGroup (Fin 10)),
      U ≠ ⊥ ∧ IsPGroup 2 U ∧
        3 ≤ primeRank 3 (Subgroup.normalizer (U : Set (alternatingGroup (Fin 10)))) :=
  ⟨R, R_ne_bot, R_isPGroup, three_le_primeRank_normalizer⟩

end alternatingGroup.TenTwoLocalRank
