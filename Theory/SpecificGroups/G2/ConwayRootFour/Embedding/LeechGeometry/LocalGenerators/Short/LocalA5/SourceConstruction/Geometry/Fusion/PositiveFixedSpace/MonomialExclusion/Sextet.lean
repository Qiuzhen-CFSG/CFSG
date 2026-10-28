module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.MonomialReduction

/-!
# The Golay sextet forced by equal quaternion kernels

The three negative-square relations make the two inverse coordinate permutations
commuting fixed-point-free involutions whose product is fixed-point-free. Their
orbits are therefore six tetrads.

For two different orbits, take the lattice vector with coordinate four on one
pair from each orbit. Its displacement under the first quaternion generator is
twice a Leech vector. Equality of the binary kernels gives the same divisibility
for the second generator. Half of this second displacement has coordinates
±2 on precisely the union of the two orbits. The literal Leech congruences then
put that union in the Golay code, so it is an octad. This proves the sextet
property, rather than assuming it from the orbit sizes.

The final interfaces describe the standard-sextet calculation still needed for
the dimension exclusion. They retain `ScalarOrigin`, including centralization
of the whole scalar A₄. `quaternionParts_conjugate` is consumed by the parent
module to reduce the original exclusion to this standard case.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5,
pp.283–284, Lemma 47.2, p.261, and the root-four conventions on p.269.
This coordinate reduction uses the existing attributed ATLAS Golay and Leech
models; no additional ATLAS source is copied here.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped BigOperators
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion


/-- The inverse coordinate permutation, matching `monomialEmbedding_apply`. -/
abbrev monomialPull (a : GolayMonomialGroup) : Equiv.Perm Omega := a.right.val.symm

/-- The quaternion relations induce a free coordinate action of a four-group. -/
theorem monomial_quaternion_parameters (a b : GolayMonomialGroup)
    (ha : (monomialEmbedding a) ^ 2 = negationIsometry)
    (hb : (monomialEmbedding b) ^ 2 = negationIsometry)
    (hab : (monomialEmbedding a * monomialEmbedding b) ^ 2 = negationIsometry) :
    Function.Involutive (monomialPull a) ∧ Function.Involutive (monomialPull b) ∧
    (∀ i, monomialPull a (monomialPull b i) = monomialPull b (monomialPull a i)) ∧
    (∀ i, monomialPull a i ≠ i) ∧ (∀ i, monomialPull b i ≠ i) ∧
    (∀ i, monomialPull a (monomialPull b i) ≠ i) := by
  obtain ⟨hpa, _, hna⟩ := monomial_square_negation_parameters a ha
  obtain ⟨hpb, _, hnb⟩ := monomial_square_negation_parameters b hb
  obtain ⟨hpab, _, hnab⟩ := monomial_square_negation_parameters (a * b) (by rwa [map_mul])
  change ∀ i, monomialPull a (monomialPull a i) = i at hpa
  change ∀ i, monomialPull b (monomialPull b i) = i at hpb
  change ∀ i, monomialPull b (monomialPull a (monomialPull b (monomialPull a i))) = i at hpab
  change ∀ i, monomialPull b (monomialPull a i) ≠ i at hnab
  have hc (i) : monomialPull a (monomialPull b i) = monomialPull b (monomialPull a i) := by
    have h := congrArg (monomialPull b) (hpab (monomialPull a i))
    simpa only [hpa, hpb] using h
  exact ⟨hpa, hpb, hc, hna, hnb, fun i => by rw [hc]; exact hnab i⟩

private def pairFour (i j : Omega) : leech :=
  ⟨coordinateVector i 4 + coordinateVector j 4, coordinate_pair_mem i j⟩

private theorem pair_displacement (a : GolayMonomialGroup)
    (ha : (monomialEmbedding a) ^ 2 = negationIsometry) (i : Omega) :
    ∃ j, (monomialEmbedding a).val (pairFour i (monomialPull a i)) - pairFour i (monomialPull a i) =
      -⟨coordinateVector j 8, coordinate_eight_mem j⟩ := by
  obtain ⟨hp, hs, hn⟩ := monomial_square_negation_parameters a ha
  change ∀ i, monomialPull a (monomialPull a i) = i at hp
  have he (k) : monomialPull a k = i ↔ k = monomialPull a i := by
    constructor
    · intro h; have hh := congrArg (monomialPull a) h; simpa only [hp] using hh
    · rintro rfl; exact hp i
  have he' (k) : monomialPull a k = monomialPull a i ↔ k = i := (monomialPull a).injective.eq_iff
  rcases bit_cases (a.left.toAdd.val i) with hi | hi
  · refine ⟨monomialPull a i, ?_⟩
    apply Subtype.ext; funext k
    simp only [Submodule.coe_sub, Pi.sub_apply, monomialEmbedding_apply, pairFour,
      coordinateVector, Pi.add_apply, Pi.single_apply, Submodule.coe_neg, Pi.neg_apply]
    by_cases hk : k = i
    · subst k; simp [hi, hn i, (hn i).symm]
    · by_cases hk' : k = monomialPull a i
      · subst k
        have hsi := hs i
        rw [hi] at hsi
        simp [hsi, hp i, hn i, (hn i).symm]
      · simp [hk, hk', (he k).not.mpr hk', (he' k).not.mpr hk]
  · refine ⟨i, ?_⟩
    apply Subtype.ext; funext k
    simp only [Submodule.coe_sub, Pi.sub_apply, monomialEmbedding_apply, pairFour,
      coordinateVector, Pi.add_apply, Pi.single_apply, Submodule.coe_neg, Pi.neg_apply]
    by_cases hk : k = i
    · subst k; simp [hi, hn i, (hn i).symm]
    · by_cases hk' : k = monomialPull a i
      · subst k
        have hsi := hs i
        rw [hi] at hsi
        have hsi' : a.left.toAdd.val (monomialPull a i) = 0 := by simpa using hsi
        simp [hsi', hp i, hn i, (hn i).symm]
      · simp [hk, hk', (he k).not.mpr hk', (he' k).not.mpr hk]

private theorem pair_sum_fixed (a : GolayMonomialGroup)
    (ha : (monomialEmbedding a) ^ 2 = negationIsometry) (i j : Omega) :
    leechReduction (pairFour i (monomialPull a i) + pairFour j (monomialPull a j)) ∈
      binaryFixed (monomialEmbedding a) := by
  obtain ⟨k, hk⟩ := pair_displacement a ha i
  obtain ⟨l, hl⟩ := pair_displacement a ha j
  change leechModTwoRepresentation (monomialEmbedding a) _ - _ = 0
  simp only [LinearMap.id_apply]
  rw [leechModTwoRepresentation_reduce, ← map_sub, leechReduction_eq_zero]
  refine ⟨-pairFour k l, ?_⟩
  have hd : (monomialEmbedding a).val (pairFour i (monomialPull a i) + pairFour j (monomialPull a j)) -
      (pairFour i (monomialPull a i) + pairFour j (monomialPull a j)) =
      -⟨coordinateVector k 8, coordinate_eight_mem k⟩ -
      ⟨coordinateVector l 8, coordinate_eight_mem l⟩ := by
    rw [map_add, add_sub_add_comm, hk, hl]; rfl
  rw [hd]
  apply Subtype.ext; funext z
  change 2 * -(coordinateVector k 4 z + coordinateVector l 4 z) =
    -coordinateVector k 8 z - coordinateVector l 8 z
  simp only [coordinateVector, Pi.single_apply]
  split_ifs <;> norm_num

private theorem fixed_four_support (b : GolayMonomialGroup)
    (hb : Function.Involutive (monomialPull b)) (S : Finset Omega)
    (hd : Disjoint S (S.image (monomialPull b))) (x : leech)
    (hx : ∀ k, x.val k = if k ∈ S then 4 else 0)
    (hf : leechReduction x ∈ binaryFixed (monomialEmbedding b)) :
    ∃ c : golay, support c.val = S ∪ S.image (monomialPull b) := by
  change ∀ i, monomialPull b (monomialPull b i) = i at hb
  have hz : leechReduction ((monomialEmbedding b).val x - x) = 0 := by
    rw [map_sub, ← leechModTwoRepresentation_reduce]
    exact hf
  obtain ⟨y, hy⟩ := (leechReduction_eq_zero _).mp hz
  have hyc (k) : 2 * y.val k =
      (if b.left.toAdd.val k = 0 then (if monomialPull b k ∈ S then 4 else 0)
       else -(if monomialPull b k ∈ S then 4 else 0)) - (if k ∈ S then 4 else 0) := by
    have h := congrArg (fun v : leech => v.val k) hy
    change 2 * y.val k = ((monomialEmbedding b).val x).val k - x.val k at h
    simpa only [monomialEmbedding_apply, hx] using h
  have hm (k) : k ∈ S.image (monomialPull b) ↔ monomialPull b k ∈ S := by
    constructor
    · rintro h
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp h
      simpa only [hb] using hl
    · intro h
      exact Finset.mem_image.mpr ⟨monomialPull b k, h, hb k⟩
  have heven (k) : y.val k % 2 = 0 := by
    have h := hyc k
    split_ifs at h <;> omega
  obtain ⟨m, _, hpar, hcode, _⟩ := (mem_leech y.val).mp y.property
  have hm0 : m = 0 := (hpar ((0,0),0)).symm.trans (heven _)
  subst m
  refine ⟨⟨halfResidue y.val 0, hcode⟩, ?_⟩
  ext k
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, hm]
  have h := hyc k
  have hdis : ¬ (k ∈ S ∧ monomialPull b k ∈ S) := by
    rintro ⟨hk, hqk⟩
    exact Finset.disjoint_left.mp hd hk ((hm k).mpr hqk)
  change (((y.val k - 0) / 2 : ℤ) : Bit) ≠ 0 ↔ _
  by_cases hk : k ∈ S <;> by_cases hq : monomialPull b k ∈ S <;>
    by_cases hs : b.left.toAdd.val k = 0 <;>
    simp only [hk, hq, hs, if_true, if_false] at h
  all_goals (try exact (hdis ⟨hk,hq⟩).elim)
  all_goals have hv : y.val k = 0 ∨ y.val k = 2 ∨ y.val k = -2 := by omega
  all_goals rcases hv with hv | hv | hv <;> (first | omega | norm_num [hv, hk, hq])

/-- The four coordinates in the orbit of two commuting involutions. -/
def quaternionTetrad (p q : Equiv.Perm Omega) (i : Omega) : Finset Omega :=
  {i, p i, q i, p (q i)}

section Orbits
variable (p q : Equiv.Perm Omega)
  (hp : ∀ i, p (p i) = i) (hq : ∀ i, q (q i) = i)
  (hc : ∀ i, p (q i) = q (p i))
  (hnp : ∀ i, p i ≠ i) (hnq : ∀ i, q i ≠ i) (hnpq : ∀ i, p (q i) ≠ i)

include hp hnp hnq hnpq in
theorem quaternionTetrad_card (i : Omega) : (quaternionTetrad p q i).card = 4 := by
  have h1 : p i ≠ q i := by
    intro h
    exact hnpq i ((congrArg p h).symm.trans (hp i))
  have h2 : p i ≠ p (q i) := fun h => hnq i ((p.injective h).symm)
  apply Finset.card_eq_four.mpr
  exact ⟨i, p i, q i, p (q i), (hnp i).symm, (hnq i).symm,
    (hnpq i).symm, h1, h2, (hnp (q i)).symm, rfl⟩

include hp hc in
private theorem tetrad_at_p (i : Omega) :
     quaternionTetrad p q (p i) = quaternionTetrad p q i := by
  ext k
  simp only [quaternionTetrad, hp, ← hc, Finset.mem_insert, Finset.mem_singleton]
  tauto

include hq in
private theorem tetrad_at_q (i : Omega) :
     quaternionTetrad p q (q i) = quaternionTetrad p q i := by
  ext k
  simp only [quaternionTetrad, hq, Finset.mem_insert, Finset.mem_singleton]
  tauto

include hp hq hc in
theorem quaternionTetrad_eq_of_mem {i j : Omega} (h : j ∈ quaternionTetrad p q i) :
     quaternionTetrad p q j = quaternionTetrad p q i := by
  simp only [quaternionTetrad, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl
  · rfl
  · exact tetrad_at_p p q hp hc i
  · exact tetrad_at_q p q hq i
  · rw [tetrad_at_p p q hp hc, tetrad_at_q p q hq]

include hp hq hc in
theorem quaternionTetrad_disjoint {i j : Omega}
     (h : quaternionTetrad p q i ≠ quaternionTetrad p q j) :
     Disjoint (quaternionTetrad p q i) (quaternionTetrad p q j) := by
  apply Finset.disjoint_left.mpr
  intro k hki hkj
  exact h ((quaternionTetrad_eq_of_mem p q hp hq hc hki).symm.trans
    (quaternionTetrad_eq_of_mem p q hp hq hc hkj))

include hp hc hnq hnpq in
private theorem pair_halves_disjoint (i : Omega) :
    Disjoint ({i, p i} : Finset Omega) (({i, p i} : Finset Omega).image q) := by
  have h1 : p i ≠ q i := by
    intro h
    exact hnpq i ((congrArg p h).symm.trans (hp i))
  simp [Finset.image_insert, Finset.image_singleton, ← hc, hnq i, hnpq i, h1, ne_comm]

include hc in
private theorem pair_halves_cover (i : Omega) :
    ({i, p i} : Finset Omega) ∪ ({i, p i} : Finset Omega).image q =
      quaternionTetrad p q i := by
  ext k
  simp only [Finset.image_insert, Finset.image_singleton, ← hc,
    quaternionTetrad, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

include hp hq hc hnq hnpq in
private theorem pair_union_disjoint {i j : Omega}
    (hne : quaternionTetrad p q i ≠ quaternionTetrad p q j) :
    Disjoint (({i, p i} : Finset Omega) ∪ {j, p j})
      ((({i, p i} : Finset Omega) ∪ {j, p j}).image q) := by
  have hd := quaternionTetrad_disjoint p q hp hq hc hne
  have hi := pair_halves_cover p q hc i
  have hj := pair_halves_cover p q hc j
  rw [← hi, ← hj] at hd
  rw [Finset.disjoint_union_left, Finset.disjoint_union_right,
    Finset.disjoint_union_right] at hd
  rw [Finset.image_union, Finset.disjoint_union_left,
    Finset.disjoint_union_right, Finset.disjoint_union_right]
  exact ⟨⟨pair_halves_disjoint p q hp hc hnq hnpq i, hd.1.2⟩,
    ⟨hd.2.1.symm, pair_halves_disjoint p q hp hc hnq hnpq j⟩⟩

end Orbits

/-- Equal binary kernels force the union of two coordinate orbits to be a Golay octad. -/
theorem quaternion_pair_octad (a b : GolayMonomialGroup)
    (ha : (monomialEmbedding a) ^ 2 = negationIsometry)
    (hb : (monomialEmbedding b) ^ 2 = negationIsometry)
    (hab : (monomialEmbedding a * monomialEmbedding b) ^ 2 = negationIsometry)
    (heq : binaryFixed (monomialEmbedding a) = binaryFixed (monomialEmbedding b))
    (i j : Omega)
    (hne : quaternionTetrad (monomialPull a) (monomialPull b) i ≠ quaternionTetrad (monomialPull a) (monomialPull b) j) :
    quaternionTetrad (monomialPull a) (monomialPull b) i ∪ quaternionTetrad (monomialPull a) (monomialPull b) j ∈ octads := by
  obtain ⟨hp, hq, hc, hnp, hnq, hnpq⟩ := monomial_quaternion_parameters a b ha hb hab
  change ∀ i, monomialPull a (monomialPull a i) = i at hp
  change ∀ i, monomialPull b (monomialPull b i) = i at hq
  let S := ({i, monomialPull a i} : Finset Omega) ∪ {j, monomialPull a j}
  let x := pairFour i (monomialPull a i) + pairFour j (monomialPull a j)
  have hd := quaternionTetrad_disjoint (monomialPull a) (monomialPull b) hp hq hc hne
  have hs : Disjoint ({i, monomialPull a i} : Finset Omega) {j, monomialPull a j} := by
    apply hd.mono
    · intro k hk; simp only [quaternionTetrad, Finset.mem_insert, Finset.mem_singleton] at *; tauto
    · intro k hk; simp only [quaternionTetrad, Finset.mem_insert, Finset.mem_singleton] at *; tauto
  have hpair (l k : Omega) : (pairFour l (monomialPull a l)).val k =
      if k ∈ ({l, monomialPull a l} : Finset Omega) then 4 else 0 := by
    have hn := hnp l
    simp only [pairFour, Pi.add_apply, coordinateVector, Pi.single_apply,
      Finset.mem_insert, Finset.mem_singleton]
    by_cases hl : k = l <;> by_cases hp : k = monomialPull a l <;> simp_all
  have hx (k) : x.val k = if k ∈ S then 4 else 0 := by
    change (pairFour i (monomialPull a i)).val k + (pairFour j (monomialPull a j)).val k = _
    rw [hpair, hpair]
    simp only [S, Finset.mem_union]
    by_cases hi : k ∈ ({i, monomialPull a i} : Finset Omega)
    · have hj := Finset.disjoint_left.mp hs hi
      simp only [hi, hj, true_or, if_true, if_false, add_zero]
    · by_cases hj : k ∈ ({j, monomialPull a j} : Finset Omega) <;> simp [hi, hj]
  have hf : leechReduction x ∈ binaryFixed (monomialEmbedding b) :=
    heq ▸ pair_sum_fixed a ha i j
  obtain ⟨c, hcS⟩ := fixed_four_support b hq S
    (pair_union_disjoint (monomialPull a) (monomialPull b) hp hq hc hnq hnpq hne) x hx hf
  have hS : S ∪ S.image (monomialPull b) =
      quaternionTetrad (monomialPull a) (monomialPull b) i ∪ quaternionTetrad (monomialPull a) (monomialPull b) j := by
    ext k
    simp only [S, Finset.image_union, Finset.image_insert, Finset.image_singleton,
      ← hc, quaternionTetrad, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [hS] at hcS
  apply (octads_mem _).mpr
  refine ⟨c, ?_, hcS⟩
  change (support c.val).card = 8
  rw [hcS, Finset.card_union_of_disjoint hd,
    quaternionTetrad_card (monomialPull a) (monomialPull b) hp hnp hnq hnpq,
    quaternionTetrad_card (monomialPull a) (monomialPull b) hp hnp hnq hnpq]

/-- The coordinate-orbit partition of the two monomial quaternion generators. -/
def quaternionParts (a b : GolayMonomialGroup) : Finset (Finset Omega) :=
  Finset.univ.image (quaternionTetrad (monomialPull a) (monomialPull b))

/-- The six quaternion coordinate orbits form an actual Golay sextet. -/
theorem quaternion_sextet (a b : GolayMonomialGroup)
    (ha : (monomialEmbedding a) ^ 2 = negationIsometry)
    (hb : (monomialEmbedding b) ^ 2 = negationIsometry)
    (hab : (monomialEmbedding a * monomialEmbedding b) ^ 2 = negationIsometry)
    (heq : binaryFixed (monomialEmbedding a) = binaryFixed (monomialEmbedding b)) :
    IsUnorderedSextet (quaternionParts a b) := by
  obtain ⟨hp, hq, hc, hnp, hnq, hnpq⟩ := monomial_quaternion_parameters a b ha hb hab
  change ∀ i, monomialPull a (monomialPull a i) = i at hp
  change ∀ i, monomialPull b (monomialPull b i) = i at hq
  have hcard (T : Finset Omega) (hT : T ∈ quaternionParts a b) : T.card = 4 := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hT
    exact quaternionTetrad_card (monomialPull a) (monomialPull b) hp hnp hnq hnpq i
  have hmem (i : Omega) : quaternionTetrad (monomialPull a) (monomialPull b) i ∈ quaternionParts a b :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hpart (i : Omega) : ∃! T, T ∈ quaternionParts a b ∧ i ∈ T := by
    refine ⟨quaternionTetrad (monomialPull a) (monomialPull b) i,
      ⟨hmem i, by simp [quaternionTetrad]⟩, ?_⟩
    rintro T ⟨hT, hi⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hT
    exact (quaternionTetrad_eq_of_mem (monomialPull a) (monomialPull b) hp hq hc hi).symm
  have hdis : (quaternionParts a b : Set (Finset Omega)).PairwiseDisjoint id := by
    intro T hT R hR hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hR
    exact quaternionTetrad_disjoint (monomialPull a) (monomialPull b) hp hq hc hne
  have hcover : (quaternionParts a b).biUnion id = Finset.univ := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, iff_true, id_eq]
    obtain ⟨T, hT, _⟩ := hpart i
    exact ⟨T, hT⟩
  refine ⟨?_, hcard, hpart, ?_⟩
  · have hn := Finset.card_biUnion hdis
    rw [hcover] at hn
    have hs : (∑ T ∈ quaternionParts a b, T.card) = (quaternionParts a b).card * 4 := by
      rw [Finset.sum_congr rfl (fun T hT => hcard T hT), Finset.sum_const, smul_eq_mul]
    change (Finset.univ : Finset Omega).card = (∑ T ∈ quaternionParts a b, T.card) at hn
    rw [hs] at hn
    have ho : (Finset.univ : Finset Omega).card = 24 := by decide
    omega
  · intro T hT R hR hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hR
    exact quaternion_pair_octad a b ha hb hab heq i j hne

private theorem pull_conjugate (r a : GolayMonomialGroup) (k : Omega) :
    monomialPull (r * a * r⁻¹) k = r.right.val (monomialPull a (r.right.val.symm k)) := rfl

/-- Monomial conjugation transports the actual orbit partition by its coordinate permutation. -/
theorem quaternionParts_conjugate (r a b : GolayMonomialGroup) :
    quaternionParts (r * a * r⁻¹) (r * b * r⁻¹) =
      permuteSextetParts r.right.val (quaternionParts a b) := by
  have hT (i : Omega) : quaternionTetrad (monomialPull (r * a * r⁻¹)) (monomialPull (r * b * r⁻¹)) (r.right.val i) =
      (quaternionTetrad (monomialPull a) (monomialPull b) i).image r.right.val := by
    simp only [quaternionTetrad, pull_conjugate, Equiv.symm_apply_apply,
      Finset.image_insert, Finset.image_singleton]
  ext T
  constructor
  · intro hTmem
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hTmem
    obtain ⟨j, rfl⟩ := r.right.val.surjective i
    apply Finset.mem_image.mpr
    refine ⟨quaternionTetrad (monomialPull a) (monomialPull b) j,
      Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, ?_⟩
    exact (hT j).symm
  · intro hmem
    obtain ⟨R, hR, hRT⟩ := Finset.mem_image.mp hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hR
    subst R
    exact Finset.mem_image.mpr ⟨r.right.val i, Finset.mem_univ _, (hT i).trans hRT⟩

theorem quaternionTetrad_eq_standard (a b : GolayMonomialGroup)
    (hstd : quaternionParts a b = distinguishedUnorderedSextet.val) (i : Omega) :
    quaternionTetrad (monomialPull a) (monomialPull b) i = tetrad i.1 := by
  have hmem : quaternionTetrad (monomialPull a) (monomialPull b) i ∈ distinguishedUnorderedSextet.val := by
    rw [← hstd]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
  have hi : i ∈ tetrad j := by rw [hj]; simp [quaternionTetrad]
  exact hj.symm.trans (congrArg tetrad ((mem_tetrad i j).mp hi).symm)

theorem standard_quaternion_coordinate_columns (a b : GolayMonomialGroup)
    (hstd : quaternionParts a b = distinguishedUnorderedSextet.val) (i : Omega) :
    (monomialPull a i).1 = i.1 ∧ (monomialPull b i).1 = i.1 := by
  have hi := quaternionTetrad_eq_standard a b hstd i
  have ha : monomialPull a i ∈ quaternionTetrad (monomialPull a) (monomialPull b) i := by simp [quaternionTetrad]
  have hb : monomialPull b i ∈ quaternionTetrad (monomialPull a) (monomialPull b) i := by simp [quaternionTetrad]
  rw [hi, mem_tetrad] at ha hb
  exact ⟨ha, hb⟩

theorem quaternionParts_preserved (a b m : GolayMonomialGroup)
    (hma : Commute (monomialEmbedding m) (monomialEmbedding a))
    (hmb : Commute (monomialEmbedding m) (monomialEmbedding b)) :
    permuteSextetParts m.right.val (quaternionParts a b) = quaternionParts a b := by
  have ha : m * a = a * m := monomialEmbedding_injective (by
    simpa only [map_mul] using hma.eq)
  have hb : m * b = b * m := monomialEmbedding_injective (by
    simpa only [map_mul] using hmb.eq)
  rw [← quaternionParts_conjugate, ha, hb, mul_inv_cancel_right, mul_inv_cancel_right]

/-- The commuting third element has its coordinate permutation in the literal sextet stabilizer. -/
theorem standard_commuting_coordinate_stabilizer (a b m : GolayMonomialGroup)
    (hstd : quaternionParts a b = distinguishedUnorderedSextet.val)
    (hma : Commute (monomialEmbedding m) (monomialEmbedding a))
    (hmb : Commute (monomialEmbedding m) (monomialEmbedding b)) :
    m.right ∈ sextetStabilizer := by
  apply Subtype.ext
  change permuteSextetParts m.right.val distinguishedUnorderedSextet.val =
    distinguishedUnorderedSextet.val
  rw [← hstd]
  exact quaternionParts_preserved a b m hma hmb

/-- The remaining calculation, with the six quaternion orbits equal to the
six literal tetrads of the Golay encoder. All original scalar data remain. -/
def StandardQuaternionExclusion : Prop :=
  ∀ a b m : GolayMonomialGroup,
    quaternionParts a b = distinguishedUnorderedSextet.val →
    (monomialEmbedding a) ^ 2 = negationIsometry →
    (monomialEmbedding b) ^ 2 = negationIsometry →
    (monomialEmbedding a * monomialEmbedding b) ^ 2 = negationIsometry →
    (monomialEmbedding m) ^ 2 = 1 →
    Commute (monomialEmbedding m) (monomialEmbedding a) →
    Commute (monomialEmbedding m) (monomialEmbedding b) →
    binaryFixed (monomialEmbedding a) = binaryFixed (monomialEmbedding b) →
    ScalarOrigin a b m →
    Module.finrank Bit ↥(binaryFixed (monomialEmbedding a) ⊓
      binaryFixed (monomialEmbedding m)) ≠ 6

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion
