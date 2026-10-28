module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal
public import Theory.Mathieu.M24.LocalGeometry.Defs

/-!
# The tetrad class of a native sextet

The union of two different parts of a sextet is a Golay octad. Consequently
all six tetrads have the same class in the native even cocode. Minimum distance
eight makes this class nonzero and shows that intersecting tetrads with equal
classes must coincide. The sextet partition can therefore be recovered from
its class, and its vector stabilizer is precisely the native sextet stabilizer.

The geometric line is contained in the span of pairs within the parts and is
fixed by the entire stabilizer. No dimension or action of the intrinsic
two-core is assumed or asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the discussion
preceding H.15.1 (printed p.398) and the tetrad line in H.15.3(1) (p.400).
The minimum-distance result is reused through the licensed ATLAS port; see
`CocodeLocal.lean` and `LICENSES/ATLAS.txt` for its attribution.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
open scoped Pointwise
namespace MathieuCode
noncomputable section

lemma evenSetVector_equivariant (g : M24) (B : Finset (Fin 24)) (hB : Even B.card) :
    cocodeRepresentation g (evenSetVector B hB) =
      evenSetVector (g • B) (by simpa using hB) := by
  change codeInCore.mkQ (coreRepresentation g
    ⟨wordOfSet B, wordOfSet_mem_core_of_even B hB⟩) = _
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  exact permute_wordOfSet g.val B

lemma evenSetVector_ne_zero_of_card_lt_eight (B : Finset (Fin 24)) (hB : Even B.card)
    (hpos : 0 < B.card) (hlt : B.card < 8) : evenSetVector B hB ≠ 0 := by
  intro hz
  have hm : wordOfSet B ∈ golay :=
    (Submodule.Quotient.mk_eq_zero codeInCore).mp hz
  have hn : wordOfSet B ≠ 0 := by
    intro h
    have hw := wordOfSet_weight B
    rw [h, hammingNorm_zero] at hw
    omega
  have hl := native_golay_minimum hm hn
  rw [wordOfSet_weight] at hl
  omega

lemma sextet_tetrad_even (S : Sextet) {B : Finset (Fin 24)} (hB : B ∈ S.parts) :
    Even B.card := by rw [S.tetrad B hB]; decide

lemma sextet_tetradVector_eq (S : Sextet) {B C : Finset (Fin 24)}
    (hB : B ∈ S.parts) (hC : C ∈ S.parts) :
    evenSetVector B (sextet_tetrad_even S hB) =
      evenSetVector C (sextet_tetrad_even S hC) := by
  by_cases hBC : B = C
  · subst C; rfl
  apply (Submodule.Quotient.eq codeInCore).mpr
  change wordOfSet B - wordOfSet C ∈ golay
  have hd := Finset.disjoint_left.mp (S.disjoint B hB C hC hBC)
  have he : wordOfSet B - wordOfSet C = wordOfSet (B ∪ C) := by
    ext i
    by_cases hi : i ∈ B <;> by_cases hj : i ∈ C
    · exact (hd hi hj).elim
    · simp [wordOfSet, hi, hj]
    · simp [wordOfSet, hi, hj]
    · simp [wordOfSet, hi, hj]
  rw [he, golay_eq_span_octads]
  exact Submodule.subset_span ⟨B ∪ C, S.octad B hB C hC hBC, rfl⟩

lemma sextet_parts_nonempty (S : Sextet) : S.parts.Nonempty := by
  apply Finset.card_pos.mp
  rw [S.card]
  decide

/-- The common cocode class of the six tetrads. -/
def sextetVector (S : Sextet) : Cocode :=
  evenSetVector (sextet_parts_nonempty S).choose
    (sextet_tetrad_even S (sextet_parts_nonempty S).choose_spec)

lemma sextetVector_eq (S : Sextet) {B : Finset (Fin 24)} (hB : B ∈ S.parts) :
    sextetVector S = evenSetVector B (sextet_tetrad_even S hB) :=
  sextet_tetradVector_eq S (sextet_parts_nonempty S).choose_spec hB

lemma sextetVector_ne_zero (S : Sextet) : sextetVector S ≠ 0 := by
  rw [sextetVector_eq S (sextet_parts_nonempty S).choose_spec]
  apply evenSetVector_ne_zero_of_card_lt_eight
  · rw [S.tetrad _ (sextet_parts_nonempty S).choose_spec]; decide
  · rw [S.tetrad _ (sextet_parts_nonempty S).choose_spec]; decide

lemma sextetVector_fixed (S : Sextet) (g : sextetStabilizer S) :
    cocodeRepresentation g.val (sextetVector S) = sextetVector S := by
  obtain ⟨B,hB⟩ := sextet_parts_nonempty S
  have hg : g.val • S.parts = S.parts := g.property
  have hBg : g.val • B ∈ S.parts := hg ▸ Finset.smul_mem_smul_finset hB
  rw [sextetVector_eq S hB, evenSetVector_equivariant]
  exact sextet_tetradVector_eq S hBg hB

/-- The geometric tetrad line; its relation to the two-core fixed space is a theorem. -/
def sextetTetradLine (S : Sextet) : Submodule (ZMod 2) Cocode :=
  Submodule.span (ZMod 2) {sextetVector S}

lemma sextetTetradLine_eq (S : Sextet) {B : Finset (Fin 24)} (hB : B ∈ S.parts) :
    sextetTetradLine S =
      Submodule.span (ZMod 2) {evenSetVector B (sextet_tetrad_even S hB)} := by
  rw [sextetTetradLine, sextetVector_eq S hB]

lemma sextetTetradLine_finrank (S : Sextet) :
    Module.finrank (ZMod 2) (sextetTetradLine S) = 1 :=
  finrank_span_singleton (sextetVector_ne_zero S)

lemma sextetTetradLine_le_fixed (S : Sextet) :
    sextetTetradLine S ≤ fixedSpace cocodeRepresentation (sextetStabilizer S) := by
  apply Submodule.span_le.mpr
  rw [Set.singleton_subset_iff]
  exact sextetVector_fixed S

lemma tetradVector_mem_supportedPairSpace {B : Finset (Fin 24)} (hB : B.card = 4) :
    evenSetVector B (by rw [hB]; decide) ∈ supportedPairSpace B := by
  obtain ⟨a,b,c,d,hab,hac,had,hbc,hbd,hcd,rfl⟩ := Finset.card_eq_four.mp hB
  let P : PointPair := ⟨{a,b}, by simp [hab]⟩
  let Q : PointPair := ⟨{c,d}, by simp [hcd]⟩
  have hp : P.val ⊆ ({a,b,c,d} : Finset (Fin 24)) := by
    intro i hi; simp only [P, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
    tauto
  have hq : Q.val ⊆ ({a,b,c,d} : Finset (Fin 24)) := by
    intro i hi; simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
    tauto
  have he : evenSetVector {a,b,c,d} (by simp [hab,hac,had,hbc,hbd,hcd]; decide) =
      pairVector P + pairVector Q := by
    change codeInCore.mkQ _ = codeInCore.mkQ _ + codeInCore.mkQ _
    rw [← map_add]
    apply congrArg codeInCore.mkQ
    apply Subtype.ext
    ext i
    by_cases ha : i = a
    · subst i; simp [wordOfSet, P, Q, hab, hac, had]
    by_cases hb : i = b
    · subst i; simp [wordOfSet, P, Q, hbc, hbd]
    by_cases hc : i = c
    · subst i; simp [wordOfSet, P, Q, hac.symm, hbc.symm]
    by_cases hd : i = d
    · subst i; simp [wordOfSet, P, Q, had.symm, hbd.symm]
    · simp [wordOfSet, P, Q, ha, hb, hc, hd]
  rw [he]
  exact (supportedPairSpace _).add_mem (pairVector_mem_supportedPairSpace P hp)
    (pairVector_mem_supportedPairSpace Q hq)

lemma supportedPairSpace_map_le (g : M24) (B : Finset (Fin 24)) :
    (supportedPairSpace B).map (cocodeRepresentation g) ≤ supportedPairSpace (g • B) := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro v ⟨P, hP, rfl⟩
  change cocodeRepresentation g (pairVector P) ∈ supportedPairSpace (g • B)
  rw [pairVector_equivariant]
  apply pairVector_mem_supportedPairSpace
  exact Finset.image_mono (fun i : Fin 24 => g • i) hP

/-- Intersecting tetrads cannot represent the same class unless they coincide. -/
lemma tetrad_eq_of_vector_eq_of_inter {B C : Finset (Fin 24)}
    (hB : B.card = 4) (hC : C.card = 4) (hi : (B ∩ C).Nonempty)
    (he : evenSetVector B (by rw [hB]; decide) =
      evenSetVector C (by rw [hC]; decide)) : B = C := by
  have hm : wordOfSet B - wordOfSet C ∈ golay :=
    (Submodule.Quotient.eq codeInCore).mp he
  have hz : wordOfSet B - wordOfSet C = 0 := by
    by_contra hn
    have hl := native_golay_minimum hm hn
    have hu : hammingNorm (wordOfSet B - wordOfSet C) ≤ (B ∪ C).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      by_contra hn
      simp only [Finset.mem_union, not_or] at hn
      simp [wordOfSet, hn.1, hn.2] at hi
    have hc := Finset.card_union_add_card_inter B C
    have hp := Finset.card_pos.mpr hi
    omega
  exact wordOfSet_injective (sub_eq_zero.mp hz)

/-- The vector remembers precisely the six tetrads in the sextet. -/
lemma evenSetVector_eq_sextetVector_iff (S : Sextet) {B : Finset (Fin 24)}
    (hB : B.card = 4) :
    evenSetVector B (by rw [hB]; decide) = sextetVector S ↔ B ∈ S.parts := by
  constructor
  · intro he
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < B.card by omega)
    have hiS : i ∈ S.parts.biUnion id := by rw [S.cover]; exact Finset.mem_univ _
    obtain ⟨C, hC, hiC⟩ := Finset.mem_biUnion.mp hiS
    have hBC : B = C := tetrad_eq_of_vector_eq_of_inter hB (S.tetrad C hC)
      ⟨i, Finset.mem_inter.mpr ⟨hi, hiC⟩⟩ (he.trans (sextetVector_eq S hC))
    exact hBC ▸ hC
  · intro h
    exact (sextetVector_eq S h).symm

lemma sextetVector_injective : Function.Injective sextetVector := by
  intro S T h
  have hparts : S.parts = T.parts := by
    apply Finset.eq_of_subset_of_card_le
    · intro B hB
      apply (evenSetVector_eq_sextetVector_iff T (S.tetrad B hB)).mp
      exact (sextetVector_eq S hB).symm.trans h
    · rw [S.card, T.card]
  cases S
  cases T
  congr

/-- The vector stabilizer is the actual stabilizer of the six-part partition. -/
lemma sextetVector_stabilizer (S : Sextet) :
    cocodeVectorStabilizer cocodeRepresentation (sextetVector S) = sextetStabilizer S := by
  apply le_antisymm
  · intro g hg
    change g • S.parts = S.parts
    apply Finset.eq_of_subset_of_card_le
    · intro C hC
      obtain ⟨B,hB,rfl⟩ := Finset.mem_smul_finset.mp hC
      apply (evenSetVector_eq_sextetVector_iff S (by simpa using S.tetrad B hB)).mp
      rw [← evenSetVector_equivariant g B (sextet_tetrad_even S hB),
        ← sextetVector_eq S hB]
      exact hg
    · simp
  · intro g hg
    exact sextetVector_fixed S ⟨g,hg⟩

/-- A pair and a tetrad cannot differ by a nonzero Golay word. -/
lemma pairVector_ne_sextetVector (S : Sextet) (P : PointPair) :
    pairVector P ≠ sextetVector S := by
  obtain ⟨B,hB⟩ := sextet_parts_nonempty S
  rw [sextetVector_eq S hB]
  intro h
  have hm : wordOfSet P.val - wordOfSet B ∈ golay :=
    (Submodule.Quotient.eq codeInCore).mp h
  have hn : wordOfSet P.val - wordOfSet B ≠ 0 := by
    intro hz
    have he := wordOfSet_injective (sub_eq_zero.mp hz)
    have hc := congrArg Finset.card he
    rw [P.property, S.tetrad B hB] at hc
    omega
  have hl := native_golay_minimum hm hn
  have hu := wordOfSet_sub_weight_le P.val B
  rw [P.property, S.tetrad B hB] at hu
  omega

lemma pairVector_not_mem_sextetTetradLine (S : Sextet) (P : PointPair) :
    pairVector P ∉ sextetTetradLine S := by
  intro h
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp h
  have hc' : c = 0 ∨ c = 1 := by
    fin_cases c
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hc' with rfl | rfl
  · simp only [zero_smul] at hc
    exact pairVector_ne_zero P hc.symm
  · simp only [one_smul] at hc
    exact pairVector_ne_sextetVector S P hc.symm


end
end MathieuCode
