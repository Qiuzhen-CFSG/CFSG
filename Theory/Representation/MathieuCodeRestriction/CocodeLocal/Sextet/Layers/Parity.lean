module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Sextet.Geometry
public import Theory.Representation.MathieuCodeRestriction.Orthogonality

/-!
# Tetrad parity and the top sextet cocode factor

Summing coordinates in each of the six native tetrads maps the even core onto
its six-part even permutation module. Orthogonality of Golay shows that its
image is the constant line; minimum distance excludes a zero image. Thus the
map descends to the native cocode. Its kernel is exactly the span of pairs
within tetrads, by decomposing a word with zero tetrad parity into even words
supported on individual parts. Rank-nullity gives dimension seven.

The induced quotient equivalence respects the actual permutation of the six
parts. The natural six-part action is faithful: a permutation fixing all pair
classes fixes every part, since a difference of two pair words cannot be a
nonzero constant word on six points. Surjectivity of the native part action and
the middle hexacode factor are separate assertions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.3(1),
printed p.400. The argument uses the native Golay orthogonality and the licensed
ATLAS minimum-distance result through `Sextet.Geometry`; see LICENSES/ATLAS.txt.
-/

@[expose] public section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open scoped BigOperators Pointwise
namespace MathieuCode
noncomputable section

abbrev SextetPart (S : Sextet) := {B : Finset (Fin 24) // B ∈ S.parts}

instance sextetPartNonempty (S : Sextet) : Nonempty (SextetPart S) :=
  let h := sextet_parts_nonempty S
  ⟨⟨h.choose, h.choose_spec⟩⟩

lemma card_sextetPart (S : Sextet) : Fintype.card (SextetPart S) = 6 := by
  simpa using S.card

def sextetParity (S : Sextet) : Full →ₗ[ZMod 2] BinaryPermutation.Full (SextetPart S) where
  toFun v B := ∑ i ∈ B.val, v i
  map_add' v w := by ext B; exact Finset.sum_add_distrib
  map_smul' c v := by ext B; exact (Finset.mul_sum _ _ _).symm

lemma sextetPart_nonempty (S : Sextet) (B : SextetPart S) : B.val.Nonempty := by
  apply Finset.card_pos.mp
  rw [S.tetrad _ B.property]
  decide

lemma sextetPart_eq_of_mem (S : Sextet) (B C : SextetPart S) {i : Fin 24}
    (hiB : i ∈ B.val) (hiC : i ∈ C.val) : B = C := by
  by_contra h
  exact Finset.disjoint_left.mp (S.disjoint _ B.property _ C.property
    (fun e => h (Subtype.ext e))) hiB hiC

lemma sextetPart_exists (S : Sextet) (i : Fin 24) : ∃ B : SextetPart S, i ∈ B.val := by
  have hi : i ∈ S.parts.biUnion id := by rw [S.cover]; exact Finset.mem_univ _
  obtain ⟨B,hB,hi⟩ := Finset.mem_biUnion.mp hi
  exact ⟨⟨B,hB⟩,hi⟩

lemma sextetParity_single (S : Sextet) (B : SextetPart S) {i : Fin 24} (hi : i ∈ B.val) :
    sextetParity S (Pi.single i 1) = Pi.single B 1 := by
  ext C
  change (∑ j ∈ C.val, Pi.single i (1 : ZMod 2) j) = (Pi.single B (1 : ZMod 2) : SextetPart S → ZMod 2) C
  by_cases hBC : B = C
  · subst C
    simp [hi]
  · have hn : i ∉ C.val := fun hc => hBC (sextetPart_eq_of_mem S B C hi hc)
    simp [hn, hBC]

lemma sextetParity_surjective (S : Sextet) : Function.Surjective (sextetParity S) := by
  intro v
  let r (B : SextetPart S) := (sextetPart_nonempty S B).choose
  refine ⟨∑ B, v B • Pi.single (r B) 1, ?_⟩
  rw [map_sum]
  have hr (B : SextetPart S) : sextetParity S (Pi.single (r B) 1) = Pi.single B 1 :=
    sextetParity_single S B (sextetPart_nonempty S B).choose_spec
  simp only [map_smul, hr]
  ext B
  simp [Pi.single_apply]

lemma sextetParity_sum (S : Sextet) (v : Full) :
    ∑ B, sextetParity S v B = ∑ i, v i := by
  change (∑ B : SextetPart S, ∑ i ∈ B.val, v i) = _
  rw [show (∑ B : SextetPart S, ∑ i ∈ B.val, v i) =
    ∑ B ∈ S.parts, ∑ i ∈ B, v i from Finset.sum_attach S.parts (fun B => ∑ i ∈ B, v i)]
  rw [← Finset.sum_biUnion (fun B hB C hC hBC => S.disjoint B hB C hC hBC)]
  change (∑ i ∈ S.parts.biUnion id, v i) = _
  rw [S.cover]

lemma sextetParity_core (S : Sextet) {v : Full} (hv : v ∈ Core) :
    sextetParity S v ∈ BinaryPermutation.core (SextetPart S) := by
  rw [BinaryPermutation.mem_core, sextetParity_sum]
  exact hv

lemma dotForm_wordOfSet (B : Finset (Fin 24)) (v : Full) :
    dotForm (wordOfSet B) v = ∑ i ∈ B, v i := by
  simp [dotForm, dotProductBilin, dotProduct, wordOfSet]

lemma sextetParity_golay_constant (S : Sextet) {v : Full} (hv : v ∈ golay)
    (B C : SextetPart S) : sextetParity S v B = sextetParity S v C := by
  have hm : wordOfSet B.val - wordOfSet C.val ∈ golay :=
    (Submodule.Quotient.eq codeInCore).mp (sextet_tetradVector_eq S B.property C.property)
  have he := golay_le_orthogonal hv _ hm
  rw [map_sub, LinearMap.sub_apply, dotForm_wordOfSet, dotForm_wordOfSet] at he
  exact sub_eq_zero.mp he

lemma sextetParity_golay_mem_constants (S : Sextet) {v : Full} (hv : v ∈ golay) :
    sextetParity S v ∈ BinaryPermutation.constants (SextetPart S) := by
  let B : SextetPart S := Classical.choice inferInstance
  apply Submodule.mem_span_singleton.mpr
  refine ⟨sextetParity S v B, ?_⟩
  ext C
  exact (mul_one _).trans (sextetParity_golay_constant S hv B C)

lemma sextetParity_golay_allOne (S : Sextet) :
    ∃ v ∈ golay, sextetParity S v = BinaryPermutation.allOne (SextetPart S) := by
  let B : SextetPart S := Classical.choice inferInstance
  have hn : ∃ v ∈ golay, sextetParity S v B ≠ 0 := by
    by_contra! hn
    have hb : wordOfSet B.val ∈ golay := by
      rw [← golay_orthogonal_eq]
      intro v hv
      rw [dotForm_symmetric.eq, dotForm_wordOfSet]
      exact hn v hv
    have hz : evenSetVector B.val (sextet_tetrad_even S B.property) = 0 :=
      (Submodule.Quotient.mk_eq_zero codeInCore).mpr hb
    exact sextetVector_ne_zero S ((sextetVector_eq S B.property).trans hz)
  obtain ⟨v,hv,hn⟩ := hn
  refine ⟨v,hv,?_⟩
  have he : sextetParity S v B = 1 := by
    generalize hh : sextetParity S v B = h at *
    fin_cases h
    · exact (hn rfl).elim
    · rfl
  ext C
  exact (sextetParity_golay_constant S hv C B).trans he

private def twoPointWord (i j : Fin 24) : Core :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [BinaryPermutation.mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩

private lemma twoPointWord_mem (B : Finset (Fin 24)) {i j : Fin 24}
    (hi : i ∈ B) (hj : j ∈ B) : codeInCore.mkQ (twoPointWord i j) ∈ supportedPairSpace B := by
  by_cases hij : i = j
  · subst j
    have he : twoPointWord i i = 0 := by
      apply Subtype.ext
      ext k
      exact CharTwo.add_self_eq_zero _
    rw [he, map_zero]
    exact Submodule.zero_mem _
  · let P : PointPair := ⟨{i,j}, by simp [hij]⟩
    have he : codeInCore.mkQ (twoPointWord i j) = pairVector P := by
      apply congrArg codeInCore.mkQ
      apply Subtype.ext
      change Pi.single i (1 : ZMod 2) + Pi.single j 1 = wordOfSet {i,j}
      ext k
      by_cases hki : k = i
      · subst k; simp [wordOfSet, hij]
      by_cases hkj : k = j
      · subst k; simp [wordOfSet, Ne.symm hij]
      · simp [wordOfSet, hki, hkj]
    rw [he]
    apply pairVector_mem_supportedPairSpace
    intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hk
    · exact hi
    · exact Finset.mem_singleton.mp hk ▸ hj

lemma supported_evenWord_mem_pairSpace (B : Finset (Fin 24)) (hB : B.Nonempty)
    (v : Core) (hsupp : ∀ i ∉ B, v.val i = 0) :
    codeInCore.mkQ v ∈ supportedPairSpace B := by
  obtain ⟨a,ha⟩ := hB
  have hsum : ∑ i ∈ B, v.val i = 0 := by
    calc
      _ = ∑ i, v.val i := Finset.sum_subset (Finset.subset_univ B) (by simpa using hsupp)
      _ = 0 := v.property
  have he : (∑ i ∈ B, v.val i • twoPointWord i a) = v := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change (∑ i ∈ B, v.val i • (Pi.single i 1 + Pi.single a 1)) = v.val
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hsum, zero_smul, add_zero]
    ext j
    by_cases hj : j ∈ B
    · simp [Finset.sum_apply, Pi.single_apply, hj]
    · simp [Finset.sum_apply, Pi.single_apply, hj, hsupp j hj]
  rw [← he, map_sum]
  apply Submodule.sum_mem
  intro i hi
  rw [map_smul]
  exact Submodule.smul_mem _ _ (twoPointWord_mem B hi ha)

lemma sextetParity_zero_class_mem (S : Sextet) (v : Core)
    (hv : sextetParity S v.val = 0) :
    codeInCore.mkQ v ∈ ⨆ B ∈ S.parts, supportedPairSpace B := by
  let w (B : SextetPart S) : Core :=
    ⟨fun i => if i ∈ B.val then v.val i else 0, by
      change (∑ i, if i ∈ B.val then v.val i else 0) = 0
      simpa [sextetParity] using congrFun hv B⟩
  have he : (∑ B, w B) = v := by
    apply Subtype.ext
    simp only [Submodule.coe_sum]
    ext i
    obtain ⟨B,hB⟩ := sextetPart_exists S i
    simp only [Finset.sum_apply]
    change (∑ C : SextetPart S, if i ∈ C.val then v.val i else 0) = v.val i
    rw [Finset.sum_eq_single B]
    · simp [hB]
    · intro C _ hCB
      have hn : i ∉ C.val := fun hC => hCB (sextetPart_eq_of_mem S C B hC hB)
      simp [hn]
    · simp
  rw [← he, map_sum]
  apply Submodule.sum_mem
  intro B _
  have hle : supportedPairSpace B.val ≤ ⨆ B ∈ S.parts, supportedPairSpace B :=
    le_iSup_of_le B.val (le_iSup_of_le B.property le_rfl)
  exact hle (supported_evenWord_mem_pairSpace B.val (sextetPart_nonempty S B) (w B)
    (by intro i hi; simp [w, hi]))

/-- Tetrad parity in the natural six-part permutation module, on the native cocode. -/
def sextetCocodeParity (S : Sextet) : Cocode →ₗ[ZMod 2]
    BinaryPermutation.natural (SextetPart S) :=
  codeInCore.liftQ
    ((((BinaryPermutation.constants (SextetPart S)).mkQ.comp (sextetParity S)).comp
      Core.subtype).codRestrict _ (fun v => ⟨_, sextetParity_core S v.property, rfl⟩)) (by
    intro v hv
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).mpr (sextetParity_golay_mem_constants S hv))

lemma sextetCocodeParity_mk (S : Sextet) (v : Core) :
    (sextetCocodeParity S (codeInCore.mkQ v)).val =
      (BinaryPermutation.constants (SextetPart S)).mkQ (sextetParity S v.val) := rfl

lemma sextetCocodeParity_surjective (S : Sextet) : Function.Surjective (sextetCocodeParity S) := by
  intro x
  obtain ⟨v,hv,he⟩ := x.property
  obtain ⟨w,hw⟩ := sextetParity_surjective S v
  have hm : w ∈ Core := by
    change (∑ i, w i) = 0
    rw [← sextetParity_sum S w, hw]
    exact hv
  refine ⟨codeInCore.mkQ ⟨w,hm⟩, ?_⟩
  apply Subtype.ext
  rw [sextetCocodeParity_mk, hw]
  exact he

lemma sextetCocodeParity_ker (S : Sextet) :
    (sextetCocodeParity S).ker = ⨆ B ∈ S.parts, supportedPairSpace B := by
  apply le_antisymm
  · intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ v =>
      have hc : sextetParity S v.val ∈ BinaryPermutation.constants (SextetPart S) := by
        apply (Submodule.Quotient.mk_eq_zero _).mp
        exact congrArg Subtype.val hx
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hc
      obtain ⟨w,hw,he⟩ := sextetParity_golay_allOne S
      let z : Core := v - c • ⟨w, golay_le_core hw⟩
      have hz : sextetParity S z.val = 0 := by
        change sextetParity S (v.val - c • w) = 0
        rw [map_sub, map_smul, he, hc, sub_self]
      have hq : codeInCore.mkQ z = codeInCore.mkQ v := by
        change codeInCore.mkQ (v - c • ⟨w, golay_le_core hw⟩) = _
        have hw0 : codeInCore.mkQ (⟨w, golay_le_core hw⟩ : Core) = 0 :=
          (Submodule.Quotient.mk_eq_zero codeInCore).mpr hw
        rw [map_sub, map_smul, hw0, smul_zero, sub_zero]
      change codeInCore.mkQ v ∈ _
      rw [← hq]
      exact sextetParity_zero_class_mem S z hz
  · refine iSup_le fun B => iSup_le fun hB => ?_
    apply Submodule.span_le.mpr
    rintro x ⟨P,hP,rfl⟩
    obtain ⟨i,j,hij,he⟩ := Finset.card_eq_two.mp P.property
    have hi : i ∈ B := hP (by rw [he]; simp)
    have hj : j ∈ B := hP (by rw [he]; simp)
    have hp : wordOfSet P.val = Pi.single i 1 + Pi.single j 1 := by
      rw [he]
      ext k
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp_all [wordOfSet]
    apply Subtype.ext
    change (BinaryPermutation.constants (SextetPart S)).mkQ (sextetParity S (wordOfSet P.val)) = 0
    rw [hp, map_add, sextetParity_single S ⟨B,hB⟩ hi,
      sextetParity_single S ⟨B,hB⟩ hj]
    have hz : (Pi.single (⟨B,hB⟩ : SextetPart S) (1 : ZMod 2) : SextetPart S → ZMod 2) +
        Pi.single ⟨B,hB⟩ 1 = 0 := by ext i; exact CharTwo.add_self_eq_zero _
    rw [hz, map_zero]

lemma sextetPairSpan_finrank (S : Sextet) :
    Module.finrank (ZMod 2) ↥(⨆ B ∈ S.parts, supportedPairSpace B) = 7 := by
  have hr := (sextetCocodeParity S).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (sextetCocodeParity_surjective S), finrank_top,
    BinaryPermutation.finrank_natural_even _ (by rw [card_sextetPart]; decide),
    card_sextetPart, sextetCocodeParity_ker, finrank_cocode] at hr
  omega

/-- The actual permutation of the six native tetrads. -/
def sextetPartPerm (S : Sextet) : sextetStabilizer S →* Equiv.Perm (SextetPart S) where
  toFun g :=
    { toFun B := ⟨g.val • B.val, by
        have hg : g.val • S.parts = S.parts := g.property
        exact (congrArg (fun F : Finset (Finset (Fin 24)) => g.val • B.val ∈ F) hg).mp
          (Finset.smul_mem_smul_finset B.property)⟩
      invFun B := ⟨g.val⁻¹ • B.val, by
        have hg : g.val⁻¹ • S.parts = S.parts := (g⁻¹).property
        exact (congrArg (fun F : Finset (Finset (Fin 24)) => g.val⁻¹ • B.val ∈ F) hg).mp
          (Finset.smul_mem_smul_finset B.property)⟩
      left_inv B := by apply Subtype.ext; exact inv_smul_smul _ _
      right_inv B := by apply Subtype.ext; exact smul_inv_smul _ _ }
  map_one' := by ext B : 1; apply Subtype.ext; exact one_smul _ _
  map_mul' g h := by ext B : 1; apply Subtype.ext; exact mul_smul _ _ _

lemma sextetPartPerm_apply (S : Sextet) (g : sextetStabilizer S) (B : SextetPart S) :
    (sextetPartPerm S g B).val = g.val • B.val := rfl

lemma sextetParity_equivariant (S : Sextet) (g : sextetStabilizer S) (v : Full) :
    sextetParity S (fullRepresentation g.val v) =
      BinaryPermutation.representation (SextetPart S) (sextetPartPerm S g) (sextetParity S v) := by
  ext B
  change (∑ i ∈ B.val, v (g.val.val.symm i)) = ∑ i ∈ g.val⁻¹ • B.val, v i
  rw [Finset.smul_finset_def, Finset.sum_image]
  · rfl
  · intro i _ j _ he
    exact g.val.val.symm.injective he

lemma sextetCocodeParity_equivariant (S : Sextet) (g : sextetStabilizer S) (v : Cocode) :
    sextetCocodeParity S (cocodeRepresentation g.val v) =
      BinaryPermutation.naturalRepresentation (SextetPart S) (sextetPartPerm S g)
        (sextetCocodeParity S v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    apply Subtype.ext
    change (BinaryPermutation.constants (SextetPart S)).mkQ
      (sextetParity S (fullRepresentation g.val v.val)) =
      (BinaryPermutation.constants (SextetPart S)).mkQ
        (BinaryPermutation.representation (SextetPart S) (sextetPartPerm S g) (sextetParity S v.val))
    rw [sextetParity_equivariant]

/-- The concrete quotient by the within-tetrad pair space. -/
def sextetTopEquiv (S : Sextet) :
    (Cocode ⧸ ⨆ B ∈ S.parts, supportedPairSpace B) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (SextetPart S) :=
  (Submodule.quotEquivOfEq _ _ (sextetCocodeParity_ker S).symm).trans
    ((sextetCocodeParity S).quotKerEquivOfSurjective (sextetCocodeParity_surjective S))

lemma sextetTopEquiv_mk (S : Sextet) (v : Cocode) :
    sextetTopEquiv S ((⨆ B ∈ S.parts, supportedPairSpace B).mkQ v) =
      sextetCocodeParity S v := rfl

/-- The natural module on the six literal parts has faithful symmetric-group action. -/
lemma sextetNatural_faithful (S : Sextet) :
    Function.Injective (BinaryPermutation.naturalRepresentation (SextetPart S)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  apply Equiv.ext
  intro i
  by_contra hgi
  change g i ≠ i at hgi
  have hj : ({i,g i} : Finset (SextetPart S)).card < Fintype.card (SextetPart S) := by
    rw [card_sextetPart]
    exact lt_of_le_of_lt (Finset.card_le_two) (by decide)
  obtain ⟨j,_,hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({i,g i} : Finset (SextetPart S)).card < Finset.univ.card by simpa using hj)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
  let u : BinaryPermutation.Full (SextetPart S) := Pi.single i 1 + Pi.single j 1
  have hu : u ∈ BinaryPermutation.core (SextetPart S) := by
    simp [u, BinaryPermutation.mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]
  let x : BinaryPermutation.natural (SextetPart S) :=
    ⟨(BinaryPermutation.constants (SextetPart S)).mkQ u, u, hu, rfl⟩
  have he := congrArg Subtype.val (LinearMap.congr_fun hg x)
  have hm : BinaryPermutation.representation (SextetPart S) g u - u ∈
      BinaryPermutation.constants (SextetPart S) := (Submodule.Quotient.eq _).mp he
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hm
  have hperm (a : SextetPart S) :
      BinaryPermutation.representation (SextetPart S) g (Pi.single a 1) = Pi.single (g a) 1 := by
    ext k
    simp [Pi.single_apply, Equiv.symm_apply_eq]
  rw [show BinaryPermutation.representation (SextetPart S) g u =
    Pi.single (g i) 1 + Pi.single (g j) 1 by exact (map_add _ _ _).trans (congrArg₂ (· + ·) (hperm i) (hperm j))] at hc
  have hk : ({i,j,g i,g j} : Finset (SextetPart S)).card < Fintype.card (SextetPart S) := by
    rw [card_sextetPart]
    have hh := Finset.card_le_four (a := i) (b := j) (c := g i) (d := g j)
    omega
  obtain ⟨k,_,hk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show ({i,j,g i,g j} : Finset (SextetPart S)).card < Finset.univ.card by simpa using hk)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have hc0 : c = 0 := by
    have he := congrFun hc k
    simpa [u, BinaryPermutation.allOne, Pi.single_apply, hk.1, hk.2.1, hk.2.2.1, hk.2.2.2] using he
  have he := congrFun hc (g i)
  have hij : i ≠ j := Ne.symm hj.1
  simp [hc0, u, BinaryPermutation.allOne, hgi, Ne.symm hj.2, hij] at he

end
end MathieuCode
