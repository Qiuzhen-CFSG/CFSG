module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal
public import Theory.Mathieu.M24.LocalGeometry.Defs

/-!
# Supported octad spaces in the native Golay cocode

Extending an even word on an octad by zero gives a concrete map into the
native cocode. Its range is the span of the octad's pair classes. Minimum
distance identifies its kernel with the constant line, giving dimension
six and a linear equivalence with the natural section of the eight-point
permutation module. The equivalence intertwines the actual stabilizer
permutations with the restricted native cocode action.

For an octad containing the distinguished point, the seven pair classes
through that point belong to the literal M23 source orbit and sum to zero.
They cannot all have the same nonzero image in a one-dimensional quotient.
Consequently an orbit-avoiding subspace of the octad space has dimension
at most four. No fixed-space identification, quadratic form, or full
orthogonal/transvection action is assumed or asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.15.2(2–3) and its proof, printed pp.398–399. The imported minimum-distance
result uses the licensed ATLAS port cited in the parent CocodeLocal module.
-/

@[expose] public section

open scoped BigOperators Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
namespace MathieuCode.CocodeOctad
noncomputable section

/-- Extend a word on a coordinate subset by zero. -/
def extend (B : Finset (Fin 24)) : (B → ZMod 2) →ₗ[ZMod 2] Full where
  toFun v i := if hi : i ∈ B then v ⟨i, hi⟩ else 0
  map_add' v w := by ext i; by_cases hi : i ∈ B <;> simp [hi]
  map_smul' c v := by ext i; by_cases hi : i ∈ B <;> simp [hi]

@[simp] lemma extend_apply_mem (B : Finset (Fin 24)) (v : B → ZMod 2) (i : B) :
    extend B v i = v i := by simp [extend, i.property]

@[simp] lemma extend_apply_not_mem (B : Finset (Fin 24)) (v : B → ZMod 2)
    (i : Fin 24) (hi : i ∉ B) : extend B v i = 0 := by simp [extend, hi]

lemma extend_injective (B : Finset (Fin 24)) : Function.Injective (extend B) := by
  intro v w h
  funext i
  simpa using congrFun h i.val

lemma sum_extend (B : Finset (Fin 24)) (v : B → ZMod 2) :
    ∑ i, extend B v i = ∑ i, v i := by
  calc
    ∑ i, extend B v i = ∑ i ∈ B, extend B v i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ B)
      intro i _ hi
      exact extend_apply_not_mem B v i hi
    _ = ∑ i : B, extend B v i := Finset.sum_subtype B (fun _ => Iff.rfl) _
    _ = ∑ i, v i := by simp

/-- The actual inclusion of even words on a subset into the ambient core. -/
def coreInclusion (B : Finset (Fin 24)) : BinaryPermutation.core B →ₗ[ZMod 2] Core :=
  (extend B).restrict (fun v hv => by
    change (∑ i, extend B v i) = 0
    rw [sum_extend]
    exact hv)

/-- The quotient map taking supported even words to their native cocode class. -/
def toCocode (B : Finset (Fin 24)) : BinaryPermutation.core B →ₗ[ZMod 2] Cocode :=
  codeInCore.mkQ.comp (coreInclusion B)

lemma pair_mem_core {B : Finset (Fin 24)} (a b : B) :
    Pi.single a (1 : ZMod 2) + Pi.single b 1 ∈ BinaryPermutation.core B := by
  simp [BinaryPermutation.mem_core, Finset.sum_add_distrib]

lemma extend_pair {B : Finset (Fin 24)} (a b : B) (hab : a ≠ b) :
    extend B (Pi.single a (1 : ZMod 2) + Pi.single b 1) =
      wordOfSet {a.val, b.val} := by
  ext i
  by_cases hi : i ∈ B
  · have ha : (⟨i, hi⟩ : B) = a ↔ i = a.val := Subtype.ext_iff
    have hb : (⟨i, hi⟩ : B) = b ↔ i = b.val := Subtype.ext_iff
    have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    simp only [extend, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hi, Pi.add_apply,
      Pi.single_apply, ha, hb, wordOfSet, Finset.mem_insert, Finset.mem_singleton]
    by_cases hia : i = a.val <;> by_cases hib : i = b.val <;> simp_all
  · have ha : i ≠ a.val := fun h => hi (h ▸ a.property)
    have hb : i ≠ b.val := fun h => hi (h ▸ b.property)
    simp [extend, hi, wordOfSet, ha, hb]

lemma toCocode_pair {B : Finset (Fin 24)} (a b : B) (hab : a ≠ b) :
    toCocode B ⟨Pi.single a 1 + Pi.single b 1, pair_mem_core a b⟩ =
      pairVector ⟨{a.val, b.val}, by simp [show a.val ≠ b.val from
        fun h => hab (Subtype.ext h)]⟩ := by
  apply congrArg codeInCore.mkQ
  exact Subtype.ext (extend_pair a b hab)

lemma range_toCocode (B : Finset (Fin 24)) [Nonempty B] :
    (toCocode B).range = supportedPairSpace B := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    let a : B := Classical.choice inferInstance
    let W := (supportedPairSpace B).comap (toCocode B)
    have hp (i : B) : (⟨Pi.single i 1 + Pi.single a 1, pair_mem_core i a⟩ :
        BinaryPermutation.core B) ∈ W := by
      change toCocode B _ ∈ supportedPairSpace B
      by_cases hi : i = a
      · subst i
        have hz : (⟨Pi.single a 1 + Pi.single a 1, pair_mem_core a a⟩ :
            BinaryPermutation.core B) = 0 := by
          ext j
          exact CharTwo.add_self_eq_zero _
        rw [hz, map_zero]
        exact Submodule.zero_mem _
      · rw [toCocode_pair i a hi]
        exact pairVector_mem_supportedPairSpace _ (by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact i.property
          · exact Finset.mem_singleton.mp hj ▸ a.property)
    have he : (∑ i : B, v.val i •
        (⟨Pi.single i 1 + Pi.single a 1, pair_mem_core i a⟩ :
          BinaryPermutation.core B)) = v := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, smul_add, Finset.sum_add_distrib,
        ← Finset.sum_smul]
      have hv : ∑ i, v.val i = 0 := v.property
      rw [hv, zero_smul, add_zero]
      simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using Finset.univ_sum_single v.val
    change v ∈ W
    rw [← he]
    exact W.sum_mem fun i _ => W.smul_mem _ (hp i)
  · apply Submodule.span_le.mpr
    rintro _ ⟨P, hP, rfl⟩
    obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp P.property
    have ha : a ∈ B := hP (by simp [he])
    have hb : b ∈ B := hP (by simp [he])
    refine ⟨⟨Pi.single ⟨a, ha⟩ 1 + Pi.single ⟨b, hb⟩ 1,
      pair_mem_core ⟨a, ha⟩ ⟨b, hb⟩⟩, ?_⟩
    rw [toCocode_pair _ _ (by intro h; exact hab (congrArg Subtype.val h))]
    exact congrArg pairVector (Subtype.ext he.symm)

lemma octad_word_mem (O : Octad) : wordOfSet O.val ∈ golay := by
  rw [golay_eq_span_octads]
  exact Submodule.subset_span ⟨O.val, O.property, rfl⟩

lemma extend_allOne (B : Finset (Fin 24)) :
    extend B (BinaryPermutation.allOne B) = wordOfSet B := by
  ext i
  by_cases hi : i ∈ B <;> simp [extend, BinaryPermutation.allOne, wordOfSet, hi]

/-- Minimum distance says the only codewords supported on an octad are zero
and the octad word itself. -/
lemma supported_golay_word (O : Octad) {w : Full} (hw : w ∈ golay)
    (hs : ∀ i ∉ O.val, w i = 0) : w = 0 ∨ w = wordOfSet O.val := by
  by_cases hz : w = 0
  · exact Or.inl hz
  right
  have hsub : Finset.univ.filter (fun i => w i ≠ 0) ⊆ O.val := by
    intro i hi
    by_contra hn
    exact (Finset.mem_filter.mp hi).2 (hs i hn)
  have he : Finset.univ.filter (fun i => w i ≠ 0) = O.val :=
    Finset.eq_of_subset_of_card_le hsub (by
      rw [m24Blocks_card _ O.property]
      exact native_golay_minimum hw hz)
  ext i
  by_cases hi : i ∈ O.val
  · have hn : w i ≠ 0 := by
      have := hi
      rw [← he] at this
      exact (Finset.mem_filter.mp this).2
    have h1 : w i = 1 := by
      have hb : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
      exact hb _ hn
    simpa [wordOfSet, hi] using h1
  · simp [wordOfSet, hi, hs i hi]

lemma ker_toCocode (O : Octad) :
    (toCocode O.val).ker = (BinaryPermutation.constants O.val).comap
      (BinaryPermutation.core O.val).subtype := by
  ext v
  change toCocode O.val v = 0 ↔ v.val ∈ BinaryPermutation.constants O.val
  change codeInCore.mkQ (coreInclusion O.val v) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change extend O.val v.val ∈ golay ↔ _
  constructor
  · intro hv
    rcases supported_golay_word O hv (fun i hi => extend_apply_not_mem _ _ i hi) with h | h
    · have hz : v.val = 0 := (extend_injective O.val) (by simpa using h)
      rw [hz]
      exact Submodule.zero_mem _
    · have h1 : v.val = BinaryPermutation.allOne O.val :=
        (extend_injective O.val) (h.trans (extend_allOne O.val).symm)
      rw [h1]
      exact Submodule.subset_span (Set.mem_singleton _)
  · intro hv
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
    rw [← hc, map_smul, extend_allOne]
    exact golay.smul_mem c (octad_word_mem O)

lemma finrank_supportedPairSpace (O : Octad) :
    Module.finrank (ZMod 2) (supportedPairSpace O.val) = 6 := by
  have hc : Fintype.card O.val = 8 := by simp [m24Blocks_card _ O.property]
  have : Nonempty O.val := Fintype.card_pos_iff.mp (by omega)
  have he : Even (Fintype.card O.val) := by rw [hc]; decide
  have h := (toCocode O.val).finrank_range_add_finrank_ker
  rw [range_toCocode, ker_toCocode,
    (Submodule.comapSubtypeEquivOfLe
      ((BinaryPermutation.constants_le_core_iff O.val).mpr he)).finrank_eq,
    BinaryPermutation.finrank_constants, BinaryPermutation.finrank_core, hc] at h
  omega

/-- The star of pairs through an anchor, including the zero diagonal term. -/
def starWord (B : Finset (Fin 24)) (a i : B) : BinaryPermutation.core B :=
  ⟨Pi.single i 1 + Pi.single a 1, pair_mem_core i a⟩

@[simp] lemma starWord_self (B : Finset (Fin 24)) (a : B) : starWord B a a = 0 := by
  ext j
  exact CharTwo.add_self_eq_zero _

lemma sum_starWord (O : Octad) (a : O.val) :
    ∑ i, starWord O.val a i =
      ⟨BinaryPermutation.allOne O.val, by
        apply (BinaryPermutation.constants_le_core_iff O.val).mpr
          (show Even (Fintype.card O.val) by
            rw [Fintype.card_coe, m24Blocks_card _ O.property]
            decide)
        exact Submodule.subset_span (Set.mem_singleton _)⟩ := by
  ext j
  simp only [Submodule.coe_sum, Finset.sum_apply, starWord, Pi.add_apply,
    Finset.sum_add_distrib, BinaryPermutation.allOne]
  simp [Pi.single_apply, m24Blocks_card _ O.property, show (8 : ZMod 2) = 0 by decide]

lemma sum_star_cocode (O : Octad) (a : O.val) :
    ∑ i, toCocode O.val (starWord O.val a i) = 0 := by
  rw [← map_sum, sum_starWord]
  apply (Submodule.Quotient.mk_eq_zero codeInCore).mpr
  change extend O.val (BinaryPermutation.allOne O.val) ∈ golay
  rw [extend_allOne]
  exact octad_word_mem O

lemma star_mem_supportedPairSpace (O : Octad) (a i : O.val) :
    toCocode O.val (starWord O.val a i) ∈ supportedPairSpace O.val := by
  have : Nonempty O.val := ⟨a⟩
  rw [← range_toCocode]
  exact LinearMap.mem_range_self _ _

lemma m23_star_mem_orbit (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (i : O.val) (hi : i ≠ ⟨0, hO⟩) :
    toCocode O.val (starWord O.val ⟨0, hO⟩ i) ∈ m23WeightTwoOrbit := by
  rw [starWord, toCocode_pair _ _ hi]
  have hi0 : i.val ≠ 0 := fun h => hi (Subtype.ext h)
  let j : Fin 23 := m23PointEquiv.symm ⟨i.val, hi0⟩
  have hj : m23PointEmbedding j = i.val :=
    congrArg Subtype.val (m23PointEquiv.apply_symm_apply ⟨i.val, hi0⟩)
  refine ⟨j, ?_⟩
  apply congrArg pairVector
  apply Subtype.ext
  change {0, m23PointEmbedding j} = {i.val, 0}
  rw [hj, Finset.pair_comm]

/-- An odd zero-sum family cannot avoid a subspace of codimension one.
The formulation includes one zero term, matching the eight-point star. -/
private lemma finrank_quotient_ge_two_of_even_star {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι)
    (he : Even (Fintype.card ι)) (v : ι → V) (hva : v a = 0)
    (hs : ∑ i, v i = 0) (I : Submodule (ZMod 2) V)
    (ha : ∀ i, i ≠ a → v i ∉ I) (hn : 2 ≤ Fintype.card ι) :
    2 ≤ Module.finrank (ZMod 2) (V ⧸ I) := by
  by_contra hlt
  have hdim : Module.finrank (ZMod 2) (V ⧸ I) ≤ 1 := by omega
  obtain ⟨b, hb⟩ : ∃ b : ι, b ≠ a := by
    by_contra h
    push Not at h
    have : Subsingleton ι := ⟨fun i j => (h i).trans (h j).symm⟩
    have := Fintype.card_le_one_iff_subsingleton.mpr this
    omega
  let w := I.mkQ (v b)
  have hw : w ≠ 0 := by
    intro h
    exact ha b hb ((Submodule.Quotient.mk_eq_zero I).mp h)
  have hpos : 0 < Module.finrank (ZMod 2) (V ⧸ I) :=
    Module.finrank_pos_iff.mpr ⟨w, 0, hw⟩
  have hone : Module.finrank (ZMod 2) (V ⧸ I) = 1 := by omega
  have heq (i : ι) (hi : i ≠ a) : I.mkQ (v i) = w := by
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hone hw (I.mkQ (v i))
    have hc0 : c ≠ 0 := by
      intro hc0
      rw [hc0, zero_smul] at hc
      exact ha i hi ((Submodule.Quotient.mk_eq_zero I).mp hc.symm)
    have hbinary : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
    rw [hbinary c hc0, one_smul] at hc
    exact hc.symm
  have hsum : ∑ i ∈ Finset.univ.erase a, I.mkQ (v i) = 0 := by
    have ht := congrArg I.mkQ hs
    rw [map_sum, map_zero] at ht
    have hh := Finset.sum_erase_add (Finset.univ : Finset ι) (fun i => I.mkQ (v i))
      (Finset.mem_univ a)
    rw [hva, map_zero, add_zero, ht] at hh
    exact hh
  have hodd : Odd (Fintype.card ι - 1) := by
    obtain ⟨k, hk⟩ := he
    refine ⟨k - 1, ?_⟩
    omega
  have hsum' : ∑ i ∈ Finset.univ.erase a, I.mkQ (v i) = w := by
    calc
      _ = ∑ _i ∈ Finset.univ.erase a, w :=
        Finset.sum_congr rfl fun i hi => heq i (Finset.mem_erase.mp hi).1
      _ = ((Fintype.card ι - 1 : ℕ) : ZMod 2) • w := by
        simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a),
          Finset.card_univ]
        exact (Nat.cast_smul_eq_nsmul (R := ZMod 2) _ _).symm
      _ = w := by rw [hodd.natCast_zmod_two, one_smul]
  exact hw (hsum'.symm.trans hsum)

/-- H.15.2(3) for the M23 source orbit, on the literal geometric octad space. -/
lemma m23_avoiding_finrank_le (O : Octad) (hO : (0 : Fin 24) ∈ O.val)
    (I : Submodule (ZMod 2) Cocode) (hI : I ≤ supportedPairSpace O.val)
    (ha : Disjoint (I : Set Cocode) m23WeightTwoOrbit) :
    Module.finrank (ZMod 2) I ≤ 4 := by
  let U := supportedPairSpace O.val
  let J := I.comap U.subtype
  let a : O.val := ⟨0, hO⟩
  let v (i : O.val) : U := ⟨toCocode O.val (starWord O.val a i),
    star_mem_supportedPairSpace O a i⟩
  have hd : 2 ≤ Module.finrank (ZMod 2) (U ⧸ J) := by
    apply finrank_quotient_ge_two_of_even_star a
      (by
            rw [Fintype.card_coe, m24Blocks_card _ O.property]
            decide) v
    · apply Subtype.ext
      change toCocode O.val (starWord O.val a a) = 0
      rw [starWord_self, map_zero]
    · apply Subtype.ext
      simpa only [Submodule.coe_sum, ZeroMemClass.coe_zero] using sum_star_cocode O a
    · intro i hi hv
      exact Set.disjoint_left.mp ha hv (m23_star_mem_orbit O hO i hi)
    · simp [m24Blocks_card _ O.property]
  have he := J.finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe hI).finrank_eq,
    finrank_supportedPairSpace] at he
  omega

/-- The core-to-deleted-module map, with its range retained as a subspace. -/
def toNatural (B : Finset (Fin 24)) : BinaryPermutation.core B →ₗ[ZMod 2]
    BinaryPermutation.Deleted B :=
  (BinaryPermutation.constants B).mkQ.domRestrict (BinaryPermutation.core B)

lemma range_toNatural (B : Finset (Fin 24)) :
    (toNatural B).range = BinaryPermutation.natural B :=
  LinearMap.range_domRestrict _ _

lemma ker_toNatural (B : Finset (Fin 24)) :
    (toNatural B).ker = (BinaryPermutation.constants B).comap
      (BinaryPermutation.core B).subtype := by
  rw [toNatural, LinearMap.ker_domRestrict, Submodule.ker_mkQ]

/-- The supported octad cocode space is the actual six-dimensional natural
section of the permutation module on its eight points. -/
def naturalEquiv (O : Octad) :
    BinaryPermutation.natural O.val ≃ₗ[ZMod 2] supportedPairSpace O.val := by
  letI : Nonempty O.val := Fintype.card_pos_iff.mp (by
    rw [Fintype.card_coe, m24Blocks_card _ O.property]
    decide)
  exact (LinearEquiv.ofEq _ _ (range_toNatural O.val)).symm.trans
    ((toNatural O.val).quotKerEquivRange.symm.trans
      ((Submodule.quotEquivOfEq _ _ ((ker_toNatural O.val).trans (ker_toCocode O).symm)).trans
        ((toCocode O.val).quotKerEquivRange.trans
          (LinearEquiv.ofEq _ _ (range_toCocode O.val)))))

lemma naturalEquiv_apply (O : Octad) (v : BinaryPermutation.core O.val) :
    (naturalEquiv O ⟨toNatural O.val v, by
      rw [← range_toNatural]
      exact LinearMap.mem_range_self _ _⟩ : Cocode) = toCocode O.val v := by
  change ((toCocode O.val).quotKerEquivRange
    ((Submodule.quotEquivOfEq _ _ ((ker_toNatural O.val).trans (ker_toCocode O).symm))
      ((toNatural O.val).quotKerEquivRange.symm
        ⟨toNatural O.val v, LinearMap.mem_range_self _ _⟩)) : Cocode) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- Setwise stabilizers preserve the geometric pair span under the native action. -/
lemma supportedPairSpace_invariant (B : Finset (Fin 24)) (g : M24)
    (hg : g • B = B) {v : Cocode} (hv : v ∈ supportedPairSpace B) :
    cocodeRepresentation g v ∈ supportedPairSpace B := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨P, hP, rfl⟩ := hv
      rw [pairVector_equivariant]
      apply pairVector_mem_supportedPairSpace
      change g • P.val ⊆ B
      rw [← hg]
      exact Finset.smul_finset_subset_smul_finset hP
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add v w _ _ hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw
  | smul c v _ hv => simpa only [map_smul] using Submodule.smul_mem _ c hv

/-- The literal action of the native octad stabilizer on its supported cocode space. -/
def pairRepresentation (O : Octad) : Representation (ZMod 2) (octadStabilizer O)
    (supportedPairSpace O.val) where
  toFun g := (cocodeRepresentation g.val).restrict
    (fun _ hv => supportedPairSpace_invariant O.val g.val g.property hv)
  map_one' := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (map_one cocodeRepresentation) v.val
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact LinearMap.congr_fun (map_mul cocodeRepresentation g.val h.val) v.val

/-- Restriction of each native stabilizer permutation to the actual eight-point octad. -/
def coordinateAction (O : Octad) : octadStabilizer O →* Equiv.Perm O.val where
  toFun g := g.val.val.subtypePerm (MulAction.mem_stabilizer_finset.mp g.property)
  map_one' := by ext a; rfl
  map_mul' g h := by ext a; rfl

lemma coordinateAction_apply (O : Octad) (g : octadStabilizer O) (i : O.val) :
    (coordinateAction O g i).val = g.val.val i.val := rfl

lemma coordinateAction_symm_apply (O : Octad) (g : octadStabilizer O) (i : O.val) :
    ((coordinateAction O g).symm i).val = g.val.val.symm i.val := rfl

lemma extend_permute (O : Octad) (g : octadStabilizer O) (v : O.val → ZMod 2) :
    extend O.val (BinaryPermutation.representation O.val (coordinateAction O g) v) =
      fullRepresentation g.val (extend O.val v) := by
  ext i
  have hg := MulAction.mem_stabilizer_finset.mp g.property
  have hi : g.val.val.symm i ∈ O.val ↔ i ∈ O.val := by
    have hh : g.val.val (g.val.val.symm i) ∈ O.val ↔
        g.val.val.symm i ∈ O.val := hg (g.val.val.symm i)
    simpa only [Equiv.apply_symm_apply] using hh.symm
  by_cases h : i ∈ O.val
  · have h' := hi.mpr h
    change (if hi : i ∈ O.val then
      v ((coordinateAction O g).symm ⟨i, hi⟩) else 0) =
      (if hj : g.val.val.symm i ∈ O.val then v ⟨g.val.val.symm i, hj⟩ else 0)
    simp only [dif_pos h, dif_pos h']
    rfl
  · have h' : g.val.val.symm i ∉ O.val := fun hh => h (hi.mp hh)
    change (if hi : i ∈ O.val then _ else 0) =
      (if hj : g.val.val.symm i ∈ O.val then _ else 0)
    simp only [dif_neg h, dif_neg h']

lemma toCocode_equivariant (O : Octad) (g : octadStabilizer O)
    (v : BinaryPermutation.core O.val) :
    toCocode O.val (BinaryPermutation.coreRepresentation O.val (coordinateAction O g) v) =
      cocodeRepresentation g.val (toCocode O.val v) := by
  apply congrArg codeInCore.mkQ
  apply Subtype.ext
  exact extend_permute O g v.val

/-- The equivalence retains the actual stabilizer action, rather than transporting
an unrelated action onto the six-dimensional space. -/
lemma naturalEquiv_equivariant (O : Octad) (g : octadStabilizer O)
    (v : BinaryPermutation.natural O.val) :
    naturalEquiv O (BinaryPermutation.naturalRepresentation O.val (coordinateAction O g) v) =
      pairRepresentation O g (naturalEquiv O v) := by
  obtain ⟨w, hw, hwv⟩ := v.property
  have hv : v = ⟨toNatural O.val ⟨w, hw⟩, by
      rw [← range_toNatural]
      exact LinearMap.mem_range_self _ _⟩ := Subtype.ext hwv.symm
  subst v
  apply Subtype.ext
  have h : BinaryPermutation.naturalRepresentation O.val (coordinateAction O g)
      ⟨toNatural O.val ⟨w, hw⟩, by
        rw [← range_toNatural]
        exact LinearMap.mem_range_self _ _⟩ =
      ⟨toNatural O.val (BinaryPermutation.coreRepresentation O.val (coordinateAction O g)
        ⟨w, hw⟩), by
          rw [← range_toNatural]
          exact LinearMap.mem_range_self _ _⟩ := by
    apply Subtype.ext
    rfl
  rw [h, naturalEquiv_apply]
  change _ = cocodeRepresentation g.val
    (naturalEquiv O ⟨toNatural O.val ⟨w, hw⟩, _⟩).val
  rw [naturalEquiv_apply]
  exact toCocode_equivariant O g ⟨w, hw⟩

end
end MathieuCode.CocodeOctad
