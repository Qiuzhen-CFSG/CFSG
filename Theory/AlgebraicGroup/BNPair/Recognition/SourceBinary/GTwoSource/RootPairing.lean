module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CommutationFromMixed

/-!
# The actual middle-root pairing before field normalization

Both radical-derived bounds put DC in the intersection of the two middle
triples, whose coordinates are AC. The short reflection interchanges D and
C and preserves A, so the same commutator also has AD coordinates. Root
factor uniqueness removes D and proves DC ≤ A without any mixed equation.
Cartan irreducibility makes a nonzero pairing onto. The earlier radical
argument then kills the opposite pairing, giving the orientation of II (9.2).

The DC coefficient is constructed from the actual root maps. Adjacent
commutation makes it biadditive; when it is nonzero, Weyl conjugation and
Cartan irreducibility make it symmetric and nondegenerate. These properties
do not assert compatibility with field multiplication for arbitrary local
labels. At q=2, nontriviality determines the single nonzero coefficient,
hence the normalized DC equation and, through RootPairingApplication, all
previously constructed marked source comparisons.

All geometric and additive statements include q=2 and q=4 and either
orientation. The exclusion of simultaneous vanishing of the two middle
pairings and compatible whole-pinning field labels in larger fields remain
source obligations. Nonabelianness of the radicals is not substituted for
nontriviality of this particular pairing.

Source: Fong--Seitz I (3G), pp.14--16; II (9.1)--(9.5), pp.211--212,
and the pairing normalization underlying (9.13)--(9.14), pp.215--216.
The commutators and ordered exchanges below use the consumer's left
convention; subgroup Weyl transport uses rightConjugate.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X} (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))

private theorem ssq (i : Fin 2) : Q.simple i * Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem conjugate_commutator (A B : Subgroup (X ⧸ Q.D)) (v : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ v = ⁅rightConjugate A v,rightConjugate B v⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]

include hK μ in
/-- The actual two radical bounds and reflection put DC in A, before any labels. -/
theorem middle_pairing_le_root (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    ⁅rootAt Q split i (Q.simple j),rootAt Q split i (Q.simple j*Q.simple i)⁆ ≤
      rootAt Q split j (Q.simple i*Q.simple j) := by
  let A := rootAt Q split j (Q.simple i*Q.simple j)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split i (Q.simple j)
  let K := ⁅D,C⁆
  have hM1 : K ≤ middleRoots Q split i j := by
    apply le_trans (commutator_mono (exchanged_roots_le_remainder Q split hm i j hij).1
      (exchanged_roots_le_remainder Q split hm i j hij).2)
    exact radical_commutator_le_middle_of_linear Q split hm i j hij (hK i) (μ i)
  have hM2 : K ≤ middleRoots Q split j i := by
    have hle := middleRoots_le_remainder Q split hm j i hij.symm
    apply le_trans (commutator_mono
      ((show D ≤ middleRoots Q split j i from le_sup_left.trans le_sup_left).trans hle)
      ((show C ≤ middleRoots Q split j i from le_sup_right).trans hle))
    exact radical_commutator_le_middle_of_linear Q split hm j i hij.symm (hK j) (μ j)
  let v := representative (Q.simple i)
  have hv := representative_spec (Q.simple i)
  have hAv : rightConjugate A (v : X ⧸ Q.D) = A := by
    dsimp only [A]
    rw [rootAt_right Q split _ _ _ v hv,orthogonal_root_stabilizer Q split hm j i hij.symm]
  have hCv : rightConjugate C (v : X ⧸ Q.D) = D := by
    dsimp only [C, D]
    rw [rootAt_right Q split _ _ _ v hv,mul_assoc,ssq,mul_one]
  have hDv : rightConjugate D (v : X ⧸ Q.D) = C := by
    dsimp only [D, C]
    rw [rootAt_right Q split _ _ _ v hv]
  have hKv : rightConjugate K (v : X ⧸ Q.D) = K := by
    change rightConjugate ⁅D,C⁆ _ = ⁅D,C⁆
    rw [conjugate_commutator,hDv,hCv,commutator_comm]
  intro x hx
  have hxv : (v : X ⧸ Q.D)*x*(v : X ⧸ Q.D)⁻¹ ∈ K := by
    change x ∈ rightConjugate K (v : X ⧸ Q.D)
    rwa [hKv]
  obtain ⟨a,ha,c,hc,he⟩ := middle_intersection_two_coordinates Q split hm i j hij _
    (hM1 hxv) (hM2 hxv)
  let a' := (v : X ⧸ Q.D)⁻¹*a*(v : X ⧸ Q.D)
  let d := (v : X ⧸ Q.D)⁻¹*c*(v : X ⧸ Q.D)
  have ha' : a' ∈ A := by
    rw [← hAv]
    change (v : X ⧸ Q.D)*a'*(v : X ⧸ Q.D)⁻¹ ∈ A
    simpa only [a',mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ha
  have hd : d ∈ D := by
    rw [← hCv]
    change (v : X ⧸ Q.D)*d*(v : X ⧸ Q.D)⁻¹ ∈ C
    simpa only [d,mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one] using hc
  have hxd : x = a'*d := by
    have ht := congrArg (MulAut.conj (v : X ⧸ Q.D)⁻¹) he
    simpa only [MulAut.conj_apply,inv_inv,mul_assoc,inv_mul_cancel_left,
      mul_inv_cancel_left,mul_inv_cancel,inv_mul_cancel,mul_one,a',d] using ht
  have haM : a' ∈ middleRoots Q split i j := mem_sup_right ha'
  have hdM : d ∈ middleRoots Q split i j := by
    have ht := (middleRoots Q split i j).mul_mem
      ((middleRoots Q split i j).inv_mem haM) (hM1 hx)
    simpa only [hxd,inv_mul_cancel_left] using ht
  have hd1 := disjoint_def.mp (terminal_disjoint_middle Q split hm i j hij) hd hdM
  simpa only [hxd,hd1,mul_one] using ha'

include hK μ in
/-- Cartan irreducibility makes the source middle pairing either zero or onto. -/
theorem middle_pairing_eq_root_of_ne_bot (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hne : ⁅rootAt Q split i (Q.simple j),rootAt Q split i (Q.simple j*Q.simple i)⁆ ≠ ⊥) :
    ⁅rootAt Q split i (Q.simple j),rootAt Q split i (Q.simple j*Q.simple i)⁆ =
      rootAt Q split j (Q.simple i*Q.simple j) := by
  apply QuadrangleStructure.rootAt_eq_of_torus_invariant Q split j (μ j) (hK j) _ _
    (middle_pairing_le_root Q split hK μ hm i j hij) hne
  intro v hv
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (rootAt_torus_normalizes Q split i (Q.simple j) hv),
    mem_normalizer_iff_map_conj_eq.mp
      (rootAt_torus_normalizes Q split i (Q.simple j*Q.simple i) hv)]

include hK μ in
/-- A nonzero source middle pairing forces the opposite pairing and EC to vanish. -/
theorem commutations_of_middle_pairing_ne_bot (hm : rotationOrder Q = 6) (short : Fin 2)
    (hne : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ ≠ ⊥) :
    ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥ ∧
      ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 2⁆ = ⊥ := by
  have hij : short ≠ 1-short := by fin_cases short <;> decide
  have hdc := middle_pairing_eq_root_of_ne_bot Q split hK μ hm short (1-short) hij hne
  have hec := orthogonal_commutator_eq_bot_of_dc Q split hK μ hm short (1-short) hij hdc
  refine ⟨?_,hec⟩
  have hdb := congrArg (fun V => rightConjugate V
    (representative (Q.simple short) : X ⧸ Q.D)) hec
  rw [conjugate_commutator,←rootAt_eq Q split (1-short) (Q.simple short) _ (representative_spec _),
    rootAt_right Q split _ _ _ _ (representative_spec _),mul_assoc,ssq,mul_one,commutator_comm] at hdb
  have hdb' : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 1⁆ = ⊥ :=
    hdb.trans (by simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot])
  have hcb := (positiveCarrier_adjacent_commutators Q split hm hK short).2.1
  have hA : positiveCarrier Q split short 0 ≤
      centralizer (positiveCarrier Q split short 1 : Set (X ⧸ Q.D)) := by
    change rootAt Q split (1-short) (Q.simple short*Q.simple (1-short)) ≤ _
    rw [←hdc]
    exact (Subgroup.commutator_le_sup _ _).trans
      (sup_le (commutator_eq_bot_iff_le_centralizer.mp hdb')
        (commutator_eq_bot_iff_le_centralizer.mp hcb))
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hA

include hK μ in
/-- The source orientation in (9.2) exists without any choice of field labels. -/
theorem exists_orientation_opposite_pairing_zero (hm : rotationOrder Q = 6) :
    ∃ short : Fin 2, ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥ := by
  by_cases hz : ⁅positiveCarrier Q split 0 3,positiveCarrier Q split 0 2⁆ = ⊥
  · exact ⟨1,hz⟩
  · exact ⟨0,(commutations_of_middle_pairing_ne_bot Q split hK μ hm 0 hz).1⟩

variable (n : ∀ i, RootReflection Q split i) (short : Fin 2)

private theorem root_mem (k : Fin 6) (a : F) :
    (alignedSourceRoots Q split hK μ n short).x k a ∈ positiveCarrier Q split short k := by
  rw [←alignedSourceRoots_range Q split hK μ n short k]
  exact ⟨.ofAdd a,rfl⟩

private theorem root_inj (k : Fin 6) :
    Function.Injective ((alignedSourceRoots Q split hK μ n short).x k) :=
  (alignedSourceRoots_injective Q split hK μ n short k).comp Multiplicative.ofAdd.injective

/-- The actual DC commutator has a unique highest-root coordinate, without
assuming any polynomial equation or nonzero pairing. -/
theorem exists_unique_middle_coefficient (hm : rotationOrder Q = 6) (d c : F) :
    ∃! a : F, ⁅(alignedSourceRoots Q split hK μ n short).x 3 d,
      (alignedSourceRoots Q split hK μ n short).x 2 c⁆ =
        (alignedSourceRoots Q split hK μ n short).x 0 a := by
  have hh := middle_pairing_le_root Q split hK μ hm short (1-short)
    (by fin_cases short <;> decide)
    (commutator_mem_commutator (root_mem Q split hK μ n short 3 d)
      (root_mem Q split hK μ n short 2 c))
  change _ ∈ positiveCarrier Q split short 0 at hh
  rw [←alignedSourceRoots_range Q split hK μ n short 0] at hh
  obtain ⟨a,ha⟩ := hh
  refine ⟨a.toAdd,ha.symm,?_⟩
  intro b hb
  exact root_inj Q split hK μ n short 0 (hb.symm.trans ha.symm)

/-- The coefficient is defined from the actual commutator, rather than supplied
as source data. Its compatibility with field multiplication is a later step. -/
def middleCoefficient (hm : rotationOrder Q = 6) (d c : F) : F :=
  (exists_unique_middle_coefficient Q split hK μ n short hm d c).exists.choose

theorem middleCoefficient_spec (hm : rotationOrder Q = 6) (d c : F) :
    ⁅(alignedSourceRoots Q split hK μ n short).x 3 d,
      (alignedSourceRoots Q split hK μ n short).x 2 c⁆ =
        (alignedSourceRoots Q split hK μ n short).x 0
          (middleCoefficient Q split hK μ n short hm d c) :=
  (exists_unique_middle_coefficient Q split hK μ n short hm d c).exists.choose_spec

theorem middleCoefficient_add_left (hm : rotationOrder Q = 6) (d d' c : F) :
    middleCoefficient Q split hK μ n short hm (d+d') c =
      middleCoefficient Q split hK μ n short hm d c +
        middleCoefficient Q split hK μ n short hm d' c := by
  let L := alignedSourceRoots Q split hK μ n short
  have hda (d a : F) : Commute (L.x 3 d) (L.x 0 a) := by
    exact (mem_centralizer_iff.mp
      ((commutator_eq_bot_iff_le_centralizer.mp
        (positiveCarrier_adjacent_commutators Q split hm hK short).2.2.1)
          (root_mem Q split hK μ n short 3 d)) _
            (root_mem Q split hK μ n short 0 a)).symm
  have hf := middleCoefficient_spec Q split hK μ n short hm
  apply root_inj Q split hK μ n short 0
  rw [←hf,PositiveRoots.x_add,commutatorElement_mul_left_eq_conj_mul,
    hf,hf,PositiveRoots.x_add]
  rw [(hda d _).eq]
  simp only [L,mul_assoc,mul_inv_cancel_left]
  rw [←PositiveRoots.x_add,←PositiveRoots.x_add,add_comm]

theorem middleCoefficient_add_right (hm : rotationOrder Q = 6) (d c c' : F) :
    middleCoefficient Q split hK μ n short hm d (c+c') =
      middleCoefficient Q split hK μ n short hm d c +
        middleCoefficient Q split hK μ n short hm d c' := by
  let L := alignedSourceRoots Q split hK μ n short
  have hca (c a : F) : Commute (L.x 2 c) (L.x 0 a) := by
    exact (mem_centralizer_iff.mp
      ((commutator_eq_bot_iff_le_centralizer.mp
        (positiveCarrier_adjacent_commutators Q split hm hK short).1)
          (root_mem Q split hK μ n short 2 c)) _
            (root_mem Q split hK μ n short 0 a)).symm
  have hf := middleCoefficient_spec Q split hK μ n short hm
  apply root_inj Q split hK μ n short 0
  rw [←hf,PositiveRoots.x_add,commutatorElement_mul_right_eq_mul_conj,
    hf,hf,PositiveRoots.x_add]
  rw [mul_assoc _ (L.x 2 c) _,(hca c _).eq]
  simp only [L,mul_assoc,mul_inv_cancel,mul_one]


@[simp] theorem middleCoefficient_zero_left (hm : rotationOrder Q = 6) (c : F) :
    middleCoefficient Q split hK μ n short hm 0 c = 0 := by
  simpa using (middleCoefficient_add_left Q split hK μ n short hm 0 0 c).symm

@[simp] theorem middleCoefficient_zero_right (hm : rotationOrder Q = 6) (d : F) :
    middleCoefficient Q split hK μ n short hm d 0 = 0 := by
  simpa using (middleCoefficient_add_right Q split hK μ n short hm d 0 0).symm

/-- The nonzero subgroup pairing supplies all ten pointwise commutations,
without normalizing its field coefficient. -/
theorem aligned_commuting_of_middle_pairing_ne_bot (hm : rotationOrder Q = 6)
    (hne : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ ≠ ⊥) :
    (alignedSourceRoots Q split hK μ n short).CommutingRelations :=
  aligned_commuting_of_two Q split hK μ n short hm
    (commutations_of_middle_pairing_ne_bot Q split hK μ hm short hne).1
    (commutations_of_middle_pairing_ne_bot Q split hK μ hm short hne).2

/-- The short Weyl action makes the actual middle pairing symmetric. -/
theorem middleCoefficient_symmetric (hm : rotationOrder Q = 6)
    (hne : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ ≠ ⊥)
    (d c : F) : middleCoefficient Q split hK μ n short hm d c =
      middleCoefficient Q split hK μ n short hm c d := by
  let L := alignedSourceRoots Q split hK μ n short
  let s : X ⧸ Q.D := (n short).val
  have R := aligned_commuting_of_middle_pairing_ne_bot Q split hK μ n short hm hne
  have hsA (a : F) : MulAut.conj s (L.x 0 a) = L.x 0 a :=
    sourceBorelWeyl_sA Q split hK μ n short split.abelian hm R a
  have hsC (a : F) : MulAut.conj s (L.x 2 a) = L.x 3 a :=
    sourceBorelWeyl_sC Q split hK μ n short split.abelian a
  have hsD (a : F) : MulAut.conj s (L.x 3 a) = L.x 2 a :=
    sourceBorelWeyl_sD Q split hK μ n short split.abelian a
  have hf := middleCoefficient_spec Q split hK μ n short hm
  have he := congrArg (MulAut.conj s) (hf d c)
  rw [map_commutatorElement,hsD,hsC,hsA,←commutatorElement_inv,hf,root_inv] at he
  exact (root_inj Q split hK μ n short 0 he).symm

/-- No nonzero middle root centralizes the entire opposite middle root.
This is the nonsingularity of the constructed additive pairing. -/
theorem middleCoefficient_nondegenerate (hm : rotationOrder Q = 6)
    (hne : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ ≠ ⊥)
    (c : F) : (∀ d, middleCoefficient Q split hK μ n short hm d c = 0) ↔ c = 0 := by
  constructor
  · intro hc
    let C := positiveCarrier Q split short 2
    let D := positiveCarrier Q split short 3
    have hz : C ⊓ centralizer (D : Set (X ⧸ Q.D)) = ⊥ := by
      by_contra hh
      have hn := (le_inf (positiveCarrier_torus_normalizes Q split short 2)
        ((positiveCarrier_torus_normalizes Q split short 3).trans
          (normalizer_le_normalizer_centralizer D))).trans inf_normalizer_le_normalizer_inf
      have he := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split short
        (μ short) (hK short) _ (C ⊓ centralizer (D : Set (X ⧸ Q.D))) inf_le_left hh hn
      apply hne
      rw [commutator_comm]
      apply commutator_eq_bot_iff_le_centralizer.mpr
      change C ≤ centralizer (D : Set (X ⧸ Q.D))
      change C ⊓ centralizer (D : Set (X ⧸ Q.D)) = C at he
      rw [←he]
      exact inf_le_right
    have hmem : (alignedSourceRoots Q split hK μ n short).x 2 c ∈
        C ⊓ centralizer (D : Set (X ⧸ Q.D)) := by
      refine ⟨root_mem Q split hK μ n short 2 c,mem_centralizer_iff.mpr ?_⟩
      intro d hd
      change d ∈ positiveCarrier Q split short 3 at hd
      rw [←alignedSourceRoots_range Q split hK μ n short 3] at hd
      obtain ⟨d,rfl⟩ := hd
      apply commutatorElement_eq_one_iff_mul_comm.mp
      change ⁅(alignedSourceRoots Q split hK μ n short).x 3 d.toAdd,
        (alignedSourceRoots Q split hK μ n short).x 2 c⁆ = 1
      rw [middleCoefficient_spec Q split hK μ n short hm,hc,PositiveRoots.x_zero]
    rw [hz,mem_bot] at hmem
    apply root_inj Q split hK μ n short 2
    simpa only [PositiveRoots.x_zero] using hmem
  · rintro rfl d
    exact middleCoefficient_zero_right Q split hK μ n short hm d

omit [CharP F 2] [Finite F] in
private theorem binary_cases (hF : Nat.card F = 2) (a : F) : a = 0 ∨ a = 1 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  obtain ⟨x,hx,hu⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hF
  exact Or.inr ((hu a ha).trans (hu 1 one_ne_zero).symm)

/-- At q=2 the actual nonzero pairing determines its sole nonzero coefficient.
No field-label compatibility or external binary recognition is assumed. -/
theorem binary_middleCoefficient (hm : rotationOrder Q = 6) (hF : Nat.card F = 2)
    (hne : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ ≠ ⊥)
    (d c : F) : middleCoefficient Q split hK μ n short hm d c = c*d := by
  have hone : middleCoefficient Q split hK μ n short hm 1 1 = 1 := by
    apply (binary_cases hF _).resolve_left
    intro hz
    apply hne
    apply bot_unique
    apply commutator_le.mpr
    intro d hd c hc
    rw [←alignedSourceRoots_range Q split hK μ n short 3] at hd
    rw [←alignedSourceRoots_range Q split hK μ n short 2] at hc
    obtain ⟨d,rfl⟩ := hd
    obtain ⟨c,rfl⟩ := hc
    change ⁅(alignedSourceRoots Q split hK μ n short).x 3 d.toAdd,
      (alignedSourceRoots Q split hK μ n short).x 2 c.toAdd⁆ ∈ (⊥ : Subgroup (X ⧸ Q.D))
    rw [middleCoefficient_spec Q split hK μ n short hm,mem_bot]
    rcases binary_cases hF d.toAdd with hd | hd <;>
      rcases binary_cases hF c.toAdd with hc | hc <;>
        simp only [hd,hc,middleCoefficient_zero_left,middleCoefficient_zero_right,hz,PositiveRoots.x_zero]
  rcases binary_cases hF d with rfl | rfl <;>
    rcases binary_cases hF c with rfl | rfl <;>
      simp only [middleCoefficient_zero_left,middleCoefficient_zero_right,hone,mul_zero,mul_one]

/-- The binary source DC equation follows from the nonzero subgroup pairing. -/
theorem binary_aligned_dc_of_middle_pairing_ne_bot (hm : rotationOrder Q = 6)
    (hF : Nat.card F = 2)
    (hne : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ ≠ ⊥)
    (d c : F) : (alignedSourceRoots Q split hK μ n short).x 3 d *
      (alignedSourceRoots Q split hK μ n short).x 2 c =
        (alignedSourceRoots Q split hK μ n short).x 0 (c*d) *
          (alignedSourceRoots Q split hK μ n short).x 2 c *
            (alignedSourceRoots Q split hK μ n short).x 3 d := by
  have he := middleCoefficient_spec Q split hK μ n short hm d c
  rw [binary_middleCoefficient Q split hK μ n short hm hF hne] at he
  rw [←he]
  simp only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
