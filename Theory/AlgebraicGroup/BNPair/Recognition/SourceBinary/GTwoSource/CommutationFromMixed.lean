module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.LowerPositive
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SmallSections

/-!
# The DC equation forces the complete positive commutation table

Write K = [V_short,V_short] for the derived subgroup of the actual short
parabolic radical. The DC image puts A in K. Reflecting DC gives the FC
subgroup image B without first assuming pointwise fixation of C. Since B
is disjoint from K, Cartan irreducibility makes C disjoint from K too.

The two radical-derived bounds place DB in the intersection of the two
middle triples, whose literal coordinates are AC. Thus DB lies in A.
Reflecting gives FA contained in B, while normality puts FA in K. Hence
FA = 1 and Weyl transport gives EC = DB = 1. Finally B centralizes both
C and D, so it centralizes their commutator A. The previously proved
adjacent-root commutations then give the whole ten-pair table and the
pointwise FC equation. All arguments include q=2 and q=4 and either
orientation, with the same quotient, roots and actual radical normalizers.

The normalized DC equation itself, FD, EB containment and normalization,
the lower FE coefficients and the auxiliary torus remain in LowerPositiveData.
This is a reduction of those source obligations, not the completed
6E(a) -> 9A reconstruction. MixedPositiveApplication supplies the literal
positive, full marked, original and geometric consumers.

Source: Fong--Seitz I (3G), pp.14--16; II (9.4)--(9.6), printed p.212,
and (9.13)--(9.14), pp.215--216. Subgroup exponents use right conjugation;
aligned_dc_subgroup explicitly converts the consumer's ordered exchange
to the left commutator used in the subgroup argument.
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
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)

private theorem root_mem (k : Fin 6) (a : F) :
    (alignedSourceRoots Q split hK μ n short).x k a ∈ positiveCarrier Q split short k := by
  rw [← alignedSourceRoots_range Q split hK μ n short k]
  exact ⟨.ofAdd a,rfl⟩

private theorem ssq (i : Fin 2) : Q.simple i * Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem conjugate_commutator (A B : Subgroup (X ⧸ Q.D)) (v : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ v = ⁅rightConjugate A v,rightConjugate B v⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]

/-- The last root of a radical is disjoint from its three middle roots. -/
theorem terminal_disjoint_middle (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    Disjoint (rootAt Q split i (Q.simple j)) (middleRoots Q split i j) := by
  apply disjoint_def.mpr
  intro x hx hmemb
  have hm' := (middleRoots_eq_intersection Q split hm i j hij
    (representative (Q.simple j)) (representative_spec _) ▸ hmemb).2
  rw [rootAt_eq Q split i (Q.simple j) _ (representative_spec _)] at hx
  have he := disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) hx hm'
  apply (MulAut.conj (representative (Q.simple j) : X ⧸ Q.D)).injective
  simpa only [MulAut.conj_apply,MulEquiv.coe_toMonoidHom,map_one] using he

/-- The intersection of the two middle triples has exactly the two common factors. -/
theorem middle_intersection_two_coordinates (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (x : X ⧸ Q.D)
    (hi : x ∈ middleRoots Q split i j) (hj : x ∈ middleRoots Q split j i) :
    ∃ a ∈ rootAt Q split j (Q.simple i*Q.simple j),
      ∃ c ∈ rootAt Q split i (Q.simple j*Q.simple i), x = a*c := by
  have hx : x ∈ (middleRoots Q split j i : Set (X ⧸ Q.D)) := hj
  rw [middleRoots_product Q split hm j i hij.symm] at hx
  obtain ⟨da,⟨d,hd,a,ha,rfl⟩,c,hc,rfl⟩ := hx
  have haM : a ∈ middleRoots Q split i j :=
    (show rootAt Q split j (Q.simple i*Q.simple j) ≤ middleRoots Q split i j from le_sup_right) ha
  have hcM : c ∈ middleRoots Q split i j :=
    (show rootAt Q split i (Q.simple j*Q.simple i) ≤ middleRoots Q split i j from
      le_sup_right.trans le_sup_left) hc
  have hdM : d ∈ middleRoots Q split i j := by
    have ht := (middleRoots Q split i j).mul_mem hi
      ((middleRoots Q split i j).inv_mem ((middleRoots Q split i j).mul_mem haM hcM))
    simpa only [mul_assoc,mul_inv_rev,mul_inv_cancel_left,mul_inv_cancel,mul_one] using ht
  have hd1 := disjoint_def.mp (terminal_disjoint_middle Q split hm i j hij) hd hdM
  exact ⟨a,ha,c,hc,by simp only [hd1,one_mul]⟩

/-- The actual long reflection carries the DC image onto the FC image;
only its geometric normalization of C is used, not pointwise fixation. -/
theorem fc_subgroup_of_dc (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hdc : ⁅rootAt Q split i (Q.simple j),rootAt Q split i (Q.simple j*Q.simple i)⁆ =
      rootAt Q split j (Q.simple i*Q.simple j)) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ =
      rootAt Q split j (Q.simple i) := by
  have he := congrArg (fun A => rightConjugate A (representative (Q.simple j) : X ⧸ Q.D)) hdc
  rw [conjugate_commutator,rootAt_right Q split _ _ _ _ (representative_spec _),
    rootAt_right Q split _ _ _ _ (representative_spec _),
    rootAt_right Q split _ _ _ _ (representative_spec _),ssq,rootAt_one,
    orthogonal_root_stabilizer Q split hm i j hij,mul_assoc,ssq,mul_one] at he
  exact he

/-- The normalized DC equation identifies the entire source root commutator. -/
theorem aligned_dc_subgroup
    (hdc : ∀ d c, (alignedSourceRoots Q split hK μ n short).x 3 d *
      (alignedSourceRoots Q split hK μ n short).x 2 c =
      (alignedSourceRoots Q split hK μ n short).x 0 (c*d) *
      (alignedSourceRoots Q split hK μ n short).x 2 c *
      (alignedSourceRoots Q split hK μ n short).x 3 d) :
    ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 2⁆ =
      positiveCarrier Q split short 0 := by
  have he (d c : F) : ⁅(alignedSourceRoots Q split hK μ n short).x 3 d,
      (alignedSourceRoots Q split hK μ n short).x 2 c⁆ =
        (alignedSourceRoots Q split hK μ n short).x 0 (c*d) := by
    rw [commutatorElement_def,hdc]
    simp only [mul_assoc,mul_inv_cancel,mul_one]
  apply le_antisymm
  · apply commutator_le.mpr
    intro d hd c hc
    rw [← alignedSourceRoots_range Q split hK μ n short 3] at hd
    rw [← alignedSourceRoots_range Q split hK μ n short 2] at hc
    obtain ⟨d,rfl⟩ := hd
    obtain ⟨c,rfl⟩ := hc
    exact he d.toAdd c.toAdd ▸ root_mem Q split hK μ n short 0 (c.toAdd*d.toAdd)
  · intro a ha
    rw [← alignedSourceRoots_range Q split hK μ n short 0] at ha
    obtain ⟨a,rfl⟩ := ha
    have hh := commutator_mem_commutator
      (root_mem Q split hK μ n short 3 1) (root_mem Q split hK μ n short 2 a.toAdd)
    rw [he,mul_one] at hh
    simpa only [PositiveRoots.x,ofAdd_toAdd] using hh

include hK μ in
/-- The nonzero DC image forces all three orthogonal commutators to vanish.
This is the radical-derived argument of II (9.4)--(9.5), including q=2. -/
theorem orthogonal_commutator_eq_bot_of_dc (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hdc : ⁅rootAt Q split i (Q.simple j),rootAt Q split i (Q.simple j*Q.simple i)⁆ =
      rootAt Q split j (Q.simple i*Q.simple j)) :
    ⁅simpleRoot Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥ := by
  let A := rootAt Q split j (Q.simple i*Q.simple j)
  let B := rootAt Q split j (Q.simple i)
  let C := rootAt Q split i (Q.simple j*Q.simple i)
  let D := rootAt Q split i (Q.simple j)
  let K := ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆
  have hKm : K ≤ middleRoots Q split j i :=
    radical_commutator_le_middle_of_linear Q split hm j i hij.symm (hK j) (μ j)
  have hBD : Disjoint B K :=
    (terminal_disjoint_middle Q split hm j i hij.symm).mono_right hKm
  have hDK : D ≤ simpleRemainder Q split i :=
    (show D ≤ middleRoots Q split j i from le_sup_left.trans le_sup_left).trans
      (middleRoots_le_remainder Q split hm j i hij.symm)
  have hCK : C ≤ simpleRemainder Q split i :=
    (show C ≤ middleRoots Q split j i from le_sup_right).trans
      (middleRoots_le_remainder Q split hm j i hij.symm)
  have hAK : A ≤ K := calc
    A = ⁅D,C⁆ := hdc.symm
    _ ≤ K := commutator_mono hDK hCK
  have hUN : split.U ≤ normalizer (K : Set (X ⧸ Q.D)) :=
    split.U_le.trans ((Q.tits.B_le_standardParabolic _).trans
      (radical_commutator_normalized Q split i (hK i)))
  have hFC : ⁅simpleRoot Q split i,C⁆ = B := fc_subgroup_of_dc Q split hm i j hij hdc
  have hCD : Disjoint C K := by
    by_contra hn
    have hne : C ⊓ K ≠ ⊥ := fun he => hn (disjoint_iff.mpr he)
    have hH : Q.tits.B ⊓ Q.tits.N ≤ normalizer ((C ⊓ K : Subgroup (X ⧸ Q.D)) : Set _) :=
      (le_inf (rootAt_torus_normalizes Q split i _)
        (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans
          (radical_commutator_normalized Q split i (hK i))))).trans inf_normalizer_le_normalizer_inf
    have he := QuadrangleStructure.rootAt_eq_of_torus_invariant Q split i (μ i) (hK i)
      (Q.simple j*Q.simple i) (C ⊓ K) inf_le_left hne hH
    have hCK' : C ≤ K := calc
      C = C ⊓ K := he.symm
      _ ≤ K := inf_le_right
    have hBK : B ≤ K := calc
      B = ⁅simpleRoot Q split i,C⁆ := hFC.symm
      _ ≤ K := (commutator_mono le_rfl hCK').trans
        (le_normalizer_iff_commutator_le_right.mp ((simpleRoot_le Q split i).trans hUN))
    exact rootAt_ne_bot Q split j (Q.simple i)
      (eq_bot_iff.mpr fun x hx => mem_bot.mpr (disjoint_def.mp hBD hx (hBK hx)))
  have hDB : ⁅D,B⁆ ≤ A := by
    have hBVi : B ≤ simpleRemainder Q split i :=
      (exchanged_roots_le_remainder Q split hm j i hij.symm).1
    have hDVi : D ≤ simpleRemainder Q split j :=
      (exchanged_roots_le_remainder Q split hm i j hij).1
    have hBVj : B ≤ simpleRemainder Q split j :=
      (show B ≤ middleRoots Q split i j from le_sup_left.trans le_sup_left).trans
        (middleRoots_le_remainder Q split hm i j hij)
    have hDBK := commutator_mono hDK hBVi
    have hDBM := (commutator_mono hDVi hBVj).trans
      (radical_commutator_le_middle_of_linear Q split hm i j hij (hK i) (μ i))
    intro x hx
    obtain ⟨a,ha,c,hc,he⟩ := middle_intersection_two_coordinates Q split hm i j hij x
      (hDBM hx) (hKm (hDBK hx))
    have hcK : c ∈ K := by
      have ht := K.mul_mem (K.inv_mem (hAK ha)) (hDBK hx)
      simpa only [he,inv_mul_cancel_left] using ht
    have hc1 := disjoint_def.mp hCD hc hcK
    simpa only [he,hc1,mul_one] using ha
  have hFA : ⁅simpleRoot Q split i,A⁆ ≤ B := by
    have ht := comap_mono (f := (MulAut.conj (representative (Q.simple j) : X ⧸ Q.D)).toMonoidHom) hDB
    change rightConjugate ⁅D,B⁆ _ ≤ rightConjugate A _ at ht
    dsimp only [A,B,D] at ht
    rw [conjugate_commutator,rootAt_right Q split _ _ _ _ (representative_spec _),
      rootAt_right Q split _ _ _ _ (representative_spec _),
      rootAt_right Q split _ _ _ _ (representative_spec _),ssq,rootAt_one,
      mul_assoc,ssq,mul_one] at ht
    exact ht
  have hFA0 : ⁅simpleRoot Q split i,A⁆ = ⊥ := by
    have hFK := (commutator_mono le_rfl hAK).trans
      (le_normalizer_iff_commutator_le_right.mp ((simpleRoot_le Q split i).trans hUN))
    exact bot_unique ((le_inf hFA hFK).trans (disjoint_iff.mp hBD).le)
  have hDB0 := congrArg (fun V => rightConjugate V (representative (Q.simple j) : X ⧸ Q.D)) hFA0
  dsimp only [A] at hDB0
  rw [conjugate_commutator,←rootAt_eq Q split i (Q.simple j) _ (representative_spec _),
    rootAt_right Q split _ _ _ _ (representative_spec _),mul_assoc,ssq,mul_one] at hDB0
  have hDB0' : ⁅D,B⁆ = ⊥ := hDB0.trans (by
    simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot])
  have hCE0 := congrArg (fun V => rightConjugate V (representative (Q.simple i) : X ⧸ Q.D)) hDB0'
  dsimp only [D,B] at hCE0
  rw [conjugate_commutator,rootAt_right Q split _ _ _ _ (representative_spec _),
    rootAt_right Q split _ _ _ _ (representative_spec _),ssq,rootAt_one,commutator_comm] at hCE0
  exact hCE0.trans (by simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot])

/-- No separate EC premise is needed once the DC field equation is proved. -/
theorem aligned_ec_of_dc (hm : rotationOrder Q = 6)
    (hdc : ∀ d c, (alignedSourceRoots Q split hK μ n short).x 3 d *
      (alignedSourceRoots Q split hK μ n short).x 2 c =
      (alignedSourceRoots Q split hK μ n short).x 0 (c*d) *
      (alignedSourceRoots Q split hK μ n short).x 2 c *
      (alignedSourceRoots Q split hK μ n short).x 3 d) :
    ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 2⁆ = ⊥ :=
  orthogonal_commutator_eq_bot_of_dc Q split hK μ hm short (1-short)
    (by fin_cases short <;> decide) (aligned_dc_subgroup Q split hK μ n short hdc)

/-- DC also forces BA: B centralizes both C and D, hence their commutator A. -/
theorem aligned_ba_of_dc (hm : rotationOrder Q = 6)
    (hdc : ∀ d c, (alignedSourceRoots Q split hK μ n short).x 3 d *
      (alignedSourceRoots Q split hK μ n short).x 2 c =
      (alignedSourceRoots Q split hK μ n short).x 0 (c*d) *
      (alignedSourceRoots Q split hK μ n short).x 2 c *
      (alignedSourceRoots Q split hK μ n short).x 3 d) :
    ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥ := by
  have hec := aligned_ec_of_dc Q split hK μ n short hm hdc
  have hdb := congrArg (fun V => rightConjugate V
    (representative (Q.simple short) : X ⧸ Q.D)) hec
  change rightConjugate ⁅simpleRoot Q split (1-short),
    rootAt Q split short (Q.simple (1-short)*Q.simple short)⁆ _ = _ at hdb
  rw [conjugate_commutator,←rootAt_eq Q split (1-short) (Q.simple short) _ (representative_spec _),
    rootAt_right Q split _ _ _ _ (representative_spec _),mul_assoc,ssq,mul_one,commutator_comm] at hdb
  have hdb' : ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 1⁆ = ⊥ :=
    hdb.trans (by simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot])
  have hcb := (positiveCarrier_adjacent_commutators Q split hm hK short).2.1
  have hA : positiveCarrier Q split short 0 ≤
      centralizer (positiveCarrier Q split short 1 : Set (X ⧸ Q.D)) := by
    rw [←aligned_dc_subgroup Q split hK μ n short hdc]
    exact (Subgroup.commutator_le_sup _ _).trans
      (sup_le (commutator_eq_bot_iff_le_centralizer.mp hdb')
        (commutator_eq_bot_iff_le_centralizer.mp hcb))
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hA

/-- Both remaining source commutation clauses now follow from the mixed data. -/
theorem aligned_commutators_of_lower (hm : rotationOrder Q = 6)
    (d : LowerPositiveData (alignedSourceRoots Q split hK μ n short)) :
    ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥ ∧
    ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 2⁆ = ⊥ :=
  ⟨aligned_ba_of_dc Q split hK μ n short hm d.dc,
    aligned_ec_of_dc Q split hK μ n short hm d.dc⟩

/-- The entire commutation table and FC are derived before filling the old input. -/
def aligned_partial_of_mixed (hm : rotationOrder Q = 6)
    (d : LowerPositiveData (alignedSourceRoots Q split hK μ n short)) :
    PartialPositiveData (alignedSourceRoots Q split hK μ n short) :=
  aligned_partial_of_lower Q split hK μ n short hm
    (aligned_commutators_of_lower Q split hK μ n short hm d).1
    (aligned_commutators_of_lower Q split hK μ n short hm d).2 d

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
