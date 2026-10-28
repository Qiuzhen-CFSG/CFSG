module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.OrthogonalRoots

/-!
# Geometric reduction of the lower positive G₂ equations

Relative normality of the canonical parabolic radicals and the two-root
ordered factorization put the commutator of two adjacent roots in the
second root. Applying the same argument in the opposite orientation and
transporting by the actual Weyl group puts it in the first root. Their
intersection is trivial. Conjugating gives all five adjacent pairs in
the A--F order, without any field coordinates or field-size restriction.

The other positive commuting pairs form two Weyl orbits. Thus the entire
ten-pair table requires only the BA clause of Fong--Seitz II (9.2) and
the EC clause of (9.5). From EC, the existing orthogonal-root argument
makes the long rank-one group centralize C. Conjugating DC by its actual
reflection then proves FC, with exactly the consumer's left-conjugation
and parameter conventions.

LowerPositiveData retains DC, FD, EB containment and normalization, the
lower FE coefficients and the auxiliary torus. These, and the two source
commutator clauses, are still obligations of source reconstruction. No
coupled-module identification or complete 6E(a) -> 9A theorem is claimed.
The resulting PartialPositiveData is consumed by LowerPositiveApplication
on the same marked quotient, including q=2, q=4 and both orientations.

Source: Fong--Seitz I (3G), pp.14--16, and (5C), pp.25--26;
II (9.2), (9.5), (9.13)--(9.16), pp.211--216.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open RootCoordinates HexagonStructure Atlas.G2.RootPresentationRecognition
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem ssq (i : Fin 2) : Q.simple i * Q.simple i = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem i)).2

private theorem conjugate_commutator (A B : Subgroup (X ⧸ Q.D)) (v : X ⧸ Q.D) :
    rightConjugate ⁅A,B⁆ v = ⁅rightConjugate A v,rightConjugate B v⁆ := by
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]

private theorem adjacent_product (i j : Fin 2) (hij : i ≠ j) :
    ((simpleRoot Q split i ⊔ rootAt Q split j (Q.simple i) : Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split i : Set (X ⧸ Q.D)) * (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) := by
  have h (b : Bool) := orderedRoots_product Q split b 2 (rotationOrder_ge_two Q)
  have hlist (b : Bool) : orderedRoots Q split b 2 =
      [simpleRoot Q split (if b then 1 else 0),
       rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0))] := by
    cases b <;> rfl
  have hh (b : Bool) :
      ((simpleRoot Q split (if b then 1 else 0) ⊔
        rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)) :
          Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
      (simpleRoot Q split (if b then 1 else 0) : Set (X ⧸ Q.D)) *
        (rootAt Q split (if b then 0 else 1) (Q.simple (if b then 1 else 0)) : Set (X ⧸ Q.D)) := by
    have he := h b
    rw [hlist b] at he
    change _ * (_ * 1) = _ at he
    rw [mul_one] at he
    rw [sup_eq_closure_mul,he,closure_eq]
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact hh false
  · exact hh true
  · exact (hij rfl).elim

private theorem adjacent_commutator_le (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i) :
    ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i)⁆ ≤ rootAt Q split j (Q.simple i) := by
  have hB := (exchanged_roots_le_remainder Q split hm j i hij.symm).1
  have hn := (simpleRoot_le Q split i).trans (split.U_le.trans
    ((Q.tits.B_le_standardParabolic _).trans (remainder_parabolic_normalizes Q split i hKi)))
  have hc := (commutator_mono le_rfl hB).trans
    (le_normalizer_iff_commutator_le_right.mp hn)
  intro x hx
  have hxV := hc hx
  have hxprod : x ∈ ((simpleRoot Q split i ⊔ rootAt Q split j (Q.simple i) :
      Subgroup (X ⧸ Q.D)) : Set (X ⧸ Q.D)) := Subgroup.commutator_le_sup _ _ hx
  rw [adjacent_product Q split i j hij] at hxprod
  obtain ⟨a,ha,b,hb,rfl⟩ := hxprod
  have haV : a ∈ simpleRemainder Q split i := by
    have he := (simpleRemainder Q split i).mul_mem hxV
      ((simpleRemainder Q split i).inv_mem (hB hb))
    simpa only [mul_inv_cancel_right] using he
  have he : a = 1 := (disjoint_iff.mp (simpleRoot_disjoint_remainder Q split i)).le ⟨ha,haV⟩
  change a*b ∈ rootAt Q split j (Q.simple i)
  rw [he,one_mul]
  exact hb

private theorem rootAt_four (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j*Q.simple i) =
      rootAt Q split i (Q.simple j) := by
  rw [← rootAt_right Q split i _ (Q.simple i) (representative (Q.simple i)) (representative_spec _),
    orthogonal_root_stabilizer Q split hm i j hij,
    rootAt_right Q split i _ (Q.simple i) (representative (Q.simple i)) (representative_spec _),
    mul_assoc,ssq,mul_one]

private theorem rootAt_five (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) :
    rootAt Q split i (Q.simple j*Q.simple i*Q.simple j*Q.simple i*Q.simple j) =
      simpleRoot Q split i := by
  rw [← rootAt_right Q split i _ (Q.simple j) (representative (Q.simple j)) (representative_spec _),
    rootAt_four Q split hm i j hij,
    rootAt_right Q split i _ (Q.simple j) (representative (Q.simple j)) (representative_spec _),
    ssq,rootAt_one]

/-- Consecutive roots commute using both actual radical normalizers. -/
theorem adjacent_source_roots_commute (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) :
    ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i)⁆ = ⊥ := by
  have hfirst := adjacent_commutator_le Q split hm i j hij hKi
  have hother := adjacent_commutator_le Q split hm j i hij.symm hKj
  let w := Q.simple i*Q.simple j*Q.simple i*Q.simple j
  let v := representative w
  have ht := comap_mono (f := (MulAut.conj (v : X ⧸ Q.D)).toMonoidHom) hother
  change rightConjugate _ (v : X ⧸ Q.D) ≤ rightConjugate _ (v : X ⧸ Q.D) at ht
  rw [conjugate_commutator,← rootAt_eq Q split j w v (representative_spec w),
    rootAt_right Q split i (Q.simple j) w v (representative_spec w)] at ht
  have hj : rootAt Q split j w = rootAt Q split j (Q.simple i) :=
    rootAt_four Q split hm j i hij.symm
  have hi : rootAt Q split i (Q.simple j*w) = simpleRoot Q split i := by
    simpa only [w,mul_assoc] using rootAt_five Q split hm i j hij
  rw [hj,hi,commutator_comm] at ht
  exact bot_unique ((le_inf ht hfirst).trans
    (disjoint_iff.mp ((simpleRoot_disjoint_remainder Q split i).mono_right
      (exchanged_roots_le_remainder Q split hm j i hij.symm).1)).le)


private theorem conjugate_bot {A B : Subgroup (X ⧸ Q.D)} (h : ⁅A,B⁆ = ⊥) (v : X ⧸ Q.D) :
    ⁅rightConjugate A v,rightConjugate B v⁆ = ⊥ := by
  rw [← conjugate_commutator,h]
  simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]

/-- Five adjacent positive pairs commute before choosing field labels. -/
theorem positiveCarrier_adjacent_commutators (hm : rotationOrder Q = 6)
    (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i) (short : Fin 2) :
    ⁅positiveCarrier Q split short 2,positiveCarrier Q split short 0⁆ = ⊥ ∧
    ⁅positiveCarrier Q split short 2,positiveCarrier Q split short 1⁆ = ⊥ ∧
    ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 0⁆ = ⊥ ∧
    ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 3⁆ = ⊥ ∧
    ⁅positiveCarrier Q split short 5,positiveCarrier Q split short 1⁆ = ⊥ := by
  have hij : short ≠ 1-short := by fin_cases short <;> decide
  have fb := adjacent_source_roots_commute Q split hm short (1-short) hij (hK short) (hK (1-short))
  have ed := adjacent_source_roots_commute Q split hm (1-short) short hij.symm (hK (1-short)) (hK short)
  have da := conjugate_bot Q fb (representative (Q.simple (1-short)) : X ⧸ Q.D)
  rw [← rootAt_eq Q split short (Q.simple (1-short)) _ (representative_spec _),
    rootAt_right Q split (1-short) (Q.simple short) (Q.simple (1-short)) _ (representative_spec _)] at da
  have ca := conjugate_bot Q da (representative (Q.simple short) : X ⧸ Q.D)
  rw [rootAt_right Q split short (Q.simple (1-short)) (Q.simple short) _ (representative_spec _),
    rootAt_right Q split (1-short) (Q.simple short*Q.simple (1-short)) (Q.simple short) _ (representative_spec _),
    orthogonal_root_stabilizer Q split hm (1-short) short hij.symm] at ca
  have bc := conjugate_bot Q ed (representative (Q.simple short) : X ⧸ Q.D)
  rw [← rootAt_eq Q split (1-short) (Q.simple short) _ (representative_spec _),
    rootAt_right Q split short (Q.simple (1-short)) (Q.simple short) _ (representative_spec _),
    commutator_comm] at bc
  exact ⟨ca,bc,da,ed,fb⟩

/-- Apart from the adjacent pairs, the three orthogonal pairs are Weyl
conjugate, and the two long-root pairs are Weyl conjugate. -/
theorem positiveCarrier_remaining_commutators (hm : rotationOrder Q = 6) (short : Fin 2)
    (hba : ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥)
    (hec : ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 2⁆ = ⊥) :
    ⁅positiveCarrier Q split short 3,positiveCarrier Q split short 1⁆ = ⊥ ∧
    ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 0⁆ = ⊥ ∧
    ⁅positiveCarrier Q split short 5,positiveCarrier Q split short 0⁆ = ⊥ := by
  have hij : short ≠ 1-short := by fin_cases short <;> decide
  change ⁅rootAt Q split (1-short) (Q.simple short),
    rootAt Q split (1-short) (Q.simple short*Q.simple (1-short))⁆ = ⊥ at hba
  change ⁅simpleRoot Q split (1-short),
    rootAt Q split short (Q.simple (1-short)*Q.simple short)⁆ = ⊥ at hec
  have ea := conjugate_bot Q hba (representative (Q.simple short) : X ⧸ Q.D)
  rw [rootAt_right Q split (1-short) (Q.simple short) (Q.simple short) _ (representative_spec _),
    rootAt_right Q split (1-short) (Q.simple short*Q.simple (1-short)) (Q.simple short) _ (representative_spec _),
    ssq,rootAt_one,orthogonal_root_stabilizer Q split hm (1-short) short hij.symm] at ea
  have db := conjugate_bot Q hec (representative (Q.simple short) : X ⧸ Q.D)
  rw [← rootAt_eq Q split (1-short) (Q.simple short) _ (representative_spec _),
    rootAt_right Q split short (Q.simple (1-short)*Q.simple short) (Q.simple short) _ (representative_spec _),
    mul_assoc,ssq,mul_one,commutator_comm] at db
  have fa := conjugate_bot Q db (representative (Q.simple (1-short)) : X ⧸ Q.D)
  rw [rootAt_right Q split short (Q.simple (1-short)) (Q.simple (1-short)) _ (representative_spec _),
    rootAt_right Q split (1-short) (Q.simple short) (Q.simple (1-short)) _ (representative_spec _),
    ssq,rootAt_one] at fa
  exact ⟨db,ea,fa⟩

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
  (hK : ∀ i, simpleRemainder Q split i ≤ localKernel Q i)
  (μ : ∀ i, localGroup Q split i ≃* PSL(2,F))
  (n : ∀ i, RootReflection Q split i) (short : Fin 2)

/-- The source commutation table reduces to (9.2) and the EC member of (9.5).
All eight other pairs follow from geometry and relative radical normality. -/
theorem aligned_commuting_of_two (hm : rotationOrder Q = 6)
    (hba : ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥)
    (hec : ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 2⁆ = ⊥) :
    (alignedSourceRoots Q split hK μ n short).CommutingRelations := by
  obtain ⟨ca,cb,da,ed,fb⟩ := positiveCarrier_adjacent_commutators Q split hm hK short
  obtain ⟨db,ea,fa⟩ := positiveCarrier_remaining_commutators Q split hm short hba hec
  have hc (i j : Fin 6) (h : ⁅positiveCarrier Q split short i,positiveCarrier Q split short j⁆ = ⊥)
      (a b : F) :
      (alignedSourceRoots Q split hK μ n short).x i a * (alignedSourceRoots Q split hK μ n short).x j b =
      (alignedSourceRoots Q split hK μ n short).x j b * (alignedSourceRoots Q split hK μ n short).x i a := by
    have hx (k : Fin 6) (c : F) : (alignedSourceRoots Q split hK μ n short).x k c ∈
        positiveCarrier Q split short k := by
      rw [← alignedSourceRoots_range Q split hK μ n short k]
      exact ⟨.ofAdd c,rfl⟩
    exact (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp h) (hx i a)) _ (hx j b)).symm
  exact ⟨hc 1 0 hba,hc 2 0 ca,hc 2 1 cb,hc 3 0 da,hc 3 1 db,
    hc 4 0 ea,hc 4 2 hec,hc 4 3 ed,hc 5 0 fa,hc 5 1 fb⟩


/-- The DC exchange determines FC by the actual long source reflection.
The sole centralization input is the EC member of (9.5). -/
theorem aligned_fc_of_dc (hm : rotationOrder Q = 6)
    (hec : ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 2⁆ = ⊥)
    (hdc : ∀ d c, (alignedSourceRoots Q split hK μ n short).x 3 d *
      (alignedSourceRoots Q split hK μ n short).x 2 c =
      (alignedSourceRoots Q split hK μ n short).x 0 (c*d) *
      (alignedSourceRoots Q split hK μ n short).x 2 c *
      (alignedSourceRoots Q split hK μ n short).x 3 d) (z c : F) :
    (alignedSourceRoots Q split hK μ n short).x 5 z *
      (alignedSourceRoots Q split hK μ n short).x 2 c =
      (alignedSourceRoots Q split hK μ n short).x 1 (c*z) *
      (alignedSourceRoots Q split hK μ n short).x 2 c *
      (alignedSourceRoots Q split hK μ n short).x 5 z := by
  let d := sourceBorelWeyl Q split hK μ n short split.abelian
  have hij : short ≠ 1-short := by fin_cases short <;> decide
  have hc := rankOne_centralizes_orthogonal_of_simple Q split hm short (1-short) hij (n (1-short))
    (commutator_eq_bot_iff_le_centralizer.mp hec)
  have hC (a : F) : MulAut.conj d.r (d.x 2 a) = d.x 2 a := by
    have hx : d.x 2 a ∈ positiveCarrier Q split short 2 := by
      rw [← alignedSourceRoots_range Q split hK μ n short 2]
      exact ⟨.ofAdd a,rfl⟩
    change d.r * d.x 2 a * d.r⁻¹ = d.x 2 a
    have hh : d.x 2 a*d.r = d.r*d.x 2 a :=
      mem_centralizer_iff.mp (hc (n (1-short)).mem_rankOne) _ hx
    rw [← hh,mul_assoc,mul_inv_cancel,mul_one]
  have hD (a : F) : MulAut.conj d.r (d.x 3 a) = d.x 5 a :=
    sourceBorelWeyl_rD Q split hK μ n short split.abelian a
  have hA (a : F) : MulAut.conj d.r (d.x 0 a) = d.x 1 a :=
    sourceBorelWeyl_rA Q split hK μ n short split.abelian a
  have he := congrArg (MulAut.conj d.r) (hdc z c)
  change MulAut.conj d.r (d.x 3 z*d.x 2 c) =
    MulAut.conj d.r (d.x 0 (c*z)*d.x 2 c*d.x 3 z) at he
  simp only [map_mul,hD,hC,hA] at he
  exact he

/-- The remaining mixed-module input. The eight redundant commutations,
FC, and highest-root injectivity are deliberately absent. This record is
an intermediate obligation, not a consequence of 6E(a) established here. -/
structure LowerPositiveData {K Y : Type*} [Field K] [Group Y] (L : PositiveRoots K Y) where
  dc : ∀ d c, L.x 3 d * L.x 2 c = L.x 0 (c*d) * L.x 2 c * L.x 3 d
  fd : ∀ z d, L.x 5 z * L.x 3 d =
    L.x 0 (d^2*z) * L.x 1 (d*z^2) * L.x 3 d * L.x 5 z
  eb_mem : ∀ b e, ⁅L.x 4 e,L.x 1 b⁆ ∈ (L.root 0).range
  eb_one : ⁅L.x 4 1,L.x 1 1⁆ = L.x 0 1
  fe_mem : ∀ z e, ∃ a, L.x 5 z * L.x 4 e =
    L.x 0 a * L.x 1 (e*z^3) * L.x 2 (e*z^2) * L.x 3 (e*z) * L.x 4 e * L.x 5 z
  torus : Kˣ × Kˣ → Y
  torus_root : ∀ l m i a, torus (l,m)*L.x i a*(torus (l,m))⁻¹ =
    L.x i (BorelWeylData.weight l m i*a)

/-- Fill the literal old consumer using proved geometric commutations and FC.
The two earlier source clauses and mixed-module input remain explicit. -/
def aligned_partial_of_lower (hm : rotationOrder Q = 6)
    (hba : ⁅positiveCarrier Q split short 1,positiveCarrier Q split short 0⁆ = ⊥)
    (hec : ⁅positiveCarrier Q split short 4,positiveCarrier Q split short 2⁆ = ⊥)
    (d : LowerPositiveData (alignedSourceRoots Q split hK μ n short)) :
    PartialPositiveData (alignedSourceRoots Q split hK μ n short) where
  A_injective := alignedSourceRoots_injective Q split hK μ n short 0
  commuting := aligned_commuting_of_two Q split hK μ n short hm hba hec
  dc := d.dc
  fc := aligned_fc_of_dc Q split hK μ n short hm hec d.dc
  fd := d.fd
  eb_mem := d.eb_mem
  eb_one := d.eb_one
  fe_mem := d.fe_mem
  torus := d.torus
  torus_root := d.torus_root

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
