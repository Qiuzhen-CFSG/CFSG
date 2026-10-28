module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SixRootIntervals
public import Theory.Frattini.OmegaProducts

/-!
# The abelian-root three-subgroup argument in source (6H)(b)

When the near commutator vanishes, the perpendicular root centralizes
both adjacent roots and its near same-type root. If the simple root is
abelian, the six-root support theorem therefore places the commutator
of the two remaining roots in its centralizer. The three-subgroup lemma
and the reflected (6.4) equality force perpendicular Omega centralization.

Source: Fong--Seitz I (1973), p.53, the binary nonzero-(6.4) branch.
The CFSG BinaryTerminal consumer supplies abelianness from the actual
Sz(2) root and (6.4) from its proved nonzero-to-Omega upgrade. The argument
is restricted to abelian roots; no claim that a positive-parameter Suzuki
root lies in the center of a subgroup containing it is used.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i j : Fin 2)

private theorem ssq (k : Fin 2) : Q.simple k*Q.simple k=1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2
private theorem right_comm (A B : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate ⁅A,B⁆ (representative w : X ⧸ Q.D) =
      ⁅rightConjugate A (representative w : X ⧸ Q.D),
        rightConjugate B (representative w : X ⧸ Q.D)⁆ := by
  simp only [rightConjugate, comap_equiv_eq_map_symm', map_commutator]
private theorem right_bot (w : Weyl Q) :
    rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (representative w : X ⧸ Q.D) = ⊥ := by
  simp only [rightConjugate, comap_equiv_eq_map_symm', Subgroup.map_bot]
private theorem right_simple (k : Fin 2) (w : Weyl Q) :
    rightConjugate (simpleRoot Q split k) (representative w : X ⧸ Q.D) =
      rootAt Q split k w := rfl
private theorem right_rep (k : Fin 2) (v w : Weyl Q) :
    rightConjugate (rootAt Q split k v) (representative w : X ⧸ Q.D) =
      rootAt Q split k (v*w) := rootAt_right Q split k v w _ (representative_spec _)
private theorem right_omega (A : Subgroup (X ⧸ Q.D)) (w : Weyl Q) :
    rightConjugate (omegaOneAmbient A) (representative w : X ⧸ Q.D) =
      omegaOneAmbient (rightConjugate A (representative w : X ⧸ Q.D)) := by
  simp only [rightConjugate, comap_equiv_eq_map_symm']
  exact map_omegaOneAmbient_injective _ (MulEquiv.injective _) _

/-- For an abelian simple root, the nonzero-(6.4) branch forces the perpendicular Omega commutator to vanish. -/
theorem abelian_omega_perpendicular_of_near_trivial_of_six_four
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (hab : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (hnear : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥)
    (hfour : ⁅simpleRoot Q split i,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ =
      omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i))) :
    ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ := by
  let E := rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)
  have hCE : ⁅rootAt Q split i (Q.simple j),E⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple j) : X ⧸ Q.D)) hnear
    simpa only [right_comm,right_bot,right_simple,right_rep] using hh
  have hDE : ⁅rootAt Q split j (Q.simple i*Q.simple j),E⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple i*Q.simple j) : X ⧸ Q.D))
      (adjacent_commutator_eq_bot Q split hm j i hij.symm hKj hKi)
    simpa only [right_comm,right_bot,right_simple,right_rep,←mul_assoc] using hh
  have hED : ⁅E,rootAt Q split j (Q.simple i*Q.simple j*Q.simple i)⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D))
      (adjacent_commutator_eq_bot Q split hm i j hij hKi hKj)
    rw [right_comm,right_bot,right_simple,
      (four_interval_reflection Q split hm i j hij _ (representative_spec _)).1] at hh
    exact hh
  have hEE : ⁅E,E⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)) hab
    simpa only [right_comm,right_bot,right_simple] using hh
  have hbase : ⁅⁅simpleRoot Q split j,rootAt Q split i (Q.simple j*Q.simple i)⁆,E⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro x hx
    obtain ⟨bcd,⟨bc,⟨b,hb,c,hc,rfl⟩,d,hd,rfl⟩,e,he,rfl⟩ :=
      distance_five_commutator_support Q split hm j i hij.symm hKj hKi x hx
    exact (centralizer (E : Set (X ⧸ Q.D))).mul_mem
      ((centralizer (E : Set (X ⧸ Q.D))).mul_mem
        ((centralizer (E : Set (X ⧸ Q.D))).mul_mem
          (commutator_eq_bot_iff_le_centralizer.mp hCE hb)
          (commutator_eq_bot_iff_le_centralizer.mp hDE hc))
        (commutator_eq_bot_iff_le_centralizer.mp hEE hd))
      (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hED) he)
  have hrot : ⁅⁅rootAt Q split j (Q.simple i),rootAt Q split i (Q.simple j)⁆,E⁆ = ⊥ := by
    have hh := congrArg (fun A => rightConjugate A (representative (Q.simple i) : X ⧸ Q.D)) hbase
    rw [right_comm,right_comm,right_bot,right_simple,
      show rightConjugate E (representative (Q.simple i) : X ⧸ Q.D) = E from
        perpendicular_root_stable Q split hm i j hij _ (representative_spec _),right_rep] at hh
    simpa only [mul_assoc,ssq,mul_one] using hh
  have htriple : ⁅⁅E,rootAt Q split j (Q.simple i)⁆,rootAt Q split i (Q.simple j)⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hrot (by rw [hCE,commutator_bot_left])
  have hfour' : ⁅E,rootAt Q split j (Q.simple i)⁆ =
      omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i)) := by
    have hh := congrArg (fun A => rightConjugate A
      (representative (Q.simple j*Q.simple i*Q.simple j) : X ⧸ Q.D)) hfour
    rw [right_comm,right_simple,right_omega,
      (four_interval_reflection Q split hm i j hij _ (representative_spec _)).2.1,
      (four_interval_reflection Q split hm i j hij _ (representative_spec _)).2.2] at hh
    exact hh
  rw [hfour'] at htriple
  have hh := congrArg (fun A => rightConjugate A
    (representative (Q.simple i*Q.simple j) : X ⧸ Q.D)) htriple
  simpa only [right_comm,right_bot,right_omega,right_rep,mul_assoc,
    ←mul_assoc (Q.simple i) (Q.simple i),ssq,one_mul,mul_one,rootAt_one] using hh

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
