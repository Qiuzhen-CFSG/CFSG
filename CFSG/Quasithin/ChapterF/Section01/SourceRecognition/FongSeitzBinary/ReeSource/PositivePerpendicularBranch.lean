module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PerpendicularSupport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SmallCharacteristic
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OmegaNonzero

/-!
# Perpendicular support in the vanishing near-commutator branch

If the whole perpendicular Suzuki root lies in the actual radical Frattini
subgroup, its Omega lies in the second Frattini subgroup. The positive
Suzuki actor centralizes that small characteristic subgroup. Right conjugation
by the perpendicular reflection word therefore makes the simple-root Omega
centralize the perpendicular root. The existing generation and (6.1)
arguments then force the near commutator to fill the intervening linear root.

Consequently, in the remaining near-zero branch, both the Frattini and
positive-parameter derived intersections with the perpendicular root equal
precisely its Omega. This removes the whole-root alternative in that branch;
it does not assert that the near-zero branch itself has been excluded.

Source: Fong--Seitz I (1973), pp.52--53, the perpendicular support argument
in (6H)(b). The literal panel markings, independent-field size comparison,
and both endpoint orientations are retained. OriginalPerpendicularBranch
applies the result to the original cores and the actual quotient Q.q.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i j : Fin 2)
  (m : ℕ) (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (n : ℕ) (hn : 0 < n)
  (ν : (Endpoint Q j ⧸ panelKernel Q j) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q j).map ν.toMonoidHom = normalizer (T : Set _))

private theorem ssq (k : Fin 2) : Q.simple k*Q.simple k = 1 := by
  simpa only [pow_two] using (Q.tits.involutions _ (Q.simple_mem k)).2

include μ hB in
private theorem omega_le_frattini_of_root_le (w : Weyl Q)
    (D : Subgroup (X ⧸ Q.D)) (hD : IsPGroup 2 D)
    (hA : rootAt Q split i w ≤ D) :
    omegaOneAmbient (rootAt Q split i w) ≤ (frattini D).map D.subtype := by
  let e := (MulAut.conj (representative w : X ⧸ Q.D)).symm
  have he : (simpleRoot Q split i).map e.toMonoidHom = rootAt Q split i w := by
    simp only [rootAt,rightConjugate,comap_equiv_eq_map_symm']; rfl
  have hΩ : omegaOneAmbient (rootAt Q split i w) =
      (frattini (rootAt Q split i w)).map (rootAt Q split i w).subtype := by
    rw [←he,frattini_image_map _ _ e.injective,
      suzuki_frattini_image Q split i m μ hB,
      map_omegaOneAmbient_injective e.toMonoidHom e.injective]
  rw [hΩ]
  exact frattini_image_le_of_le hA hD

include μ hB ν hC in
/-- Perpendicular Frattini containment forces the required Omega centralization. -/
theorem source_positive_omega_perpendicular_of_frattini
    (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : (Nat.card (BinaryGaloisField n))^4 < (2^(2*m+1))^6)
    (hE : rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
      (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype) :
    ⁅omegaOneAmbient (simpleRoot Q split i),
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)⁆ = ⊥ := by
  let hV := marked_suzuki_remainder_le_kernel Q split i m μ hB
  let d := frattiniRadicalSection Q split i hV
  let w := Q.simple j*Q.simple i*Q.simple j
  have hΩ : omegaOneAmbient (rootAt Q split i w) ≤ centralizer
      (rankOne Q split i : Set (X ⧸ Q.D)) :=
    (omega_le_frattini_of_root_le Q split i m μ hB w d.numerator d.isTwo hE).trans
      (source_positive_small_characteristic_centralizes Q split i j ν T hC m μ hB
        hmpos hc hm hij hsize).1
  have hcomm : ⁅omegaOneAmbient (rootAt Q split i w),simpleRoot Q split i⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (hΩ.trans (centralizer_le (show (simpleRoot Q split i : Set (X ⧸ Q.D)) ⊆
        (rankOne Q split i : Set (X ⧸ Q.D)) from (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left))))
  have hh := congrArg (fun A : Subgroup (X ⧸ Q.D) =>
    rightConjugate A (representative w : X ⧸ Q.D)) hcomm
  have hw : w*w = 1 := by
    dsimp only [w]
    simp only [mul_assoc,←mul_assoc (Q.simple j) (Q.simple j),ssq,
      ←mul_assoc (Q.simple i) (Q.simple i),one_mul]
  have hω : rightConjugate (omegaOneAmbient (rootAt Q split i w))
      (representative w : X ⧸ Q.D) = omegaOneAmbient (simpleRoot Q split i) := by
    change (omegaOneAmbient (rootAt Q split i w)).comap
      (MulAut.conj (representative w : X ⧸ Q.D)).toMonoidHom = _
    rw [comap_equiv_eq_map_symm',map_omegaOneAmbient_injective _ (MulEquiv.injective _)]
    rw [←comap_equiv_eq_map_symm']
    change omegaOneAmbient (rightConjugate (rootAt Q split i w)
      (representative w : X ⧸ Q.D)) = _
    rw [rootAt_right Q split i _ _ _ (representative_spec _),hw,rootAt_one]
  have hr (A B : Subgroup (X ⧸ Q.D)) : rightConjugate ⁅A,B⁆ (representative w : X ⧸ Q.D) =
      ⁅rightConjugate A (representative w : X ⧸ Q.D),
        rightConjugate B (representative w : X ⧸ Q.D)⁆ := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
  have hb : rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (representative w : X ⧸ Q.D) = ⊥ := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',Subgroup.map_bot]
  rw [hr,hω,hb] at hh
  exact hh

private theorem strict_size_of_le
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1)) :
    (Nat.card (BinaryGaloisField n))^4 < (2^(2*m+1))^6 := by
  exact (Nat.pow_le_pow_left hsize 4).trans_lt
    (Nat.pow_lt_pow_right (Nat.one_lt_pow (by omega) (by decide : 1 < 2)) (by decide))

include μ hB hn ν hC in
/-- A whole perpendicular root in the Frattini subgroup forces the near equality. -/
theorem source_positive_near_eq_of_perpendicular_le_frattini
    (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1))
    (hE : rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
      (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype) :
    ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ =
      rootAt Q split j (Q.simple i) := by
  exact source_positive_near_eq_of_omega_perpendicular_commutes Q split i j m μ hB n hn ν T hC
    hmpos hc hm hij hsize (source_positive_omega_perpendicular_of_frattini Q split i j m μ hB
      n ν T hC hmpos hc hm hij (strict_size_of_le m n hsize) hE)

include μ hB hn ν hC in
/-- Under a vanishing near commutator, the perpendicular Frattini intersection is exactly Omega. -/
theorem source_positive_perpendicular_frattini_of_near_trivial
    (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1))
    (hnear : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    ((frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype) ⊓
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) =
      omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)) := by
  have hnot : ¬ rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) ≤
      (frattini (simpleRemainder Q split i)).map (simpleRemainder Q split i).subtype := by
    intro hE
    have he := source_positive_near_eq_of_perpendicular_le_frattini Q split i j m μ hB n hn ν T hC
      hmpos hc hm hij hsize hE
    rw [hnear] at he
    have hne : rootAt Q split j (Q.simple i) ≠ ⊥ := by
      intro hz
      have hcard := linear_rootAt_card Q split j n ν T hC hn (Q.simple i)
      rw [hz,Nat.card_unique] at hcard
      exact (Nat.one_lt_pow hn.ne' (by decide : 1 < 2)).ne hcard
    exact hne he.symm
  apply le_antisymm
  · apply suzuki_rootAt_intersection_le_omega_of_not_le Q split i m μ hB _ _ _ hnot
    exact (inf_le_left.trans (Q.tits.B_le_standardParabolic _)).trans
      (source_frattini_parabolic_normalizes Q split i m μ hB)
  · exact le_inf (source_omega_le_frattini Q split i m μ hB _
      (octagon_three_roots_le_remainder Q split hm i j hij).2.2) (omegaOneAmbient_le _)

include μ hB hn ν hC in
/-- The actual derived intersection has the same precise support in the near-zero branch. -/
theorem source_positive_perpendicular_derived_of_near_trivial
    (hmpos : 0 < m)
    (hc : centralizer (pCore 2 (Endpoint Q i) : Set (Endpoint Q i)) ≤ pCore 2 (Endpoint Q i))
    (hm : rotationOrder Q = 8) (hij : i ≠ j)
    (hsize : Nat.card (BinaryGaloisField n) ≤ 2^(2*m+1))
    (hnear : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j*Q.simple i)⁆ = ⊥) :
    (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)) ⊓
      rootAt Q split i (Q.simple j*Q.simple i*Q.simple j) =
      omegaOneAmbient (rootAt Q split i (Q.simple j*Q.simple i*Q.simple j)) := by
  let V := simpleRemainder Q split i
  let : Fact (IsPGroup 2 V) := ⟨split.isTwo.to_le inf_le_left⟩
  have hD : ⁅V,V⁆ ≤ (frattini V).map V.subtype := by
    rw [←map_subtype_commutator]
    exact map_mono (commutator_le_frattini_of_isPGroup (p := 2))
  apply le_antisymm
  · exact (inf_le_inf_right _ hD).trans
      (source_positive_perpendicular_frattini_of_near_trivial Q split i j m μ hB n hn ν T hC
        hmpos hc hm hij hsize hnear).le
  · exact le_inf (source_positive_omega_le_derived Q split i m μ hB hmpos _
      (octagon_three_roots_le_remainder Q split hm i j hij).2.2) (omegaOneAmbient_le _)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
