module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FourCartan
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitaryLinearActions
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.CenterIrreducibility
public import Theory.Representation.OrthogonalFourMinusRankOne.RootActors

/-!
# Root centers in the actual U₅ Hermitian derived layer

The SL₂ Hermitian realization of the linear radical's derived subgroup
identifies the two diagonal lines with the derived subgroups (hence centers)
of the two nonabelian unitary roots. Fixed points of the upper root identify
the top line, and the specified reflection identifies the bottom line.
The crossed linear root is the off-diagonal plane: the center-valued
commutator kills one diagonal entry, and reflection kills the other.

This identifies actual source subgroups, including q = 2. The inherited
tensor action consequently gives the trace crossing and the crossing with
a central unitary-root element. These are equations on the whole derived
subgroup, not only equations modulo a Frattini subgroup. Synchronization
with the full SU₃ root parameters remains a separate source obligation.
Source: Fong--Seitz II (8C), pp.206--207, (8.21)--(8.23), (8.30).
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative commutatorElement
open Theory.PSL2.SemilinearCoverage
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource UnitarySource

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) [NeZero n]
  (i j : Fin 2) (hij : i ≠ j) (hm : rotationOrder Q = 4)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i)
  (l : SL(2,Field n) →* X ⧸ Q.D)
  (e : Multiplicative (Space n) ≃*
    (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D)))
local notation "v" => (MonoidHom.comp (Subgroup.subtype (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ : Subgroup (X ⧸ Q.D))) (MulEquiv.toMonoidHom e))
local notation "r" => (FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v)
variable
  (he : ∀ (g : SL(2,Field n)) (p : Space n),
    l g * (e (.ofAdd p) : X ⧸ Q.D) * (l g)⁻¹ = e (.ofAdd (action n g p)))
  (hA : (l.comp (SpecialLinearGroup.upperUnipotentHom (Field n))).range = simpleRoot Q split i)
  (hs : l (weyl (Field n)) = (s.val : X ⧸ Q.D))

local instance : Module (ZMod 2) (Space n) := SL2.BinarySmall.spaceBinaryModule n

/-- The crossed derived layer is the right conjugate of the original one. -/
theorem crossed_derived_eq :
    ⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i)⁆ =
      rightConjugate ⁅simpleRoot Q split j,simpleRoot Q split j⁆
        (s.val : X ⧸ Q.D) := by
  rw [rootAt_eq Q split j (Q.simple i) s.val s.class_eq]
  simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]

include s in
/-- Specialness identifies the crossed derived layer with its intrinsic center,
embedded in the actual quotient. -/
theorem crossed_derived_center_eq
    (hZ : _root_.commutator (simpleRoot Q split j) = center (simpleRoot Q split j)) :
    ⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i)⁆ =
      (center (rootAt Q split j (Q.simple i))).map (rootAt Q split j (Q.simple i)).subtype := by
  rw [crossed_derived_eq Q split i j s,←map_subtype_commutator,hZ,
    rightConjugate_center,←rootAt_eq Q split j (Q.simple i) s.val s.class_eq]

include he hA in
private theorem derived_top_of_centralizes (p : Space n)
    (hp : (e (.ofAdd p) : X ⧸ Q.D) ∈ centralizer (simpleRoot Q split i : Set (X ⧸ Q.D))) :
    ∃ d : fixedField n, p = FourTensor.diagonalTop (Field n) (conjugation n) (conjugation_involutive n) d := by
  have hf : p ∈ fixedSpace (SL2.BinarySmall.hermitian n) (SpecialLinearGroup.upperUnipotent (Field n)) := by
    intro g
    obtain ⟨a,ha⟩ := (SpecialLinearGroup.mem_upperUnipotent _ _).mp g.property
    have hmem : l g.val ∈ simpleRoot Q split i := by
      rw [←hA]
      refine ⟨.ofAdd a,?_⟩
      change l (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) a) = l g.val
      exact congrArg l ha
    have hc := mem_centralizer_iff.mp hp (l g.val) hmem
    apply Multiplicative.ofAdd.injective
    apply e.injective
    apply Subtype.val_injective
    change (e (.ofAdd (action n g.val p)) : X ⧸ Q.D) = e (.ofAdd p)
    rw [←he]
    rw [hc, mul_inv_cancel_right]
  obtain ⟨hb,hc⟩ := (RankOne.mem_fixedSpace_upper_iff n p).mp hf
  refine ⟨⟨p.val 0 0,entry_fixed n p 0⟩,?_⟩
  apply Subtype.ext
  ext a b
  fin_cases a <;> fin_cases b
  · rfl
  · exact hc
  · change p.val 1 0 = 0
    simpa only [hc,map_zero] using (entry_conjugate n p 1 0).symm
  · exact hb

theorem derived_D_injective : Function.Injective (r).D := by
  intro a b hab
  have hh := e.injective (Subtype.val_injective hab)
  have ht := congrArg (fun p : Multiplicative (Space n) => p.toAdd.val 0 0) hh
  exact congrArg Multiplicative.ofAdd (Subtype.ext ht)

include hij hm hVi hVj he hA in
private theorem derived_cross_le_D :
    ⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i)⁆ ≤ (r).D.range := by
  intro x hx
  let p := (e.symm ⟨x,(commutator_mono (opposite_roots_le_remainder Q split j i hij.symm).2
      (opposite_roots_le_remainder Q split j i hij.symm).2) hx⟩).toAdd
  have hp : (e (.ofAdd p) : X ⧸ Q.D) = x := congrArg Subtype.val (e.apply_symm_apply _)
  have hc := (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (adjacent_roots_commute Q split hm i j hij hVi hVj))) ((commutator_le_self _) hx)
  obtain ⟨d,hd⟩ := derived_top_of_centralizes Q split n i l e he hA p (hp.symm ▸ hc)
  refine ⟨.ofAdd d,?_⟩
  change (e (.ofAdd (FourTensor.diagonalTop (Field n) (conjugation n) (conjugation_involutive n) d)) : X ⧸ Q.D) = x
  rw [←hd,hp]

variable (hsmall : Nat.card (⁅simpleRoot Q split j,simpleRoot Q split j⁆ : Subgroup (X ⧸ Q.D)) = 2^n)

include hij hm hVi hVj he hA hsmall s in
/-- The top line is the derived subgroup of the whole crossed unitary root. -/
theorem derived_D_range : (r).D.range = ⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i)⁆ := by
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge (derived_cross_le_D Q split n i j hij hm hVi hVj l e he hA)
  rw [←Nat.card_congr (MonoidHom.ofInjective (derived_D_injective Q split n i l e)).toEquiv]
  change Nat.card (fixedField n) ≤ Nat.card
    (⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i)⁆ : Subgroup (X ⧸ Q.D))
  rw [crossed_derived_eq Q split i j s,card_rightConjugate,card_fixedField,hsmall]

theorem derived_B_injective : Function.Injective (r).B := by
  intro a b hab
  have hh := e.injective (Subtype.val_injective hab)
  have ht := congrArg (fun p : Multiplicative (Space n) => p.toAdd.val 1 1) hh
  exact congrArg Multiplicative.ofAdd (Subtype.ext ht)

include hij hm hVi hVj he hA hsmall hs in
/-- Reflection identifies the bottom line with the unitary simple-root derived subgroup. -/
theorem derived_B_range : (r).B.range = ⁅simpleRoot Q split j,simpleRoot Q split j⁆ := by
  have hd := derived_D_range Q split n i j hij hm hVi hVj s l e he hA hsmall
  rw [crossed_derived_eq Q split i j s] at hd
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨b,rfl⟩
    have hb := FourCartan.weyl_B (Field n) (conjugation n) (conjugation_involutive n) l v he b.toAdd
    rw [hs] at hb
    change (s.val : X ⧸ Q.D) * (r).B b * s.val = (r).D b at hb
    have hm : (r).D b ∈ rightConjugate ⁅simpleRoot Q split j,simpleRoot Q split j⁆ (s.val : X ⧸ Q.D) := by
      rw [←hd]; exact ⟨b,rfl⟩
    change (s.val : X ⧸ Q.D) * (r).D b * (s.val : X ⧸ Q.D)⁻¹ ∈ ⁅simpleRoot Q split j,simpleRoot Q split j⁆ at hm
    have hs2 : (s.val : X ⧸ Q.D) * s.val = 1 := by rw [←hs,←map_mul,weyl_sq,map_one]
    have heq : (s.val : X ⧸ Q.D) * (r).D b * (s.val : X ⧸ Q.D)⁻¹ = (r).B b := by
      calc
        _ = (s.val : X ⧸ Q.D) * ((s.val : X ⧸ Q.D) * (r).B b * s.val) * (s.val : X ⧸ Q.D)⁻¹ := congrArg (fun y : X ⧸ Q.D => (s.val : X ⧸ Q.D)*y*(s.val : X ⧸ Q.D)⁻¹) hb.symm
        _ = ((s.val : X ⧸ Q.D)*s.val) * (r).B b := by group
        _ = _ := by rw [hs2,one_mul]
    exact heq ▸ hm
  · rw [←Nat.card_congr (MonoidHom.ofInjective (derived_B_injective Q split n i l e)).toEquiv]
    change Nat.card (⁅simpleRoot Q split j,simpleRoot Q split j⁆ : Subgroup (X ⧸ Q.D)) ≤ Nat.card (fixedField n)
    rw [card_fixedField,hsmall]

variable
  (hcross : ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ ≤
    ⁅rootAt Q split j (Q.simple i),rootAt Q split j (Q.simple i)⁆)
  (hC : rootAt Q split i (Q.simple j) ≤
    ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆)

include hij hm hVi hVj he hA hsmall s hcross in
private theorem derived_cross_bottom_zero (p : Space n)
    (hp : (e (.ofAdd p) : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j)) : p.val 1 1 = 0 := by
  have hu : l (uni (1 : Field n)) ∈ simpleRoot Q split i := by
    rw [←hA]
    exact ⟨.ofAdd 1,rfl⟩
  have hc := hcross (commutator_mem_commutator hu hp)
  rw [←derived_D_range Q split n i j hij hm hVi hVj s l e he hA hsmall] at hc
  obtain ⟨d,hd⟩ := hc
  have hec : (e (.ofAdd (action n (uni 1) p - p)) : X ⧸ Q.D) =
      ⁅l (uni 1),(e (.ofAdd p) : X ⧸ Q.D)⁆ := by
    change v (.ofAdd (action n (uni 1) p - p)) = _
    rw [sub_eq_add_neg,ofAdd_add,ofAdd_neg,map_mul,map_inv]
    change (e (.ofAdd (action n (uni 1) p)) : X ⧸ Q.D) * (e (.ofAdd p) : X ⧸ Q.D)⁻¹ = _
    rw [←he]
    rfl
  have hh := congrArg (fun z : Multiplicative (Space n) => z.toAdd.val 0 1)
    (e.injective (Subtype.val_injective (hec.trans hd.symm)))
  change ((uni (1 : Field n)).val * p.val * adjoint (conjugation n) (uni (1 : Field n)).val) 0 1 - p.val 0 1 = 0 at hh
  simpa [uni_val,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using hh

include hij hm hVi hVj he hA hsmall hs hcross hC in
private theorem derived_cross_le_C : rootAt Q split i (Q.simple j) ≤ (r).C.range := by
  intro x hx
  let p := (e.symm ⟨x,hC hx⟩).toAdd
  have hp : (e (.ofAdd p) : X ⧸ Q.D) = x := congrArg Subtype.val (e.apply_symm_apply _)
  have hpC : (e (.ofAdd p) : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := hp.symm ▸ hx
  have hb := derived_cross_bottom_zero Q split n i j hij hm hVi hVj s l e he hA hsmall hcross p hpC
  have hpw : (e (.ofAdd (action n (weyl (Field n)) p)) : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := by
    rw [←he,hs]
    exact (SetLike.ext_iff.mp (cross_root_reflection_fixed Q split hm i j hij s.val s.class_eq) _).mpr hpC
  have hw := derived_cross_bottom_zero Q split n i j hij hm hVi hVj s l e he hA hsmall hcross
    (action n (weyl (Field n)) p) hpw
  have ht : p.val 0 0 = 0 := by
    change ((weyl (Field n)).val * p.val * adjoint (conjugation n) (weyl (Field n)).val) 1 1 = 0 at hw
    simpa [weyl,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two] using hw
  have heq : p = FourTensor.offDiagonal (Field n) (conjugation n) (conjugation_involutive n) (p.val 0 1) := by
    apply Subtype.ext
    ext a b
    fin_cases a <;> fin_cases b
    · exact ht
    · rfl
    · exact (entry_conjugate n p 1 0).symm
    · exact hb
  refine ⟨.ofAdd (p.val 0 1),?_⟩
  change (e (.ofAdd (FourTensor.offDiagonal (Field n) (conjugation n) (conjugation_involutive n) (p.val 0 1))) : X ⧸ Q.D) = x
  rw [←heq,hp]

theorem derived_C_injective : Function.Injective (r).C := by
  intro a b hab
  have hh := e.injective (Subtype.val_injective hab)
  exact congrArg Multiplicative.ofAdd (congrArg (fun p : Multiplicative (Space n) => p.toAdd.val 0 1) hh)

include hij hm hVi hVj he hA hsmall hs hcross hC in
/-- The off-diagonal tensor root is the crossed larger source root. -/
theorem derived_C_range (hlarge : Nat.card (simpleRoot Q split i) = Nat.card (Field n)) :
    (r).C.range = rootAt Q split i (Q.simple j) := by
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge (derived_cross_le_C Q split n i j hij hm hVi hVj s l e he hA hs hsmall hcross hC)
  rw [←Nat.card_congr (MonoidHom.ofInjective (derived_C_injective Q split n i l e)).toEquiv]
  change Nat.card (Field n) ≤ Nat.card (rootAt Q split i (Q.simple j))
  simp only [rootAt,card_rightConjugate,hlarge,le_refl]

section RootCenterOrder
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open BenderSuzuki.MatrixGroups.HermitianForm
open BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.EvenCenterAction

include hVj in
/-- The actual unitary root-derived subgroup is its full center and has order q,
including the quaternion root when q = 2. -/
theorem simpleRoot_derived_center_card
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {d : ℕ} (hd : 0 < d)
    (hE : Nat.card E = (2^d)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^d)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    ⁅simpleRoot Q split j,simpleRoot Q split j⁆ =
      (center (simpleRoot Q split j)).map (simpleRoot Q split j).subtype ∧
    Nat.card (⁅simpleRoot Q split j,simpleRoot Q split j⁆ : Subgroup (X ⧸ Q.D)) = 2^d := by
  have hz := (unitary_simpleRoot_special Q split J hd hE hfixed hJ j hVj ν).2
  have heq : ⁅simpleRoot Q split j,simpleRoot Q split j⁆ =
      (center (simpleRoot Q split j)).map (simpleRoot Q split j).subtype := by
    rw [←map_subtype_commutator,hz]
  refine ⟨heq,?_⟩
  let u := simpleRootUnitaryEquiv J Q split hd hE hfixed hJ j hVj ν
  let z : center (hermitianUnipotentCoord J) ≃*
      Multiplicative (BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus.EvenCenterAction.fixedField J) :=
    (MulEquiv.subgroupCongr (binary_coord_center J hd hE hfixed)).trans
      (MonoidHom.ofInjective (centralCoord_injective J)).symm
  rw [heq,card_map_of_injective (simpleRoot Q split j).subtype_injective,
    Nat.card_congr (centerCongr u).toEquiv,Nat.card_congr z.toEquiv,
    Nat.card_congr Multiplicative.toAdd]
  exact hfixed

end RootCenterOrder

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
