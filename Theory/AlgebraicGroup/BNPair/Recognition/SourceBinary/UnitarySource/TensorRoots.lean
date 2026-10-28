module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.TensorCartan
public import Theory.Representation.OrthogonalFourMinusRankOne.RootActors

/-!
# All four tensor coordinates are the actual source roots

For the genuine Hermitian intertwiner on the same complementary subgroup,
its upper-root fixed space is the upper diagonal line. The adjacent-root
commuting theorem places the crossed smaller source root on that line;
its order gives equality. The specified large reflection then identifies
the bottom diagonal line with the smaller simple root.

The other crossed root has commutators with the large simple root only
in the upper diagonal line. The upper-right entry of one displacement
therefore kills its bottom entry. Its invariance under the large reflection
kills the top entry, identifying the entire off-diagonal root by its order.
Thus all four maps have their literal root ranges, including q=2. The
smaller root actor fixes the highest root pointwise, supplying the labelled
D equation for the second reflection without an action premise.

TensorRootApplication constructs the intertwiner and both root orders
from the original quadratic profile and applies these equalities on the
same quotient. TensorSecondReflection determines the A/C coefficient and
TensorReflectionApplication normalizes those labels. The second rank-one
and Cartan equations, and full unitary recognition remain to be proved.
Source: Fong--Seitz I (3G), (6A)(b), pp.14--16,37--38; II (8B),
pp.201--202, the indicated natural tensor basis and equation (8.9).
-/

@[expose] public noncomputable section
open Subgroup Representation Matrix Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative commutatorElement
open Theory.PSL2.SemilinearCoverage
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open RootCoordinates HexagonStructure QuadrangleStructure GTwoSource

variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) [NeZero n]
  (i j : Fin 2) (hij : i ≠ j) (hm : rotationOrder Q = 4)
  (hVi : simpleRemainder Q split i ≤ localKernel Q i)
  (hVj : simpleRemainder Q split j ≤ localKernel Q j)
  (s : RootReflection Q split i)
  (l : SL(2,Field n) →* X ⧸ Q.D)
  (e : Multiplicative (Space n) ≃* simpleRemainder Q split i)
local notation "v" => (MonoidHom.comp (Subgroup.subtype (simpleRemainder Q split i)) (MulEquiv.toMonoidHom e))
local notation "r" => (FourTensor.roots (Field n) (conjugation n) (conjugation_involutive n) l v)
variable
  (he : ∀ (g : SL(2,Field n)) (p : Space n),
    l g * (e (.ofAdd p) : X ⧸ Q.D) * (l g)⁻¹ = e (.ofAdd (action n g p)))
  (hA : (l.comp (SpecialLinearGroup.upperUnipotentHom (Field n))).range = simpleRoot Q split i)
  (hs : l (weyl (Field n)) = (s.val : X ⧸ Q.D))

local instance : Module (ZMod 2) (Space n) := SL2.BinarySmall.spaceBinaryModule n

include he hA in
private theorem tensor_top_of_centralizes (p : Space n)
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

theorem tensor_D_injective : Function.Injective (r).D := by
  intro a b hab
  have hh := e.injective (Subtype.val_injective hab)
  have ht := congrArg (fun p : Multiplicative (Space n) => p.toAdd.val 0 0) hh
  exact congrArg Multiplicative.ofAdd (Subtype.ext ht)

include hij hm hVi hVj he hA in
private theorem tensor_cross_le_D : rootAt Q split j (Q.simple i) ≤ (r).D.range := by
  intro x hx
  let p := (e.symm ⟨x,(opposite_roots_le_remainder Q split j i hij.symm).2 hx⟩).toAdd
  have hp : (e (.ofAdd p) : X ⧸ Q.D) = x := congrArg Subtype.val (e.apply_symm_apply _)
  have hc := (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (adjacent_roots_commute Q split hm i j hij hVi hVj))) hx
  obtain ⟨d,hd⟩ := tensor_top_of_centralizes Q split n i l e he hA p (hp.symm ▸ hc)
  refine ⟨.ofAdd d,?_⟩
  change (e (.ofAdd (FourTensor.diagonalTop (Field n) (conjugation n) (conjugation_involutive n) d)) : X ⧸ Q.D) = x
  rw [←hd,hp]

variable (hsmall : Nat.card (simpleRoot Q split j) = 2^n)

include hij hm hVi hVj he hA hsmall in
/-- The tensor's highest root is the actual crossed smaller source root. -/
theorem tensor_D_range : (r).D.range = rootAt Q split j (Q.simple i) := by
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge (tensor_cross_le_D Q split n i j hij hm hVi hVj l e he hA)
  rw [←Nat.card_congr (MonoidHom.ofInjective (tensor_D_injective Q split n i l e)).toEquiv]
  change Nat.card (fixedField n) ≤ Nat.card (rootAt Q split j (Q.simple i))
  simp only [rootAt,card_rightConjugate,card_fixedField,hsmall,le_refl]

theorem tensor_B_injective : Function.Injective (r).B := by
  intro a b hab
  have hh := e.injective (Subtype.val_injective hab)
  have ht := congrArg (fun p : Multiplicative (Space n) => p.toAdd.val 1 1) hh
  exact congrArg Multiplicative.ofAdd (Subtype.ext ht)

include hij hm hVi hVj he hA hsmall hs in
/-- Reflection transports the identified highest root to the actual smaller simple root. -/
theorem tensor_B_range : (r).B.range = simpleRoot Q split j := by
  have hd := tensor_D_range Q split n i j hij hm hVi hVj l e he hA hsmall
  rw [rootAt_eq Q split j (Q.simple i) s.val s.class_eq] at hd
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨b,rfl⟩
    have hb := FourCartan.weyl_B (Field n) (conjugation n) (conjugation_involutive n) l v he b.toAdd
    rw [hs] at hb
    change (s.val : X ⧸ Q.D) * (r).B b * s.val = (r).D b at hb
    have hm : (r).D b ∈ rightConjugate (simpleRoot Q split j) (s.val : X ⧸ Q.D) := by
      rw [←hd]; exact ⟨b,rfl⟩
    change (s.val : X ⧸ Q.D) * (r).D b * (s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j at hm
    have hs2 : (s.val : X ⧸ Q.D) * s.val = 1 := by rw [←hs,←map_mul,weyl_sq,map_one]
    have heq : (s.val : X ⧸ Q.D) * (r).D b * (s.val : X ⧸ Q.D)⁻¹ = (r).B b := by
      calc
        _ = (s.val : X ⧸ Q.D) * ((s.val : X ⧸ Q.D) * (r).B b * s.val) * (s.val : X ⧸ Q.D)⁻¹ := congrArg (fun y : X ⧸ Q.D => (s.val : X ⧸ Q.D)*y*(s.val : X ⧸ Q.D)⁻¹) hb.symm
        _ = ((s.val : X ⧸ Q.D)*s.val) * (r).B b := by group
        _ = _ := by rw [hs2,one_mul]
    exact heq ▸ hm
  · rw [←Nat.card_congr (MonoidHom.ofInjective (tensor_B_injective Q split n i l e)).toEquiv]
    change Nat.card (simpleRoot Q split j) ≤ Nat.card (fixedField n)
    rw [card_fixedField,hsmall]

include hij hm hVi hVj he hA hsmall in
private theorem tensor_cross_bottom_zero (p : Space n)
    (hp : (e (.ofAdd p) : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j)) : p.val 1 1 = 0 := by
  have hu : l (uni (1 : Field n)) ∈ simpleRoot Q split i := by
    rw [←hA]
    exact ⟨.ofAdd 1,rfl⟩
  have hc := (cross_root_commutator_le Q split hm i j hij hVi)
    (commutator_mem_commutator hu hp)
  rw [←tensor_D_range Q split n i j hij hm hVi hVj l e he hA hsmall] at hc
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

include hij hm hVi hVj he hA hsmall hs in
private theorem tensor_cross_le_C : rootAt Q split i (Q.simple j) ≤ (r).C.range := by
  intro x hx
  let p := (e.symm ⟨x,cross_root_le_own_remainder Q split hm i j hij hx⟩).toAdd
  have hp : (e (.ofAdd p) : X ⧸ Q.D) = x := congrArg Subtype.val (e.apply_symm_apply _)
  have hpC : (e (.ofAdd p) : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := hp.symm ▸ hx
  have hb := tensor_cross_bottom_zero Q split n i j hij hm hVi hVj l e he hA hsmall p hpC
  have hpw : (e (.ofAdd (action n (weyl (Field n)) p)) : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := by
    rw [←he,hs]
    exact (SetLike.ext_iff.mp (cross_root_reflection_fixed Q split hm i j hij s.val s.class_eq) _).mpr hpC
  have hw := tensor_cross_bottom_zero Q split n i j hij hm hVi hVj l e he hA hsmall
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

theorem tensor_C_injective : Function.Injective (r).C := by
  intro a b hab
  have hh := e.injective (Subtype.val_injective hab)
  exact congrArg Multiplicative.ofAdd (congrArg (fun p : Multiplicative (Space n) => p.toAdd.val 0 1) hh)

include hij hm hVi hVj he hA hsmall hs in
/-- The off-diagonal tensor root is the crossed larger source root. -/
theorem tensor_C_range (hlarge : Nat.card (simpleRoot Q split i) = Nat.card (Field n)) :
    (r).C.range = rootAt Q split i (Q.simple j) := by
  apply Eq.symm
  apply Subgroup.eq_of_le_of_card_ge (tensor_cross_le_C Q split n i j hij hm hVi hVj s l e he hA hs hsmall)
  rw [←Nat.card_congr (MonoidHom.ofInjective (tensor_C_injective Q split n i l e)).toEquiv]
  change Nat.card (Field n) ≤ Nat.card (rootAt Q split i (Q.simple j))
  simp only [rootAt,card_rightConjugate,hlarge,le_refl]

include hij hm hVi hVj he hA hsmall hs in
/-- The entire smaller root actor fixes every labelled highest-root element. -/
theorem tensor_smallActor_centralizes_D :
    rankOne Q split j ≤ centralizer ((r).D.range : Set (X ⧸ Q.D)) := by
  have hB := tensor_B_range Q split n i j hij hm hVi hVj s l e he hA hs hsmall
  have hD := tensor_D_range Q split n i j hij hm hVi hVj l e he hA hsmall
  have hc : ⁅(r).B.range,(r).D.range⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    rintro x ⟨b,rfl⟩
    apply mem_centralizer_iff.mpr
    rintro y ⟨d,rfl⟩
    exact ((FourTensor.relations (Field n) (conjugation n) (conjugation_involutive n) l v he).BD b d).symm.eq
  rw [hB,hD] at hc
  exact hD.symm ▸ rankOne_centralizes_cross_root Q split hm j i hij.symm hc

include hij hm hVi hVj he hA hsmall hs in
/-- In particular the second reflection fixes D pointwise in these same coordinates. -/
theorem tensor_secondReflection_D (t : RootReflection Q split j) (d : fixedField n) :
    (t.val : X ⧸ Q.D) * (r).D (.ofAdd d) * (t.val : X ⧸ Q.D)⁻¹ = (r).D (.ofAdd d) := by
  have hc := mem_centralizer_iff.mp
    (tensor_smallActor_centralizes_D Q split n i j hij hm hVi hVj s l e he hA hs hsmall t.mem_rankOne)
    ((r).D (.ofAdd d)) ⟨.ofAdd d,rfl⟩
  rw [←hc,mul_inv_cancel_right]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
