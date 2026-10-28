module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.LinearLocalRoots
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.FieldTheory.Finiteness

/-!
# The actual binary radical quotient and its induced representation

The quotient is the abelianization of the canonical simple remainder.
Its projection kernel, embedded back in the original quotient carrier, is
exactly the ambient subgroup commutator. The five-root factorization shows
that elementary simple roots give this abelianization exponent two, so its
additive group is a vector space over F2. Conjugation by the actual R_i
descends functorially to this quotient and gives the linear representation.

The inverse-actor equation states the source right-conjugation convention
on actual representatives. This supplies the action and scalar structure
used by Fong--Seitz I (6E)(b), printed pp.43--45. Irreducibility and the
identification of the derived subgroup with the middle root are not assumed
or concluded; these remain the structural argument's next obligations.
-/

public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)

theorem rootAt_elementary (i : Fin 2) (w : Weyl Q)
    (hE : IsElementaryAbelian 2 (simpleRoot Q split i)) :
    IsElementaryAbelian 2 (rootAt Q split i w) := by
  let := hE
  exact IsElementaryAbelian.comap_of_injective
    (MulAut.conj (representative w : X ⧸ Q.D)).toMonoidHom
    (MulAut.conj (representative w : X ⧸ Q.D)).injective _

/-- The quotient in 6E is the abelianization of the literal canonical radical. -/
abbrev RadicalQuotient (i : Fin 2) := Abelianization (simpleRemainder Q split i)

/-- Its kernel, embedded in the source carrier, is exactly the subgroup commutator. -/
theorem radicalProjection_kernel (i : Fin 2) :
    (Abelianization.of : simpleRemainder Q split i →* RadicalQuotient Q split i).ker.map
      (simpleRemainder Q split i).subtype =
        ⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ := by
  rw [Abelianization.ker_of, map_subtype_commutator]

/-- Five elementary root factors make the actual radical abelianization binary. -/
theorem radicalQuotient_elementary (hm : rotationOrder Q = 6)
    (hE : ∀ i, IsElementaryAbelian 2 (simpleRoot Q split i)) (j : Fin 2) :
    IsElementaryAbelian 2 (RadicalQuotient Q split j) := by
  let V := simpleRemainder Q split j
  let f : V →* RadicalQuotient Q split j := (powMonoidHom 2).comp Abelianization.of
  let K := f.ker.map V.subtype
  have hA (A : Subgroup (X ⧸ Q.D)) (hAV : A ≤ V) (hAE : IsElementaryAbelian 2 A) : A ≤ K := by
    intro a ha
    let := hAE
    have hav : (⟨a,hAV ha⟩ : V)^2 = 1 := Subtype.ext
      (elemPow_eq_one_of_isElementaryAbelian a ha)
    refine ⟨⟨a,hAV ha⟩,?_,rfl⟩
    change (Abelianization.of (⟨a,hAV ha⟩ : V))^2 = 1
    rw [← map_pow, hav, map_one]
  let i : Fin 2 := 1-j
  have hij : i ≠ j := by dsimp [i]; omega
  have hroot := simpleRoot_le_other_remainder Q split hm i j hij
  have hmiddle := middleRoots_le_remainder Q split hm i j hij
  have hlast := (exchanged_roots_le_remainder Q split hm i j hij).1
  have hBK : rootAt Q split j (Q.simple i) ≤ K :=
    hA _ ((show rootAt Q split j (Q.simple i) ≤ middleRoots Q split i j from
      le_sup_left.trans le_sup_left).trans hmiddle) (rootAt_elementary Q split _ _ (hE j))
  have hCK : rootAt Q split i (Q.simple j*Q.simple i) ≤ K :=
    hA _ ((show rootAt Q split i (Q.simple j*Q.simple i) ≤ middleRoots Q split i j from
      le_sup_right.trans le_sup_left).trans hmiddle) (rootAt_elementary Q split _ _ (hE i))
  have hDK : rootAt Q split j (Q.simple i*Q.simple j) ≤ K :=
    hA _ ((show rootAt Q split j (Q.simple i*Q.simple j) ≤ middleRoots Q split i j from
      le_sup_right).trans hmiddle) (rootAt_elementary Q split _ _ (hE j))
  have hVK : V ≤ K := by
    intro x hx
    have hx' : x ∈ (simpleRemainder Q split j : Set (X ⧸ Q.D)) := hx
    rw [radical_five_product Q split hm i j hij] at hx'
    obtain ⟨abcd,⟨abc,⟨ab,⟨a,ha,b,hb,rfl⟩,c,hc,rfl⟩,d,hd,rfl⟩,e,he,rfl⟩ := hx'
    exact K.mul_mem (K.mul_mem (K.mul_mem (K.mul_mem (hA _ hroot (hE i) ha)
      (hBK hb)) (hCK hc)) (hDK hd)) (hA _ hlast (rootAt_elementary Q split _ _ (hE i)) he)
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  obtain ⟨v,rfl⟩ := (Quotient.mk_surjective : Function.Surjective
    (Abelianization.of : V → RadicalQuotient Q split j)) x
  obtain ⟨u,hu,he⟩ := hVK v.property
  have huv : u = v := Subtype.ext he
  subst u
  exact hu

/-- The actual rank-one conjugation action descends to the actual radical quotient. -/
def radicalQuotientAction (j : Fin 2)
    (hK : simpleRemainder Q split j ≤ localKernel Q j) :
    rankOne Q split j →* MulAut (RadicalQuotient Q split j) where
  toFun r := (radicalAction Q split j hK r).abelianizationCongr
  map_one' := by
    rw [map_one]
    exact abelianizationCongr_refl
  map_mul' r s := by
    ext v
    induction v using QuotientGroup.induction_on with
    | H v =>
      change (radicalAction Q split j hK (r*s)).abelianizationCongr (Abelianization.of v) =
        (radicalAction Q split j hK r).abelianizationCongr
          ((radicalAction Q split j hK s).abelianizationCongr (Abelianization.of v))
      simp only [abelianizationCongr_of, map_mul, MulAut.mul_apply]

@[simp] theorem radicalQuotientAction_of (j : Fin 2)
    (hK : simpleRemainder Q split j ≤ localKernel Q j)
    (r : rankOne Q split j) (v : simpleRemainder Q split j) :
    radicalQuotientAction Q split j hK r (Abelianization.of v) =
      Abelianization.of (radicalAction Q split j hK r v) := by rfl

/-- The binary scalar structure proved from the five actual root factors. -/
@[instance_reducible] def radicalModule (hm : rotationOrder Q = 6)
    (hE : ∀ i, IsElementaryAbelian 2 (simpleRoot Q split i)) (j : Fin 2) :
    Module (ZMod 2) (Additive (RadicalQuotient Q split j)) := by
  let := radicalQuotient_elementary Q split hm hE j
  exact IsElementaryAbelian.isVectorSpace 2

variable (j : Fin 2) (hK : simpleRemainder Q split j ≤ localKernel Q j)
    [IsElementaryAbelian 2 (RadicalQuotient Q split j)]

/-- R_j acts linearly on U_sj/U_sj', via its actual conjugation action. -/
def radicalRepresentation : Representation (ZMod 2) (rankOne Q split j)
    (Additive (RadicalQuotient Q split j)) where
  toFun r := (radicalQuotientAction Q split j hK r).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by ext v; simp only [map_one]; rfl
  map_mul' r s := by ext v; simp only [map_mul]; rfl

@[simp] theorem radicalRepresentation_of (r : rankOne Q split j)
    (v : simpleRemainder Q split j) :
    radicalRepresentation Q split j hK r (Additive.ofMul (Abelianization.of v)) =
      Additive.ofMul (Abelianization.of (radicalAction Q split j hK r v)) := by
  exact congrArg Additive.ofMul (radicalQuotientAction_of Q split j hK r v)

/-- Right conjugation of actual representatives induces precisely the source
linear action; equality is in the same finite quotient carrier. -/
theorem radicalRepresentation_right_conjugation (r : rankOne Q split j)
    (v v' : simpleRemainder Q split j)
    (hv : (v' : X ⧸ Q.D) = (r : X ⧸ Q.D)⁻¹*v*(r : X ⧸ Q.D)) :
    radicalRepresentation Q split j hK r⁻¹ (Additive.ofMul (Abelianization.of v)) =
      Additive.ofMul (Abelianization.of v') := by
  rw [radicalRepresentation_of]
  congr 2
  exact Subtype.ext ((radicalAction_right_conjugation Q split j hK r v).trans hv.symm)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
