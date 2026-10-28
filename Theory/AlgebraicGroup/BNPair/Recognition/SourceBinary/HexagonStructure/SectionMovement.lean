module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.EffectiveSections

/-!
# Effective sections detected by an opposite root

For a literal invariant section A/B of the canonical radical V_j, suppose
U_i lies in A and B, embedded in the same finite quotient, lies in V_i.
The actual odd reflection--unipotent product cannot centralize A/B:
its inverse carries U_i into V_i, which is disjoint from U_i. The proved
linear normal-kernel and coprime Frattini arguments therefore give faithful
action on A/Φ(A)B(H ∩ A), with precisely the source denominator.

Construct the relative quotient V_j/(V_j ∩ M) for an invariant ambient
subgroup M. In particular, the three-middle-root product is normal in V_j
when U_i is abelian, and the quotient is effective whenever R_j preserves
that product. This is the actual section needed in the unequal-parameter
argument, rather than effectiveness assumed as an input.

Source: Fong--Seitz I (5D)(b), printed pp.26--27, and (6E), printed p.44.
The linear argument includes fields of orders two and four. Nonlinear
local groups and the general solvable-supplement reduction remain separate.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates GTwoSource Theory.PSL2.SemilinearCoverage
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
  (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
  (μ : localGroup Q split j ≃* PSL(2,F)) (s : RootReflection Q split j)

/-- Root movement on the literal section, before passing to its effective quotient. -/
theorem oddProduct_moves_section (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (d : RootSection Q split j)
    (hroot : simpleRoot Q split i ≤ d.numerator)
    (hden : d.denominator.map d.numerator.subtype ≤ simpleRemainder Q split i) :
    d.action (oddProduct Q split j hKj μ s) ≠ 1 := by
  intro he
  have hei : d.action (oddProduct Q split j hKj μ s)⁻¹ = 1 := by
    rw [map_inv, he, inv_one]
  let u := oddPartner Q split j hKj μ s
  have huU : (u : X ⧸ Q.D) ∈ split.U :=
    simpleRoot_le Q split j (oddPartner_mem_root Q split j hKj μ s)
  have huN : (u : X ⧸ Q.D) ∈ normalizer (simpleRemainder Q split i : Set _) :=
    remainder_parabolic_normalizes Q split i hKi
      (Q.tits.B_le_standardParabolic _ (split.U_le huU))
  apply simpleRoot_ne_bot Q split i
  apply eq_bot_iff.mpr
  intro a ha
  let x : d.numerator := ⟨a,hroot ha⟩
  let y := d.numeratorAction (oddProduct Q split j hKj μ s)⁻¹ x
  have hy : (y : X ⧸ Q.D) =
      (u : X ⧸ Q.D)⁻¹*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*u := by
    dsimp only [y]
    rw [d.numeratorAction_apply]
    simp only [coe_inv, oddProduct_coe, mul_inv_rev, inv_inv, mul_assoc]
    rfl
  have hrootV : rootAt Q split i (Q.simple j) ≤ simpleRemainder Q split i :=
    (show rootAt Q split i (Q.simple j) ≤ middleRoots Q split j i from
      le_sup_left.trans le_sup_left).trans
        (middleRoots_le_remainder Q split hm j i hij.symm)
  have haR : (s.val : X ⧸ Q.D)⁻¹*a*s.val ∈ rootAt Q split i (Q.simple j) := by
    rw [rootAt_eq Q split i (Q.simple j) s.val s.class_eq]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using ha
  have hyV : (y : X ⧸ Q.D) ∈ simpleRemainder Q split i := by
    rw [hy]
    simpa only [inv_inv] using (mem_normalizer_iff.mp
      ((normalizer _).inv_mem huN) _).mp (hrootV haR)
  have hd : y / x ∈ d.denominator := by
    apply QuotientGroup.eq_iff_div_mem.mp
    change d.action (oddProduct Q split j hKj μ s)⁻¹ (QuotientGroup.mk x) =
      QuotientGroup.mk x
    rw [hei]; rfl
  have hdV : (y : X ⧸ Q.D) / a ∈ simpleRemainder Q split i :=
    hden (mem_map_of_mem d.numerator.subtype hd)
  have haV : a ∈ simpleRemainder Q split i := by
    have ht := (simpleRemainder Q split i).mul_mem (inv_mem hdV) hyV
    simpa only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using ht
  exact mem_bot.mpr (disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haV)

include hKj μ s in
/-- A section detected by the opposite canonical root is faithful on its
literal effective quotient. -/
theorem linear_root_section_injective (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (d : RootSection Q split j)
    (hroot : simpleRoot Q split i ≤ d.numerator)
    (hden : d.denominator.map d.numerator.subtype ≤ simpleRemainder Q split i) :
    Function.Injective d.effectiveRepresentation :=
  d.effectiveRepresentation_injective
    (linear_section_effectiveAction_injective Q split j hKj μ s d
      (oddProduct_moves_section Q split j hKj μ s hm i hij hKi d hroot hden))

/-- The radical modulo its intersection with a relatively normal invariant subgroup. -/
@[expose] def radicalFactorSection (N : Subgroup (X ⧸ Q.D))
    (hVN : simpleRemainder Q split j ≤ normalizer (N : Set _))
    (hRN : rankOne Q split j ≤ normalizer (N : Set _)) : RootSection Q split j where
  numerator := simpleRemainder Q split j
  le_radical := le_rfl
  normalized := (rankOne_le_parabolic Q split j).trans
    (remainder_parabolic_normalizes Q split j hKj)
  denominator := N.subgroupOf (simpleRemainder Q split j)
  normal := normal_subgroupOf_of_le_normalizer hVN
  invariant r := by
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact (mem_normalizer_iff.mp (hRN r.property) _).mp hy
    · intro x hx
      refine ⟨(radicalAction Q split j hKj r⁻¹) x, ?_, ?_⟩
      · change ((radicalAction Q split j hKj r⁻¹ x : simpleRemainder Q split j) : X ⧸ Q.D) ∈ N
        rw [radicalAction_apply]
        exact (mem_normalizer_iff.mp (hRN (inv_mem r.property)) _).mp hx
      · apply Subtype.ext
        change (r : X ⧸ Q.D)*((radicalAction Q split j hKj r⁻¹ x : simpleRemainder Q split j) : X ⧸ Q.D)*
          (r : X ⧸ Q.D)⁻¹ = (x : X ⧸ Q.D)
        rw [radicalAction_apply]
        simp only [coe_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

/-- Under the linear-root hypothesis, the source middle product is normal
inside the radical. This is relative, not ambient, normality. -/
theorem radical_normalizes_middle (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥) :
    simpleRemainder Q split j ≤ normalizer (middleRoots Q split i j : Set _) := by
  apply le_normalizer_iff_commutator_le_right.mpr
  exact (commutator_mono le_rfl (middleRoots_le_remainder Q split hm i j hij)).trans
    (radical_commutator_le_middle Q split hm i j hij hKi hA)

/-- The source candidate V_j/X, with X the exact three-middle-root product. -/
@[expose] def middleFactorSection (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (hR : rankOne Q split j ≤ normalizer (middleRoots Q split i j : Set _)) :
    RootSection Q split j :=
  radicalFactorSection Q split j hKj (middleRoots Q split i j)
    (radical_normalizes_middle Q split j hm i hij hKi hA) hR

include hKj μ s in
/-- (5D) on precisely the quotient used in the second paragraph of (6E). -/
theorem middleFactorSection_injective (hm : rotationOrder Q = 6)
    (i : Fin 2) (hij : i ≠ j)
    (hKi : simpleRemainder Q split i ≤ localKernel Q i)
    (hA : ⁅simpleRoot Q split i,simpleRoot Q split i⁆ = ⊥)
    (hR : rankOne Q split j ≤ normalizer (middleRoots Q split i j : Set _)) :
    Function.Injective
      (middleFactorSection Q split j hKj hm i hij hKi hA hR).effectiveRepresentation := by
  apply linear_root_section_injective Q split j hKj μ s hm i hij hKi
    (middleFactorSection Q split j hKj hm i hij hKi hA hR)
    (simpleRoot_le_other_remainder Q split hm i j hij)
  change ((middleRoots Q split i j).subgroupOf (simpleRemainder Q split j)).map
    (simpleRemainder Q split j).subtype ≤ simpleRemainder Q split i
  rw [map_subgroupOf_eq_of_le (middleRoots_le_remainder Q split hm i j hij)]
  exact middleRoots_le_other_remainder Q split hm i j hij

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
