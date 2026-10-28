module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.EffectiveSections
public import Theory.Frattini.Intersection

/-!
# Frattini detection and nonlinear root movement

For a literal invariant section X/Y, the action image of the kernel on
X/Φ(X)Y(H ∩ X) lies in the Frattini automorphism kernel of X/Y. It is
therefore a two-group. This proves the full kernel step, not merely
nontriviality of the reflection on a larger quotient.

Reduced root coordinates give reflection movement on sections and on the
Frattini subgroup of the radical. A nontrivial square from either an
opposite root or the own-root conjugate supplies the latter movement.
The own-root version applies even when the opposite root is elementary.
All sections are in the same finite quotient, with relative normality
and the literal denominator from Sections retained.

Source: Fong–Seitz I (5D)–(5F), printed pp.26–28, and the successive
Frattini-section applications of (4F) in (6C), printed pp.39–41.
The concrete Suzuki application is in SuzukiSections. Solvable actors
and unitary covers still require their own normal-subgroup arguments.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

namespace RootSection
variable {Q split} {j : Fin 2} (d : RootSection Q split j)

theorem effectiveKernel_action_le_frattiniKernel :
    d.effectiveAction.ker.map d.action ≤ (quotientAut (frattini d.Carrier)).ker := by
  rintro _ ⟨r,hr,rfl⟩
  change quotientAut (frattini d.Carrier) (d.action r) = 1
  ext z
  induction z using QuotientGroup.induction_on with
  | H z =>
    induction z using QuotientGroup.induction_on with
    | H x =>
      change quotientAut (frattini d.Carrier) (d.action r)
        (QuotientGroup.mk' (frattini d.Carrier) (QuotientGroup.mk' d.denominator x)) =
        QuotientGroup.mk' (frattini d.Carrier) (QuotientGroup.mk' d.denominator x)
      rw [quotientAut_apply_mk]
      change QuotientGroup.mk (d.action r (QuotientGroup.mk x)) = QuotientGroup.mk (QuotientGroup.mk x)
      rw [d.action_mk]
      change QuotientGroup.mk' (frattini d.Carrier) (QuotientGroup.mk' d.denominator (d.numeratorAction r x)) =
        QuotientGroup.mk' (frattini d.Carrier) (QuotientGroup.mk' d.denominator x)
      apply QuotientGroup.eq_iff_div_mem.mpr
      rw [← map_div]
      have hx : d.numeratorAction r x / x ∈ d.effectiveDenominator := by
        apply QuotientGroup.eq_iff_div_mem.mp
        change d.effectiveAction r (QuotientGroup.mk x) = QuotientGroup.mk x
        rw [show d.effectiveAction r = 1 from hr]; rfl
      have hle : d.effectiveDenominator ≤ (frattini d.Carrier).comap (QuotientGroup.mk' d.denominator) := by
        rw [d.effectiveDenominator_eq]
        apply sup_le (frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective _))
        intro y hy
        change QuotientGroup.mk' d.denominator y ∈ frattini d.Carrier
        have he : QuotientGroup.mk' d.denominator y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
        rw [he]
        exact one_mem _
      exact hle hx

theorem effectiveKernel_action_isTwo : IsPGroup 2 (d.effectiveAction.ker.map d.action) :=
  (isPGroup_quotientAut_frattini_kernel (d.isTwo.to_quotient d.denominator)).to_le
    d.effectiveKernel_action_le_frattiniKernel

theorem effectiveKernel_isTwo_of_faithful (hf : Function.Injective d.action) :
    IsPGroup 2 d.effectiveAction.ker :=
  d.effectiveKernel_action_isTwo.of_equiv
    (d.effectiveAction.ker.equivMapOfInjective d.action hf).symm
end RootSection

/-- The actual reflection moves a section whenever its numerator contains a
nonidentity element of the opposite root and its denominator lies in the
opposite radical. No local-model hypothesis is used for root movement. -/
theorem reflection_moves_section (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (d : RootSection Q split j) (a : X ⧸ Q.D)
    (ha : a ∈ simpleRoot Q split i) (hax : a ∈ d.numerator) (hne : a ≠ 1)
    (hden : d.denominator.map d.numerator.subtype ≤ simpleRemainder Q split i) :
    d.action ⟨s.val,s.mem_rankOne⟩ ≠ 1 := by
  intro he
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  have hei : d.action r⁻¹ = 1 := by rw [map_inv, he, inv_one]
  let x : d.numerator := ⟨a,hax⟩
  let y := d.numeratorAction r⁻¹ x
  have hy : (y : X ⧸ Q.D) = (s.val : X ⧸ Q.D)⁻¹*a*s.val := by
    rw [d.numeratorAction_apply]
    simp only [coe_inv, inv_inv]
    rfl
  have hyR : (y : X ⧸ Q.D) ∈ rootAt Q split i (Q.simple j) := by
    rw [hy, rootAt_eq Q split i (Q.simple j) s.val s.class_eq]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*a*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split i
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using ha
  have hrootV : rootAt Q split i (Q.simple j) ≤ simpleRemainder Q split i :=
    (show rootAt Q split i (Q.simple j) ≤ middleRoots Q split j i from
      le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm j i hij.symm)
  have hd : y / x ∈ d.denominator := by
    apply QuotientGroup.eq_iff_div_mem.mp
    change d.action r⁻¹ (QuotientGroup.mk x) = QuotientGroup.mk x
    rw [hei]; rfl
  have hdV : (y : X ⧸ Q.D) / a ∈ simpleRemainder Q split i :=
    hden (mem_map_of_mem d.numerator.subtype hd)
  have haV : a ∈ simpleRemainder Q split i := by
    have ht := (simpleRemainder Q split i).mul_mem (inv_mem hdV) (hrootV hyR)
    simpa only [coe_div, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc,
      inv_mul_cancel_left, inv_mul_cancel, mul_one] using ht
  exact hne (disjoint_def.mp (simpleRoot_disjoint_remainder Q split i) ha haV)

/-- Restricting an invariant section to the Frattini subgroup of its
numerator, with trivial denominator, gives an actual section of the same radical. -/
@[expose] def frattiniSection (j : Fin 2) (d : RootSection Q split j) : RootSection Q split j where
  numerator := (frattini d.numerator).map d.numerator.subtype
  le_radical := (map_subtype_le _).trans d.le_radical
  normalized := by
    apply le_normalizer_iff.mpr
    rintro r hr x ⟨y,hy,rfl⟩
    let a := d.numeratorAction ⟨r,hr⟩
    exact ⟨a y, characteristic_iff_le_comap.mp inferInstance a hy, rfl⟩
  denominator := ⊥
  invariant _ := map_bot _

/-- A nontrivial square in the opposite root supplies movement on the
Frattini subgroup of the whole radical, as required for the second (4F) bound. -/
theorem reflection_moves_frattini_radical (hm : rotationOrder Q = 6)
    (i j : Fin 2) (hij : i ≠ j) (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (a : simpleRoot Q split i) (ha : a^2 ≠ 1) :
    (frattiniSection Q split j (radicalSection Q split j hKj)).action
      ⟨s.val,s.mem_rankOne⟩ ≠ 1 := by
  let d := radicalSection Q split j hKj
  let v : d.numerator := inclusion (simpleRoot_le_other_remainder Q split hm i j hij) a
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  apply reflection_moves_section Q split hm i j hij s _ ((a : X ⧸ Q.D)^2)
    (pow_mem a.property 2)
  · exact ⟨v^2, pth_power_mem_frattini_of_isPGroup (p := 2) v, rfl⟩
  · intro he
    exact ha (Subtype.ext he)
  · change (⊥ : Subgroup _).map _ ≤ _
    rw [Subgroup.map_bot]
    exact bot_le

/-- The own-root conjugate in the radical also detects reflection movement
on its Frattini subgroup. This applies when the opposite root is elementary. -/
theorem reflection_moves_frattini_radical_of_conjugate_square
    (hm : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (s : RootReflection Q split j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (a : rootAt Q split j (Q.simple i)) (ha : a^2 ≠ 1) :
    (frattiniSection Q split j (radicalSection Q split j hKj)).action
      ⟨s.val,s.mem_rankOne⟩ ≠ 1 := by
  let d := radicalSection Q split j hKj
  let f := frattiniSection Q split j d
  have hAV : rootAt Q split j (Q.simple i) ≤ d.numerator :=
    (show rootAt Q split j (Q.simple i) ≤ middleRoots Q split i j from
      le_sup_left.trans le_sup_left).trans (middleRoots_le_remainder Q split hm i j hij)
  let v : d.numerator := inclusion hAV a
  let : Fact (IsPGroup 2 d.numerator) := ⟨d.isTwo⟩
  let x : f.numerator := ⟨(a : X ⧸ Q.D)^2,
    ⟨v^2,pth_power_mem_frattini_of_isPGroup (p := 2) v,rfl⟩⟩
  let r : rankOne Q split j := ⟨s.val,s.mem_rankOne⟩
  intro he
  have hei : f.action r⁻¹ = 1 := by rw [map_inv, he, inv_one]
  have hx : f.numeratorAction r⁻¹ x = x := by
    have hh := congrArg (fun z : MulAut f.Carrier => z (QuotientGroup.mk x)) hei
    rw [f.action_mk] at hh
    exact congrArg QuotientGroup.quotientBot hh
  have hxa : (s.val : X ⧸ Q.D)⁻¹*(a : X ⧸ Q.D)^2*s.val = (a : X ⧸ Q.D)^2 := by
    have hh := congrArg Subtype.val hx
    rw [f.numeratorAction_apply] at hh
    simpa only [coe_inv, inv_inv] using hh
  have hconj : (a : X ⧸ Q.D)^2 ∈ rootAt Q split j (Q.simple i*Q.simple j) := by
    rw [← rootAt_right Q split j (Q.simple i) (Q.simple j) s.val s.class_eq, ← hxa]
    change (s.val : X ⧸ Q.D)*((s.val : X ⧸ Q.D)⁻¹*(a : X ⧸ Q.D)^2*s.val)*
      (s.val : X ⧸ Q.D)⁻¹ ∈ rootAt Q split j (Q.simple i)
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using
      pow_mem a.property 2
  exact ha (Subtype.ext (disjoint_def.mp
    (exchanged_roots_disjoint Q split hm j i hij.symm) (pow_mem a.property 2) hconj))
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
