module
public import Theory.Representation.SL3.AdjointCubicCentralizer.GraphExtension.Commutant
public import Theory.SpecificGroups.PSL3.OuterSolvable.StandardQuotient

/-!
# Scalar characters of adjoint extensions

Compare an extension with ordinary conjugation at each GL₃ element. Their
ratio commutes with the actual PSL₃ action, hence is an F-scalar. Uniqueness
of that scalar supplies a character, trivial on the literal SL₃ image.

Source motivation: Aschbacher–Smith B.4.14, printed p.98, and the nonblock
argument for original 4.3.2, pp.618–619. These are representation consequences
of explicit action hypotheses; constructing the source Frattini marking and
discharging its action-kernel descent are separate source obligations.
-/

open Matrix Representation
open scoped MatrixGroups
namespace Representation.SL3.AdjointCubicCentralizer.GraphExtension
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (F : Type*) [Field F] [CharP F 2] [Finite F]
attribute [local instance] ZMod.algebra

abbrev binaryAdjoint : Representation (ZMod 2) (GL (Fin 3) F) (TraceZero F) :=
  restrictScalars (k := ZMod 2) (adjointAction F)

omit [Finite F] in
theorem binaryAdjoint_smul (g : GL (Fin 3) F) (c : F) (v : TraceZero F) :
    binaryAdjoint F g (c • v) = c • binaryAdjoint F g v :=
  (adjointAction F g).map_smul c v

theorem extension_scalar (hF : Nat.card F = 4)
    (R : Representation (ZMod 2) (GL (Fin 3) F) (TraceZero F))
    (hR : ∀ s : SL(3,F), R (SpecialLinearGroup.toGL s) = binaryAdjoint F (SpecialLinearGroup.toGL s))
    (g : GL (Fin 3) F) :
    ∃ c : F, ∀ v, R g v = c • binaryAdjoint F g v := by
  let A := binaryAdjoint F
  let f := A g⁻¹ * R g
  obtain ⟨c,hc⟩ := commutant_scalar F hF f (by
    intro s v
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) s
    let y := Matrix.PSL3.OuterSolvable.linearConjSL F g x
    have hy : SpecialLinearGroup.toGL y = g * SpecialLinearGroup.toGL x * g⁻¹ :=
      Matrix.PSL3.OuterSolvable.linearConjSL_toGL F g x
    have he : R g * A (SpecialLinearGroup.toGL x) = A (SpecialLinearGroup.toGL y) * R g := by
      rw [←hR,←hR,hy,←map_mul,←map_mul]
      simp only [mul_assoc,inv_mul_cancel,mul_one]
    have ha : A g⁻¹ * A (SpecialLinearGroup.toGL y) = A (SpecialLinearGroup.toGL x) * A g⁻¹ := by
      rw [←map_mul,←map_mul,hy]
      congr 1
      group
    change (f * A (SpecialLinearGroup.toGL x)) v = (A (SpecialLinearGroup.toGL x) * f) v
    dsimp only [f]
    rw [mul_assoc,he,←mul_assoc,ha,mul_assoc])
  refine ⟨c,fun v => ?_⟩
  have he := congrArg (A g) (hc v)
  change (A g * A g⁻¹) (R g v) = A g (c • v) at he
  rw [←map_mul,mul_inv_cancel,map_one] at he
  exact he.trans (binaryAdjoint_smul F g c v)

theorem scalar_extension_character (hF : Nat.card F = 4)
    (R : Representation (ZMod 2) (GL (Fin 3) F) (TraceZero F))
    (hR : ∀ s : SL(3,F), R (SpecialLinearGroup.toGL s) = binaryAdjoint F (SpecialLinearGroup.toGL s)) :
    ∃ χ : GL (Fin 3) F →* Fˣ,
      (∀ g v, R g v = (χ g : F) • binaryAdjoint F g v) ∧
      ∀ s : SL(3,F), χ (SpecialLinearGroup.toGL s) = 1 := by
  choose c hc using extension_scalar F hF R hR
  have hn (g : GL (Fin 3) F) : c g ≠ 0 := by
    intro hz
    have hh := hc g (highestRoot F)
    rw [hz,zero_smul] at hh
    exact highestRoot_ne_zero F ((R.apply_bijective g).1 (hh.trans (map_zero _).symm))
  have heq (g : GL (Fin 3) F) {a b : F}
      (h : ∀ v, a • binaryAdjoint F g v = b • binaryAdjoint F g v) : a = b := by
    obtain ⟨v,hv⟩ := (binaryAdjoint F).apply_bijective g |>.2 (highestRoot F)
    exact smul_left_injective F (highestRoot_ne_zero F) (hv ▸ h v)
  have hmul (g k : GL (Fin 3) F) : c (g*k) = c g * c k := by
    apply heq (g*k)
    intro v
    rw [←hc,map_mul,Module.End.mul_apply,hc,hc,
      binaryAdjoint_smul F g,smul_smul]
    rw [map_mul,Module.End.mul_apply]
  have hspecial (s : SL(3,F)) : c (SpecialLinearGroup.toGL s) = 1 := by
    apply heq (SpecialLinearGroup.toGL s)
    intro v
    rw [←hc,hR,one_smul]
  let χ : GL (Fin 3) F →* Fˣ :=
    { toFun g := Units.mk0 (c g) (hn g)
      map_one' := Units.ext (by simpa using hspecial 1)
      map_mul' g k := Units.ext (hmul g k) }
  exact ⟨χ,hc,fun s => Units.ext (hspecial s)⟩

end
end Representation.SL3.AdjointCubicCentralizer.GraphExtension
