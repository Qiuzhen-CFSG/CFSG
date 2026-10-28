module
public import Theory.Representation.SL3.AdjointCubicCentralizer.GraphExtension.Character

/-!
# Graph-field compatibility removes adjoint twists

Transpose followed by coefficient transport intertwines ordinary conjugation
with inverse transpose and field transport. Any binary intertwiner differs
from this map by an F-scalar. Compatibility both preserves and inverts the
scalar character, which has odd order three, so the extension is ordinary.

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
variable (F : Type*) [Field F] [CharP F 2]
attribute [local instance] ZMod.algebra

def graphFieldMap (σ : F ≃+* F) : Module.End (ZMod 2) (TraceZero F) :=
  AddMonoidHom.toZModLinearMap 2
    ({ toFun X := ⟨(X.val.map σ).transpose,by
         change Matrix.trace (X.val.map σ).transpose = 0
         rw [Matrix.trace_transpose]
         have ht : X.val 0 0 + X.val 1 1 + X.val 2 2 = 0 := by
           have h := X.property
           change Matrix.trace X.val = 0 at h
           simpa only [Matrix.trace,Fin.sum_univ_three,Matrix.diag_apply] using h
         simp only [Matrix.trace,Fin.sum_univ_three,Matrix.diag_apply,Matrix.map_apply]
         rw [←map_add,←map_add,ht,map_zero]⟩
       map_zero' := by
         apply Subtype.ext
         ext i j
         exact map_zero σ
       map_add' X Y := by
         apply Subtype.ext
         ext i j
         exact map_add σ (X.val j i) (Y.val j i) } : TraceZero F →+ TraceZero F)

theorem graphFieldMap_smul (σ : F ≃+* F) (c : F) (v : TraceZero F) :
    graphFieldMap F σ (c • v) = σ c • graphFieldMap F σ v := by
  apply Subtype.ext
  ext i j
  exact map_mul σ c (v.val j i)

theorem graphFieldMap_inverse (σ : F ≃+* F) (v : TraceZero F) :
    graphFieldMap F σ.symm (graphFieldMap F σ v) = v := by
  apply Subtype.ext
  ext i j
  exact σ.symm_apply_apply (v.val i j)

def graphFieldEquiv (σ : F ≃+* F) : TraceZero F ≃ₗ[ZMod 2] TraceZero F :=
  LinearEquiv.ofBijective (graphFieldMap F σ)
    ⟨Function.LeftInverse.injective (graphFieldMap_inverse F σ),fun v =>
      ⟨graphFieldMap F σ.symm v,by
        simpa only [RingEquiv.symm_symm] using graphFieldMap_inverse F σ.symm v⟩⟩

theorem graphFieldMap_inverse_right (σ : F ≃+* F) (v : TraceZero F) :
    graphFieldMap F σ (graphFieldMap F σ.symm v) = v := by
  simpa using graphFieldMap_inverse F σ.symm v

theorem graphFieldMap_adjoint (σ : F ≃+* F) (g : GL (Fin 3) F) (v : TraceZero F) :
    graphFieldMap F σ (binaryAdjoint F g v) =
      binaryAdjoint F (graphFieldGL F σ g) (graphFieldMap F σ v) := by
  apply Subtype.ext
  change ((g.val * v.val * g.inv).map σ).transpose =
    (g.inv.map σ).transpose * (v.val.map σ).transpose * (g.val.map σ).transpose
  simp only [Matrix.map_mul,Matrix.transpose_mul,mul_assoc]

variable [Finite F]

omit [Finite F] in
private theorem representation_eq_of_det_one
    (R : Representation (ZMod 2) (GL (Fin 3) F) (TraceZero F))
    (hR : ∀ s : SL(3,F), R (SpecialLinearGroup.toGL s) = binaryAdjoint F (SpecialLinearGroup.toGL s))
    (g : GL (Fin 3) F) (hg : GeneralLinearGroup.det g = 1) : R g = binaryAdjoint F g := by
  let s := (Matrix.PSL3.OuterSolvable.slEquivDetKernel F).symm ⟨g,hg⟩
  have hs : SpecialLinearGroup.toGL s = g :=
    Matrix.PSL3.OuterSolvable.slEquivDetKernel_symm_toGL F _
  rw [←hs]
  exact hR s

theorem intertwiner_scalar (hF : Nat.card F = 4)
    (R : Representation (ZMod 2) (GL (Fin 3) F) (TraceZero F))
    (hR : ∀ s : SL(3,F), R (SpecialLinearGroup.toGL s) = binaryAdjoint F (SpecialLinearGroup.toGL s))
    (σ : F ≃+* F) (u : TraceZero F ≃ₗ[ZMod 2] TraceZero F)
    (hu : ∀ g v, u (R g v) = R (graphFieldGL F σ g) (u v)) :
    ∃ c : F, c ≠ 0 ∧ ∀ v, u v = c • graphFieldMap F σ v := by
  let f := (graphFieldMap F σ.symm).comp u.toLinearMap
  obtain ⟨b,hb⟩ := commutant_scalar F hF f (by
    intro s v
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL(3,F)) s
    have hd : GeneralLinearGroup.det (graphFieldGL F σ (SpecialLinearGroup.toGL x)) = 1 := by
      rw [det_graphFieldGL,SpecialLinearGroup.coeToGL_det,inv_one,map_one]
    have he := hu (SpecialLinearGroup.toGL x) v
    rw [hR,representation_eq_of_det_one F R hR _ hd] at he
    apply (graphFieldEquiv F σ).injective
    change graphFieldMap F σ (graphFieldMap F σ.symm (u (binaryAdjoint F _ v))) =
      graphFieldMap F σ (binaryAdjoint F _ (graphFieldMap F σ.symm (u v)))
    rw [graphFieldMap_inverse_right F σ,graphFieldMap_adjoint,
      graphFieldMap_inverse_right F σ]
    exact he)
  have he (v) : u v = σ b • graphFieldMap F σ v := by
    have h := congrArg (graphFieldMap F σ) (hb v)
    change graphFieldMap F σ (graphFieldMap F σ.symm (u v)) = _ at h
    rw [graphFieldMap_inverse_right F σ,graphFieldMap_smul] at h
    exact h
  refine ⟨σ b,?_,he⟩
  intro hz
  have hh := he (highestRoot F)
  rw [hz,zero_smul] at hh
  exact highestRoot_ne_zero F (u.injective (hh.trans u.map_zero.symm))

theorem ordinary_of_graphField (hF : Nat.card F = 4)
    (R : Representation (ZMod 2) (GL (Fin 3) F) (TraceZero F))
    (hR : ∀ s : SL(3,F), R (SpecialLinearGroup.toGL s) = binaryAdjoint F (SpecialLinearGroup.toGL s))
    (σ : F ≃+* F) (u : TraceZero F ≃ₗ[ZMod 2] TraceZero F)
    (hu : ∀ g v, u (R g v) = R (graphFieldGL F σ g) (u v)) : R = binaryAdjoint F := by
  obtain ⟨χ,hχ,hχs⟩ := scalar_extension_character F hF R hR
  obtain ⟨c,hc,hcu⟩ := intertwiner_scalar F hF R hR σ u hu
  have htriv (g : GL (Fin 3) F) : χ g = 1 := by
    have he (v : TraceZero F) :
        (σ (χ g : F)) • binaryAdjoint F (graphFieldGL F σ g) (graphFieldMap F σ v) =
        (χ (graphFieldGL F σ g) : F) •
          binaryAdjoint F (graphFieldGL F σ g) (graphFieldMap F σ v) := by
      have hh := hu g v
      rw [hcu,hχ,graphFieldMap_smul,graphFieldMap_adjoint,hχ,hcu,
        binaryAdjoint_smul] at hh
      apply (smul_right_injective _ hc)
      simpa only [smul_smul,mul_comm c] using hh
    have hn : binaryAdjoint F (graphFieldGL F σ g) (graphFieldMap F σ (highestRoot F)) ≠ 0 := by
      intro hz
      have hh := (binaryAdjoint F).apply_bijective (graphFieldGL F σ g) |>.1
      have hz' : graphFieldMap F σ (highestRoot F) = 0 := hh (hz.trans (map_zero _).symm)
      exact highestRoot_ne_zero F ((graphFieldEquiv F σ).injective (hz'.trans (map_zero _).symm))
    have hval := smul_left_injective F hn (he (highestRoot F))
    rw [character_graphField F χ hχs] at hval
    have huinv : Units.map σ.toMonoidHom (χ g) = Units.map σ.toMonoidHom (χ g)⁻¹ := Units.ext hval
    have hinv : χ g = (χ g)⁻¹ := by
      apply Units.ext
      exact σ.injective (congrArg Units.val huinv)
    have hsq : χ g ^ 2 = 1 := by
      calc
        χ g ^ 2 = χ g * χ g := pow_two _
        _ = χ g * (χ g)⁻¹ := congrArg (fun z => χ g * z) hinv
        _ = 1 := mul_inv_cancel _
    have hcube := units_cube_of_card_four F hF (χ g)
    simpa only [pow_succ,hsq,one_mul] using hcube
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  simpa only [htriv,Units.val_one,one_smul] using hχ g v

end
end Representation.SL3.AdjointCubicCentralizer.GraphExtension
