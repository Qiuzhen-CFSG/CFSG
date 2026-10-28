module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.FieldExtraction.Descent
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.ModelConjugacyAbsolute
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.PerfectField
public import Theory.SpecificGroups.PSp4Three.MatrixModel

/-!
# Literal symplectic coordinates for compatible trace-field models

A compatible model carries its own nondegenerate alternating form. A genuine
symplectic basis transports its faithful action to the standard matrix group.
Scalar extension retains an actual intertwiner with the original action;
thus a carrier order comparison can recognize the whole coefficient copy.
This supplies the source-specific trace-and-order route in the model inspection
of Aschbacher--Smith G.4.1, printed p.342.
-/

@[expose] public noncomputable section
open Matrix Subgroup Representation
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual
open scoped TensorProduct
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
variable {K F G V:Type*} [Field K] [Field F] [Group G]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- An actual invariant nondegenerate alternating four-form gives a marked
faithful action in the literal symplectic four-space over its own field. -/
theorem exists_marked_symplectic_four_action
    (ρ:Representation K G V) (hf:Function.Injective ρ)
    (hd:Module.finrank K V=4) (B:LinearMap.BilinForm K V)
    (halt:B.IsAlt) (hn:B.Nondegenerate)
    (hp:∀g v w,B (ρ g v) (ρ g w)=B v w) :
    ∃ E:V≃ₗ[K]Vector K, ∃ j:G→*Sp K, Function.Injective j ∧
      ∀g v,E (ρ g v)=j g•E v := by
  obtain ⟨e⟩ := Matrix.PSp4Three.exists_isometry 2 B halt hn hd
  let σ:Representation K G (Vector K) := e.toLinearEquiv.conjRingEquiv.toMonoidHom.comp ρ
  let f := LinearMap.toMatrixAlgEquiv'.toMonoidHom.comp σ
  have hpres (g:G) : f g∈Matrix.symplecticGroup (Fin 2) K := by
    apply Matrix.PSp4Three.mem_iff_preserves.mpr
    intro v w
    change Matrix.PSp4Three.form ((LinearMap.toMatrix' (σ g))*ᵥv)
      ((LinearMap.toMatrix' (σ g))*ᵥw)=_
    rw [LinearMap.toMatrix'_mulVec,LinearMap.toMatrix'_mulVec]
    change Matrix.PSp4Three.form (e (ρ g (e.symm v))) (e (ρ g (e.symm w)))=_
    rw [e.map_app,hp]
    exact (e.map_app (e.symm w) (e.symm v)).symm.trans (by simp)
  let j:G→*Sp K := f.codRestrict _ hpres
  have hj:Function.Injective j := by
    intro a b h
    apply hf
    apply e.toLinearEquiv.conjRingEquiv.injective
    apply LinearMap.toMatrixAlgEquiv'.injective
    exact congrArg Subtype.val h
  refine ⟨e.toLinearEquiv,j,hj,?_⟩
  intro g v
  change e (ρ g v)=LinearMap.toMatrix' (σ g)*ᵥe v
  rw [LinearMap.toMatrix'_mulVec]
  change e (ρ g v)=e (ρ g (e.symm (e v)))
  exact congrArg (fun z=>e (ρ g z)) (e.toLinearEquiv.symm_apply_apply v).symm

section Coefficients
variable [Algebra K F]
variable {ι κ:Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Scalar extension carries an actual coordinate intertwiner to the literal
entrywise coefficient representations, allowing different index types. -/
def coefficientEquivOfEquiv
    (ρ:Representation K G (ι→K)) (τ:Representation K G (κ→K))
    (e:ρ≃ₗτ) : mapCoefficients (algebraMap K F) ρ ≃ₗ
      mapCoefficients (algebraMap K F) τ := by
  let eF:extendScalars F ρ≃ₗextendScalars F τ := .mk
    (e.toLinearEquiv.baseChange K F _ _) (by
      intro g
      simpa only [LinearEquiv.coe_baseChange,extendScalars_apply,
        ←LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange F) (e.isIntertwining' g))
  exact (extendScalarsMapCoefficientsEquiv (E:=F) ρ).symm.trans
    (eF.trans (extendScalarsMapCoefficientsEquiv (E:=F) τ))
end Coefficients

variable [Finite F] [CharP F 2]

set_option linter.unusedSectionVars false in
/-- A compatible trace-field model retains a faithful action in the actual
symplectic coefficient group and an original-F linear intertwiner. -/
theorem exists_symplectic_action_of_trace_model
    (H:Subgroup (Sp F)) (K:Subfield F)
    (M:TraceFieldDescent.Model ((symplecticNatural 2).comp H.subtype) (form F) K) :
    ∃ j:H→*Sp K, Function.Injective j ∧
      ∃ A:Vector F≃ₗ[F]Vector F, ∀g:H,∀v,
        A ((g:Sp F)•v)=coefficientInclusion K (j g)•A v := by
  let ρ:Representation F H (Vector F) := (symplecticNatural 2).comp H.subtype
  have hf:Function.Injective M.action := by
    intro a b hab
    apply Subtype.ext
    have hcoeff : mapCoefficients K.subtype M.action a=mapCoefficients K.subtype M.action b := by
      apply LinearMap.toMatrix'.injective
      simp only [mapCoefficients_toMatrix,hab]
    have he : ρ a=ρ b := by
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := M.equiv.toLinearEquiv.surjective v
      have ha := LinearMap.congr_fun (M.equiv.isIntertwining' a) w
      have hb := LinearMap.congr_fun (M.equiv.isIntertwining' b) w
      exact ha.symm.trans ((congrArg M.equiv (LinearMap.congr_fun hcoeff w)).trans hb)
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext v
    exact LinearMap.congr_fun he v
  have hd:Module.finrank K (Fin (Module.finrank F (Vector F))→K)=4 := by simp [Vector]
  obtain ⟨E,j,hj,hE⟩ := exists_marked_symplectic_four_action M.action hf hd
    M.form M.alternating M.nondegenerate M.invariant
  let τ:Representation K H (Vector K) := (symplecticNatural 2).comp j
  let e:M.action≃ₗτ := .mk E (by
    intro g
    apply LinearMap.ext
    exact hE g)
  let ef := coefficientEquivOfEquiv (F:=F) M.action τ e
  let A := M.equiv.toLinearEquiv.symm.trans ef.toLinearEquiv
  refine ⟨j,hj,A,?_⟩
  intro g v
  have h1:=LinearMap.congr_fun (M.equiv.symm.isIntertwining' g) v
  have h2:=LinearMap.congr_fun (ef.isIntertwining' g) (M.equiv.symm v)
  change ef (M.equiv.symm (ρ g v))=coefficientInclusion K (j g)•ef (M.equiv.symm v)
  rw [show M.equiv.symm (ρ g v)=mapCoefficients K.subtype M.action g (M.equiv.symm v) from h1]
  rw [show ef (mapCoefficients K.subtype M.action g (M.equiv.symm v))=
    mapCoefficients K.subtype τ g (ef (M.equiv.symm v)) from h2]
  have hm : mapCoefficients K.subtype τ g=symplecticNatural 2 (coefficientInclusion K (j g)) := by
    apply LinearMap.toMatrix'.injective
    rw [mapCoefficients_toMatrix]
    change (LinearMap.toMatrix' ((j g).val.mulVecLin)).map K.subtype=
      LinearMap.toMatrix' ((coefficientInclusion K (j g)).val.mulVecLin)
    rw [show (j g).val.mulVecLin=Matrix.toLin' (j g).val from rfl,
      show (coefficientInclusion K (j g)).val.mulVecLin=
        Matrix.toLin' (coefficientInclusion K (j g)).val from rfl,
      LinearMap.toMatrix'_toLin',LinearMap.toMatrix'_toLin']
    ext i k
    exact (coefficientInclusion_apply K (j g) i k).symm
  exact LinearMap.congr_fun hm _
end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
