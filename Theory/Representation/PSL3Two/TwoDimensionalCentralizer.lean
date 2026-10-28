module

public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.Representation.ScalarMultiplicity
public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Linear-three actions on a two-dimensional multiplicity space

In characteristic two an endomorphism of a two-dimensional space whose
fourth power is one already has square one. An explicit order-four element
of PSL₃(2), together with simplicity, makes every such action trivial.
The scalar commutant calculation then rules out a nontrivial commuting
PSL₃(2) action on two natural SL₃ copies, over any binary field.

Source application: Aschbacher–Smith 13.4.7(2), printed p.902.
-/

public noncomputable section
open Subgroup Representation
open Matrix.PSL3Two
namespace Representation.PSL3Two

private theorem square_eq_one_of_fourth_eq_one
    {F : Type*} [Field F] [CharP F 2]
    (u : Module.End F (Fin 2 → F)) (hu : u^4=1) : u^2=1 := by
  let : CharP (Module.End F (Fin 2 → F)) 2 := charP_of_injective_algebraMap' F 2
  have h4 : (u-1)^4=0 := by
    have h := sub_pow_char_pow_of_commute (R := Module.End F (Fin 2 → F)) 2 2
      (Commute.one_right u)
    simpa only [show 2^2=4 from rfl,hu,one_pow,sub_self] using h
  have hker := Module.End.ker_pow_le_ker_pow_finrank (u-1) 4
  rw [Module.finrank_fintype_fun_eq_card,Fintype.card_fin,h4,LinearMap.ker_zero] at hker
  have h2 : (u-1)^2=0 := LinearMap.ker_eq_top.mp (top_le_iff.mp hker)
  have h := sub_pow_char_of_commute (R := Module.End F (Fin 2 → F)) 2 (Commute.one_right u)
  rw [h2,one_pow] at h
  exact sub_eq_zero.mp h.symm

theorem two_dimensional_not_faithful
    {F : Type*} [Field F] [CharP F 2] (ρ : Representation F PSL (Fin 2 → F)) :
    ¬ Function.Injective ρ := by
  intro hf
  let x : SL := ⟨!![1,1,0; 0,1,1; 0,0,1], by decide⟩
  let y : PSL := equiv x
  have hx4 : x ^ 4 = 1 := by decide
  have hx2 : x ^ 2 ≠ 1 := by decide
  have hy4 : y ^ 4 = 1 := by
    change equiv x ^ 4 = 1
    rw [←map_pow,hx4,map_one]
  have h4 : ρ y ^ 4 = 1 := by rw [←map_pow,hy4,map_one]
  have h2 : y ^ 2 = 1 := hf (by
    rw [map_pow,map_one]
    exact square_eq_one_of_fourth_eq_one (ρ y) h4)
  apply hx2
  apply equiv.injective
  simpa only [map_pow,map_one] using h2

theorem two_dimensional_trivial
    {F : Type*} [Field F] [CharP F 2] (ρ : Representation F PSL (Fin 2 → F)) :
    ∀ a, ρ a = 1 := by
  let : IsSimpleGroup PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker inferInstance with h | h
  · exact (two_dimensional_not_faithful ρ ((MonoidHom.ker_eq_bot_iff ρ).mp h)).elim
  · intro a
    exact h.ge (mem_top a)

/-- A PSL₃(2) action commuting with doubled natural SL₃ fixes the entire module. -/
theorem doubled_natural_commuting_trivial
    {F : Type*} [Field F] [Algebra (ZMod 2) F] (ρ : Representation (ZMod 2) PSL
      (SL3DoubledNaturalOffenders.Space F))
    (hc : ∀ a g v, ρ a (SL3DoubledNaturalOffenders.representation F g v) =
      SL3DoubledNaturalOffenders.representation F g (ρ a v)) :
    ∀ a v, ρ a v = v := by
  let σ := Representation.restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)
  obtain ⟨μ,hμ⟩ := ScalarMultiplicity.exists_multiplicity (F := F) σ
    (fun f hf => SL3DoubledNaturalOffenders.natural_centralizer_scalar f.toAddMonoidHom hf)
    ρ hc
  let : CharP F 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  have ht := two_dimensional_trivial μ
  intro a v
  have he : v = ∑ i : Fin 2, Pi.single i (v i) := by funext i; fin_cases i <;> simp
  rw [he,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs : (fun j => (Pi.single i (1:F) : Fin 2 → F) j • v i) = Pi.single i (v i) := by
    funext j
    by_cases h : i=j
    · subst j; simp
    · simp [Ne.symm h]
  rw [←hs,hμ,ht]
  rfl

theorem doubled_natural_commuting_trivial_of_coordinates
    {F W : Type*} [Field F] [Algebra (ZMod 2) F]
    [AddCommGroup W] [Module (ZMod 2) W] (τ : Representation (ZMod 2) PSL W)
    (α : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) F) W)
    (hc : ∀ a g v, τ a (α g v) = α g (τ a v))
    (e : W ≃ₗ[ZMod 2] SL3DoubledNaturalOffenders.Space F)
    (he : ∀ g v, e (α g v) = SL3DoubledNaturalOffenders.representation F g (e v)) :
    ∀ a v, τ a v = v := by
  let β := e.conjRingEquiv.toMonoidHom.comp τ
  have hβ (a : PSL) (v) : β a v = e (τ a (e.symm v)) := rfl
  have hcomm (a : PSL) (g : Matrix.SpecialLinearGroup (Fin 3) F) (v) :
      β a (SL3DoubledNaturalOffenders.representation F g v) =
        SL3DoubledNaturalOffenders.representation F g (β a v) := by
    rw [hβ,hβ]
    have hi : e.symm (SL3DoubledNaturalOffenders.representation F g v) = α g (e.symm v) := by
      apply e.injective
      rw [e.apply_symm_apply,he,e.apply_symm_apply]
    rw [hi,hc,he]
  have ht := doubled_natural_commuting_trivial β hcomm
  intro a v
  apply e.injective
  simpa only [hβ,e.symm_apply_apply] using ht a (e v)

end Representation.PSL3Two
