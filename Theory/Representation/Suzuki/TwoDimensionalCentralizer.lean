module

public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import Theory.SpecificGroups.Suzuki.RootOvoidGeometry
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.Representation.ScalarMultiplicity
public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Theory.Representation.FirstCohomologyLinearTransport

/-!
# Suzuki actions on a two-dimensional multiplicity space

An endomorphism of a two-dimensional space in characteristic two whose fourth
power is one already has square one: its nilpotent part has square zero.
The actual order-four Suzuki root element rules out a faithful representation
in this dimension, and simplicity makes every such representation trivial.
The scalar commutant of natural SL₃ then shows that a commuting Suzuki action
on two natural copies fixes the whole module, allowing arbitrary mixing of
the copies. The coordinate version preserves the original action.

Source: Huppert–Blackburn III, XI.3.1 and XI.3.6; Aschbacher–Smith B.5.9(3),
B.5.10(2), and the quiet branch of 10.1.1.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups Subgroup Representation
namespace Representation.Suzuki

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
    {F : Type*} [Field F] [CharP F 2] {m : ℕ} (hm : 0<m)
    (ρ : Representation F (SuzukiMatrixGroup m) (Fin 2 → F)) :
    ¬ Function.Injective ρ := by
  intro hf
  obtain ⟨_,_,_,_,⟨x,hx⟩,_⟩ := BenderSuzuki.External.huppert_blackburn_XI_3_1
    m hm (suzukiTits m) (suzukiTits_sq m)
  let e := subgroupOfEquivOfLe (suzukiRootClosure_le m)
  let y : SuzukiMatrixGroup m := (e.symm x).val
  have hy : orderOf y = 4 :=
    (orderOf_injective (SuzukiRootSubgroup m).subtype
      (SuzukiRootSubgroup m).subtype_injective (e.symm x)).trans
      ((orderOf_injective e.symm.toMonoidHom e.symm.injective x).trans hx)
  have hy4 : y^4=1 := by simpa only [hy] using pow_orderOf_eq_one y
  have h4 : ρ y ^4=1 := by rw [←map_pow,hy4,map_one]
  have h2 : y^2=1 := hf (by rw [map_pow,map_one]; exact square_eq_one_of_fourth_eq_one (ρ y) h4)
  have hd := orderOf_dvd_of_pow_eq_one h2
  rw [hy] at hd
  norm_num at hd

theorem two_dimensional_trivial
    {F : Type*} [Field F] [CharP F 2] {m : ℕ} (hm : 0<m)
    (ρ : Representation F (SuzukiMatrixGroup m) (Fin 2 → F)) :
    ∀ a, ρ a = 1 := by
  let : IsSimpleGroup (SuzukiMatrixGroup m) := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker inferInstance with h | h
  · exact (two_dimensional_not_faithful hm ρ ((MonoidHom.ker_eq_bot_iff ρ).mp h)).elim
  · intro a
    exact h.ge (mem_top a)

/-- A Suzuki action commuting with doubled natural SL₃ fixes the entire module. -/
theorem doubled_natural_commuting_trivial
    {F : Type*} [Field F] [Algebra (ZMod 2) F] {m : ℕ} (hm : 0<m)
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m)
      (SL3DoubledNaturalOffenders.Space F))
    (hc : ∀ a g v, ρ a (SL3DoubledNaturalOffenders.representation F g v) =
      SL3DoubledNaturalOffenders.representation F g (ρ a v)) :
    ∀ a v, ρ a v = v := by
  let σ := Representation.restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)
  obtain ⟨μ,hμ⟩ := ScalarMultiplicity.exists_multiplicity (F := F) σ
    (fun f hf => SL3DoubledNaturalOffenders.natural_centralizer_scalar f.toAddMonoidHom hf)
    ρ hc
  let : CharP F 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  have ht := two_dimensional_trivial hm μ
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
    [AddCommGroup W] [Module (ZMod 2) W] {m : ℕ} (hm : 0<m)
    (τ : Representation (ZMod 2) (SuzukiMatrixGroup m) W)
    (α : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 3) F) W)
    (hc : ∀ a g v, τ a (α g v) = α g (τ a v))
    (e : W ≃ₗ[ZMod 2] SL3DoubledNaturalOffenders.Space F)
    (he : ∀ g v, e (α g v) = SL3DoubledNaturalOffenders.representation F g (e v)) :
    ∀ a v, τ a v = v := by
  let β := e.conjRingEquiv.toMonoidHom.comp τ
  have hβ (a : SuzukiMatrixGroup m) (v) : β a v = e (τ a (e.symm v)) := rfl
  have hcomm (a : SuzukiMatrixGroup m) (g : Matrix.SpecialLinearGroup (Fin 3) F) (v) :
      β a (SL3DoubledNaturalOffenders.representation F g v) =
        SL3DoubledNaturalOffenders.representation F g (β a v) := by
    rw [hβ,hβ]
    have hi : e.symm (SL3DoubledNaturalOffenders.representation F g v) = α g (e.symm v) := by
      apply e.injective
      rw [e.apply_symm_apply,he,e.apply_symm_apply]
    rw [hi,hc,he]
  have ht := doubled_natural_commuting_trivial hm β hcomm
  intro a v
  apply e.injective
  simpa only [hβ,e.symm_apply_apply] using ht a (e v)

end Representation.Suzuki
