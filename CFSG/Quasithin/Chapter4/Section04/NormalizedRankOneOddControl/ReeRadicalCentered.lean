module

public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.ReeLocal
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Suzuki.Centered
public import Theory.GroupTheory.PRadical.NormalComponentImages

/-!
# Centered modules in radical Ree normalizers

Full normalizer coverage puts the actual radical in a parabolic. Radical
saturation contains the parabolic radical. In the Suzuki parabolic, its
center centralizes the perfect seed, which contains every perfect actor.
Consequently a centered module equal to its actor commutator is trivial.
The linear parabolic is excluded through its actual projection.

Source: Aschbacher--Smith C.3.5 and 4.2.12--13, pp.150,610--612;
F.1.12(I)(5), pp.263--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open ReeF4.ConverseParabolics

private theorem perfect_le_suzuki_seed {m : ℕ} (hm : 1 ≤ m)
    (B : Subgroup (parabolic m .suzuki)) [Group.IsPerfect B] :
    B ≤ CoreActionRigidity.suzukiSeed m := by
  let D := solvableResidual (parabolic m .suzuki)
  have hBD : B ≤ D := le_solvableResidual_of_isPerfect B
  by_cases hd : Group.IsSolvable D
  · let := hd
    have hs : Subsingleton D := by
      by_contra! hn
      exact Group.IsPerfect.not_isSolvable D inferInstance
    have he : D = ⊥ := by
      apply bot_unique
      intro x hx
      exact congrArg D.subtype (hs.elim (⟨x,hx⟩ : D) 1)
    exact (hBD.trans he.le).trans bot_le
  · rw [CoreActionRigidity.suzuki_perfect_normal_eq_seed hm D hd] at hBD
    exact hBD

/-- Radical saturation and the original radical center kill a commutator
module in the full Suzuki-side Ree parabolic. -/
theorem ree_suzuki_radical_centered_commutator
    {m : ℕ} (hm : 1 ≤ m) (P B U : Subgroup (ReeF4.Model m))
    [Group.IsPerfect B]
    (hp : IsPGroup 2 P) (hpr : (normalizer (P : Set _)).pCoreIn 2 = P)
    (hcov : normalizer (P : Set _) ≤ parabolic m .suzuki)
    (hB : B ≤ normalizer (P : Set _))
    (hU : U ≤ P ⊓ centralizer (P : Set _)) (hcomm : U = ⁅U,B⁆) : U = ⊥ := by
  let Z := radical m .suzuki
  have hZP : Z ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le P Z
    hp (radical_isPGroup m .suzuki) hpr.le
    (hcov.trans (suzuki_parabolic_le_radical_normalizer m))
  have hUP : U ≤ parabolic m .suzuki := (hU.trans inf_le_left).trans (P.le_normalizer.trans hcov)
  have hUZ : U ≤ centralizer (Z : Set _) := (hU.trans inf_le_right).trans (centralizer_le hZP)
  have hUR : U ≤ Z := by
    intro u hu
    have hu' : (⟨u,hUP hu⟩ : parabolic m .suzuki) ∈
        centralizer (intrinsicRadical m .suzuki : Set (parabolic m .suzuki)) := by
      intro z hz
      exact Subtype.ext (hUZ hu z.val hz)
    exact suzuki_intrinsicRadical_centralizer_le hm hu'
  let A := B.subgroupOf (parabolic m .suzuki)
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (hB.trans hcov)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (hB.trans hcov)).symm.surjective
  have hseed : B ≤ ReeF4.Parabolics.seed m .suzuki := by
    intro b hb
    have hh := perfect_le_suzuki_seed hm A (show (⟨b,hB.trans hcov hb⟩ : parabolic m .suzuki) ∈ A from hb)
    rwa [CoreActionRigidity.suzukiSeed_eq_subgroupOf] at hh
  have hc : U ≤ centralizer (B : Set _) := by
    intro u hu b hb
    exact (ReeF4.NormalizedRootCentralizers.CenterExponent.suzuki_radical_center_centralizes_seed m
      u (by rw [←radical_eq_rootRadical]; exact hUR hu)
      (fun z hz => (hUZ hu z (by change z ∈ radical m .suzuki; rwa [radical_eq_rootRadical])).symm)
      b (hseed hb)).eq.symm
  exact hcomm.trans (commutator_eq_bot_iff_le_centralizer.mpr hc)

/-- Full normalizer coverage excludes every centered radical module moved
by the actual marked residual. The full normalizer, not just its actor, is covered. -/
theorem no_ree_radical_centered_module
    {A S : Type*} [Group A] [Group.IsPerfect A] [Group S] [Finite S] [IsSimpleGroup S]
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : A →* S) (hπ : Function.Surjective π)
    {m : ℕ} (hm : 1 ≤ m) (P U : Subgroup (ReeF4.Model m))
    (hp : IsPGroup 2 P) (hpr : (normalizer (P : Set _)).pCoreIn 2 = P)
    (hU : U ≤ P ⊓ centralizer (P : Set _)) (hne : U ≠ ⊥)
    (r : A →* ReeF4.Model m) [Group.IsSolvable r.ker]
    (hr : r.range ≤ normalizer (P : Set _)) (hcomm : U = ⁅U,r.range⁆) : False := by
  have hpne : P ≠ ⊥ := fun he => hne (bot_unique ((hU.trans inf_le_left).trans he.le))
  obtain ⟨g,b,hcover⟩ := normalizer_cover hm P hpne hp
  let c := (MulAut.conj g).toMonoidHom
  let P' := P.map c
  let U' := U.map c
  let r' := c.comp r
  have hr' : r'.range ≤ normalizer (P' : Set _) := by
    rw [MonoidHom.range_comp]
    exact (map_mono hr).trans (P.le_normalizer_map c)
  have hc' : normalizer (P' : Set _) ≤ parabolic m b := by
    rwa [map_equiv_normalizer_eq] at hcover
  have hker : Group.IsSolvable r'.ker := by
    rw [show r'.ker = r.ker from MonoidHom.ker_comp_of_injective r c (MulAut.conj g).injective]
    infer_instance
  let := hker
  cases b with
  | linear =>
    let k := r'.codRestrict (parabolic m .linear) (fun x => hc' (hr' ⟨x,rfl⟩))
    have hk : k.ker = r'.ker := by ext x; exact Subtype.ext_iff
    let : Group.IsSolvable k.ker := hk.symm ▸ hker
    exact no_ree_linear_parabolic hS hexp π hπ hm k
  | suzuki =>
    have hP' : (normalizer (P' : Set _)).pCoreIn 2 = P' :=
      map_normalizer_core_of_p_kernel P hp hpr c (MulAut.conj g).surjective (by
        rw [(MonoidHom.ker_eq_bot_iff c).mpr (MulAut.conj g).injective]; exact bot_le)
    have hU' : U' ≤ P' ⊓ centralizer (P' : Set _) :=
      le_inf (map_mono (hU.trans inf_le_left))
        ((map_mono (hU.trans inf_le_right)).trans (map_centralizer_le_centralizer_image _ _))
    have hm' : U' = ⁅U',r'.range⁆ := by
      rw [MonoidHom.range_comp,←map_commutator]
      exact congrArg (map c) hcomm
    let : Group.IsPerfect r'.range := Group.IsPerfect.range r'
    have hb := ree_suzuki_radical_centered_commutator hm P' r'.range U'
      (hp.map c) hP' hc' hr' hU' hm'
    exact hne ((U.map_eq_bot_iff_of_injective (MulAut.conj g).injective).mp hb)

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
