module
public import Theory.GroupTheory.NormalizerAction.OmegaCenterModels
public import CFSG.Quasithin.Chapter15.Section01.CaseI.OrdinarySource.CentralizerComparison
public import Theory.GroupTheory.PResidual.PrimeToPerfect
/-!
# The actual ordinary-component omega center and residual escape

A model's elementary Sylow-fixer bound controls the omega center of the
literal image of N_S(L) in N_{G1}(L)/C_{G1}(L). Every original central
involution maps into that omega center. If the actual two-perfect residual
Y inside L escaped M_Z but centralized this image, central two-kernel
rigidity would make Y centralize all original central involutions, placing
Y in M_Z. Thus the image escapes, and the omega center has order two.

The final comparison consumes these two deductions on the original
quotient maps. It retains the marked model, component, and the earlier
source residual escape; it assumes no replacement parabolic.
Source: Aschbacher--Smith15.1.22(**), printed p.1099.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Chapter15.Section03 Chapter15.Section03.InitialSource ChapterA.Section05To06
open Subgroup.NormalizerAction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

theorem ordinary_omega_bound_of_model (d : CaseIComponentData T M Mc V)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hcenter : center d.L = pCore 2 d.L)
    (hSL : Chapter1.IsSylowIn 2 d.SL d.L)
    {X : Type*} [Group X] (e : (d.L ⧸ pCore 2 d.L) ≃* X)
    (hfix : ∀ (Q : Sylow 2 X) (B : Subgroup (MulAut X)),
      IsElementaryAbelian 2 B → (∀ b ∈ B, ∀ x ∈ Q, b x = x) → Nat.card B ≤ 2) :
    Nat.card (omega₁ (center (sylowImage (d.L.subgroupOf d.G1)
      (d.S.subgroupOf d.G1))) (p := 2)) ≤ 2 := by
  let K := d.L.subgroupOf d.G1
  let a : K ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  let eK : (K ⧸ center K) ≃* X :=
    ((QuotientGroup.congr _ _ a (map_center_equiv a)).trans
      (QuotientGroup.quotientMulEquivOfEq hcenter)).trans e
  let := hL.2
  obtain ⟨P,hP⟩ := hSL
  let Q := P.mapSurjective (f := a.symm.toMonoidHom) a.symm.surjective
  apply omega_center_card_le_of_model_fixers K (d.S.subgroupOf d.G1) Q _ eK hfix
  rintro x ⟨y,hy,rfl⟩
  exact (hP ▸ mem_map_of_mem d.L.subtype hy).1

/-- The original central involutions remain in the omega center of the exact star Sylow image. -/
theorem ordinary_central_image_mem_omega (d : CaseIComponentData T M Mc V)
    (hn : centralInvolutions T ≤ normalizer (d.L : Set G)) (hZ1T : d.Z1 ≤ (T : Subgroup G))
    {z : G} (hz : z ∈ centralInvolutions T) :
    ∃ zn : normalizer (d.L.subgroupOf d.G1 : Set d.G1),
      ((zn : d.G1) : G) = z ∧ quotient (d.L.subgroupOf d.G1) zn ∈
        omegaCenterIn (sylowImage (d.L.subgroupOf d.G1) (d.S.subgroupOf d.G1)) := by
  let K := d.L.subgroupOf d.G1
  have hzG : z ∈ d.G1 := centralizer_le hZ1T (centralInvolutions_le_centralizer_sylow T hz)
  let zn : normalizer (K : Set d.G1) :=
    ⟨⟨z,hzG⟩,le_normalizer_comap d.G1.subtype (hn hz)⟩
  refine ⟨zn,rfl,(mem_omegaCenterIn_iff _ _).mpr ⟨?_,?_,?_⟩⟩
  · exact ⟨zn,⟨centralInvolutions_le_sylow T hz,hzG⟩,rfl⟩
  · rintro _ ⟨s,hs,rfl⟩
    have hh : s * zn = zn * s := Subtype.ext (Subtype.ext
      (centralInvolutions_le_centralizer_sylow T hz s.val.val hs.1))
    simpa only [map_mul] using congrArg (quotient K) hh
  · rw [←map_pow]
    have hz2g : z ^ 2 = 1 := by
      change z ∈ omegaCenterIn (T : Subgroup G) at hz
      exact (mem_omegaCenterIn_iff _ _).mp hz |>.2.2
    have hz2 : zn ^ 2 = 1 := Subtype.ext (Subtype.ext hz2g)
    rw [hz2,map_one]

/-- Escape of the actual two-perfect residual gives escape in the faithful image, even for a central cover. -/
theorem ordinary_residual_image_escape (d : CaseIComponentData T M Mc V)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hn : centralInvolutions T ≤ normalizer (d.L : Set G)) (hZ1T : d.Z1 ≤ (T : Subgroup G))
    (hcenterTwo : IsPGroup 2 (center d.L))
    (Y : Subgroup G) (hYL : Y ≤ d.L) (hYp : IsPPerfect 2 Y) (hout : ¬ Y ≤ d.MZ) :
    let K := d.L.subgroupOf d.G1
    let A := sylowImage K (d.S.subgroupOf d.G1)
    ¬ omegaCenterIn A ≤ centralizer
      (((Y.subgroupOf d.G1).subgroupOf (normalizer (K : Set d.G1))).map
        (quotient K) : Set (NormalizerAction.Star K)) := by
  dsimp only
  let K := d.L.subgroupOf d.G1
  let B := Y.subgroupOf d.G1
  let a : K ≃* d.L := subgroupOfEquivOfLe d.L_component.1
  have hYg : Y ≤ d.G1 := hYL.trans d.L_component.1
  have hpB : IsPPerfect 2 B := hYp.of_surjective
    (subgroupOfEquivOfLe hYg).symm.toMonoidHom (subgroupOfEquivOfLe hYg).symm.surjective
  have hzK : IsPGroup 2 (center K) := hcenterTwo.of_equiv (centerCongr a).symm
  intro hc
  have hYc : Y ≤ centralizer (centralInvolutions T : Set G) := by
    intro y hy z hz
    obtain ⟨zn,hzn,hzo⟩ := d.ordinary_central_image_mem_omega hn hZ1T hz
    have hh := centralizes_of_quotient_centralizes K B (comap_mono hYL) hpB hzK zn (hc hzo)
    have he := hh (⟨y,hYg hy⟩ : d.G1) hy
    have he' := congrArg Subtype.val he
    change y * ((zn : d.G1) : G) = ((zn : d.G1) : G) * y at he'
    rw [hzn] at he'
    exact he'.symm
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  exact hout (le_inf hYg (hYc.trans hMc.2))

/-- Source22 ordinary equality with both faithful-image obligations discharged by a marked model. -/
theorem ordinary_residual_centralizer_of_model (d : CaseIComponentData T M Mc V)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hcenter : center d.L = pCore 2 d.L)
    (hcenterTwo : IsPGroup 2 (center d.L))
    (hn : centralInvolutions T ≤ normalizer (d.L : Set G))
    (hSL : Chapter1.IsSylowIn 2 d.SL d.L) (hZ1T : d.Z1 ≤ (T : Subgroup G))
    {X : Type*} [Group X] (e : (d.L ⧸ pCore 2 d.L) ≃* X)
    (hfix : ∀ (Q : Sylow 2 X) (B : Subgroup (MulAut X)),
      IsElementaryAbelian 2 B → (∀ b ∈ B, ∀ x ∈ Q, b x = x) → Nat.card B ≤ 2)
    (hout : ¬ (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
      (M ⊓ d.L).subtype ≤ d.MZ) :
    d.S ⊓ centralizer (((primeToResidual 3 (M ⊓ d.L : Subgroup G)).map
      (M ⊓ d.L).subtype) : Set G) = d.S ⊓ centralizer (d.L : Set G) := by
  let Y := (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype
  have hp : IsPPerfect 2 Y := (isPPerfect_primeToResidual 3 2 (by decide)).of_surjective
    ((primeToResidual 3 (M ⊓ d.L : Subgroup G)).equivMapOfInjective
      (M ⊓ d.L).subtype (M ⊓ d.L).subtype_injective).toMonoidHom
    ((primeToResidual 3 (M ⊓ d.L : Subgroup G)).equivMapOfInjective
      (M ⊓ d.L).subtype (M ⊓ d.L).subtype_injective).surjective
  have he := d.ordinary_residual_image_escape hu hn hZ1T hcenterTwo Y
    ((map_subtype_le _).trans inf_le_right) hp hout
  have hb := d.ordinary_omega_bound_of_model hL hcenter hSL e hfix
  have hc : Nat.card (omega₁ (center (sylowImage (d.L.subgroupOf d.G1)
      (d.S.subgroupOf d.G1))) (p := 2)) = 2 := by
    have hn : omega₁ (center (sylowImage (d.L.subgroupOf d.G1)
        (d.S.subgroupOf d.G1))) (p := 2) ≠ ⊥ := by
      intro hh
      apply he
      simp only [omegaCenterIn,hh,Subgroup.map_bot]
      exact bot_le
    have hh := (one_lt_card_iff_ne_bot _).mpr hn
    omega
  exact d.source22_ordinary_residual_centralizer hTM ⟨d.L_component.1,hL⟩ hc he
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
