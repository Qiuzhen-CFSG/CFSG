module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.Setup
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.ThompsonImage.Offenders
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.ThompsonImage.Kernel
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel.CharacteristicControl.ThompsonImage.RankOneOffenders

/-!
# Assembling the Thompson image from its maximum elementary generators

For R = O₂(XU) and Q = O₂(K₁R), assume Q ≤ R. Weak closure ensures a
maximum elementary subgroup of R escapes Q. The literal conjugation action
on Ω₁(Z(Q)) has kernel Q, and its natural block section identifies each
nontrivial maximum elementary image with a Sylow two-subgroup of the first
block's image. These Sylow images lie in the common two-group image of U,
so they equal the image of U ∩ K₁. Generation and the kernel equality then
give J(R)Q = (U ∩ K₁)Q. The radical containment Q ≤ R remains explicit.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the rank-one
case of C.2.7(3)(a)(i), p.146, used in 15.4.20, p.1164.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable {c : ContraryData κ d i j} (b : ExchangedBlock c)
namespace ThompsonImage

/-- Generation lifts equality of the nontrivial maximum elementary images.
Both the kernel identification and the rank-one image theorem must still
be supplied by the source assembly. -/
theorem sup_eq_of_maximum_images (hQ : blockRadicalCore b ≤ contraryCore c)
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b))
    (himages : ∀ A ∈ elementaryAbelianMaxSubgroups (contraryCore c),
      image b A ≠ ⊥ → image b A = image b (c.U ⊓ b.first)) :
    coreThompson c ⊔ blockRadicalCore b = (c.U ⊓ b.first) ⊔ blockRadicalCore b := by
  have hS : c.U ⊓ b.first ≤ localGroup b := inf_le_right.trans le_sup_left
  apply le_antisymm
  · apply sup_le _ le_sup_right
    apply sSup_le
    intro A hA
    by_cases hAQ : A ≤ blockRadicalCore b
    · exact hAQ.trans le_sup_right
    · have hi := himages A hA ((image_ne_bot_iff_of_kernel b hker
        (hA.1.trans le_sup_right)).mpr hAQ)
      exact (image_le_iff_of_kernel b hker (hA.1.trans le_sup_right) hS).mp hi.le
  · obtain ⟨A, hA, hAQ⟩ := exists_maximum_not_le_core b hQ
    have hi := himages A hA ((image_ne_bot_iff_of_kernel b hker
      (hA.1.trans le_sup_right)).mpr hAQ)
    exact sup_le (((image_le_iff_of_kernel b hker hS
      (hA.1.trans le_sup_right)).mp hi.ge).trans
        (sup_le_sup_right (show A ≤ coreThompson c from le_sSup hA) _)) le_sup_right

/-- The intersection with the ambient Sylow remains Sylow in the action image. -/
theorem firstSylow_image_isSylow :
    ∃ P : Sylow 2 (image b b.first),
      (P : Subgroup (image b b.first)).map (image b b.first).subtype =
        image b (c.U ⊓ b.first) := by
  have hfirst : b.first ≤ localGroup b := le_sup_left
  let f : b.first →* image b b.first :=
    { toFun x := ⟨action b ⟨x, hfirst x.property⟩,
        ⟨⟨x, hfirst x.property⟩, x.property, rfl⟩⟩
      map_one' := Subtype.ext ((action b).map_one)
      map_mul' x y := Subtype.ext ((action b).map_mul
        ⟨x, hfirst x.property⟩ ⟨y, hfirst y.property⟩) }
  have hf : Function.Surjective f := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨S, hS⟩ := exists_first_sylow b
  refine ⟨S.mapSurjective hf, ?_⟩
  rw [Sylow.coe_mapSurjective, map_map, hS]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hfirst x.property⟩, ⟨hx, x.property⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩

/-- Every relevant image lies in the image of the same two-subgroup U. -/
theorem image_U_isPGroup : IsPGroup 2 (image b c.U) := by
  have hU : IsPGroup 2 c.U := c.sylow_image ▸ c.sylow.isPGroup'.map c.H.subtype
  exact hU.comap_subtype.map (action b)

/-- Sylow images lying in the common two-subgroup coincide. -/
theorem image_eq_firstSylow_of_isSylow {A : Subgroup G}
    (hAU : A ≤ c.U)
    (hA : ∃ P : Sylow 2 (image b b.first),
      (P : Subgroup (image b b.first)).map (image b b.first).subtype = image b A) :
    image b A = image b (c.U ⊓ b.first) := by
  obtain ⟨P, hP⟩ := hA
  obtain ⟨S, hS⟩ := firstSylow_image_isSylow b
  have htwo : IsPGroup 2 ((image b c.U).subgroupOf (image b b.first)) :=
    (image_U_isPGroup b).comap_subtype
  have hPU : (P : Subgroup (image b b.first)) ≤
      (image b c.U).subgroupOf (image b b.first) := by
    intro x hx
    have hm : (x : MulAut (omegaModule b)) ∈ image b A :=
      hP ▸ mem_map_of_mem _ hx
    exact map_mono (show A.subgroupOf (localGroup b) ≤ c.U.subgroupOf (localGroup b)
      from fun _ hx => hAU hx) hm
  have hSU : (S : Subgroup (image b b.first)) ≤
      (image b c.U).subgroupOf (image b b.first) := by
    intro x hx
    have hm : (x : MulAut (omegaModule b)) ∈ image b (c.U ⊓ b.first) :=
      hS ▸ mem_map_of_mem _ hx
    exact map_mono (show (c.U ⊓ b.first).subgroupOf (localGroup b) ≤
      c.U.subgroupOf (localGroup b) from fun _ hx => hx.1) hm
  have he : (P : Subgroup (image b b.first)) = S :=
    (P.is_maximal' htwo hPU).symm.trans (S.is_maximal' htwo hSU)
  rw [← hP, ← hS, he]

/-- Final generation needs the rank-one Sylow conclusion only for images
of maximum elementary subgroups of R. -/
theorem sup_eq_of_maximum_sylow_images
    (hQ : blockRadicalCore b ≤ contraryCore c)
    (hker : (action b).ker = (blockRadicalCore b).subgroupOf (localGroup b))
    (hsylow : ∀ A ∈ elementaryAbelianMaxSubgroups (contraryCore c),
      image b A ≠ ⊥ → ∃ P : Sylow 2 (image b b.first),
        (P : Subgroup (image b b.first)).map (image b b.first).subtype = image b A) :
    coreThompson c ⊔ blockRadicalCore b = (c.U ⊓ b.first) ⊔ blockRadicalCore b := by
  apply sup_eq_of_maximum_images b hQ hker
  intro A hA hne
  exact image_eq_firstSylow_of_isSylow b (hA.1.trans (contraryCore_le_U c))
    (hsylow A hA hne)

end ThompsonImage

/-- The Thompson subgroup and the first block's Sylow subgroup have the same
image modulo Q = O₂(K₁R). The centralizer kernel and natural-module offender
premises are discharged by the actual omega-center action. -/
theorem coreThompson_sup_blockRadicalCore
    (_hc : ⁅b.first, BorelPlacement.ExchangedBlock.second b⁆ = ⊥)
    (hQ : blockRadicalCore b ≤ contraryCore c) :
    coreThompson c ⊔ blockRadicalCore b = (c.U ⊓ b.first) ⊔ blockRadicalCore b := by
  apply ThompsonImage.sup_eq_of_maximum_sylow_images b hQ
    (ThompsonImage.action_kernel_eq_core b)
  intro A hA hne
  exact ThompsonImage.maximum_image_isSylow b hQ
    (ThompsonImage.action_kernel_eq_core b) hA hne

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.BorelPlacement.ControlledBorel
