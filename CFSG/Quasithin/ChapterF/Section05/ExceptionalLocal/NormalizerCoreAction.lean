module

public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerCore
public import Theory.GroupTheory.SpecificGroups.DihedralEightProductElementaryQuotient

/-!
# The faithful core action and its actual elementary-four subgroup

Self-centralization identifies N_G(Aᵢ)/Aᵢ with its conjugation image in
Aut(Aᵢ). The Sylow overgroup R normalizes Aᵢ and has order64; its image in
this quotient has order4. In the D₈×D₈ model the elementary sixteen Aᵢ
contains every square, so that image is elementary abelian.

These are the exact faithful-action and elementary-four inputs to the
plane quotient recognition in Aschbacher--Smith F.5.4(4), printed p.301.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (t : G) (hf : FusionFacts c i z t)

def normalizerCoreAction (b : Bool) : normalizerQuotient c i b →* MulAut (A c i b) :=
  QuotientGroup.lift _ (A c i b).normalizerMonoidHom (by
    rw [normalizerMonoidHom_ker,A_self_centralizer c i z t hf b])

theorem normalizerCoreAction_injective (b : Bool) :
    Function.Injective (normalizerCoreAction c i z t hf b) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [normalizerMonoidHom_ker,A_self_centralizer c i z t hf b]

theorem normalizerCoreAction_mk_apply (b : Bool)
    (n : normalizer (A c i b : Set G)) (a : A c i b) :
    (normalizerCoreAction c i z t hf b
      (QuotientGroup.mk' ((A c i b).subgroupOf (normalizer (A c i b : Set G))) n) a).val =
        n.val * a.val * n.val⁻¹ := rfl

include hf in
/-- The image of the original R in each normalizer quotient is an elementary
four; the quotient map retains the literal inclusion of R. -/
theorem normalizer_quotient_has_elementary_four (R : Sylow 2 (C c i))
    (hR : Tf c i ≤ (R : Subgroup (C c i))) (b : Bool) :
    ∃ P : Subgroup (normalizerQuotient c i b),
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 := by
  let N := normalizer (A c i b : Set G)
  let q := QuotientGroup.mk' ((A c i b).subgroupOf N)
  let f : Rimage c i R →* normalizerQuotient c i b :=
    q.comp (inclusion (normalizer_R_normalizes_A c i z t hf R hR b))
  let B := (A c i b).subgroupOf (Rimage c i R)
  have hAR := normalizer_A_le_Rimage c i z t hf R hR b
  have hk : f.ker = B := by
    ext a
    exact QuotientGroup.eq_one_iff (inclusion (normalizer_R_normalizes_A c i z t hf R hR b) a)
  have hB : Nat.card B = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAR).toEquiv).trans (hf.A_card b)
  have hc : Nat.card f.range = 4 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,hk,hB,normalizer_R_card c i z t hf] at hh
    omega
  obtain ⟨e⟩ := normalizer_R_iso c i z t hf R
  let E := B.map e.toMonoidHom
  let := hf.A_elementary b
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAR
  have hEe : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hEc : Nat.card E = 16 := (card_map_of_injective e.injective).trans hB
  have hEk : E ≤ (f.comp e.symm.toMonoidHom).ker := by
    rintro _ ⟨a,ha,rfl⟩
    change f (e.symm (e a)) = 1
    rw [e.symm_apply_apply]
    exact (show a ∈ f.ker by rw [hk];exact ha)
  have helem := DihedralGroup.elementary_image_of_sixteen_kernel
    (f.comp e.symm.toMonoidHom) E hEe hEc hEk
  have hr : (f.comp e.symm.toMonoidHom).range = f.range := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective]
    exact f.range_eq_map.symm
  exact ⟨f.range,hr ▸ helem,hc⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
