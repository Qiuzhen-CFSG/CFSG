module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.Frattini
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Uniqueness

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.Singer

/-!
# The literal action of the chosen line normalizer

Conjugation acts on the additive binary space of the original flag subgroup,
with kernel exactly its ambient centralizer. Restricting the ambient Sylow
and mapping it onto the action image produces the actual Sylow image. The
Singer calculation lifts its normality through this exact kernel to C_G(U)XT.
The geometric regularity and Sylow-normalization identities remain explicit;
this module does not claim to construct them from the natural marking.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.2.3, printed pp.768--769.
-/

open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : ChapterB.QuasisimpleSource.BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c)

/-- Conjugation on the binary vector space underlying the original V₁. -/
def lineAction : normalizer (f.Vi 0 : Set G) →*
    (Additive (f.Vi 0) ≃ₗ[ZMod 2] Additive (f.Vi 0)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive (f.Vi 0))).toMonoidHom.comp
    (Components.flagAction f 0).asGroupHom

/-- Its kernel is the literal C_G(V₁), restricted to N_G(V₁). -/
theorem lineAction_ker :
    (lineAction f).ker =
      (centralizer (f.Vi 0 : Set G)).subgroupOf (normalizer (f.Vi 0 : Set G)) := by
  rw [lineAction, MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _)]
  rw [← Components.flagAction_ker f 0]
  ext g
  exact Units.ext_iff

/-- The image of an ambient subgroup under the original line action. -/
def lineImage (H : Subgroup G) :
    Subgroup (Additive (f.Vi 0) ≃ₗ[ZMod 2] Additive (f.Vi 0)) :=
  (H.subgroupOf (normalizer (f.Vi 0 : Set G))).map (lineAction f)

/-- The actual Sylow image in the faithful line-action group. -/
def lineSylow : Sylow 2 (lineAction f).range :=
  (T.subtype (f.invariant 0)).mapSurjective (lineAction f).rangeRestrict_surjective

/-- The Sylow image uses precisely the original T and action homomorphism. -/
theorem lineSylow_image :
    (lineSylow f : Subgroup (lineAction f).range).map (lineAction f).range.subtype =
      lineImage f T := by
  change (((T : Subgroup G).subgroupOf (normalizer (f.Vi 0 : Set G))).map
    (lineAction f).rangeRestrict).map (lineAction f).range.subtype = _
  rw [map_map]
  rfl

/-- The Cartan image has odd order, inherited from the original Hall subgroup. -/
theorem lineImage_odd {X : Subgroup G} (hX : IsCartan T L X)
    (hXU : X ≤ normalizer (f.Vi 0 : Set G)) : Odd (Nat.card (lineImage f X)) := by
  have ho : Odd (Nat.card (X.subgroupOf (normalizer (f.Vi 0 : Set G)))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hXU).toEquiv]
    exact hX.odd
  exact ho.of_dvd_nat (card_map_dvd _ (lineAction f))

/-- The preceding flag identity gives Cartan invariance without choosing a
new line or a new Cartan. -/
theorem chosen_cartan_normalizes_line_of_fixedSpace {X : Subgroup G}
    (hX : IsCartan T L X)
    (hfixed : f.Vi 0 = V ⊓ centralizer (sourceTL T L : Set G)) :
    X ≤ normalizer (f.Vi 0 : Set G) := by
  rw [hfixed]
  exact (le_inf (hX.1.trans inf_le_left |>.trans D.normalizes)
    (hX.1.trans inf_le_right |>.trans (normalizer_le_normalizer_centralizer _))).trans
      inf_normalizer_le_normalizer_inf

/-- Lift the normal image through the actual centralizer kernel. -/
theorem line_join_normalized_of_image {X : Subgroup G}
    (hXU : X ≤ normalizer (f.Vi 0 : Set G))
    (hn : (lineAction f).range ≤ normalizer ((lineImage f X ⊔ lineImage f T : Subgroup _) : Set _)) :
    normalizer (f.Vi 0 : Set G) ≤
      normalizer ((centralizer (f.Vi 0 : Set G) ⊔ X ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
  let Y := normalizer (f.Vi 0 : Set G)
  let B := centralizer (f.Vi 0 : Set G) ⊔ X ⊔ (T : Subgroup G)
  have hBY : B ≤ Y := sup_le (sup_le (Subgroup.centralizer_le_normalizer _) hXU) (f.invariant 0)
  have hk : (lineAction f).ker ≤ B.subgroupOf Y := by
    rw [lineAction_ker]
    exact comap_mono (le_sup_left.trans le_sup_left)
  have hm : (B.subgroupOf Y).map (lineAction f) = lineImage f X ⊔ lineImage f T := by
    rw [show B.subgroupOf Y =
      (centralizer (f.Vi 0 : Set G)).subgroupOf Y ⊔ X.subgroupOf Y ⊔
        (T : Subgroup G).subgroupOf Y from by
          rw [subgroupOf_sup (sup_le (Subgroup.centralizer_le_normalizer _) hXU) (f.invariant 0),
            subgroupOf_sup (Subgroup.centralizer_le_normalizer _) hXU]]
    rw [Subgroup.map_sup, Subgroup.map_sup, ← lineAction_ker, Subgroup.map_ker_self, bot_sup_eq]
    rfl
  have he : (lineImage f X ⊔ lineImage f T).comap (lineAction f) = B.subgroupOf Y := by
    rw [← hm]
    exact comap_map_eq_self hk
  have hnormal : (B.subgroupOf Y).Normal := by
    rw [← he, ← normalizer_eq_top_iff]
    apply top_unique
    intro y _
    exact (lineImage f X ⊔ lineImage f T).le_normalizer_comap (lineAction f)
      (hn (MonoidHom.mem_range.mpr ⟨y,rfl⟩))
  exact (normal_subgroupOf_iff_le_normalizer hBY).mp hnormal
/-- Cyclicity of the literal Sylow image, from the preceding scalar-line action. -/
theorem lineSylow_isCyclic {X : Subgroup G}
    (hcyc : IsCyclic (lineImage f X))
    (hreg : LinearGroup.IsRegularOnNonzero (lineImage f X))
    (hTN : lineImage f T ≤ normalizer (lineImage f X : Set _)) :
    IsCyclic (lineSylow f) := by
  let := hcyc
  have hp : IsPGroup 2 (lineImage f T) :=
    ((T.isPGroup'.comap_subtype (K := normalizer (f.Vi 0 : Set G))).map (lineAction f))
  have hh := LineAction.regular_two_subgroup_cyclic (lineImage f X) (lineImage f T) hreg hp hTN
  have hi : IsCyclic ((lineSylow f : Subgroup (lineAction f).range).map
      (lineAction f).range.subtype) := (lineSylow_image f).symm ▸ hh
  exact ((lineSylow f : Subgroup (lineAction f).range).equivMapOfInjective
    (lineAction f).range.subtype (lineAction f).range.subtype_injective).isCyclic.mpr hi

/-- This discharges the hzero normality input of the source Frattini consumer
from scalar-line geometry, without assuming the supplement or its normality. -/
theorem chosen_line_normalized_of_singer {X : Subgroup G}
    (hX : IsCartan T L X) (hXU : X ≤ normalizer (f.Vi 0 : Set G))
    (hcyc : IsCyclic (lineImage f X))
    (hreg : LinearGroup.IsRegularOnNonzero (lineImage f X))
    (hTN : lineImage f T ≤ normalizer (lineImage f X : Set _)) :
    normalizer (f.Vi 0 : Set G) ≤
      normalizer ((centralizer (f.Vi 0 : Set G) ⊔ X ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
  let := hcyc
  let : Nontrivial (f.Vi 0) := (Subgroup.nontrivial_iff_ne_bot _).mpr (f.V_ne_bot 0)
  apply line_join_normalized_of_image f hXU
  have hn := LineAction.singer_sylow_join_normalized (lineImage f X) (lineAction f).range
    hreg (map_le_range _ _) (lineImage_odd f hX hXU) (lineSylow f)
    (by simpa only [lineSylow_image] using hTN)
  simpa only [lineSylow_image] using hn

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
