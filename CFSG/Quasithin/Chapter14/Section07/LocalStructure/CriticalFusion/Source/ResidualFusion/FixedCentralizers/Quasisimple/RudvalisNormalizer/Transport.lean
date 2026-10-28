module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.RudvalisNormalizer.Preimage
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.Max4Normalizers

/-!
# Shared transport for the original V-normalizer

Restrict the recognition map to the original V. Its kernel is trivial because
V meets the covering line trivially. A marked image identifies V with the
literal Ru eight, compatibly with conjugation. The model's full normalizer
bound gives one inclusion for the original component normalizer. Once the
source complement argument supplies the reverse inclusion, the intrinsic
preimage results give its two-perfectness, quotient, and center order.

This leaf module supplies shared maps to both source prerequisites. It leaves
marked-eight placement and preservation of V explicit. The parent module
assembles the three intrinsic conclusions once these premises are discharged.

Source: Aschbacher–Smith 14.7.68(2), printed p.1071 (PDF p.1088).
-/

@[expose] public section
noncomputable section
open Subgroup Representation Theory.GroupTheory
open Rudvalis.SylowOvergroups Rudvalis.CoreQuotients
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable {d : Data T L V F W} {u : F.U} {Lu : Subgroup G}
namespace FixedRudvalisCover
variable (r : d.FixedRudvalisCover u Lu)

def seedProjection (hV : V ≤ Lu) : V →* Rudvalis.Model :=
  r.projection.comp (inclusion hV)

theorem seedProjection_injective (hV : V ≤ Lu)
    (hdisj : zpowers (u : G) ⊓ V = ⊥) : Function.Injective (r.seedProjection hV) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm ?_ bot_le
  intro v hv
  have hk : (v : G) ∈ zpowers (u : G) := by
    rw [← r.kernel]
    exact mem_map_of_mem Lu.subtype (show inclusion hV v ∈ r.projection.ker from hv)
  have he : (v : G) ∈ (⊥ : Subgroup G) := hdisj ▸ (show (v : G) ∈ zpowers (u : G) ⊓ V from ⟨hk, v.property⟩)
  exact Subtype.ext he

/-- The coordinates on V are the restriction of the recognition map. -/
def seedEquiv (hV : V ≤ Lu) (hdisj : zpowers (u : G) ⊓ V = ⊥)
    (hmap : (V.subgroupOf Lu).map r.projection = elementary 2) : V ≃* elementary 2 := by
  let f := r.seedProjection hV
  have hr : f.range = elementary 2 := by
    rw [show f = r.projection.comp (inclusion hV) from rfl,
      MonoidHom.range_comp, inclusion_range, hmap]
  let q := f.codRestrict (elementary 2) (fun v => hr ▸ (show f v ∈ f.range from ⟨v, rfl⟩))
  apply MulEquiv.ofBijective q
  constructor
  · intro x y he
    exact r.seedProjection_injective hV hdisj (congrArg Subtype.val he)
  · intro y
    have hy : (y : Rudvalis.Model) ∈ f.range := hr.symm ▸ y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩

@[simp] theorem seedEquiv_apply (hV : V ≤ Lu) (hdisj : zpowers (u : G) ⊓ V = ⊥)
    (hmap : (V.subgroupOf Lu).map r.projection = elementary 2) (v : V) :
    (r.seedEquiv hV hdisj hmap v : Rudvalis.Model) = r.projection (inclusion hV v) := rfl

/-- The easy inclusion uses the full ambient normalizer of the actual model eight. -/
theorem normalizer_le_max4Preimage (hV : V ≤ Lu)
    (hmap : (V.subgroupOf Lu).map r.projection = elementary 2) :
    (d.fixedComponentNormalizer Lu).subgroupOf Lu ≤ r.max4Preimage := by
  intro x hx
  have hn : x ∈ normalizer (V.subgroupOf Lu : Set Lu) := by
    rw [← subgroupOf_normalizer_eq hV]
    exact hx.2
  have him := (V.subgroupOf Lu).le_normalizer_map r.projection
    (mem_map_of_mem r.projection hn)
  rw [hmap] at him
  exact max4NormalizerBounds 2 (by decide) (by decide) him

/-- The opposite inclusion is the source complement-normalization obligation. -/
theorem normalizer_eq_max4Preimage (hV : V ≤ Lu)
    (hmap : (V.subgroupOf Lu).map r.projection = elementary 2)
    (hnorm : r.max4Preimage ≤ (normalizer (V : Set G)).subgroupOf Lu) :
    (d.fixedComponentNormalizer Lu).subgroupOf Lu = r.max4Preimage := by
  apply le_antisymm (r.normalizer_le_max4Preimage hV hmap)
  intro x hx
  exact ⟨x.property, hnorm hx⟩

def normalizerEquiv (hV : V ≤ Lu)
    (hmap : (V.subgroupOf Lu).map r.projection = elementary 2)
    (hnorm : r.max4Preimage ≤ (normalizer (V : Set G)).subgroupOf Lu) :
    d.fixedComponentNormalizer Lu ≃* r.max4Preimage :=
  (subgroupOfEquivOfLe (show d.fixedComponentNormalizer Lu ≤ Lu from inf_le_left)).symm.trans
    (MulEquiv.subgroupCongr (r.normalizer_eq_max4Preimage hV hmap hnorm))

/-- The model coordinates intertwine the literal conjugation on the original V. -/
theorem normalizerAction_intertwines (hV : V ≤ Lu)
    (hdisj : zpowers (u : G) ⊓ V = ⊥)
    (hmap : (V.subgroupOf Lu).map r.projection = elementary 2)
    (hnorm : r.max4Preimage ≤ (normalizer (V : Set G)).subgroupOf Lu)
    (j : d.fixedComponentNormalizer Lu) (v : V) :
    r.seedEquiv hV hdisj hmap (d.fixedComponentNormalizerAction Lu j v) =
      max4EightAction (r.max4Restriction (r.normalizerEquiv hV hmap hnorm j))
        (r.seedEquiv hV hdisj hmap v) := by
  apply Subtype.ext
  rw [seedEquiv_apply, max4EightAction_apply, seedEquiv_apply]
  change r.projection ((inclusion (show d.fixedComponentNormalizer Lu ≤ Lu from inf_le_left) j) *
      inclusion hV v * (inclusion (show d.fixedComponentNormalizer Lu ≤ Lu from inf_le_left) j)⁻¹) = _
  simp only [map_mul, map_inv]
  rfl

end FixedRudvalisCover
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
