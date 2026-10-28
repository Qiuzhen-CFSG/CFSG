module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.TrivialIntersection
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.SourceCount
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.RootPairs

/-!
# Assembly of the J₂ involution geometry and source order calculation

The source is Aschbacher, *Sporadic Groups* (1994), 47.1, pp.259–260.
The two-class hypothesis already supplies a commuting representative.
A marked full-centralizer equivalence proves the intrinsic core marking and
its TI property. The genuine local pair counts 960 and 195 then give 604800
by the proved Thompson formula with the literal source pair convention.

The complete earlier-source `LocalCensus` is constructed from `Seed` in
`SourceCount`. Recognition excludes the order-48 centralizer, constructs the
marked products, and conjugates inside C_G(z) to align the component with the
prescribed X. `RootPairs` supplies the second count. Their assembly here
discharges all extra premises: `selectedGeometry_of_seed` gives the actual
centralizer and normalizer maps, and `card_eq` proves the ambient order.
The component placement concerns the selected representative only.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry

variable {G : Type*} [Group G] [Finite G]

/-- Numerical assembly from the two literal source counts and centralizer model. -/
theorem card_eq_of_source_counts {D : Seed G} {t : G} (ht : OtherInvolution D t)
    (C : SecondCentralizer D t)
    (hz : sourceCount D.z t D.z = 960) (htc : sourceCount D.z t t = 195) :
    Nat.card G = 604800 := by
  rw [source_order_formula ht, hz, htc, C.centralizer_card]

/-- The earlier-source census and marked-product count feed the actual order formula. -/
theorem card_eq_of_local_census {D : Seed G} (L : LocalCensus D)
    (S : SelectedGeometry D) (ht : sourceCount D.z S.t S.t = 195) :
    Nat.card G = 604800 :=
  card_eq_of_source_counts S.other S.model (L.count_at_z S.t S.other) ht

/-- The proved earlier-source census discharges the first count in the actual
order-formula consumer. The second-centralizer geometry and second count remain
explicit, independent inputs. -/
theorem card_eq_of_second_count {D : Seed G} (S : SelectedGeometry D)
    (ht : sourceCount D.z S.t S.t = 195) : Nat.card G = 604800 :=
  card_eq_of_local_census (localCensus_of_seed D) S ht

/-- Source 47.1(1): construct the full marked geometry from the seed, including
the intrinsic component, both normalizer factor inclusions, and the prescribed
X as a Sylow-three image in the full component centralizer. -/
theorem selectedGeometry_of_seed (D : Seed G) : Nonempty (SelectedGeometry D) :=
  Recognition.selectedGeometry_of_localCensus D (localCensus_of_seed D)

/-- Source 47.1(2): Thompson's formula gives 960 · 240 + 195 · 1920 = 604800.
The local census, second centralizer, and both counts are proved from the seed. -/
theorem card_eq (D : Seed G) : Nat.card G = 604800 := by
  obtain ⟨S⟩ := selectedGeometry_of_seed D
  exact card_eq_of_second_count S (S.model.sourceCount_eq_195 S.other)

namespace SelectedGeometry
variable {D : Seed G} (S : SelectedGeometry D)

/-- The selected representative commutes with z because z belongs to its actual layer. -/
theorem commute : Commute D.z S.t := by
  exact mem_centralizer_singleton_iff.mp
    (map_subtype_le _ S.z_mem_component)

/-- The normalizer is the full literal normalizer, so its order is 720. -/
theorem normalizer_card : Nat.card (normalizer (rootCore S.t : Set G)) = 720 := by
  rw [Nat.card_congr S.normalizerEquiv.toEquiv, Nat.card_prod, card_A5,
    nat_card_alternatingGroup]
  norm_num

/-- The A₄ factor as an actual subgroup of the original group. -/
def normalizerFourFactor : Subgroup G :=
  ((⊤ : Subgroup A4).prod (⊥ : Subgroup A5)).map
    ((normalizer (rootCore S.t : Set G)).subtype.comp S.normalizerEquiv.symm.toMonoidHom)

theorem rootCore_le_normalizerFourFactor : rootCore S.t ≤ S.normalizerFourFactor := by
  rw [← S.normalizer_core]
  exact map_mono (prod_mono le_top le_rfl)

theorem normalizerFourFactor_le :
    S.normalizerFourFactor ≤ normalizer (rootCore S.t : Set G) := by
  rw [normalizerFourFactor, ← map_map]
  exact map_subtype_le _

/-- The first normalizer factor centralizes the retained A₅ component. -/
theorem normalizerFourFactor_centralizes :
    S.normalizerFourFactor ≤ centralizer (rootComponent S.t : Set G) := by
  rw [← S.normalizer_component]
  rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
  let f := (normalizer (rootCore S.t : Set G)).subtype.comp
    S.normalizerEquiv.symm.toMonoidHom
  change f y * f x = f x * f y
  rw [← map_mul, ← map_mul]
  apply congrArg f
  have hx2 : x.2 = 1 := hx.2
  have hy1 : y.1 = 1 := hy.1
  exact Prod.ext (by simp [hy1]) (by simp [hx2])

/-- The conditional assembly supplies the intrinsic core order, TI, and ambient order
without adding these conclusions as fields of `SelectedGeometry`. -/
theorem core_geometry_and_order
    (hz : sourceCount D.z S.t D.z = 960) (ht : sourceCount D.z S.t S.t = 195) :
    Nat.card (rootCore S.t) = 4 ∧
      (∀ g : G, rootCore S.t ⊓ (rootCore S.t).map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (rootCore S.t).map (MulAut.conj g).toMonoidHom = rootCore S.t) ∧
      Nat.card G = 604800 :=
  ⟨S.model.rootCore_card, S.model.rootCore_trivial_intersection S.other,
    card_eq_of_source_counts S.other S.model hz ht⟩

/-- Both literal pair counts for the selected representative, with no remaining
counting hypotheses. -/
theorem source_counts :
    sourceCount D.z S.t D.z = 960 ∧ sourceCount D.z S.t S.t = 195 :=
  ⟨sourceCount_at_z_eq_960 S.other, S.model.sourceCount_eq_195 S.other⟩

/-- The intrinsic core is a root four-group and a TI-subgroup in G; the same
source calculations give the ambient order. -/
theorem geometry_and_order :
    Nat.card (rootCore S.t) = 4 ∧
      (∀ g : G, rootCore S.t ⊓ (rootCore S.t).map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (rootCore S.t).map (MulAut.conj g).toMonoidHom = rootCore S.t) ∧
      Nat.card G = 604800 :=
  S.core_geometry_and_order S.source_counts.1 S.source_counts.2

end SelectedGeometry

/-- The complete selected form of 47.1, retaining the actual product models
and subgroup markings in `S`, together with the intrinsic core identification,
TI property, normalizer order, both source counts, and ambient order.
The placement of z and X is asserted only for this selected representative. -/
theorem source_geometry_and_order (D : Seed G) :
    ∃ S : SelectedGeometry D,
      Commute D.z S.t ∧
      rootCore S.t = S.model.fourFactor ∧
      Nat.card (rootCore S.t) = 4 ∧
      (∀ g : G, rootCore S.t ⊓ (rootCore S.t).map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (rootCore S.t).map (MulAut.conj g).toMonoidHom = rootCore S.t) ∧
      Nat.card (normalizer (rootCore S.t : Set G)) = 720 ∧
      sourceCount D.z S.t D.z = 960 ∧ sourceCount D.z S.t S.t = 195 ∧
      Nat.card G = 604800 := by
  obtain ⟨S⟩ := selectedGeometry_of_seed D
  obtain ⟨hcore, hTI, hG⟩ := S.geometry_and_order
  exact ⟨S, S.commute, S.model.rootCore_eq_fourFactor, hcore, hTI,
    S.normalizer_card, S.source_counts.1, S.source_counts.2, hG⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry
