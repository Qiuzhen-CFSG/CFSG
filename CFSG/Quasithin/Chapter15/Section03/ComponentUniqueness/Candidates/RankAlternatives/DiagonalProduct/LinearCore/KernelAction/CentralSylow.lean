module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.KernelAction.Setup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage.LocalSetup
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.KernelAction.CentralSylow.CubicRoots
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
/-!
# Central Sylow coverage in the linear branch

An actual PSL₃ model is centerless, by elementary generation and
perfectness of SL₃. For a central two-cover of PSL₃(4), cubic generation
puts every quotient Sylow in θ of its normalizer. If that normalizer's
full preimage lies in M ∩ L, its order-three elements lift through O₂(L)
and land in θ(M ∩ L). The Sylow preimage is therefore contained in
θ(M ∩ L)Z(L), which gives precisely `CentralSylowCoverage`.

The original quotient equivalence is used throughout. No central-cover
kernel is discarded, and no action on the center is assumed. In particular,
`local_sylow_le_theta_sup_center_four` covers the actual S ∩ L using the
Sylow marking in `BorelPlacement`. The final theorems remain conditional
on that local Borel placement; constructing it from `SourceSetup` and the
compatible outer cubic action is the remaining input. `borelSourceSetup`
only translates the identical earlier hypotheses into the image branch's
interface; it asserts no placement conclusion.
These results do not by themselves complete the source disjunction.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.11--12, 15.3.33 and the final paragraph of 15.3.37, printed p.1135.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.KernelAction.CentralSylow
variable {G H : Type*} [Group G] [Group H]

/-- Actual PSL₃ models are centerless; no statement about a central cover is inferred. -/
theorem center_eq_bot_of_isPSL {L : Subgroup G} {q : ℕ}
    (hL : ClassicalGroup.IsPSL L 3 q) : center L = ⊥ := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hL
  let _ := Atlas.sl_perfect (F := F) 3 (by decide)
  have hz : center PSL(3,F) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
  apply (center L).eq_bot_iff_forall.mpr
  intro x hx
  apply e.injective
  rw [map_one]
  have he : e x ∈ center PSL(3,F) := (centerCongr e ⟨x, hx⟩).property
  simpa only [hz, mem_bot] using he

variable [Finite G]

/-- Lift the cubic generators and cover the full Sylow preimage, retaining
both the given quotient marking and the central kernel. -/
theorem sylow_preimage_le_theta_sup_center {M L : Subgroup G}
    (e : (L ⧸ pCore 2 L) ≃* H) (hcore : pCore 2 L ≤ center L)
    (P : Sylow 2 H)
    (hgen : (P : Subgroup H) ≤ theta (normalizer (P : Set H)))
    (hplace : (normalizer (P : Set H)).comap (MatrixImage.quotientMap e) ≤ M.subgroupOf L) :
    (P : Subgroup H).comap (MatrixImage.quotientMap e) ≤
      (theta (M ⊓ L)).subgroupOf L ⊔ center L := by
  let f := MatrixImage.quotientMap e
  let X := (theta (M ⊓ L)).subgroupOf L
  have htheta : theta (normalizer (P : Set H)) ≤ X.map f := by
    apply (closure_le _).mpr
    rintro z ⟨hz, hz3⟩
    obtain ⟨x, hx, hx3⟩ := MatrixImage.order_three_lift e z hz3
    refine ⟨x, ?_, hx⟩
    have hxM : (x : G) ∈ M := hplace (show f x ∈ normalizer (P : Set H) from hx.symm ▸ hz)
    exact subset_closure ⟨⟨hxM, x.property⟩, (Subgroup.orderOf_coe x).trans hx3⟩
  have hp := comap_mono (f := f) (hgen.trans htheta)
  rw [comap_map_eq] at hp
  exact hp.trans (sup_le_sup_left (by rwa [MatrixImage.quotientMap_ker]) X)

/-- A full Sylow preimage in θ(M ∩ L)Z(L) gives exactly the required odd index. -/
theorem centralSylowCoverage_of_quotient_borel {M L : Subgroup G}
    (e : (L ⧸ pCore 2 L) ≃* H) (hcore : pCore 2 L ≤ center L)
    (P : Sylow 2 H)
    (hgen : (P : Subgroup H) ≤ theta (normalizer (P : Set H)))
    (hplace : (normalizer (P : Set H)).comap (MatrixImage.quotientMap e) ≤ M.subgroupOf L) :
    CentralSylowCoverage M L := by
  let f := MatrixImage.quotientMap e
  have hk : IsPGroup 2 f.ker := by
    rw [MatrixImage.quotientMap_ker]
    exact pCore_isPGroup
  let T := P.comapOfKerIsPGroup f hk (by
    rw [f.range_eq_top_of_surjective (MatrixImage.quotientMap_surjective e)]
    exact le_top)
  have hT : (T : Subgroup L) ≤ (theta (M ⊓ L)).subgroupOf L ⊔ center L :=
    sylow_preimage_le_theta_sup_center e hcore P hgen hplace
  exact (Nat.prime_two.coprime_iff_not_dvd.mpr T.not_dvd_index).of_dvd_right
    (index_dvd_of_le hT)

/-- The two-core is central in the actual component, including a central two-cover. -/
private theorem core_le_center {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L) : pCore 2 L ≤ center L := by
  let e := subgroupOfEquivOfLe h.component_le
  have hK := component_center_eq_twoCore h.component h.odd_core
  intro x hx
  rw [← pCore_map_iso 2 e] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact (centerCongr e ⟨y, hK.symm ▸ hy⟩).property

/-- In the central-cover branch, only local placement remains: the cubic
Sylow generation and the lift through the actual two-core are proved here. -/
theorem coverage_four_of_borel {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F)) (P : Sylow 2 PSL(3,F))
    (hplace : (normalizer (P : Set PSL(3,F))).comap (MatrixImage.quotientMap e) ≤
      d.M.subgroupOf L) : CentralSylowCoverage d.M L :=
  centralSylowCoverage_of_quotient_borel e (core_le_center h) P
    (sylow_le_theta_normalizer_four hF P) hplace

/-- The covered subgroup is the actual local Sylow S ∩ L, in the original
component. Its image is identified by the supplied Borel marking. -/
theorem local_sylow_le_theta_sup_center_four {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (hn : d.Yplus ≤ normalizer (L : Set G))
    (b : MatrixImage.BorelPlacement d.Yplus d.S d.M L hn e) :
    d.S.subgroupOf L ≤ (theta (d.M ⊓ L)).subgroupOf L ⊔ center L := by
  have hmap : d.S.subgroupOf L ≤
      (b.sylow : Subgroup PSL(3,F)).comap (MatrixImage.quotientMap e) :=
    map_le_iff_le_comap.mp b.sylow_eq.ge
  exact hmap.trans (sylow_preimage_le_theta_sup_center e (core_le_center h) b.sylow
    (sylow_le_theta_normalizer_four hF b.sylow) b.preimage_le)

omit [Finite G] in
/-- The Borel construction consumes exactly these same earlier source
hypotheses. This interface conversion proves no new local assertion. -/
theorem borelSourceSetup {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L) : MatrixImage.SourceSetup d I L where
  outside := h.outside
  sylow := h.sylow
  component_le := h.component_le
  component := h.component
  odd_core := h.odd_core
  component_outside := h.component_outside
  orbit_eq := h.orbit_eq
  rank_component := h.rank_component
  rank_yplus := h.rank_yplus
  rank_overgroup := h.rank_overgroup
  theta_eq := h.theta_eq
  normalizer_eq := h.normalizer_eq
  quotient_three := h.quotient_three
  yplus_quotient_three := h.yplus_quotient_three
  intersection_characteristic_two := h.intersection_characteristic_two
  residual_ne := h.residual_ne
  core_normalizes := h.core_normalizes
  component_cores_le := h.component_cores_le
  shadow := h.shadow
  characteristic_two_containment := h.characteristic_two_containment

/-- The exact two source model branches, conditional only on Borel placement
in the order-four field. The actual PSL branch uses its trivial center.
The extra placement premise must still be discharged in source assembly. -/
theorem center_eq_bot_or_coverage_of_placement {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    {F : Type*} [Field F] [Finite F] (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (hcase : (∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
      Nat.card F = 2 ^ n) ∨ Nat.card F = 4)
    (hplace : Nat.card F = 4 → ∃ P : Sylow 2 PSL(3,F),
      (normalizer (P : Set PSL(3,F))).comap (MatrixImage.quotientMap e) ≤
        d.M.subgroupOf L) : center L = ⊥ ∨ CentralSylowCoverage d.M L := by
  rcases hcase with ⟨n, _, _, hmodel, _⟩ | hF
  · exact Or.inl (center_eq_bot_of_isPSL hmodel)
  · obtain ⟨P, hP⟩ := hplace hF
    exact Or.inr (coverage_four_of_borel h hF e P hP)

/-- Consume the shared Borel construction in exactly its given field and
quotient coordinates. The construction of `b` remains a source obligation. -/
theorem center_eq_bot_or_coverage_of_borelPlacement {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    {F : Type*} [Field F] [Finite F] (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (hcase : MatrixImage.LinearCase L (Nat.card F))
    (hn : d.Yplus ≤ normalizer (L : Set G))
    (b : MatrixImage.BorelPlacement d.Yplus d.S d.M L hn e) :
    center L = ⊥ ∨ CentralSylowCoverage d.M L :=
  center_eq_bot_or_coverage_of_placement h e hcase (fun _ => ⟨b.sylow, b.preimage_le⟩)

end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.KernelAction.CentralSylow
