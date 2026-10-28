module
public import Theory.SpecificGroups.ReeF4.SourceCompletion.Centers
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.SylowAlignment
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Full native long-root centralizers in the general Ree group

Borel–Tits normalizer coverage and Sylow alignment put the Borel together
with a long-root involution centralizer in a proper subgroup. The Suzuki
local factor centralizes the involution; adjoining the Borel gives the full
Suzuki parabolic. The rank-two parabolic lattice therefore forces the
centralizer into that very parabolic. Perfectness identifies its embedded
solvable residual with the actual Suzuki local factor.

The same coverage argument identifies the full normalizer of this local
factor. Consequently every automorphism fixing the marked long-root
involution preserves this factor. These are intrinsic statements for all
m > 0, including q = 8, without a simplicity or recognition premise.
They provide the native centralizer comparison required in F.4.27,35,43.
Source: Aschbacher–Smith, printed pp.288,291–292,296 (`refs/quasithin.pdf`);
GLS3 Theorem 3.1.3 and §§2.3,2.6 (`refs/KGroup/GLS3/chapter3.tex`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace ReeF4.SourceCompletion
open Parabolics LargeLocalSeeds EvenInvolutionGeometry
open SectionGeometry.BNPair
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
attribute [local instance] borel_inf_normalizerWords_normal

private theorem proper_borel_overgroup_le_parabolic {m : ℕ} (hm : 0 < m)
    (X : Subgroup (Model m)) (hB : borel m ≤ X) (hX : X ≠ ⊤) :
    ∃ s : Side, X ≤ Parabolics.parabolic m s := by
  let T := titsSystem m
  have hclass := T.subgroup_eq_standardParabolic_simpleIndices X hB
  have hI := T.simpleIndices_subset X
  change T.simpleIndices X ⊆ simpleReflections m at hI
  rw [simpleReflections_eq_pair] at hI
  rcases Set.subset_pair_iff_eq.mp hI with he | he | he | he
  · refine ⟨.linear,?_⟩
    rw [hclass,he,T.standardParabolic_empty]
    exact borel_le_parabolic m .linear
  · refine ⟨.linear,?_⟩
    rw [hclass,he]
    rw [←parabolic_eq_rootParabolic]
    exact (standardParabolic_singleton_eq_parabolic m hm .linear).le
  · refine ⟨.suzuki,?_⟩
    rw [hclass,he]
    rw [←parabolic_eq_rootParabolic]
    exact (standardParabolic_singleton_eq_parabolic m hm .suzuki).le
  · have hi : T.simpleIndices X = T.S := he.trans (simpleReflections_eq_pair m).symm
    exact (hX (hclass.trans ((congrArg T.standardParabolic hi).trans T.standardParabolic_S))).elim

private theorem suzuki_overgroup_eq {m : ℕ} (hm : 0 < m)
    (X : Subgroup (Model m)) (hP : Parabolics.parabolic m .suzuki ≤ X)
    (hX : X ≠ ⊤) : X = Parabolics.parabolic m .suzuki := by
  obtain ⟨s,hs⟩ := proper_borel_overgroup_le_parabolic hm X
    ((borel_le_parabolic m .suzuki).trans hP) hX
  cases s with
  | suzuki => exact le_antisymm hs hP
  | linear =>
    have hh : (⊤ : Subgroup (Model m)) ≤ Parabolics.parabolic m .linear := by
      rw [←localFactor_sup_eq_top m]
      exact sup_le ((localFactor_le_parabolic m .suzuki).trans (hP.trans hs))
        (localFactor_le_parabolic m .linear)
    exact (Parabolics.parabolic_ne_top hm .linear (top_unique hh)).elim

/-- The full perfect Suzuki factor centralizes every long-root element. -/
theorem suzuki_localFactor_le_long_centralizer {m : ℕ} (hm : 0 < m)
    {z : Model m} (hz : z ∈ longRootGroup m) :
    localFactor m .suzuki ≤ centralizer ({z} : Set (Model m)) := by
  rw [←suzuki_center_eq_longRoot hm] at hz
  obtain ⟨a,ha,rfl⟩ := hz
  intro x hx
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_center_iff.mp ha ⟨x,hx⟩))

/-- A nonidentity long-root element has its full native centralizer in the specified Suzuki parabolic. -/
theorem long_centralizer_le_parabolic {m : ℕ} (hm : 0 < m)
    {z : Model m} (hz : z ∈ longRootGroup m) (hz1 : z ≠ 1) :
    centralizer ({z} : Set (Model m)) ≤ Parabolics.parabolic m .suzuki := by
  have hKC := suzuki_localFactor_le_long_centralizer hm hz
  have hCN : centralizer ({z} : Set (Model m)) ≤ normalizer (zpowers z : Set (Model m)) := by
    rw [←centralizer_closure ({z} : Set (Model m)),←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hz2 : orderOf z = 2 := by
    obtain ⟨t,rfl⟩ := (mem_longRootGroup m z).mp hz
    exact longRootElement_orderOf m (by simpa using hz1)
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hz2,pow_one])
  obtain ⟨U,hU⟩ := ConverseParabolics.exists_sylow_eq_unipotent m
  have hU' : (U : Subgroup (Model m)) = unipotent m :=
    hU.trans (unipotent_eq_rootUnipotent m)
  have hproper := ConverseParabolics.normalizer_sup_lt_top hm U (zpowers z)
    (fun h => hz1 (zpowers_eq_bot.mp h)) hp (by
      rw [hU']
      exact (unipotent_le_localFactor m .suzuki).trans (hKC.trans hCN))
  change normalizer ((U : Subgroup (Model m)) : Set (Model m)) ⊔
    normalizer (zpowers z : Set (Model m)) < ⊤ at hproper
  rw [hU',unipotent_normalizer_eq_borel] at hproper
  let X := borel m ⊔ normalizer (zpowers z : Set (Model m))
  have hPX : Parabolics.parabolic m .suzuki ≤ X := by
    rw [parabolic_eq_localFactor_sup_borel]
    exact sup_le ((hKC.trans hCN).trans le_sup_right) le_sup_left
  exact (hCN.trans le_sup_right).trans
    (suzuki_overgroup_eq hm X hPX (ne_of_lt hproper)).le

/-- The embedded solvable residual of the full native long-root centralizer is the Suzuki factor. -/
theorem long_centralizer_residual {m : ℕ} (hm : 0 < m)
    {z : Model m} (hz : z ∈ longRootGroup m) (hz1 : z ≠ 1) :
    (solvableResidual (centralizer ({z} : Set (Model m)))).map
      (centralizer ({z} : Set (Model m))).subtype = localFactor m .suzuki := by
  let := OuterLocal.localFactor_perfect hm .suzuki
  apply le_antisymm
  · exact (map_solvableResidual_mono (long_centralizer_le_parabolic hm hz hz1)).trans_eq
      (parabolic_solvableResidual_map hm .suzuki)
  · exact le_map_solvableResidual_of_isPerfect _ _
      (suzuki_localFactor_le_long_centralizer hm hz)

/-- The full native normalizer of the Suzuki factor is its specified parabolic. -/
theorem suzuki_localFactor_normalizer {m : ℕ} (hm : 0 < m) :
    normalizer (localFactor m .suzuki : Set (Model m)) = Parabolics.parabolic m .suzuki := by
  have hPN : Parabolics.parabolic m .suzuki ≤
      normalizer (localFactor m .suzuki : Set (Model m)) := by
    rw [←seed_eq_localFactor]
    exact parabolic_le_seed_normalizer_of_splitTorus m .suzuki
      (splitTorus_le_seed_normalizer m .suzuki)
  have hNZ := normalizer_le_normalizer_characteristic_image
    (localFactor m .suzuki) (center (localFactor m .suzuki))
  rw [suzuki_center_eq_longRoot hm] at hNZ
  have hZne : longRootGroup m ≠ ⊥ := by
    intro he
    have hh := he.le ((mem_longRootGroup m _).mpr ⟨1,rfl⟩)
    exact (by simp : longRootElement m 1 ≠ 1) (mem_bot.mp hh)
  have hp := (unipotent_isPGroup m).of_injective
    (inclusion (longRootGroup_le_unipotent m)) (inclusion_injective _)
  obtain ⟨g,s,hP,hcover⟩ := ConverseParabolics.normalizer_cover_proper hm _ hZne hp
  have hproper : normalizer (longRootGroup m : Set (Model m)) ≠ ⊤ := by
    intro he
    rw [he,map_top_of_surjective _ (MulAut.conj g).surjective] at hcover
    exact hP (top_unique hcover)
  exact suzuki_overgroup_eq hm _ hPN (fun he => hproper (top_unique (he ▸ hNZ)))

/-- Fixing one nonidentity long-root element preserves the actual Suzuki factor. -/
theorem automorphism_fixing_long_preserves_suzuki {m : ℕ} (hm : 0 < m)
    {z : Model m} (hz : z ∈ longRootGroup m) (hz1 : z ≠ 1)
    (a : MulAut (Model m)) (ha : a z = z) :
    (localFactor m .suzuki).map a.toMonoidHom = localFactor m .suzuki := by
  rw [←long_centralizer_residual hm hz hz1,
    map_embedded_solvableResidual_of_hom,
    CentralizerSmallKernelTransport.map_centralizer,ha]

end ReeF4.SourceCompletion
