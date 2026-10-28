module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# Source setup for the small-component extension calculation

The earlier local conclusions give I = LS, O^{3′}(M ∩ L) = Y₊ and
M ∩ L = N_L(V₂). Characteristic two places U_I in O₂(I); its Sylow-central
construction makes it centralize that core. Therefore U_L ≤ Z([O₂(L),L]),
and the actual marked V₂ lies in this center before any model coordinates
are chosen. The source V₁ bounds supply the eventual contradiction.

The full FF/MS classifications remain explicit universal earlier inputs.
The marked coefficient-model construction and the noncentral model
calculations remain separate obligations, not assumptions in SourceData.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.26–31, printed pp.1130–1132 (PDF pp.1147–1149).
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
open EightGeometry EightGeometry.NaturalModule EightGeometry.NaturalModule.Recognition CentralCover
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Genuine earlier local inputs for 15.3.31. The FF/MS classifications and
the small parabolic alternative are supplied separately; no extension conclusion
or marked coefficient model is a field of this record. -/
structure SourceData (κ : GroupClass.{u}) (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) where
  minimal : I ∈ d.HplusMinimal
  sqtk : IsSQTK κ I
  characteristicTwo : HasCharacteristicTwo I
  rank : primeRank 3 d.Yplus = 1
  facts : Parabolics.RankOneFacts d I
  solvableControl : SolvableInvariantControl d I
  normal : (c.L.subgroupOf I).Normal
  contains : d.Yplus ≤ c.L
  sylow : Sylow 2 I
  sylow_eq : (sylow : Subgroup I).map I.subtype = d.S
  characteristic : ∀ C : Subgroup d.S, C.Characteristic → C ≠ ⊥ →
    ¬ ((C.map d.S.subtype).subgroupOf I).Normal
  line : LineData d I
  yRank : 2 ≤ primeRank 3 d.Y
  omega : d.ZS = centralOmegaIn d.S ∧ Nat.card d.ZS = 4

namespace SourceData
variable {κ : GroupClass.{u}} {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} (s : SourceData κ d c)
include s

/-- Minimality and component containment give the source factorization. -/
theorem generated : I = c.L ⊔ d.S :=
  (lemma_15_3_27_4_of_containment d s.minimal c s.sylow s.sylow_eq s.contains
    ((s.facts.residual ▸ map_subtype_le _).trans inf_le_left)).1

/-- Restriction of O^{3′}(M ∩ I) to the relatively normal component. -/
theorem component_residual :
    d.Yplus = (primeToResidual 3 (d.M ⊓ c.L : Subgroup G)).map
      (d.M ⊓ c.L).subtype := by
  have hML : d.M ⊓ c.L ≤ d.MI I := le_inf inf_le_left (inf_le_right.trans (component_le c))
  let N := (d.M ⊓ c.L).subgroupOf (d.MI I)
  have hIL := (normal_subgroupOf_iff_le_normalizer (component_le c)).mp s.normal
  let hn : N.Normal := normal_subgroupOf_of_le_normalizer
    ((le_inf (inf_le_left.trans d.M.le_normalizer) (inf_le_right.trans hIL)).trans
      inf_normalizer_le_normalizer_inf)
  have hres : primeToResidual 3 (d.MI I) ≤ N := by
    intro x hx
    have hy : (x : G) ∈ d.Yplus := s.facts.residual ▸ mem_map_of_mem _ hx
    exact ⟨x.property.1, s.contains hy⟩
  have he := congrArg (fun H : Subgroup (d.MI I) => H.map (d.MI I).subtype)
    (embedded_primeToResidual_eq_of_normal 3 N hres)
  rw [map_embedded_primeToResidual_of_hom, map_subgroupOf_eq_of_le hML,
    ← s.facts.residual] at he
  exact he.symm

/-- The original V₂ normalizer is exactly the component parabolic. -/
theorem component_parabolic : d.M ⊓ c.L = c.L ⊓ normalizer (d.V₂ : Set G) := by
  have hN := (OutsideStructure.LocalBranches.second_choice_plane_normalizers d
    (rank_one_choice d s.rank s.yRank)).2
  exact le_antisymm
    (le_inf inf_le_right ((inf_le_inf_left d.M (component_le c)).trans
      (s.line.plane_normalized d)))
    (le_inf (inf_le_right.trans hN) inf_le_left)

/-- The Sylow-central seed puts the whole component module in Z(Q). -/
theorem componentModule_le_coreCenter : d.componentModule I c.L ≤ coreCenter c.L := by
  have hQ : extensionCore c.L ≤ I.pCoreIn 2 := by
    rw [extensionCore_eq_overgroup d c s.contains s.normal]
    exact le_normalizer_iff_commutator_le_left.mp
      ((component_le c).trans (I.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image I (pCore 2 I))))
  apply le_inf
  · rw [extensionCore_eq_overgroup d c s.contains s.normal]
    exact commutator_mono (span_le_core d s.characteristicTwo s.sylow s.sylow_eq) le_rfl
  · exact (componentModule_le_span d c).trans
      ((span_centralizes_core d s.sylow s.sylow_eq).trans (centralizer_le hQ))

/-- The marked line lies in the actual core center before choosing coordinates. -/
theorem plane_le_coreCenter : d.V₂ ≤ coreCenter c.L :=
  (s.line.plane_le_component d c s.contains).trans s.componentModule_le_coreCenter

/-- The V₁ containment and centralizer/normalizer bounds for the final contradiction. -/
theorem first_plane_control : d.V₁ ≤ I ∧
    d.V₁ ≤ centralizer (d.Yplus : Set G) ∧ normalizer (d.V₁ : Set G) ≤ d.M := by
  refine ⟨?_, ?_, (OutsideStructure.LocalBranches.second_choice_plane_normalizers d
    (rank_one_choice d s.rank s.yRank)).1⟩
  · exact ((d.action.plane_le 1).trans
      (d.action.le_planeStabilizer d.T d.sylow_le (localModule_le d.T d.sylow_le) 1)).trans
        (show d.S ≤ I from s.sylow_eq ▸ map_subtype_le _)
  · apply le_centralizer_iff.mpr
    rw [s.facts.choice.2]
    exact (map_subtype_le _).trans inf_le_right

/-- Construct the full marked MS output from the authorized earlier classifications. -/
theorem markedMS (earlier : MarkedMS.EarlierMSClassifications κ)
    (ff : Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine.CompleteClassificationInput.{u,u} κ)
    (hm : Parabolics.SmallParabolicMarking d I c.L) :
    MarkedMS.SmallMSConclusion κ d c s.normal s.generated s.characteristicTwo s.sylow
      s.sylow_eq :=
  MarkedMS.markedMS_of_source earlier ff d s.minimal.1 c s.sqtk s.characteristicTwo
    s.contains s.generated s.normal s.sylow s.sylow_eq s.characteristic s.facts
    s.solvableControl s.line s.rank s.yRank s.omega hm

/-- Apply the checked central-cover calculation after supplying the marked models
and core centralization. These two remaining inputs are not source conclusions
proved by this conditional theorem. -/
theorem centralizing_false
    (configuration : MarkedConfiguration c.L d.V₂ (d.M ⊓ c.L))
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) : False := by
  obtain ⟨hVI, hVY, hN⟩ := s.first_plane_control
  exact centralizing_branch_false d c s.contains s.normal s.component_parabolic
    s.component_residual configuration hDQ hVI hVY hN

end SourceData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension
namespace SourceData
universe u
variable {G : Type u} [Group G]
  {κ : GroupClass.{u}} {d : LocalData G} {I : Subgroup G}
  {c : ComponentWitness d I} (s : SourceData κ d c)
include s

/-- The quotient-centralizer calculation in C.1.34(1)--(2) suffices for
the commutator bound on the actual core. This includes the kernel comparison
and the perfectness/three-subgroup argument. -/
theorem commutator_le_core_of_star_centralizer
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hstar : centralizer (d.starImage I d.Yplus : Set (d.Star I)) = ⊥) :
    ⁅yplusCentralizer d I, c.L⁆ ≤ extensionCore c.L := by
  have hIL := (normal_subgroupOf_iff_le_normalizer (component_le c)).mp s.normal
  have hIQ := normalizes_extensionCore hIL
  have hzero : ∀ x : yplusCentralizer d I,
      d.starMap I ⟨x, x.property.1⟩ = 1 := by
    intro x
    apply mem_bot.mp
    rw [← hstar]
    apply mem_centralizer_iff.mpr
    rintro y ⟨j, hj, rfl⟩
    have hcomm : j * (⟨x, x.property.1⟩ : I) = ⟨x, x.property.1⟩ * j :=
      Subtype.ext (mem_centralizer_iff.mp x.property.2 j hj)
    exact (map_mul (d.starMap I) j ⟨x, x.property.1⟩).symm.trans
      ((congrArg (d.starMap I) hcomm).trans (map_mul (d.starMap I) _ _))
  have hbase : ⁅yplusCentralizer d I, c.L⁆ ≤ c.L.pCoreIn 2 := by
    apply commutator_le.mpr
    intro x hx l hl
    have hwL : ⁅x, l⁆ ∈ c.L :=
      (le_normalizer_iff_commutator_le_right.mp
        (show yplusCentralizer d I ≤ normalizer (c.L : Set G) from inf_le_left.trans hIL))
        (commutator_mem_commutator hx hl)
    let w : c.L := ⟨⁅x, l⁆, hwL⟩
    have hw : componentMap d c w = 1 := by
      apply Subtype.ext
      change d.starMap I ⁅(⟨x, hx.1⟩ : I), ⟨l, component_le c hl⟩⁆ = 1
      rw [map_commutatorElement, hzero ⟨x, hx⟩]
      simp
    have hq : QuotientGroup.mk' (pCore 2 c.L) w = 1 := by
      apply (coreQuotientEquivStar d c s.normal s.sylow s.sylow_eq).injective
      rw [map_one, coreQuotientEquivStar_apply]
      exact hw
    exact mem_map.mpr ⟨w, (QuotientGroup.eq_one_iff _).mp hq, rfl⟩
  have hrot : ⁅⁅yplusCentralizer d I, c.L⁆, c.L⁆ ≤ extensionCore c.L :=
    commutator_mono hbase le_rfl
  have hrot' : ⁅⁅c.L, yplusCentralizer d I⁆, c.L⁆ ≤ extensionCore c.L := by
    rwa [commutator_comm c.L (yplusCentralizer d I)]
  have hthree := commutator_commutator_le_of_rotate_of_le_normalizer
    ((component_le c).trans hIQ) ((component_le c).trans hIQ)
    (show yplusCentralizer d I ≤ normalizer (extensionCore c.L : Set G) from
      inf_le_left.trans hIQ) hrot' hrot
  have hp := Subgroup.isPerfect_iff.mp (component_isPerfect_of_containment d c s.contains)
  rwa [hp, commutator_comm] at hthree

/-- Actual application to the natural-module conjugate-generation argument.
The remaining model tasks supply the quotient centralizer and the intersections. -/
theorem centralizes_core_of_star_centralizer_and_generation
    [IsSimpleGroup (c.L ⧸ pCore 2 c.L)]
    (hstar : centralizer (d.starImage I d.Yplus : Set (d.Star I)) = ⊥)
    (hQ : IsMulCommutative (extensionCore c.L))
    (hgen : extensionCore c.L ≤ localSpan (extensionCore c.L ⊓ d.Yplus) c.L) :
    yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G) :=
  centralizes_extensionCore_of_conjugate_generation d c hQ
    (s.commutator_le_core_of_star_centralizer hstar) hgen

end SourceData
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension

end
