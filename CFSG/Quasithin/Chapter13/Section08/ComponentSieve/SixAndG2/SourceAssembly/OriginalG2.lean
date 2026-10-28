module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly.G2
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.G2Recognition.QuadraticConstituent

/-!
# The original G₂ orbit input from its quadratic critical pair

The selected source critical pair supplies the quadratic actor, displacement
bound and one-dimensional commutator image on the literal U_H/V₁. The proved
quadratic-component argument makes this entire section Irr⁺, retaining its
central subspace. Every Irr⁺ orbit member is then the whole module, giving
both action-image ratio bounds and the invariant alternative. The original
G₂ exclusion consumes this result in `SourceAssembly.Original`.

Source: Aschbacher–Smith, 13.8.22 and 13.8.27, printed pp.957,963;
F.9.18(3–4), pp.325–326. The carrier remains G₂(2)′. Reused model
calculations retain the attribution in LICENSES/ATLAS.txt.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
open TransvectionRecognition TransvectionRecognition.Component
open TransvectionRecognition.Component.ModelExtension
open CriticalGeometry SourceCompletion
open FieldComponents.HigherFieldReduction.ExternalModules
open AlternatingAndLinear.FourStructure.CriticalTransfer
open AlternatingAndLinear.LinearReduction.Overgroup
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FieldComponents.SmallCovers.Reduction.LocalGeometry.DynkinExclusion.OrbitInvariance
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L H K V V₁ V₂ V₃ M G₁ : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Construct both F.9.18 orbit clauses on the actual G₂ source section. -/
theorem g2_orbit_inputs_from_quadratic_actor
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hN : (K.subgroupOf H).Normal)
    (hjoin : H = K ⊔ (sourceOne L T V₁ ⊔ (T : Subgroup G)))
    (hfit : generalizedFitting (Source.Hstar H) = Source.starImage H K)
    (hUK : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (P : Sylow 2 (Source.Hstar H))
    (hP : Source.starImage H K ⊔ (P : Subgroup _) = ⊤)
    (eK : (K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    let : (Source.starImage H K).Normal := hfit ▸ inferInstance
    OrbitInputs ρ (Source.starImage H K) P hP := by
  let : (Source.starImage H K).Normal := hfit ▸ inferInstance
  let e := (Components.componentStarEquiv H K hKH hK).symm.trans eK
  obtain ⟨hq, hc⟩ := G2Parabolic.component_properties_of_fitting (Source.starImage H K) hfit e
  let := hq
  have hZ : center (Source.starImage H K) = ⊥ := by
    let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
      Atlas.G2.isSimple_commutator_binary
    let : IsSimpleGroup (Source.starImage H K) := e.isSimpleGroup
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp he))
  have hk : commutatorPreimage H (Source.UH H V₃) V₁ ≤ Source.QH H :=
    (f9_commutatorPreimage_eq _ hF9 H le_rfl).le.trans inf_le_right
  have hf := faithful_of_centralizer_le_core ρ hρ hk
  obtain ⟨w⟩ := CriticalSource.exists_selected_witness d hHz hF9 hjoin hK hN hq
    hcentral hcomm ρ hρ (g2_no_rank_one ρ hf _ hfit e)
  let c := w.pair
  have geo := local_earlierGeometry d hF9 c
  have inputs := CriticalSource.earlier_inputs d hHz hF9 hcentral hcomm ρ hρ
  have hUg : c.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans geo.Vgamma_H
  have hrev : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom := by
    apply (conjugateSpanBy_mono d.seed_le le_rfl).trans
    rw [← c.vertexGroup_gamma]
    exact geo.VH_endpoint
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)) :=
    ⟨by intro he; have := w.positive
        rw [he, Representation.BinaryOffender.rank_bot] at this
        omega,
      starImage_isElementaryAbelian H _ hUg⟩
  have hcrit := Nat.log_mono_right (b := 2)
    (c.index_comparison_of_selected_rank V₃ V₁ hUg geo.Dgamma_kernel w.comparison)
  let s := CriticalInputs.sourceSection H V₃ V₁ ρ hρ hF9.plus_le_H
    (d.line_le_plane.trans d.plane_le_seed) hF9.H_centralizes
  obtain ⟨hdim, hline, hcomm', _⟩ := critical_pair_linear_bounds s (c.gb : G)
    hUg hrev d.line_card hf hcrit
  let B := s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))
  let S := s.image (c.Aone V₁)
  have hcritical : B ≤ fixedSpace ρ (Source.starImage H (c.Ugamma V₃)) ∨
      ∃ S : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)),
        IsAtom S ∧ ∀ a ∈ Source.starImage H (c.Ugamma V₃), ∀ v ∈ B, ρ a v - v ∈ S := by
    by_cases hz : S = ⊥
    · left
      intro v hv a
      have hh := hcomm' a a.property v hv
      change ρ a v - v ∈ S at hh
      rw [hz] at hh
      exact sub_eq_zero.mp hh
    · right
      refine ⟨S, Submodule.isAtom_iff_finrank_eq_one.mpr ?_, hcomm'⟩
      have hn : Module.finrank (ZMod 2) S ≠ 0 :=
        fun hh => hz (Submodule.finrank_eq_zero.mp hh)
      change Module.finrank (ZMod 2) S ≤ 1 at hline
      omega
  have hgen : subspaceCommutator ρ ⊤ (Source.starImage H K) = ⊤ :=
    (commutatorImage_eq_subspaceCommutator K hKH ρ hρ).symm.trans
      (commutatorImage_eq_top hUK)
  have hb := inputs.estimate c w.positive w.comparison
  have hi := G2Recognition.whole_isIrrPlus_of_quadratic_actor ρ (Source.starImage H K)
    hf hc hZ e hgen _ hA w.quadratic_member.2.1 hb B hcritical hdim
  exact G2Recognition.orbitInputs_of_whole_isIrrPlus ρ (Source.starImage H K)
    hf hi _ hA w.quadratic_member.2.1 hb P hP

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.SourceAssembly
