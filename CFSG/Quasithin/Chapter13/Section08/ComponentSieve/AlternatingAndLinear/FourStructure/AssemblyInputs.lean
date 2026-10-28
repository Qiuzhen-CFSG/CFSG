module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic
/-!
# Connecting the L₄ chief-factor, cyclic and critical-pair arguments

The preimage lemma lifts the chosen irreducible submodule through the actual
central quotient. The full marked parabolic has a unique proper invariant
two-plane, so the seed plane in any chosen natural head is the same marked
plane. Its inverse image normalizes V: the quotient kernel lies in the source
Sylow subgroup and therefore in the marked parabolic.

`source_endgame_inputs` combines the finite-length B.4.9 splitting argument,
the A₁-placement and cyclic contradictions, and the forward marked-commutator
calculation. It proves the irreducible-section codimension bound in both
natural orientations, using the actual upper quotient V_H/U_H in the dual
case. The equality-case reversal is invoked only under equality; the strict
inequality case is retained. The actual conjugator accompanies the radical
containment in the output.

This intermediate result takes the preceding head and chief-factor conclusions
in `SourceData`. The source theorem in the FourStructure umbrella constructs
that data, including the generating seed, unique maximal kernel, and chosen
irreducible preimage. All subsequent module inequalities and the noncyclic
actor rank are conclusions here. The remaining inputs are the earlier source
geometry, the selected critical index inequality, and precise two-factor B.4.9.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.960–962 (PDF pp.977–979),
using 13.8.4(5), 13.8.8(2), 13.8.18, F.9.13(6), and Remark F.9.17.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08
open ComponentSieve.AlternatingAndLinear.FourStructure
open CriticalTransfer CriticalTransfer.MarkedGeometry
open CriticalTransfer.PairConsequences CriticalTransfer.PairConsequences.ReversedSourceData
open CriticalGeometry CriticalGeometry.Reorientation ChiefFactors

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.AssemblyInputs
universe u v w
variable {G : Type u} {U : Type v} [Group G] [Finite G]
  [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {L T H V V₃ V₁ : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) U}

omit [Finite G] [FiniteDimensional (ZMod 2) U] in
/-- Lift a submodule to a subgroup containing the exact quotient kernel. -/
theorem preimage_submodule (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (N : Subrepresentation ρ) :
    ∃ I : Subgroup G, V₁ ≤ I ∧ I ≤ Source.UH H V₃ ∧ s.image I = N.toSubmodule := by
  let J : Subgroup (Source.UH H V₃) :=
    N.toSubmodule.toAddSubgroup.toSubgroup.comap s.quotient
  let I := J.map (Source.UH H V₃).subtype
  refine ⟨I, ?_, map_subtype_le _, ?_⟩
  · intro z hz
    refine ⟨⟨z, s.line_le hz⟩, ?_, rfl⟩
    change (s.quotient ⟨z, s.line_le hz⟩).toAdd ∈ N
    rw [(s.quotient_eq_zero_iff _).mpr hz]
    exact N.toSubmodule.zero_mem
  · ext v
    constructor
    · rintro ⟨x, ⟨y, hy, hyx⟩, rfl⟩
      have hxy : y = x := Subtype.ext hyx
      subst y
      exact hy
    · intro hv
      obtain ⟨x, hx⟩ := s.surjective (Multiplicative.ofAdd v)
      refine ⟨x, ⟨x, ?_, rfl⟩, hx⟩
      change (s.quotient x).toAdd ∈ N
      rw [hx]
      exact hv

omit [Finite G] [FiniteDimensional (ZMod 2) U] in
/-- The seed image in the chosen head is the marked parabolic plane. -/
theorem parabolic_eq_headPlane
    (S : SourceData L T H V V₃ V₁ ρ)
    (P : Submodule (ZMod 2) NaturalSpace)
    (hmark : (Source.starImage H (S.L₁ ⊔ T)).map S.eH.toMonoidHom =
      BinaryLinear.parabolic P) :
    (Source.starImage H (S.L₁ ⊔ T)).map S.eH.toMonoidHom =
      BinaryLinear.parabolic S.plane := by
  have hp := S.plane_dim
  have h0 : S.plane ≠ ⊥ := by intro he; rw [he, finrank_bot] at hp; omega
  have h1 : S.plane ≠ ⊤ := by
    intro he
    rw [he, finrank_top] at hp
    norm_num [NaturalSpace] at hp
  have hle := S.parabolic_le
  rw [hmark] at hle
  rw [hmark, BinaryLinear.FourParabolicAction.parabolic_le_imp_eq h0 h1 hle]


omit [Finite G] [FiniteDimensional (ZMod 2) U] in
/-- Lift the marked parabolic through its Sylow-contained quotient kernel. -/
theorem source_parabolic_normalizes
    (T : Sylow 2 G) (S : SourceData L (T : Subgroup G) H V V₃ V₁ ρ)
    (hmark : (Source.starImage H (S.L₁ ⊔ (T : Subgroup G))).map S.eH.toMonoidHom =
      BinaryLinear.parabolic S.plane) :
    ∀ a : H, S.eH (QuotientGroup.mk' (pCore 2 H) a) ∈ BinaryLinear.parabolic S.plane →
      (a : G) ∈ normalizer (V : Set G) := by
  have hPH : S.L₁ ⊔ (T : Subgroup G) ≤ H := S.edge_eq.symm.le.trans inf_le_right
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hPH
  have hk : (QuotientGroup.mk' (pCore 2 H)).ker ≤
      (S.L₁ ⊔ (T : Subgroup G)).subgroupOf H := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hTH)).trans
      (subgroupOf_mono H le_sup_right)
  intro a ha
  rw [← hmark, mem_map_equiv, MulEquiv.symm_apply_apply] at ha
  change a ∈ (((S.L₁ ⊔ (T : Subgroup G)).subgroupOf H).map
    (QuotientGroup.mk' (pCore 2 H))).comap (QuotientGroup.mk' (pCore 2 H)) at ha
  rw [comap_map_eq_self hk] at ha
  exact S.edge_normalizes (S.edge_eq.symm ▸ ha)

/-- Complete critical-pair inputs without imposing equality of the two ranks.
The equality case alone invokes the constructed reversed pair. -/
theorem source_endgame_inputs
    [IsElementaryAbelian 2 (Source.VH H V)]
    (T : Sylow 2 G) (S : SourceData L (T : Subgroup G) H V V₃ V₁ ρ)
    (c : CriticalPair L (T : Subgroup G) H V)
    (hgeo : ∀ b : CriticalPair L (T : Subgroup G) H V, EarlierGeometry b V₃ V₁)
    (hcore : ∀ b : CriticalPair L (T : Subgroup G) H V,
      b.Vgamma ≤ (edgeGroup L (T : Subgroup G) H (base L (T : Subgroup G) H true) b.second).pCoreIn 2)
    (generation18 : ∀ b : CriticalPair L (T : Subgroup G) H V,
      ∀ F ≤ Source.UH H V₃,
      ¬ F ≤ Source.DH (Source.UH H V₃) (b.Ugamma V₃) (b.Aone V₁) →
      vertexGroup L (T : Subgroup G) H b.gamma =
        conjugateSpanBy F (vertexGroup L (T : Subgroup G) H b.gamma) ⊔
          edgeGroup L (T : Subgroup G) H b.gamma b.previous)
    (hp : 0 < rank (Source.starImage H (c.Ugamma V₃)))
    (hrV : 1 < rank (Source.starImage H c.Vgamma))
    (hbound : fixedCodim ρ (Source.starImage H (c.Ugamma V₃)) ≤
      2 * rank (Source.starImage H (c.Ugamma V₃)))
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃)
      (c.Aone V₁)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)))
    (V₂ : Subgroup G) (h₂₃ : V₂ ≤ V₃) (hidx : V₁.relIndex V₂ = 2)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hmark : (Source.starImage H (S.L₁ ⊔ (T : Subgroup G))).map S.eH.toMonoidHom =
      BinaryLinear.parabolic S.plane)
    (hinter : V ⊓ Source.UH H V₃ = V₃)
    {E : Type w} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (τ : Representation (ZMod 2) (Source.Hstar H) E)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ) :
    let D := S.sectionModel.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))
    let A := Source.starImage H (c.Ugamma V₃)
    let B := Source.starImage H c.Vgamma
    ∃ g : Source.Hstar H,
      Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A ∧
      2 ≤ Module.finrank (ZMod 2) (S.N.toSubmodule ⧸ D.comap S.N.toSubmodule.subtype) ∧
      (Module.finrank (ZMod 2) (U ⧸ D) = rank A → D ≤ fixedSpace ρ A) ∧
      Module.finrank (ZMod 2) (S.sectionModel.image (c.Aone V₁)) ≤ 1 ∧
      (∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S.sectionModel.image (c.Aone V₁)) ∧
      A ≤ B ∧ IsElementaryTwo B ∧ 1 < rank A ∧
      Module.finrank (ZMod 2) S.plane = 2 ∧
      (B.map (MulAut.conj g).toMonoidHom).map S.eH.toMonoidHom ≤ BinaryLinear.radical S.plane ∧
      (∀ X ≤ B, 1 < rank X → 1 < fixedCodim S.W.quotientRepresentation X) := by
  have hUV : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono S.seed_le le_rfl)
  have hγH := hUV.trans (hgeo c).Vgamma_H
  have hUJ := (conjugateSpanBy_mono S.seed_le le_rfl).trans (hgeo c).VH_endpoint
  have hreverse : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom := by
    rw [← c.vertexGroup_gamma]
    exact hUJ
  have hPH : S.L₁ ⊔ (T : Subgroup G) ≤ H := S.edge_eq.symm.le.trans inf_le_right
  let _ : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  have hB : IsElementaryTwo (Source.starImage H c.Vgamma) := by
    refine ⟨?_, starImage_isElementaryAbelian H _ (hgeo c).Vgamma_H⟩
    intro hbot
    rw [hbot, Representation.BinaryOffender.rank_bot] at hrV
    omega
  have hAB : Source.starImage H (c.Ugamma V₃) ≤ Source.starImage H c.Vgamma :=
    map_mono (subgroupOf_mono H hUV)
  have hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)) := by
    apply hB.of_le hAB
    intro hbot
    rw [hbot, Representation.BinaryOffender.rank_bot] at hp
    omega
  have hquad := (c.quadratic_star_on_Utilde V₃ V₁ S.sectionModel S.seed_le (hgeo c).VH_endpoint).1
  obtain ⟨haxes, hcenters⟩ := SplittingCyclic.nonsplitting_bounds ρ S.eH S.splitting
    S.chief_factors S.W S.maximal S.nonzero S.unique_maximal
    ⟨S.head, S.head_equivariant⟩ _ hB hquad
  obtain ⟨k, hk, hplace, _⟩ := exists_second_to_base c S.L₁
    ((S.L₁ ⊔ (T : Subgroup G)).pCoreIn 2)
    (by have := (hgeo c).length; omega) S.edge_eq (hcore c) le_rfl
  have hplace' : c.Vgamma.map (MulAut.conj (((k⁻¹ : H) : G)⁻¹)).toMonoidHom ≤
      (S.L₁ ⊔ (T : Subgroup G)).pCoreIn 2 := by
    simpa only [Subgroup.coe_inv, inv_inv] using hplace
  have hcentralizer := S.endpoint_centralizer c
  rw [c.vertexGroup_gamma] at hcentralizer
  obtain ⟨hnot, hrank⟩ := SplittingCyclic.source_placement_and_rank T c S.sectionModel
    S.normalizer_line S.line_card (hgeo c).lines_disjoint hUV (hgeo c).Vgamma_H hreverse
    hcentralizer hA hB hrV hbound hcritical V₂ S.L₀ S.L₁ S.L₀_le hPH S.cubic S.fixes_seed
    h₂₃ hidx hTV₂ S.seed_stable S.seed_irreducible S.seed_dim S.I S.line_le_I S.I_le
    S.N S.W S.irreducible S.submodule_le S.maximal.ne_top S.image_I S.eH S.chief_factors
    S.head S.head_equivariant hmark k⁻¹ hplace'
  let _ : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le
    (show V ≤ Source.VH H V from le_conjugateSpanBy V H)
  have hedge := c.edge_commutator_le_of_flag V₃ S.seed_le S.flag_index S.noncentral S.edge_normalizes
  obtain ⟨_, _, hrad, _, hcomm, _, _, hID, _, hgenI, _⟩ :=
    forward_noncontainment_of_source V₃ V₁ S.sectionModel S.L₀ S.L₁ (T : Subgroup G)
      S.L₀_le hPH S.cubic S.fixes_seed S.two_group S.seed_stable S.seed_irreducible S.seed_dim
      S.W S.maximal.ne_top S.eH S.head S.head_equivariant S.I S.line_le_I S.I_le S.N S.image_I
      S.natural_irreducible (c.gb : G) (vertexGroup L (T : Subgroup G) H c.gamma)
      (edgeGroup L (T : Subgroup G) H c.gamma c.previous) (c.Ugamma V₃) c.Vgamma (c.Aone V₁)
      c.vertexGroup_gamma (by rfl) (by rfl) hUV (hgeo c).Vgamma_H hUJ
      (S.endpoint_centralizer c) S.line_card hnot hrank
      (hcenters S.N S.irreducible S.submodule_le) k⁻¹ hplace' (generation18 c)
      (fun F hF _ hgen => c.noncentral_of_generation V₃ F S.V_le (hF.trans hUJ)
        hgen hedge S.noncentral)
  have hUA : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) :=
    hreverse.trans ((S.sectionModel.centralizes_conjugate_line (c.gb : G)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hline : Nat.card (c.Aone V₁) = 2 := by
    rw [CriticalPair.Aone, card_map_of_injective (MulAut.conj _).injective, S.line_card]
  have hgen := generation18 c (Source.UH H V₃) le_rfl (fun hle => hID (S.I_le.trans hle))
  have hindex : (Source.UH H V₃).relIndex V = 2 := by
    rw [← inf_relIndex_right, inf_comm, hinter, S.flag_index]
  have hIcodim : 2 ≤ Module.finrank (ZMod 2)
      (S.N.toSubmodule ⧸ (S.sectionModel.image (Source.DH (Source.UH H V₃)
        (c.Ugamma V₃) (c.Aone V₁))).comap S.N.toSubmodule.subtype) := by
    rcases S.natural_irreducible with hNat | ⟨e, he⟩
    · exact critical_section_codimension_ge_two_of_same_natural_head S.sectionModel
        S.I (vertexGroup L (T : Subgroup G) H c.gamma) (c.Ugamma V₃) c.Vgamma (c.Aone V₁)
        S.line_le_I S.I_le S.N S.W S.image_I hUV (hgeo c).Vgamma_H hUJ hUA
        (S.endpoint_centralizer c) hline hnot hrank S.eH hNat ⟨S.head, S.head_equivariant⟩ haxes
    · exact critical_section_codimension_ge_two_of_dual S.sectionModel
        S.I (vertexGroup L (T : Subgroup G) H c.gamma) (c.Ugamma V₃) c.Vgamma (c.Aone V₁)
        S.line_le_I S.I_le S.N S.image_I (hgeo c).Vgamma_H hUJ hUA
        (S.endpoint_centralizer c) hline hnot S.eH e he hquad hcomm
        (Source.VH H V) τ t V (le_conjugateSpanBy V H) rfl hindex S.plane S.plane_dim
        (source_parabolic_normalizes T S hmark) (c.gb : G)
        (edgeGroup L (T : Subgroup G) H c.gamma c.previous) c.vertexGroup_gamma
        (by rfl) (by rfl) S.line_card hgen hedge
        (by simpa only [commutator_comm] using S.noncentral)
  have hl := critical_pair_linear_bounds S.sectionModel (c.gb : G) hγH hreverse
    S.line_card S.faithful hcritical
  let g : Source.Hstar H := QuotientGroup.mk' (pCore 2 H) k
  have hrad' : ((Source.starImage H c.Vgamma).map (MulAut.conj g).toMonoidHom).map
      S.eH.toMonoidHom ≤ BinaryLinear.radical S.plane := by
    rw [← starImage_conjugate c.Vgamma (hgeo c).Vgamma_H k]
    simpa only [SourceData.plane, Subgroup.coe_inv, inv_inv] using hrad
  refine ⟨g, hl.1, hIcodim, ?_, hl.2.1, hl.2.2.1, hAB, hB, hrank, S.plane_dim, hrad', haxes⟩
  intro hequal
  exact (equality_case_noncontainment_and_fixation S c hgeo hcore generation18 hrank hequal).2

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.AssemblyInputs
