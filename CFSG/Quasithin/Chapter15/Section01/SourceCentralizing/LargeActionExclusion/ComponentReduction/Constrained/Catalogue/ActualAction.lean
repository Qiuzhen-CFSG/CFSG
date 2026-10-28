module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Selection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Nine

/-!
# The constrained catalogue reduction on the original marked action

The component constructed from the original marker supplies the fixed G₁,
M_Z, S and Q₁ for both deductions: the local-family Thompson obstruction
and the constrained full-Sylow-or-star-catalogue alternative. The new
rank-one-or-star application resolves the full-Sylow branch into genuine
L₂-even or A₅ blocks and supplies Q₁-normalization otherwise. The prime is
unrestricted, including the original prime-five branch. No later exchanged
plane or quotient recognition is used to construct these inputs.

The full local-family branch also supplies the original reduced
FF-module, full Thompson movement and actual image group catalogue for
every qualifying K, using K N_S(K) without imposing S-normalization or
a new selection record on K. The A₅ application identifies both its literal
Borel and centralizer and supplies the complete chosen rank-one alternative.
The natural L₂ application supplies a compatible matrix Borel marking, its
upper containment, the exact two-core of M_Z∩K, and Borel normalization.

Original 15.1.19(2) is also applied to every invariant subgroup of the
fixed G₁ equal to its lower mixed core, without ambient C-componenthood.
The orbit-Borel application supplies characteristic two and a normal Sylow
for every short local member. For the selected C-component it proves full
M_Z-invariance and reverse containment, yielding the complete rank-one
alternative in the full-Sylow branch.

The local FF quotient application retains the actual core map, its central
kernel of order one or three, and the K/O₂,Z(K) isomorphism. The marked
intersection maps to a proper overgroup of the literal Sylow image and is
exactly its full preimage. This works before exchanged selection and on
both exchanged-plane sizes.

The rank-one witness applications construct a noncentral element of the
literal moved seed fixed by J(S), before block reconstruction or Baumann
normalization. The new placement applications discharge support separation
and Baumann normalization for all eligible nonblock members. They preserve
both original primes and the later exchanged
source. The remaining orbit separation is still owned by this catalogue.

The earlier residual premise is original 15.1.14, owned by
qt-e-1514-global-thompson-residual. Its discharge remains with
qt-e-15122-pre-exclusion-catalogue. Full catalogue and quotient assembly
remain with that task and qt-e-1515-constrained-linear-quotient respectively.

Source: Aschbacher--Smith 15.1.14--20, printed pp.1090--1097.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal marker consumer for the local-family and C.2.4 reductions.
It retains the uneliminated full-Sylow alternative explicitly. -/
theorem PreparedChosenModule.source_preExclusion_constrained_catalogue_reduction
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (∀ K ∈ Chapter1.LIn d.G1 d.S, ¬ K ≤ d.MZ →
        ¬ K ≤ M ∧ ¬ K ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) ∧
          ¬ elementaryAbelianMaxJ d.S ≤ (K ⊔ d.S).pCoreIn 2) ∧
      (generalizedFitting d.L = pCore 2 d.L →
        d.SL ≤ d.Q1 ∨ ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
          StarModels.Model (starImage d.L d.Q1 d.L) ∧
            (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
            (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
              Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_,fun hf =>
    s.constrained_star_catalogue_or_full_sylow (h := h) hG hu hf⟩
  intro K hK hout
  exact ⟨d.localFamily_not_le_M hG hempty hM hu hK hout,
    d.localFamily_thompson_escape hG hempty hM hJ hu h hK hout,
    d.localFamily_thompson_not_le_core hG hempty hM hJ hu h hK hout⟩

/-- The original marker supplies the FF-module and its group list for every
S-normalized local-family member. The chosen component is not substituted
for those local subgroups, and the original prime remains unrestricted. -/
theorem PreparedChosenModule.source_preExclusion_normalized_local_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K → d.S ≤ normalizer (K : Set G) →
        d.CatalogueAction K ∧
          (let q := QuotientGroup.mk'
            (centralizer (d.catalogueModule K : Set (K ⊔ d.S : Subgroup G)))
           StarModels.Model ((K.subgroupOf (K ⊔ d.S)).map q)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout hf hn
  exact d.localFamily_normalized_catalogue hG hempty hM hJ hu h hK hq hout hf hn

/-- The original marker supplies the FF-module and its group list for every
local-family member. The chosen component is not substituted
for those local subgroups, and the original prime remains unrestricted. -/
theorem PreparedChosenModule.source_preExclusion_local_ff_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
        d.NormalizerAction K ∧
          (let q := QuotientGroup.mk'
            (centralizer (d.normalizerModule K : Set (K ⊔ d.normalizerSylow K : Subgroup G)))
           StarModels.Model ((K.subgroupOf (K ⊔ d.normalizerSylow K)).map q)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout hf
  exact d.localFamily_catalogue hG hempty hM hJ hu h hK hq hout hf

/-- Apply the genuine rank-one-or-normalized reduction to the original
marker. The original 15.1.14 residual premise remains for the pre-exclusion
assembly owner; no full-Sylow or Q₁-normalization callback remains. -/
theorem PreparedChosenModule.source_preExclusion_constrained_rankOne_or_star_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) ∨
        ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
          StarModels.Model (starImage d.L d.Q1 d.L) ∧
            (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
            (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
              Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf =>
    s.constrained_star_catalogue_or_rankOne (h := h) hG hf⟩


/-- Apply the A₅ Borel theorem to every eligible member of the original
local family and use it to complete the chosen A₅ rank-one alternative.
The earlier 15.1.14 residual premise remains for its existing producer and
pre-exclusion assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_alternatingFive_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → IsAlternatingBlock K 5 →
          d.MZ ⊓ K = K ⊓ centralizer (centralInvolutions T : Set G) ∧
          d.MZ ⊓ K = (normalizer ((d.S ⊓ K).subgroupOf K : Set K)).map K.subtype) ∧
      (generalizedFitting d.L = pCore 2 d.L →
        d.ConstrainedRankOneAlternative ∨ (∃ n : ℕ, IsL2EvenBlock d.L n) ∨
        ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
          StarModels.Model (starImage d.L d.Q1 d.L) ∧
            (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
            (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
              Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_,fun hf =>
    s.constrained_rankOne_or_l2_or_star (h := h) hG hempty hM hJ hu hf⟩
  intro K hK hq hout hb
  exact d.localFamily_alternatingFive_borel h hM.1.2 hu hK hq hout hb

/-- Apply the natural L₂ geometry to the fixed original local family. This
retains the literal core quotient and Borel marking, including at prime five.
The residual premise is original 15.1.14 and remains with the pre-exclusion
assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_linearTwo_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
        d.MZ ⊓ K ≤ (normalizer ((d.S ⊓ K).subgroupOf K : Set K)).map K.subtype ∧
        (d.MZ ⊓ K).pCoreIn 2 = d.S ⊓ K ∧
        d.MZ ⊓ normalizer (K : Set G) ≤
          normalizer ((normalizer ((d.S ⊓ K).subgroupOf K : Set K)).map K.subtype : Set G) ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
          Nat.card F = 2 ^ n ∧
          ∃ e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
            let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
            ((d.S ⊓ K).subgroupOf K).map q = Matrix.SpecialLinearGroup.upperUnipotent F ∧
            normalizer ((d.S ⊓ K).subgroupOf K : Set K) =
              (Matrix.SpecialLinearGroup.rankOneBorel F).comap q ∧
            (d.MZ.subgroupOf K).map q ≤ Matrix.SpecialLinearGroup.rankOneBorel F := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hout n hb
  exact ⟨d.localFamily_linearTwo_borel_bound hu hK hout hb,
    d.localFamily_linearTwo_core hu hK hout hb,
    d.localFamily_linearTwo_borel_normalized hu hK hout hb,
    d.localFamily_linearTwo_coordinates hu hK hout hb⟩


/-- The literal original marker supplies 15.1.19(2) for every invariant
subgroup of G₁ with characteristic two and the literal lower mixed core.
The original 15.1.14 premise remains with the pre-exclusion assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_mixed_core_control
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ≤ d.G1, d.MZ ≤ normalizer (K : Set G) →
        generalizedFitting K = pCore 2 K →
        (pPrimeCore 2 (K ⧸ pCore 2 K)).comap (QuotientGroup.mk' (pCore 2 K)) = ⊤ → K ≤ d.MZ := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun _ hK hn hf ho =>
    s.constrained_mixed_core_control (h := h) hG hM hu hne hmany hres hK hn hf ho⟩

/-- The original marker constructs the actual Borel orbit for every short
local member and the complete rank-one-or-star reduction for its selected
C-component. Original 15.1.14 remains with its named source producer. -/
theorem PreparedChosenModule.source_preExclusion_constrained_orbitBorel_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) → IsShort K →
        generalizedFitting (d.orbitSylowBorel K) = pCore 2 (d.orbitSylowBorel K) ∧
          (∃ P : Sylow 2 (d.orbitSylowBorel K),
            (P : Subgroup (d.orbitSylowBorel K)) = pCore 2 (d.orbitSylowBorel K)) ∧
          Odd (Nat.card (d.orbitSylowBorel K ⧸ pCore 2 (d.orbitSylowBorel K)))) ∧
      (generalizedFitting d.L = pCore 2 d.L →
        d.ConstrainedRankOneAlternative ∨
          ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
            StarModels.Model (starImage d.L d.Q1 d.L) ∧
              (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
              (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
                Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3)) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun _ hK hq hb => d.localFamily_orbitBorel_structure hK hq hb,
    s.constrained_rankOne_or_star (h := h) hG hempty hM hJ hu hne hmany hres⟩

/-- Apply the exact full-Sylow equivalence and disjoint C.2.7 reduction to
an original marker, including prime five. The earlier residual premise
remains with its named source producer and final assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_constrained_disjoint_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        (((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) ↔ d.SL ≤ d.Q1) ∧
        ((d.SL ≤ d.Q1 ∧ d.ConstrainedRankOneAlternative) ∨
          (¬ d.SL ≤ d.Q1 ∧
            ¬ ((∃ n : ℕ, IsL2EvenBlock d.L n) ∨ IsAlternatingBlock d.L 5) ∧
            ∃ hnL : d.Q1 ≤ normalizer (d.L : Set G),
              StarModels.Model (starImage d.L d.Q1 d.L) ∧
                (coreToStar hnL).ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
                (Nat.card (center (d.L ⧸ pCore 2 d.L)) = 1 ∨
                  Nat.card (center (d.L ⧸ pCore 2 d.L)) = 3)))) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,fun hfit => ⟨?_,?_⟩⟩
  · exact s.constrained_rankOne_block_iff_sylow_le_radical (h := h) hG hM hu hne hmany hres hfit
  · exact s.constrained_disjoint_rankOne_or_star (h := h) hG hempty hM hJ hu hne hmany hres hfit

/-- The original marker supplies the literal FF central quotient and a proper
marked overgroup of its Sylow image for every escaping constrained local member.
Original 15.1.14 remains with its named producer and pre-exclusion assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_local_ff_quotient_comparison
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
        ∃ a : d.NormalizerAction K,
          StarModels.Model (d.normalizerImage K) ∧
          a.coreToImage.ker ≤ center (K ⧸ pCore 2 K) ∧
          (Nat.card a.coreToImage.ker = 1 ∨ Nat.card a.coreToImage.ker = 3) ∧
          Nonempty ((K ⧸ centralPreimage (pCore 2 K)) ≃*
            (d.normalizerImage K ⧸ center (d.normalizerImage K))) ∧
          (d.normalizerMarkedImage K).comap (d.toNormalizerImage K) = d.MZ.subgroupOf K ∧
          d.normalizerMarkedImage K ≠ ⊤ ∧
          ∃ P : Sylow 2 (d.normalizerImage K),
            (P : Subgroup (d.normalizerImage K)) =
              ((d.S ⊓ K).subgroupOf K).map (d.toNormalizerImage K) ∧
            (P : Subgroup (d.normalizerImage K)) ≤ d.normalizerMarkedImage K := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout hf
  exact d.localFamily_ff_quotient_comparison hG hempty hM hJ hu h hK hq hout hf

/-- The later exchanged source uses the same literal normalizer quotient on
both plane sizes. The original core quotient is compared without replacing L. -/
theorem CaseIComponentData.ExchangedSource.constrained_ff_quotient_comparison
    {T : Sylow 2 G} {M Mc V : Subgroup G}
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    ∃ a : d.NormalizerAction d.L,
      StarModels.Model (d.normalizerImage d.L) ∧
      a.coreToImage.ker ≤ center (d.L ⧸ pCore 2 d.L) ∧
      (Nat.card a.coreToImage.ker = 1 ∨ Nat.card a.coreToImage.ker = 3) ∧
      Nonempty ((d.L ⧸ centralPreimage (pCore 2 d.L)) ≃*
        (d.normalizerImage d.L ⧸ center (d.normalizerImage d.L))) ∧
      (d.normalizerMarkedImage d.L).comap (d.toNormalizerImage d.L) = d.MZ.subgroupOf d.L ∧
      d.normalizerMarkedImage d.L ≠ ⊤ ∧
      ∃ P : Sylow 2 (d.normalizerImage d.L),
        (P : Subgroup (d.normalizerImage d.L)) =
          ((d.S ⊓ d.L).subgroupOf d.L).map (d.toNormalizerImage d.L) ∧
        (P : Subgroup (d.normalizerImage d.L)) ≤ d.normalizerMarkedImage d.L :=
  d.localFamily_ff_quotient_comparison hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf

/-- The original marker prepares the source seed on every local-family
normalizer, retaining the original prime before exchanged selection. -/
theorem PreparedChosenModule.source_preExclusion_local_normalizer_seed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
        let H := K ⊔ d.normalizerSylow K
        ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = d.normalizerSylow K ∧
          generalizedFitting H = pCore 2 H ∧
          pResidual 2 H = K.subgroupOf H ∧
          d.normalizerModule K ≤ normalClosure (omegaOneCenterAmbient (P : Subgroup H) : Set H) ∧
          ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (d.normalizerModule K : Set H) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun K hK hq hout hf =>
    d.localFamily_normalizer_seed_setup hG hempty hM hJ hu h hK hq hout hf⟩

/-- The later exchanged component uses the same original seed and literal residual. -/
theorem CaseIComponentData.ExchangedSource.constrained_normalizer_seed
    {T : Sylow 2 G} {M Mc V : Subgroup G} {d : CaseIComponentData T M Mc V}
    (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hf : generalizedFitting d.L = pCore 2 d.L) :
    let H := d.L ⊔ d.normalizerSylow d.L
    ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = d.normalizerSylow d.L ∧
      generalizedFitting H = pCore 2 H ∧
      pResidual 2 H = d.L.subgroupOf H ∧
      d.normalizerModule d.L ≤ normalClosure (omegaOneCenterAmbient (P : Subgroup H) : Set H) ∧
      ¬ elementaryAbelianMaxJ (P : Subgroup H) ≤ centralizer (d.normalizerModule d.L : Set H) :=
  d.localFamily_normalizer_seed_setup hG hempty hM hJ hu h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple d.L_not_le_MZ hf

/-- Original-marker application of the normalized rank-one nonblock exclusion.
The original prime is unrestricted. The 15.1.14 premise remains with its
existing owner and is discharged by the pre-exclusion assembly owner. -/
theorem PreparedChosenModule.source_preExclusion_normalized_nonblock_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        generalizedFitting K = pCore 2 K → d.S ≤ normalizer (K : Set G) →
        ¬ IsChiBlock K → ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
          ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) → K ≤ d.MZ := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hf hn hnot F _ _ _ e
  exact d.localFamily_nonblock_le_MZ_of_sylow_normalizes hG hempty hM hJ hu h hK hq hf
    hn hnot F e

/-- The later exchanged source uses the same local restriction on both
plane sizes, with the original G₁, S, M_Z and literal two-core quotient. -/
theorem CaseIComponentData.ExchangedSource.constrained_normalized_nonblock_placement
    {T : Sylow 2 G} {M Mc V : Subgroup G} {d : CaseIComponentData T M Mc V}
    (_s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (hn : d.S ≤ normalizer (K : Set G)) (hnot : ¬ IsChiBlock K)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) : K ≤ d.MZ :=
  d.localFamily_nonblock_le_MZ_of_sylow_normalizes hG hempty hM hJ hu h hK hq hf
    hn hnot F e

/-- Before prime exclusion, every escaping rank-one member of the original
local family has its noncentral fixed witness on the literal moved seed.
The marker prime is unrestricted, preserving both original primes. -/
theorem PreparedChosenModule.source_caseI_constrained_local_rankOne_fixed_witnesses
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        generalizedFitting K = pCore 2 K → ¬ K ≤ d.MZ → ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
          ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) →
          ∃ u ∈ d.normalizerMoved K, u ∈ ChapterB.thompsonAlpha d.S ∧ u ∉ centralizer (K : Set G) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hf hout F _ _ _ e
  exact d.localFamily_core_rankOne_fixed_witness hG hempty hM hJ hu h hK hq hout hf F e

/-- The later exchanged source retains the same literal fixed witness on
both plane sizes and does not assume that S normalizes K. -/
theorem CaseIComponentData.ExchangedSource.constrained_local_rankOne_fixed_witness
    {T : Sylow 2 G} {M Mc V : Subgroup G} {d : CaseIComponentData T M Mc V}
    (_s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (hout : ¬ K ≤ d.MZ)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ u ∈ d.normalizerMoved K, u ∈ ChapterB.thompsonAlpha d.S ∧ u ∉ centralizer (K : Set G) :=
  d.localFamily_core_rankOne_fixed_witness hG hempty hM hJ hu h hK hq hout hf F e


/-- The original marker supplies nonblock placement on its whole local family,
retaining the fixed G₁, S and M_Z and both original primes. -/
theorem PreparedChosenModule.source_caseI_constrained_local_nonblock_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        generalizedFitting K = pCore 2 K → ¬ IsChiBlock K →
        ∀ (F : Type) [Field F] [Finite F] [CharP F 2],
          ((K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) → K ≤ d.MZ := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hf hnot F _ _ _ e
  exact d.localFamily_nonblock_le_MZ hG hempty hM hJ hu h hK hq hf hnot F e

/-- The later exchanged source applies the same unrestricted nonblock theorem
on either plane size, without S-normality or ambient componenthood of K. -/
theorem CaseIComponentData.ExchangedSource.constrained_local_nonblock_placement
    {T : Sylow 2 G} {M Mc V : Subgroup G} {d : CaseIComponentData T M Mc V}
    (_s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (hnot : ¬ IsChiBlock K)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 2) F) : K ≤ d.MZ :=
  d.localFamily_nonblock_le_MZ hG hempty hM hJ hu h hK hq hf hnot F e

/-- The actual Nine action constructs both source records on the same marker
and supplies full local-family group/intersection rows. The natural escapes
are excluded for every eligible K, with no new component hypothesis on K.
The earlier 15.1.14 residual remains explicit. -/
theorem PreparedChosenModule.source_nine_local_constrained_source_rows
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (h9 : letI := h.elementary
      SourceCases.Nine (ChapterD.UniqueFactor.imageRepresentation M V h.normalized)
        (((T : Subgroup G).subgroupOf M).map (ChapterD.UniqueFactor.actionHom M V h.normalized).rangeRestrict))
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.row = .four ∧ Nat.card d.Z1 = 2 ∧
      d.PreExclusionSource h.normalized 3 ∧ d.ExchangedSource ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → generalizedFitting K = pCore 2 K →
          ⁅K,elementaryAbelianMaxJ d.S⁆ = K ∧
            CaseIComponentData.LocalConstrainedSourceRows d K := by
  obtain ⟨d,hr,hcard,s,g⟩ := h.source_nine_preExclusion_component
    hG T hempty hM hmany hJ hu hne hfull h9 hres
  have x := s.exchangedSource hG h g
  refine ⟨d,hr,hcard,s,x,?_⟩
  intro K hK hq hout hf
  exact x.localFamily_constrained_source_rows (h := h) s
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hf

end CFSG.Quasithin.Chapter15.Section01
