module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalSelected
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SolvableQuotients
public import Theory.GroupTheory.NormalCentralQuotientAction.SolvableKernel
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# The constrained selected carrier of a natural local escape

Restrict the original local member K to the selected component L and to
its literal Sylow intersection. Its image in L/O₂(L) is proper: O₂(L)
normalizes K, so a full image would make K normal in L, and perfectness
would force K=L. The original field-four block supplies the actual A₅
two-core quotient, including the restricted two-group kernel.

The full-Sylow local-section sieve excludes the A₅ and central A₆ rows,
and both higher binary linear rows. Solvable-kernel transport through
O₂,Z(L) retains the A₅ section, whose factor five excludes the binary
L₃ and derived G₂ rows by their actual orders. Thus in the constrained
branch the original selected carrier has central quotient A₇. No whole
A₇ block or trivial covering kernel is asserted by this quotient result.

The original-marker consumer preserves the same prime, row, moving plane,
strict containment, normal carrier, shortness, and all group/intersection
rows. The remaining A₇ embedding and ordinary carrier branches, natural
Borel containment and final source assembly remain open. Original 15.1.14
and whole-core A₆ reconstruction keep their existing producers.

Source: Aschbacher--Smith A.3.12, printed pp.47--48, and 15.1.20(2),
printed pp.1094--1095. The finite model calculations reuse the existing
licensed ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private theorem core_image_proper {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (B : Subgroup A) [Group.IsPerfect B]
    (hn : pCore 2 A ≤ normalizer (B : Set A)) (hne : B ≠ ⊤) :
    B.map (QuotientGroup.mk' (pCore 2 A)) ≠ ⊤ := by
  intro he
  have hsup : B ⊔ pCore 2 A = ⊤ := by
    simpa only [comap_map_eq,QuotientGroup.ker_mk',comap_top] using
      congrArg (comap (QuotientGroup.mk' (pCore 2 A))) he
  let : B.Normal := normalizer_eq_top_iff.mp
    (top_unique (hsup ▸ sup_le B.le_normalizer hn))
  let : Group.IsNilpotent (pCore 2 A) := pCore_isNilpotent
  exact hne (((inferInstance : B.Normal).isSubnormal.eq_solvableResidual_of_sup_eq_top
    (pCore 2 A) hsup).trans solvableResidual_eq_top)

private theorem local_five_central_order
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    {S B : Subgroup A} (hb : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (e : (A ⧸ centralPreimage (pCore 2 A)) ≃* H) : 5 ∣ Nat.card H := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (centralPreimage (pCore 2 A)))
  let : Group.IsSolvable f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact centralPreimage_pCore_isSolvable 2
  obtain ⟨eq⟩ := FiveLocalFF.SolvableQuotients.section_map f B hb eB
  exact (FiveLocalFF.SolvableQuotients.five_dvd_card _ eq).trans (B.map f).card_subgroup_dvd_card

private theorem local_five_core_exclusions
    {A : Type*} [Group A] [Finite A] [IsQuasisimple (A ⧸ pCore 2 A)]
    (S : Sylow 2 A) (B : Subgroup A) (hb : B ∈ localCComponents S)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hproper : B.map (QuotientGroup.mk' (pCore 2 A)) ≠ ⊤) :
    (¬ Nonempty ((A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))) ∧
    (¬ Nonempty ((A ⧸ centralPreimage (pCore 2 A)) ≃* alternatingGroup (Fin 6))) ∧
    (∀ n : ℕ, n = 4 ∨ n = 5 → ¬ Nonempty ((A ⧸ pCore 2 A) ≃* SL(n,ZMod 2))) := by
  let q := QuotientGroup.mk' (pCore 2 A)
  have hk : IsPGroup 2 q.ker := by
    change IsPGroup 2 (QuotientGroup.mk' (pCore 2 A)).ker
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  let : Group.IsNilpotent q.ker := hk.isNilpotent
  have hbk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  refine ⟨?_,?_,?_⟩
  · intro he
    exact FiveLocalFF.AlternatingSmall.small_alternating_image_excluded q
      (QuotientGroup.mk'_surjective _) inferInstance S B hb hproper (Or.inl he)
  · rintro ⟨e⟩
    exact FiveLocalFF.AlternatingSmall.small_alternating_image_excluded q
      (QuotientGroup.mk'_surjective _) inferInstance S B hb hproper
      (Or.inr (Or.inr ⟨(centralPreimageQuotientEquiv (pCore 2 A)).symm.trans e⟩))
  · intro n hn he
    exact FiveLocalFF.BinaryLinear.image_excluded q (QuotientGroup.mk'_surjective _)
      inferInstance S B hb hbk eB hn
      ⟨ZMod 2,inferInstance,inferInstance,by simp,
        ⟨he.some.trans (_root_.BinaryLinear.OuterCyclic.projectiveEquivSL (by omega)).symm⟩⟩

/-- A natural local escape has only the A₇ central-quotient carrier in the
constrained branch. The source hypotheses supply the literal full Sylow,
proper local image and kernel conditions of the finite-section exclusions. -/
theorem PreExclusionSource.localFamily_linearTwo_constrained_carrier_seven
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    {n : ℕ} (hb : IsL2EvenBlock K n)
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    Nonempty ((d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 7)) := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨_,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  obtain ⟨hKL,hLmax,_,_,_⟩ := s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb hp2
  let B := K.subgroupOf d.L
  let e : B ≃* K := subgroupOfEquivOfLe hKL.le
  let := Chapter1.mem_L_isPerfect hK.2
  let := Chapter1.mem_L_isPerfect s.local_component
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let := s.quasisimple
  obtain ⟨P,hP⟩ := s.component_sylow
  have hPS : (P : Subgroup d.L) = d.S.subgroupOf d.L := by
    have he : (P : Subgroup d.L) = (d.S ⊓ d.L).subgroupOf d.L := by
      apply map_injective d.L.subtype_injective
      rw [hP,map_subgroupOf_eq_of_le inf_le_right]
      rfl
    rw [he]
    ext x
    exact and_iff_left x.property
  have hB : B ∈ localCComponents P := by
    rw [hPS]
    exact local_restrict hK.2.1 hKL.le
  let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
      ((hn ▸ hb : IsL2EvenBlock K 2).four_quotient_alternatingFive.some)
  have hSN := s.localFamily_linearTwo_sylow_normalizes (h := h)
    hG hM hJ hu hfull hK hq hout hb hp2
  have hQK : pCore 2 d.L ≤ normalizer (B : Set d.L) := by
    apply le_normalizer_iff.mpr
    intro q hq k hk
    have hqS : q.val ∈ d.S := (hP ▸ mem_map_of_mem d.L.subtype
      (pCore_isPGroup.le_sylow_of_normal P hq)).1
    exact le_normalizer_iff.mp hSN q hqS k hk
  have hproper : B.map (QuotientGroup.mk' (pCore 2 d.L)) ≠ ⊤ :=
    core_image_proper B hQK (fun ht => hKL.not_ge (subgroupOf_eq_top.mp ht))
  obtain ⟨hfive,hsix,hlin⟩ := local_five_core_exclusions P B hB eB hproper
  obtain ⟨_,hr⟩ := s.localFamily_maximal_constrained_source_rows (h := h) hp2
    hG hempty hM hJ hu hne hmany hfull hres hLmax s.quasisimple d.L_not_le_MZ hf
  cases hr with
  | naturalTwo n hblock _ =>
    exact (d.L_not_le_MZ (s.localFamily_linearTwo_le_MZ_of_cComponent (h := h)
      hG hM hJ hu hne hmany hfull hres hLmax.1 d.L_component.2 s.quasisimple hblock)).elim
  | alternatingFive hblock _ _ =>
    obtain ⟨_,⟨m⟩,_⟩ := hblock.2.2
    exact (hfive ⟨m.quotientIso⟩).elim
  | linear n hn _ e _ _ _ => exact (hlin n hn ⟨e⟩).elim
  | small model _ _ =>
    cases model with
    | alternatingSeven e => exact ⟨e⟩
    | alternatingSix e => exact (hsix ⟨e⟩).elim
    | linearThree e =>
      have hd := local_five_central_order hB eB e
      rw [Matrix.PSL3Two.card_SL] at hd
      norm_num at hd
    | g2DerivedTwo e =>
      have hd := local_five_central_order hB eB e
      rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
      norm_num at hd

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal original marker retains its unique selected carrier and all
source rows. In its constrained branch only the A₇ central quotient survives
the proper full-Sylow A₅-section sieve. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_carrier_sieve
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          m.prime = 3 ∧ n = 2 ∧ m.movingPlane ≤ (blockU K).map K.subtype ∧
            Nat.card m.movingPlane = 4 ∧ K < d.L ∧
            d.L ∈ Chapter1.LStarIn d.G1 d.S ∧
            (d.L.subgroupOf d.G1).Normal ∧ d.G1 ≤ normalizer (d.L : Set G) ∧
            (IsComponent d.G1 (d.L.subgroupOf d.G1) ∨
              (generalizedFitting d.L = pCore 2 d.L ∧ IsShort d.L ∧
                Nonempty ((d.L ⧸ centralPreimage (pCore 2 d.L)) ≃* alternatingGroup (Fin 7)) ∧
                ⁅d.L,elementaryAbelianMaxJ d.S⁆ = d.L ∧
                CaseIComponentData.LocalConstrainedSourceRows d d.L)) := by
  obtain ⟨d,hZ,hr,s,hfamily⟩ := h.source_preExclusion_local_natural_selected_carrier
    hG T hempty hM hmany hJ hu hne hfull m hp hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,hW,hcard,hKL,hmax,hLn,hGn,hbranch⟩ := hfamily K hK hq hout n hb
  refine ⟨hp3,hn,hW,hcard,hKL,hmax,hLn,hGn,?_⟩
  rcases hbranch with hc | ⟨hf,hs,hm,hrows⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hf,hs,s.localFamily_linearTwo_constrained_carrier_seven (h := h)
      hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb hf,hm,hrows⟩

end CFSG.Quasithin.Chapter15.Section01
