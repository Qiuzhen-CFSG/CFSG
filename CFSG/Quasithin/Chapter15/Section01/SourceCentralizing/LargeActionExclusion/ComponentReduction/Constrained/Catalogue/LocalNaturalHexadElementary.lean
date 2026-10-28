module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalHexadSpan

/-!
# Elementary spans and the abelian full covered-hexad core

For an original natural escape, put A = ⟨(V ∩ L)^H⟩ for its full hexad
lift H. The original quadratic ratio two excludes FF-modules. Every
HQ₁-conjugate of V lies in VA ≤ Q₁ ≤ M, so the equal-order conjugate
criterion makes the exact span VA elementary abelian.

The saved identity A Z(L) = O₂(H) now makes the full covered core abelian.
The original fixed summand centralizes L and the moving summand lies in L;
thus V centralizes Z(L), and consequently all of O₂(H). The original-marker
application retains G₁, M_Z, S, Q₁, K and the full central quotient map.

These conclusions do not assert automorphism invariance in Q₁. Exclusion of
the forced automorphic displacement and original 15.1.20(2)/15.1.22 assembly
remain open. Original 15.1.14 and whole-core A₆ reconstruction retain their
existing producers.

Source: Aschbacher--Smith D.1.2(1), p.172; 15.1.9(6), 15.1.11--12 and
15.1.16--20, printed pp.1088--1095; I.2.2(6), p.412 for the full hexad cover.
-/

public section
open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory Sporadic.Mathieu Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterD.UniqueFactor ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06 Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The full original hexad span is elementary. Its complete covering core
is abelian and centralizes the same original module. -/
theorem PreExclusionSource.localFamily_linearTwo_m22_hexad_elementary
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
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n) :
    V ≤ d.Q1 ∧
    ∃ e : (d.L ⧸ center d.L) ≃* M22, ∃ B ∈ m22Blocks,
      let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
      let H := ((MulAction.stabilizer M22 B).comap q).map d.L.subtype
      let A := conjugateSpanBy (V ⊓ d.L) H
      d.ML ≤ H ∧ d.MZ ≤ normalizer (H : Set G) ∧ K ⊔ H = d.L ∧
      A ≤ H.pCoreIn 2 ∧ H.pCoreIn 2 ≤ d.Q1 ∧
      (A.subgroupOf d.L).map q = m22HexadPointwiseKernel B ∧
      A ⊔ (center d.L).map d.L.subtype = H.pCoreIn 2 ∧
      conjugateSpanBy V (H ⊔ d.Q1) = V ⊔ A ∧
      IsElementaryAbelian 2 (V ⊔ A : Subgroup G) ∧
      IsMulCommutative (H.pCoreIn 2) ∧
      V ≤ centralizer (H.pCoreIn 2 : Set G) := by
  obtain ⟨hVQ,e,B,hB,hMLH,hMZN,hgen,hAQ,hHQ,hAimage,hAcore,hspan⟩ :=
    s.localFamily_linearTwo_m22_hexad_span (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
  let H := ((MulAction.stabilizer M22 B).comap q).map d.L.subtype
  let A := conjugateSpanBy (V ⊓ d.L) H
  let Z := (center d.L).map d.L.subtype
  let E := V ⊔ A
  let := h.elementary
  let f := actionHom M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  have hnf : ¬ IsFFModule ρ := by
    intro hf
    have hh := (Representation.BinaryOffender.isFFModule_iff_quadraticRatio_le_one ρ).mp hf
    rw [h.quadratic_ratio] at hh
    norm_num at hh
  have hEM : conjugateSpanBy V (H ⊔ d.Q1) ≤ M := by
    rw [hspan]
    exact (sup_le hVQ (hAQ.trans hHQ)).trans
      ((d.catalogue_radical_le_sylow s.centralizer_sylow hu).trans
        (d.S_le_T.trans hM.1.2))
  have hE : IsElementaryAbelian 2 E := by
    rw [show E = V ⊔ A from rfl,←hspan]
    apply Representation.BinaryOffender.conjugateSpan_elementary_of_notFF
      M (H ⊔ d.Q1) V f.rangeRestrict ρ
      (by rw [MonoidHom.ker_rangeRestrict]; exact actionHom_ker _ _ _)
      (fun _ _ => rfl) ?_ hnf
    intro g hg x hx
    obtain ⟨v,hv,rfl⟩ := hx
    apply hEM
    exact subset_closure ⟨g,hg,v,hv,rfl⟩
  let : IsElementaryAbelian 2 E := hE
  have hAL : A ≤ d.L := hAQ.trans
    ((pCoreIn_le 2 H).trans (map_subtype_le _))
  have hZL : Z ≤ centralizer (d.L : Set G) := by
    rintro _ ⟨z,hz,rfl⟩ l hl
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l,hl⟩)
  have hAZ : A ≤ centralizer (Z : Set G) :=
    le_centralizer_iff.mp (hZL.trans (centralizer_le hAL))
  have hAA : A ≤ centralizer (A : Set G) :=
    ((show A ≤ E from le_sup_right).trans E.le_centralizer).trans
      (centralizer_le (show A ≤ E from le_sup_right))
  have hZZ : Z ≤ centralizer (Z : Set G) :=
    hZL.trans (centralizer_le (map_subtype_le _))
  have hcore : IsMulCommutative (H.pCoreIn 2) := by
    apply le_centralizer_iff_isMulCommutative.mp
    rw [←hAcore]
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (sup_le hAA (le_centralizer_iff.mp hAZ)))
      (le_centralizer_iff.mp (sup_le hAZ hZZ))
  have hVZ : V ≤ centralizer (Z : Set G) := by
    obtain ⟨hsplit,_,_,_⟩ := s.localFamily_linearTwo_full_action (h := h)
      hG hM hJ hu hfull hK hq hout hb (by omega)
    have hKL := (s.localFamily_linearTwo_selected_carrier (h := h)
      hG hM hJ hu hne hmany hfull hres hK hq hout hb (by omega)).1.le
    have hWL := (s.localFamily_linearTwo_moving_plane_bound (h := h)
      hG hM hJ hu hfull hK hq hout hb (by omega)).1.trans
        ((map_subtype_le _).trans hKL)
    have hF := (s.localFamily_linearTwo_fixed_carrier (h := h) hp
      hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb).le.trans inf_le_right
    exact hsplit.le.trans (sup_le (hWL.trans (le_centralizer_iff.mp hZL))
      (hF.trans (centralizer_le (map_subtype_le _))))
  have hVcore : V ≤ centralizer (H.pCoreIn 2 : Set G) := by
    rw [←hAcore]
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp
      (((show V ≤ E from le_sup_left).trans E.le_centralizer).trans
        (centralizer_le (show A ≤ E from le_sup_right)))) (le_centralizer_iff.mp hVZ)
  exact ⟨hVQ,e,B,hB,hMLH,hMZN,hgen,hAQ,hHQ,hAimage,hAcore,hspan,hE,hcore,hVcore⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC ChapterC.C27Source Section03 Section03.InitialSource ChapterA.Section05To06
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

/-- The original marker supplies an elementary hexad span and an abelian full
core centralized by V, retaining the same prime and covering projection. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_m22_hexad_elementary
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
          m.prime = 3 ∧ n = 2 ∧ V ≤ d.Q1 ∧
          ∃ e : (d.L ⧸ center d.L) ≃* Sporadic.Mathieu.M22,
            ∃ B ∈ Sporadic.Mathieu.m22Blocks,
              let q := e.toMonoidHom.comp (QuotientGroup.mk' (center d.L))
              let H := ((MulAction.stabilizer Sporadic.Mathieu.M22 B).comap q).map d.L.subtype
              let A := conjugateSpanBy (V ⊓ d.L) H
              d.ML ≤ H ∧ d.MZ ≤ normalizer (H : Set G) ∧ K ⊔ H = d.L ∧
              A ≤ H.pCoreIn 2 ∧ H.pCoreIn 2 ≤ d.Q1 ∧
              (A.subgroupOf d.L).map q = Sporadic.Mathieu.m22HexadPointwiseKernel B ∧
              A ⊔ (center d.L).map d.L.subtype = H.pCoreIn 2 ∧
              conjugateSpanBy V (H ⊔ d.Q1) = V ⊔ A ∧
              IsElementaryAbelian 2 (V ⊔ A : Subgroup G) ∧
              IsMulCommutative (H.pCoreIn 2) ∧
              V ≤ centralizer (H.pCoreIn 2 : Set G) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,_,_⟩ := s.localFamily_linearTwo_moving_plane_four (h := h)
    hp hG hM hJ hu hfull hK hq hout hb
  exact ⟨hp3,hn,s.localFamily_linearTwo_m22_hexad_elementary (h := h) hp
    hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb⟩

end CFSG.Quasithin.Chapter15.Section01
