module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourGeneration
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.LinearThree
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.NormalClauses
public import Theory.SpecificGroups.PSL2.PrimeCubicRank
public import Theory.SpecificGroups.Classical.PairedOddRank
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The full nonsolvable Hermitian residual and its source models

The marked involution in the two-core quotient is centralized by the
maximal subgroup. The central-point source calculations exclude Bender
components and higher-field symplectic components and reduce binary
linear-three components to field two. A cyclic Sylow three-subgroup
remains cyclic under every quotient. This excludes exchanged odd PSL₂
components, whose product has cubic rank at least two, and the binary
derived symplectic component.

The surviving component in the literal X/O₂(X) is normal and quasisimple,
and equals the full two-residual. The image of the original maximal core
is its full center. The surviving model rows include their actual
maximal overlap, automizer and diagram data. Their further 3/5-rotation
inspection and chief-section exclusions remain separate arguments.

Source: Aschbacher–Smith 8.2.9, printed pp.720–721, using E.2.2,
printed pp.215–216, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterB ChapterE
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]
set_option backward.isDefEq.respectTransparency false

private theorem star_three_rank_le_one
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (h3 : primeRank 3 X ≤ 1) : primeRank 3 (X ⧸ minimalParabolicCore S hP) ≤ 1 := by
  let P : Sylow 3 X := Classical.choice inferInstance
  exact P.primeRank_quotient_le_one (P.isCyclic_of_odd_of_primeRank_le_one (by decide) h3) _

private theorem not_exchanged_odd_of_three_rank
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (K : Subgroup X) (hK : K.IsCComponent) (hgen : K ⊔ (S : Subgroup X) = ⊤)
    (hn : ¬K.Normal) (h3 : primeRank 3 X ≤ 1)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) 2 p) :
    False := by
  let J := minimalParabolicCore S hP
  let q := QuotientGroup.mk' J
  let R := S.mapSurjective (QuotientGroup.mk'_surjective J)
  let B := K.map q
  let : Group.IsSolvable J := minimalParabolic_core_solvable S hP
  have hi := Structure.source_component_simple_image S hP hs K hK hgen
  have hB : B.IsCComponent := hK.map_quotient J
  have hnot : ¬ B.Normal := fun hh => hn (cComponent_normal_of_quotient_normal hK J hh)
  obtain ⟨t,_,_,_,_,⟨e,_⟩,_,_⟩ := Structure.source_pair_coordinates
    (Structure.source_star_sqtk ChapterA.Section02.theoremA_knownSimple hX S hP hs).stronglyQuasithin
    R (Structure.source_star_minimal_core_free S hP).1
    (fun hh => hs ((Group.isSolvable_iff_subgroup_quotient J).mpr ⟨inferInstance,hh⟩))
    (Structure.source_star_minimal_core_free S hP).2 hi.2.1 hB hi.2.2.2 hnot
  let D := B.map (MulAut.conj (t : X ⧸ J)).toMonoidHom
  have hpos : 1 ≤ primeRank 3 B := by
    obtain ⟨F,hF,hfin,hcard,⟨eF⟩⟩ := hm
    exact Theory.PSL2.prime_model_three_rank_pos hp ho hcard eF
  have he : primeRank 3 B = primeRank 3 D :=
    primeRank_equiv 3 ((MulAut.conj (t : X ⧸ J)).subgroupMap B)
  have hr : 2 ≤ primeRank 3 (B ⊔ D : Subgroup (X ⧸ J)) := by
    rw [←primeRank_equiv 3 e,primeRank_prod_eq_add]
    change 2 ≤ primeRank 3 B + primeRank 3 D
    omega
  have hu := (primeRank_subgroup_le 3 (B ⊔ D)).trans (star_three_rank_le_one S hP h3)
  omega

/-- The central marked involution and cubic rank exclude the exchanged and
binary symplectic rows of the literal source catalogue. -/
private theorem parabolic_normal_component_cases_of_central_marker
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hWN : (W.subgroupOf (S : Subgroup X)).Normal)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hcent : minimalParabolicMax S hP ≤ centralizer (W : Set X))
    (h3 : primeRank 3 X ≤ 1) :
    ∃ K : Subgroup X, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      K.Normal ∧ K ⊔ (S : Subgroup X) = ⊤ ∧
      SingleClauses (minimalParabolicMax S hP) K (S : Subgroup X) ∧
      (SingleOddLinearModel (minimalParabolicMax S hP) K (S : Subgroup X) ∨
       SingleOddRankThreeModel (minimalParabolicMax S hP) K (S : Subgroup X) ∨
       ClassicalGroup.IsPSL (sourceImage (minimalParabolicMax S hP) K) 3 2 ∧
         DiagramModel (minimalParabolicMax S hP) K (S : Subgroup X) 1) := by
  have hres : (pResidual 2 (minimalParabolicMax S hP)).map
      (minimalParabolicMax S hP).subtype ≤ centralizer (W : Set X) :=
    (map_subtype_le _).trans hcent
  obtain ⟨K,hK,hqs,hgen,_⟩ := Structure.source_original_component hX S hP hs
  have hn : K.Normal := by
    by_contra hn
    rcases source_exchanged_marked_cases ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX S hP hs K hK hgen hn with
      ⟨f,_,hm⟩ | ⟨p,hp,ho,_,hm⟩
    · have hb : ClassificationModels.IsBenderModel
          (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) := by
        rcases hm with ⟨F,hF,hfin,hchar,hf,hcard,e,_⟩ | ⟨m,hm,_,e,_⟩
        · exact .linear f hf ⟨F,hF,hfin,hcard,⟨e⟩⟩
        · exact .suzuki m hm ⟨e⟩
      exact Witnesses.PairedBender.source_original_component_bender_residual_exclusion
        ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen hb
        W hWS hWN hout hres
    · exact not_exchanged_odd_of_three_rank hX S hP hs K hK hgen hn h3 hp ho hm
  let := hn
  refine ⟨K,hK,hqs,hn,hgen,source_single_clauses S hP hs K hK hqs hgen,?_⟩
  rcases source_normal_geometric_cases ChapterA.Section02.theoremA_knownSimple
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX S hP hs K hK hgen with
    h2 | h3model | hb | hl | hsp | hbi
  · exact .inl h2
  · exact .inr (.inl h3model)
  · exact (Witnesses.PairedBender.source_original_component_bender_residual_exclusion
      ChapterA.Section02.theoremA_knownSimple hX S hP hs K hK hgen hb
      W hWS hWN hout hres).elim
  · obtain ⟨f,hf,hm⟩ := hl
    have he := Witnesses.source_linear_three_parameter_eq_one_of_residual_centralizes
      S hP hs K hK hgen (by omega) hm W hWS hWN hout hres
    subst f
    exact .inr (.inr ⟨by simpa only [pow_one] using hm,
      source_binary_linear_three_model S hP hs K hK hgen (by decide) hm⟩)
  · obtain ⟨f,hf,hm⟩ := hsp
    exact (Witnesses.source_not_nonbinary_symplectic_of_residual_centralizes
      S hP hs K hK hgen (by omega) hm W hWS hWN hout hres).elim
  · obtain ⟨e⟩ := hbi
    have hr := Theory.SpecificGroups.Classical.PairedOddRank.derived_psp_binary_three_rank
    rw [←primeRank_equiv 3 e] at hr
    change 2 ≤ primeRank 3 (K.map (QuotientGroup.mk' (minimalParabolicCore S hP))) at hr
    have hu := (primeRank_subgroup_le 3 (K.map (QuotientGroup.mk' (minimalParabolicCore S hP)))).trans
      (star_three_rank_le_one S hP h3)
    omega

/-- The nonsolvable source catalogue on the full two-core quotient has a
normal component. The maximal overlap, full center and actual automizer
markings are retained in each surviving row. -/
theorem parabolic_quotient_normal_component_models
    (hX : IsSQTK KnownSimple.IsKnownSimple X)
    (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤) (hs : ¬Group.IsSolvable X)
    (W : Subgroup X) [IsElementaryAbelian 2 W] (hWS : W ≤ S)
    (hout : ¬W ≤ minimalParabolicCore S hP)
    (hMW : minimalParabolicMax S hP ≤ normalizer (W : Set X))
    (hcard : Nat.card (W.map (QuotientGroup.mk' (pCore 2 X))) = 2)
    (h3 : primeRank 3 X ≤ 1) :
    let q := QuotientGroup.mk' (pCore 2 X)
    let M := (minimalParabolicMax S hP).map q
    let T := (S : Subgroup X).map q
    ∃ K : Subgroup (X ⧸ pCore 2 X), IsComponent (X ⧸ pCore 2 X) K ∧
      K.IsCComponent ∧ K.Normal ∧ pResidual 2 (X ⧸ pCore 2 X) = K ∧
      (minimalParabolicCore S hP).map q = (center K).map K.subtype ∧
      K ⊔ T = ⊤ ∧ SingleClauses M K T ∧
      (SingleOddLinearModel M K T ∨ SingleOddRankThreeModel M K T ∨
       ClassicalGroup.IsPSL (sourceImage M K) 3 2 ∧ DiagramModel M K T 1) := by
  let N := pCore 2 X
  let q := QuotientGroup.mk' N
  let R := S.mapSurjective (QuotientGroup.mk'_surjective N)
  let A := W.map q
  have hk : q.ker ≤ (S : Subgroup X) := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal S
  have hPq := minimalParabolic_surjective S hP q (QuotientGroup.mk'_surjective N) hk
  have hJpre : (minimalParabolicCore R hPq).comap q = minimalParabolicCore S hP := by
    rw [←minimalParabolicCore_map S hP q (QuotientGroup.mk'_surjective N) hk,
      comap_map_eq,QuotientGroup.ker_mk',
      sup_eq_left.mpr (minimalParabolicTwoCore_le_core S hP)]
  have hmax : minimalParabolicMax R hPq = (minimalParabolicMax S hP).map q :=
    (minimalParabolicMax_map_core S hP q (QuotientGroup.mk'_surjective N)
      (by simpa only [q,QuotientGroup.ker_mk'] using minimalParabolicTwoCore_le_core S hP)).symm
  have hAR : A ≤ (R : Subgroup (X ⧸ N)) := map_mono hWS
  have hN : minimalParabolicMax R hPq ≤ normalizer (A : Set (X ⧸ N)) := by
    rw [hmax]
    exact (map_mono hMW).trans (le_normalizer_map q)
  have hAN : (A.subgroupOf (R : Subgroup (X ⧸ N))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hAR).mpr
      ((minimalParabolicMax_spec R hPq).2.trans hN)
  have houtq : ¬A ≤ minimalParabolicCore R hPq := by
    intro ha
    apply hout
    have hh := map_le_iff_le_comap.mp ha
    rwa [hJpre] at hh
  let : Group.IsNilpotent N := (pCore_isPGroup (p := 2) (G := X)).isNilpotent
  have hsq : ¬Group.IsSolvable (X ⧸ N) := fun hh =>
    hs ((Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,hh⟩)
  have h3q : primeRank 3 (X ⧸ N) ≤ 1 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) N pCore_isPGroup).trans h3
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  obtain ⟨K,hK,hqs,hn,hgen,hclauses,hmodels⟩ :=
    parabolic_normal_component_cases_of_central_marker
      (Structure.sqtk_two_quotient hX N pCore_isPGroup) R hPq hsq A hAR hAN houtq
      (hN.trans (normalizer_le_centralizer_of_card_two A hcard)) h3q
  let := hn
  let := hqs
  let q₂ := QuotientGroup.mk' (pCore 2 (X ⧸ N))
  have hq₂ : Function.Injective q₂ := (MonoidHom.ker_eq_bot_iff q₂).mp (by
    rw [QuotientGroup.ker_mk',pCore_quotient_pCore_eq_bot 2])
  have hquasi : IsQuasisimple K := IsQuasisimple.of_mulEquiv
    ((cComponentTwoCoreQuotientEquiv hK).trans (K.equivMapOfInjective q₂ hq₂).symm)
  have hcomp : IsComponent (X ⧸ N) K := ⟨hK.subnormal,hquasi⟩
  have hres : pResidual 2 (X ⧸ N) = K := (Structure.residual_eq_layer R hcomp hgen).trans
    (Structure.layer_eq_normal_component R hcomp hgen)
  have hcenter : (minimalParabolicCore S hP).map q = (center K).map K.subtype :=
    (minimalParabolicCore_map S hP q (QuotientGroup.mk'_surjective N) hk).trans
      (Structure.core_eq_normal_component_center R hPq hsq
        (pCore_quotient_pCore_eq_bot 2) hcomp hgen)
  rw [hmax] at hclauses hmodels
  exact ⟨K,hcomp,hK,hn,hres,hcenter,hgen,hclauses,hmodels⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
