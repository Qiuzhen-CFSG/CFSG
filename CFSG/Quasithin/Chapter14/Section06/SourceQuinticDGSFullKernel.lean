module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDGSMarking
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.CommutatorGeometry
public import Theory.GroupAction.RankTwoCosetGeometry.SpanCentralizerKernel
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# The original quintic span and the full DGS second kernel

The two-group edge identifies each full first kernel with its actual core.
The marked graph centers identify the quintic neighborhood span with the
original H-orbit of the four-plane.  The full second kernel is exactly the
centralizer of that same span inside H, with the original ambient inclusion.

The centralizer-to-core containment uses only the original normalizer of
the plane, the prime index-five intersection and relative normality.  No
abelian span, quadratic action or numerical core bound is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem reduced_first_kernels_of_two_group_edge
    {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
    (hp : IsPGroup 2 (Reduction.reducedFamily L S false ⊓ Reduction.reducedFamily L S true :
      Subgroup (Reduction.G₀ L S))) :
    ∀ i, ballKernel (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) i) 1 =
      Q (Reduction.reducedFamily L S) (base (Reduction.reducedFamily L S) i) := by
  intro i
  let F := Reduction.reducedFamily L S
  have hadj : (graph F).Adj (base F i) (base F (!i)) :=
    ⟨by change i ≠ !i; cases i <;> decide,Subgroup.CosetGeometry.incident_base F i (!i)⟩
  have hU : IsPGroup 2 (U F (base F i)) := by
    apply hp.to_le
    change ballKernel F (base F i) 1 ≤ F false ⊓ F true
    have hh := ballKernel_one_le_edge F hadj
    cases i <;> simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base,
      Bool.not_false,Bool.not_true,inf_comm] using hh
  obtain ⟨T,hT⟩ := Reduction.reduced_kernel_sylow h (base F i)
  have ht : (T : Subgroup (U F (base F i))) = ⊤ :=
    (T.is_maximal' (hU.to_subgroup ⊤) le_top).symm
  rw [ht,←MonoidHom.range_eq_map,range_subtype] at hT
  exact hT

omit [Finite G] in
private theorem second_kernel_false_eq_span_centralizer
    (F : Bool → Subgroup G) (W : Subgroup G)
    (hfirst : ballKernel F (base F true) 1 = F true ⊓ centralizer (W : Set G))
    (hwhole : F false ⊓ centralizer (conjugateSpanBy W (F false) : Set G) ≤
      ballKernel F (base F false) 1) :
    ballKernel F (base F false) 2 =
      F false ⊓ centralizer (conjugateSpanBy W (F false) : Set G) := by
  let C := F false ⊓ centralizer (conjugateSpanBy W (F false) : Set G)
  have hadj : (graph F).Adj (base F false) (base F true) :=
    ⟨by change (false : Bool) ≠ true; decide,Subgroup.CosetGeometry.incident_base F false true⟩
  have hKle : ballKernel F (base F false) 2 ≤ F false := by
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using
      ballKernel_le_stabilizer F (base F false) 2
  have hKN : F false ≤ normalizer (ballKernel F (base F false) 2 : Set G) := by
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using
      stabilizer_le_normalizer_ballKernel F (base F false) 2
  have hKC : ballKernel F (base F false) 2 ≤ C :=
    le_inf hKle (le_centralizer_conjugateSpanBy_of_normalizes _ W _ hKN
      ((ballKernel_succ_le F hadj 1).trans (hfirst.le.trans inf_le_right)))
  apply le_antisymm hKC
  have hn : F false ≤ normalizer (C : Set G) :=
    (le_inf (F false).le_normalizer
      ((le_normalizer_conjugateSpanBy W (F false)).trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  let : (C.subgroupOf (F false)).Normal := normal_subgroupOf_of_le_normalizer hn
  have hCF : C ≤ F true := by
    have hh := hwhole.trans ((ballKernel_one_le_edge F hadj).trans inf_le_right)
    simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using hh
  have hCfirst : C ≤ ballKernel F (base F true) 1 := by
    rw [hfirst]
    exact le_inf hCF (inf_le_right.trans (centralizer_le (le_conjugateSpanBy W (F false))))
  have hCcore : C.subgroupOf (F false) ≤
      ((ballKernel F (base F false) 1 ⊓ ballKernel F (base F true) 1).subgroupOf
        (F false)).normalCore :=
    normal_le_normalCore.mpr (fun _ hx => ⟨hwhole hx,hCfirst hx⟩)
  rw [←base_ballKernel_two F false] at hCcore
  intro x hx
  exact hCcore (show (⟨x,hx.1⟩ : F false) ∈ C.subgroupOf (F false) from hx)

/-- The centralizer of the literal H-span lies in the full H-core, using
the original plane normalizer and prime Sylow index alone. -/
theorem source_quintic_span_centralizer_le_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M : Subgroup G} (hM : IsOrderingMaximal T M)
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) ≤ H.pCoreIn 2 := by
  let V₀ := localModule T M
  let UH := conjugateSpanBy V₀ H
  let C := H ⊓ centralizer (UH : Set G)
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hTM : (T : Subgroup G) ≤ M := hM.1.2
  have hHM : H ⊓ M = (T : Subgroup G) := by
    have hT : (T : Subgroup G) ≤ H ⊓ M := le_inf hTH hTM
    have hm := relIndex_mul_relIndex (T : Subgroup G) (H ⊓ M) H hT inf_le_left
    rw [hi] at hm
    rcases Nat.prime_mul_iff.mp (hm ▸ Nat.prime_five) with hp | hp
    · exact (hH.1.2 ((relIndex_eq_one.mp hp.2).trans inf_le_right)).elim
    · exact le_antisymm (relIndex_eq_one.mp hp.2) hT
  have hCM : C ≤ M := by
    rw [InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1]
    exact (inf_le_right.trans (centralizer_le (le_conjugateSpanBy V₀ H))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCT : C ≤ (T : Subgroup G) := by
    rw [←hHM]
    exact le_inf inf_le_left hCM
  have hn : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy V₀ H).trans
      (normalizer_le_normalizer_centralizer UH))).trans inf_normalizer_le_normalizer_inf
  exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le hCT) inf_le_left hn

/-- The graph span and full second kernel have the literal original images.
Both full first kernels are also identified with their original full cores. -/
theorem source_quintic_dgs_span_and_full_kernel
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let J := Reduction.G₀ ![H,X] (T : Subgroup G)
    let F := Reduction.reducedFamily ![H,X] (T : Subgroup G)
    let UH := conjugateSpanBy (localModule T M) H
    (∀ i, ballKernel F (base F i) 1 = Q F (base F i) ∧
      (ballKernel F (base F i) 1).map J.subtype = (family ![H,X] i).pCoreIn 2) ∧
      (V F (base F false) 1).map J.subtype = UH ∧
      (ballKernel F (base F false) 2).map J.subtype = H ⊓ centralizer (UH : Set G) := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  let UH := conjugateSpanBy (localModule T M) H
  let W := Z F (base F true)
  let R := conjugateSpanBy W (F false)
  let C := F false ⊓ centralizer (R : Set J)
  obtain ⟨hF,_,_,hB,_,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  have hHmap : (F false).map J.subtype = H := (hmaps false).1
  have hXmap : (F true).map J.subtype = X := (hmaps true).1
  have hQHmap : (Q F (base F false)).map J.subtype = H.pCoreIn 2 := (hmaps false).2
  have hQXmap : (Q F (base F true)).map J.subtype = X.pCoreIn 2 := (hmaps true).2
  have ht : LocallyRankOneTriple (fun i => (Reduction.P₀ L (T : Subgroup G) i).subgroupOf J)
      ((Reduction.B₀ L (T : Subgroup G)).subgroupOf J) := Reduction.reduced_triple hF
  change Reduction.B₀ L (T : Subgroup G) = T at hB
  have hbase : IsPGroup 2 (F false ⊓ F true : Subgroup J) := by
    change IsPGroup 2 (((Reduction.P₀ L (T : Subgroup G) 0).subgroupOf J) ⊓
      ((Reduction.P₀ L (T : Subgroup G) 1).subgroupOf J) : Subgroup J)
    rw [ht.intersection,hB]
    exact T.isPGroup'.comap_subtype
  have hfirst := reduced_first_kernels_of_two_group_edge hF hbase
  change ∀ i, ballKernel F (base F i) 1 = Q F (base F i) at hfirst
  obtain ⟨hZH,hZX⟩ := source_quintic_dgs_center_markings hG T hempty hM hu hmany hcard e H hH hi
  change (Z F (base F false)).map J.subtype = centralInvolutions T at hZH
  change W.map J.subtype = localModule T M at hZX
  have hRmap : R.map J.subtype = UH := by
    change (conjugateSpanBy W (F false)).map J.subtype = _
    rw [map_conjugateSpanBy,hZX,hHmap]
  have hCmap : C.map J.subtype = H ⊓ centralizer (UH : Set G) := by
    rw [←map_inf_centralizer_of_injective J.subtype J.subtype_injective,hHmap,hRmap]
  have hadj : (graph F).Adj (base F false) (base F true) :=
    ⟨by change (false : Bool) ≠ true; decide,Subgroup.CosetGeometry.incident_base F false true⟩
  have hspan : V F (base F false) 1 = Z F (base F false) ⊔ R := by
    apply CommutingThreeProfile.V_eq_center_sup_neighbor_conjugates F (F false)
      (by rw [stabilizer,Subgroup.CosetGeometry.stabilizer_base]) hadj
    intro z hz
    obtain ⟨g,hg,he⟩ := locally_transitive F hadj hz
    exact ⟨g,by simpa only [stabilizer,Subgroup.CosetGeometry.stabilizer_base] using hg,he⟩
  have hspanMap : (V F (base F false) 1).map J.subtype = UH := by
    rw [hspan,Subgroup.map_sup,hZH,hRmap]
    have hZV : centralInvolutions T ≤ localModule T M := le_conjugateSpanBy _ _
    exact sup_eq_right.mpr (hZV.trans (le_conjugateSpanBy _ _))
  have hseed : ballKernel F (base F true) 1 = F true ⊓ centralizer (W : Set J) := by
    apply map_injective J.subtype_injective
    rw [hfirst,hQXmap,←map_inf_centralizer_of_injective J.subtype J.subtype_injective,hXmap,hZX]
    exact (Section02.source_residualSylow_quotient hG T hempty hM hu hmany hcard e).1
  have hwhole : C ≤ ballKernel F (base F false) 1 := by
    rw [hfirst]
    apply (Subgroup.map_le_map_iff_of_injective J.subtype_injective).mp
    rw [hCmap,hQHmap]
    exact source_quintic_span_centralizer_le_core hG T hM H hH hi
  refine ⟨fun i => ⟨hfirst i,?_⟩,hspanMap,?_⟩
  · rw [hfirst]
    exact (hmaps i).2
  · rw [second_kernel_false_eq_span_centralizer F W hseed hwhole]
    exact hCmap

end CFSG.Quasithin.Chapter14.Section06
