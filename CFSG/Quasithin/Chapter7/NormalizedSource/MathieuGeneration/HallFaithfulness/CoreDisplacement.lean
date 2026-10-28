module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.CubicDisplacement

/-!
# The original core as the Mathieu displacement kernel

Every Sylow subgroup of the source section centralizer that contains
R = O₂(J) meets an outside overgroup H in exactly R. The source Sylow
statement in H proves this by maximality, with all subgroups embedded in
G. Reselecting the involution while retaining its actual pushing-up
witness then gives C_P(r) = R for every such Sylow P.

The full original cubic residual is already normal in C_G(x). Its
commutator centralization therefore survives the new involution, without
replacing the J₄ cover or the placed cubic. The actual displacement map
has kernel R restricted to its domain Q and index equal to the size of
its full commutator image. Thus either Q lies in R or the cubic-fixed
subgroup of V has order at most two.

Two further source implications are proved at these literal witnesses.
The factorization LT = L O₂(LT) forces R < P, and the normalizer condition
then forces nonzero displacement if Q is the full N_P(R). The literal Hall
application constructs the kernel and retains these implications. The
factorization and full-domain identification, the small fixed-space
exclusion, and the M₂₄ fixed-line and odd-actor comparisons remain to be
established before Hall faithfulness is assembled.

Source: Aschbacher--Smith 4.1.4(4), 4.2.13, printed pp.607,612, and
4.4.14, printed pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
/-- A proper core has a noncentralizing relative normalizer when its centralizer
is exactly the core. This is the normalizer-condition step in the source. -/
private theorem relative_core_normalizer_moves {G : Type*} [Group G] [Finite G]
    (P R : Subgroup G) (r : G) (hP : IsPGroup 2 P) (hRP : R < P)
    (hc : P ⊓ centralizer ({r} : Set G) = R) :
    ∃ s ∈ P ⊓ normalizer (R : Set G), ⁅r,s⁆ ≠ 1 := by
  let : Group.IsNilpotent P := hP.isNilpotent
  have hproper : R.subgroupOf P < ⊤ := lt_top_iff_ne_top.mpr
    (fun he => hRP.not_ge (subgroupOf_eq_top.mp he))
  obtain ⟨s,hs,hsR⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (R.subgroupOf P) hproper)
  have hsN : (s : G) ∈ normalizer (R : Set G) := by
    rwa [←subgroupOf_normalizer_eq hRP.le] at hs
  refine ⟨s,⟨s.property,hsN⟩,?_⟩
  intro he
  apply hsR
  exact hc.le ⟨s.property,mem_centralizer_singleton_iff.mpr
    (commutatorElement_eq_one_iff_mul_comm.mp he).symm⟩

/-- Once the literal full relative normalizer is the displacement domain,
strict growth forces the full image and the small cubic-fixed alternative. -/
theorem cubic_core_displacement_full_domain {G : Type*} [Group G] [Finite G]
    {V P R : Subgroup G} {r x : G}
    (hP : IsPGroup 2 P) (hRP : R < P)
    (hc : P ⊓ centralizer ({r} : Set G) = R)
    (hQ : pushingDisplacementDomain P R V r = P ⊓ normalizer (R : Set G))
    (halt : ⁅zpowers r,pushingDisplacementDomain P R V r⁆ = ⊥ ∨
      ⁅zpowers r,pushingDisplacementDomain P R V r⁆ = V)
    (hfixed : pushingDisplacementDomain P R V r ≤ R ∨
      Nat.card (V ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 2) :
    ⁅zpowers r,pushingDisplacementDomain P R V r⁆ = V ∧
      Nat.card (V ⊓ centralizer ({x} : Set G) : Subgroup G) ≤ 2 := by
  obtain ⟨s,hs,hmove⟩ := relative_core_normalizer_moves P R r hP hRP hc
  have hsQ : s ∈ pushingDisplacementDomain P R V r := hQ.symm ▸ hs
  have hne : ⁅zpowers r,pushingDisplacementDomain P R V r⁆ ≠ ⊥ := by
    intro he
    exact hmove (he.le (commutator_mem_commutator (mem_zpowers r) hsQ))
  refine ⟨halt.resolve_left hne,hfixed.resolve_left ?_⟩
  intro hQR
  have hsC := (hc.ge (hQR hsQ)).2
  exact hmove (commutatorElement_eq_one_iff_mul_comm.mpr
    (mem_centralizer_singleton_iff.mp hsC).symm)
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- Every containing source Sylow meets the actual outside overgroup in the original core. -/
theorem sourceOrbit_pushingUp_sectionSylow_intersection
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
    (hRP : J.pCoreIn 2 ≤ (P : Subgroup _).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) :
    (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ⊓ H =
      J.pCoreIn 2 := by
  have hM := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hjoin : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  have hyp := source_hypothesis411 h hjoin
  let M := normalizer (L : Set G)
  let C := sectionCentralizerIn M L
  let Mminus := coveringOvergroup M L (oddActorResidual L A)
  have hs : Mminus ∈ sigma M L := by
    refine ⟨sup_le (((oddActorResidual_le L A).trans inf_le_left).trans L.le_normalizer)
      inf_le_left,sup_le ?_ le_sup_right⟩
    intro l hl
    obtain ⟨j,hj,q,hq,rfl⟩ := hw.1.1.1.2.2.1 hl
    exact Mminus.mul_mem (hw.1.1.1.1 hj)
      ((show C ≤ Mminus from le_sup_right) (componentCore_le_sectionCentralizer L.le_normalizer hq))
  have hout : ¬ H ≤ M := fun hh => hw.2.2.2.2.1.not_ge (le_inf le_rfl hh)
  obtain ⟨S,hS⟩ := core_sylow_sectionCentralizer_outside hyp hs hw.1
    (Chapter1.mem_H_of_isTwoLocal hw.2.2.1.1) hw.2.2.2.1 hout
  let C₀ := sectionCentralizerIn (H ⊓ M) L
  let Pg := (P : Subgroup C).map C.subtype
  let Q := Pg ⊓ H
  have hQC : Q ≤ C₀ := fun q hq => ⟨⟨hq.2,(map_subtype_le _ hq.1).1⟩,
    (map_subtype_le _ hq.1).2⟩
  have hRQ : J.pCoreIn 2 ≤ Q := le_inf hRP ((pCoreIn_le 2 J).trans hw.2.2.2.1)
  have hSQ : (S : Subgroup C₀) ≤ Q.subgroupOf C₀ := by
    intro s hs
    exact hRQ (hS ▸ mem_map_of_mem C₀.subtype hs)
  have he := S.is_maximal' ((P.isPGroup'.map C.subtype).to_le
    (show Q ≤ Pg from inf_le_left)).comap_subtype hSQ
  have hm := congrArg (map C₀.subtype) he
  change (Q.subgroupOf C₀).map C₀.subtype = (S : Subgroup C₀).map C₀.subtype at hm
  rw [map_subgroupOf_eq_of_le hQC,hS] at hm
  exact hm

/-- The retained source witness makes the involution centralizer in every containing section Sylow exactly R. -/
theorem sourceOrbit_pushingUp_sectionSylow_centralizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (r : G) (hRr : J.pCoreIn 2 ≤ centralizer ({r} : Set G))
    (hCH : centralizer ({r} : Set G) ≤ H)
    (P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
    (hRP : J.pCoreIn 2 ≤ (P : Subgroup _).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) :
    (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ⊓
      centralizer ({r} : Set G) = J.pCoreIn 2 := by
  apply le_antisymm
  · exact (inf_le_inf_left _ hCH).trans (D.sourceOrbit_pushingUp_sectionSylow_intersection h hw P hRP).le
  · exact le_inf hRP hRr

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4
/-- Full residual normality survives a new involution centralizing the same full cover. -/
theorem cubic_full_resolution_reselect {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup H) (x : K) (r s : G)
    (hfull : CubicPumpupFullResolution H K x r)
    (hKs : K.map H.subtype ≤ centralizer ({s} : Set G)) :
    CubicPumpupFullResolution H K x s := by
  let S := cubicResidualImage H K x
  let Cx := centralizer ({((x : H) : G)} : Set G)
  have hSCx : S ≤ Cx := hfull.2.1.1
  have hSs : S ≤ centralizer ({s} : Set G) := by
    apply le_trans _ hKs
    rintro z ⟨k,hk,rfl⟩
    exact mem_map_of_mem H.subtype k.property
  have hz : zpowers s ≤ centralizer (S : Set G) := by
    apply zpowers_le.mpr
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hSs hy)
  have hn : Cx ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hSCx).mp hfull.2.2.1
  exact ⟨hfull.1,hfull.2.1,hfull.2.2.1,(commutator_mono hz le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp
      (hn.trans (normalizer_le_normalizer_centralizer S)))⟩

/-- The actual displacement kernel is the original core, restricted to its domain.
The selected source Sylow and its conjugator are retained. -/
@[expose] def CubicCoreDisplacementConclusion {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L V J H : Subgroup G) (K : Subgroup H) (x : K) (r : G) : Prop :=
  ∃ P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L),
    let Pg := (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype
    J.pCoreIn 2 ≤ Pg ∧ Pg ⊓ centralizer ({r} : Set G) = J.pCoreIn 2 ∧
    ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom = Pg ∧
      let Q := pushingDisplacementDomain Pg (J.pCoreIn 2) V r
      let U := ⁅zpowers r,Q⁆
      r ∈ Q ∧ U ≤ V ∧ (U = ⊥ ∨ U = V) ∧
        U ⊓ centralizer ({((x : H) : G)} : Set G) ≤ centralizer (cubicResidualImage H K x : Set G) ∧
        (Q ≤ J.pCoreIn 2 ∨
          Nat.card (V ⊓ centralizer ({((x : H) : G)} : Set G) : Subgroup G) ≤ 2) ∧
        ∃ χ : Q →* V, (∀ s : Q, (χ s : G) = ⁅r,(s : G)⁆) ∧
          χ.ker = (J.pCoreIn 2).subgroupOf Q ∧
          χ.range.map V.subtype = U ∧
          ((J.pCoreIn 2).subgroupOf Q).index = Nat.card U ∧
          (J.pCoreIn 2 < Pg → Q = Pg ⊓ normalizer (J.pCoreIn 2 : Set G) →
            U = V ∧ Nat.card (V ⊓ centralizer ({((x : H) : G)} : Set G) : Subgroup G) ≤ 2)

/-- Replace the centralizer kernel by the original source core using its proved intersection. -/
theorem cubic_displacement_core_kernel {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V J H : Subgroup G} {K : Subgroup H} {x : K} {r : G}
    (hd : CubicDisplacementConclusion T L V J H K x r)
    (hc : ∀ P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L),
      J.pCoreIn 2 ≤ (P : Subgroup _).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype →
      (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ⊓
        centralizer ({r} : Set G) = J.pCoreIn 2) :
    CubicCoreDisplacementConclusion T L V J H K x r := by
  obtain ⟨P,hRP,c,hmark,hr,hUV,halt,hfixed,hcases,χ,hχ,hker,hrange⟩ := hd
  let Pg := (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype
  let Q := pushingDisplacementDomain Pg (J.pCoreIn 2) V r
  have hQP : Q ≤ Pg := (commutatorPreimage_le _ _ _).trans (inf_le_left.trans inf_le_left)
  have he := hc P hRP
  have hk : (centralizer ({r} : Set G)).subgroupOf Q = (J.pCoreIn 2).subgroupOf Q := by
    ext q
    change (q : G) ∈ centralizer ({r} : Set G) ↔ (q : G) ∈ J.pCoreIn 2
    constructor
    · intro hq
      exact he.le ⟨hQP q.property,hq⟩
    · intro hq
      exact (he.ge hq).2
  have hkχ := hker.trans hk
  have hcases' := hcases.imp (fun hh => (le_inf hQP hh).trans he.le) id
  refine ⟨P,hRP,he,c,hmark,hr,hUV,halt,hfixed,hcases',χ,hχ,hkχ,hrange,?_,?_⟩
  · rw [←hkχ,index_ker]
    exact (card_map_of_injective V.subtype_injective).symm.trans
      (congrArg (fun U : Subgroup G => Nat.card U) hrange)
  · intro hlt hdomain
    exact cubic_core_displacement_full_domain (P.isPGroup'.map _) hlt he hdomain halt hcases'

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The source inner-action factorization forces strict enlargement in every
containing section Sylow, with the original Sylow conjugator retained. -/
theorem sourceOrbit_pushingUp_core_lt_of_localJoin
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (hjoin : (T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
    (hRP : J.pCoreIn 2 ≤ (P : Subgroup _).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) :
    J.pCoreIn 2 < (P : Subgroup _).map
      (sectionCentralizerIn (normalizer (L : Set G)) L).subtype := by
  let M := normalizer (L : Set G)
  let C := sectionCentralizerIn M L
  let Pg := (P : Subgroup C).map C.subtype
  have hM := h.sylow_normalized_maximal_unique D.sylow_normalizes_component
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have huniq : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) M :=
    ⟨hM.1,sup_le L.le_normalizer D.sylow_normalizes_component,hM.2⟩
  obtain ⟨c,hmark,_⟩ := Chapter4.Section02.Unitary.exists_fullModule_comparison h D huniq P
  apply lt_of_le_of_ne hRP
  intro he
  have hPH : Pg ≤ H := (show Pg = J.pCoreIn 2 from he.symm).le.trans
    ((pCoreIn_le 2 J).trans hw.2.2.2.1)
  have hLP : L.pCoreIn 2 ≤ Pg :=
    (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L)
      (componentCore_le_sectionCentralizer L.le_normalizer)
      (inf_le_left.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))).trans
      (pCoreIn_le_sylow C P)
  have hLH : L ≤ H := by
    intro l hl
    obtain ⟨f,hf,q,hq,rfl⟩ := hw.2.2.2.2.2.2.2.1 ▸ (show l ∈ (L : Set G) from hl)
    exact H.mul_mem (((map_subtype_le _).trans inf_le_right) hf) (hPH (hLP hq))
  let a := MulAut.conj (c : G)
  have hLa : L.map a.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp c.property.1
  have hMa : M.map a.toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer c.property.1)
  have hTa : (T : Subgroup G).map a.toMonoidHom ≤ L ⊔ Pg := by
    have hh := map_mono (f := a.toMonoidHom) hjoin
    rwa [Subgroup.map_sup,hLa,hmark] at hh
  have hIa : (L ⊔ (T : Subgroup G)).map a.toMonoidHom ≤ H := by
    rw [Subgroup.map_sup,hLa]
    exact sup_le hLH (hTa.trans (sup_le hLH hPH))
  have hIH : L ⊔ (T : Subgroup G) ≤ H.map a.symm.toMonoidHom := by
    simpa [map_map] using
      map_mono (f := a.symm.toMonoidHom) hIa
  have hHeq := huniq.2.2 _ (Theory.Quasithin.isMaximalTwoLocal_map a.symm hw.2.2.1) hIH
  have hHM : H = M := by
    have hh := congrArg (map a.toMonoidHom) hHeq
    have hh' : H = M.map a.toMonoidHom := by simpa [map_map] using hh
    exact hh'.trans hMa
  exact hw.2.2.2.2.1.ne (by rw [hHM,inf_idem])
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Sporadic.Mathieu Janko4.InvolutionCentralizers
/-- The original full source configuration with the commutator map, exact
kernel identified with the original core and its cubic-fixed image controlled. -/
@[expose] def MathieuPushingUpCoreDisplacementCase {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (L V A : Subgroup G) : Prop :=
  ∃ J H W : Subgroup G, Witness L V A J H W ∧
    ((T : Subgroup G) ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
      ∀ P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L),
        J.pCoreIn 2 ≤ (P : Subgroup _).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype →
        J.pCoreIn 2 < (P : Subgroup _).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) ∧
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ (normalizer (L : Set G)).subgroupOf H ∧
    let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
      ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
      F.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K ∧
      H = K.map H.subtype ⊔ (H ⊓ centralizer (K.map H.subtype : Set G)) ∧
      ∃ (r : H.pCoreIn 2) (H₁ : Subgroup G), orderOf r = 2 ∧
        centralizer ({(r : G)} : Set G) ≤ H₁ ∧
        IsComponentIn (K.map H.subtype) H₁ ∧
        ((K.map H.subtype).subgroupOf H₁).Normal ∧
        IsComponentIn (K.map H.subtype) (centralizer ({(r : G)} : Set G)) ∧
      ∃ e : (K ⧸ center K) ≃* Janko4.Model,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
        let R := First.centralizer.comap q
        ∃ x : R, orderOf x = 3 ∧ orderOf (q (x : K)) = 3 ∧
          (⟨x,mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer ({x} : Set R)) ∈
            solvableResidual (Subgroup.centralizer ({x} : Set R)) ∧
          solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)) =
            (solvableResidual (Subgroup.centralizer ({x} : Set R))).map
              (R.subtype.elementCentralizerMap x) ∧
          IsQuasisimple (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ∧
          Nonempty (((solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))) ⧸
            center (solvableResidual (Subgroup.centralizer ({(x : K)} : Set K)))) ≃* M22) ∧
          (∃ g : K, ((g * (x : K) * g⁻¹ : K) : H) ∈ F.subgroupOf H ∧
            let y := g * (x : K) * g⁻¹
            IsQuasisimple (solvableResidual (centralizer ({y} : Set K))) ∧
              Nonempty ((solvableResidual (centralizer ({y} : Set K)) ⧸
                center (solvableResidual (centralizer ({y} : Set K)))) ≃* M22) ∧
              CubicAmbientData H K y ∧
              (let C := centralizer ({((y : H) : G)} : Set G) ⊓ centralizer ({(r : G)} : Set G)
               IsComponentIn (cubicResidualImage H K y) C ∧
                 ((cubicResidualImage H K y).subgroupOf C).Normal) ∧
              CubicPumpupData H K y (r : G) ∧
              CubicPumpupQuotientAction H K y (r : G) ∧
              CubicPumpupFullResolution H K y (r : G) ∧
              CubicCoreDisplacementConclusion T L V J H K y (r : G) ∧
              ∀ Q : Subgroup (centralizer ({y} : Set K)), Q.IsCComponent →
                Q = solvableResidual (centralizer ({y} : Set K))) ∧
          ∀ Q : Subgroup (Subgroup.centralizer ({(x : K)} : Set K)), Q.IsCComponent →
            Q = solvableResidual (Subgroup.centralizer ({(x : K)} : Set K))


end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Reselect the involution with its actual source witness and identify the
kernel without replacing the original full component or placed cubic. -/
theorem pushingUp_core_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {A : Subgroup G} (hc : MathieuPushingUpNormalCubicCase L V A) :
    MathieuPushingUpCoreDisplacementCase T L V A := by
  obtain ⟨J,H,W,hw,hesc,K,hK,hn,hout,hFK,hWK,hprod,r,H₁,hr,hCH,hrel,hn₁,hKr,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hs,hp,hact,hfull,huy⟩,hux⟩ := hc
  obtain ⟨J₀,s,H₂,W₂,hw₀,hw₂,hJ₀J,hsame,hcore,hs,hJs,hCH₂,hrel₂,hn₂,hKs⟩ :=
    D.sourceOrbit_pushingUp_component_in_involution_centralizer
      h hmany hV hm hnon hw K hK hFK hout e
  let y := g * (x : K) * g⁻¹
  have hy : orderOf y = 3 :=
    ((MulAut.conj g).orderOf_eq (x : K)).trans ((orderOf_coe x).trans hx)
  let := hn
  let := hqy
  have hsim := cubicResidualImage_component_in_simultaneous H K y (s : G) H₂
    hrel₂.1 hn₂ hKs.1 hCH₂
  have hsG : orderOf (s : G) = 2 := (orderOf_coe s).trans hs
  have hp₂ := cubic_residual_ambient_component H K y (s : G) hsG hdata hsim.1 hey.some
  have hact₂ := cubic_pumpup_quotient_action H K y (s : G) hsG hp₂ hsim.1 hey.some
  have hfull₂ := cubic_full_resolution_reselect H K y (r : G) (s : G) hfull hKs.1
  have hdisp := D.sourceOrbit_cubic_displacement_selection h.toHypothesis1221
    (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1 hw K hFK e (s : G)
    (hw.2.2.2.2.2.2.1.ambient_core_le_radical s.property) hKs.1 y hy hg hfull₂
  have hcontrol (P : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
      (hRP : J.pCoreIn 2 ≤ (P : Subgroup _).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype) :
      (P : Subgroup _).map (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ⊓
        centralizer ({(s : G)} : Set G) = J.pCoreIn 2 := by
    have hh := D.sourceOrbit_pushingUp_sectionSylow_centralizer h.toHypothesis1221 hw₂
      (s : G) ((pCoreIn_le 2 J₀).trans hJs) hCH₂ P (hcore ▸ hRP)
    exact hh.trans hcore
  have hcoreDisp := cubic_displacement_core_kernel hdisp hcontrol
  exact ⟨J,H,W,hw,(fun hj P hRP => D.sourceOrbit_pushingUp_core_lt_of_localJoin
    h.toHypothesis1221 hw hj P hRP),hesc,K,hK,hn,hout,hFK,hWK,hprod,s,H₂,hs,hCH₂,hrel₂,hn₂,hKs,
    e,x,hx,hqx,hmem,he,hquasi,heq,⟨g,hg,hqy,hey,hdata,hsim,hp₂,hact₂,hfull₂,hcoreDisp,huy⟩,hux⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall obstruction identifies the displacement kernel with the original core.
The full cover, original quotient maps and all Hall hypotheses are retained. -/
theorem sourceOrbit_mathieu_hall_core_displacement_obstruction
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (MathieuPushingUpCoreDisplacementCase T L V A ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_normal_cubic_obstruction G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hp => hp.imp fun A => ?_
  iterate 11 apply And.imp_right
  exact Or.imp (D.pushingUp_core_displacement h hmany hV hm hnon) id

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
