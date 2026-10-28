module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightSource
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.LinearCovered
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.DiagramHall.SymplecticCovered
public import Theory.GroupTheory.SolvableRadical.TwoClosedKernel

/-!
# The intrinsic rank-two residual in the diagram source row

E.2.2 marks the image modulo the maximal-subgroup core. The actual quotient
by the component two-core surjects onto that marked image. The linear covering
theorems recover PSL₃ or SL₃ over the same field, including order four, while
the symplectic multiplier theorem recovers Sp₄. The single-component product
then identifies the component with the literal residual O²(H).

The covered Borel has a normal Sylow two-subgroup. Its normality inside the
original maximal subgroup places the whole residual Sylow intersection in
S = O₂(N_G(L) ∩ H), proving S ∩ K = T ∩ K without a selected-factor callback.
The application module uses these results for normalization and the changed
Sylow branch. Selecting the diagram parabolic, excluding the zero-core models
and the remaining normalization cases stay with the local-to-global owner.

Source: Aschbacher–Smith E.2.2(2b), I.1.3, 5.1.10–11 and 5.2.2,
printed pp.215–216,407,634–635,646–649 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]

private theorem intrinsic_source_surjection
    {M C : Subgroup X} (hC : C.IsCComponent) (hO : pCore 2 X ≤ sourceKernel M) :
    ∃ v : (C ⧸ pCore 2 C) →* sourceImage M C, Function.Surjective v := by
  let eC := cComponentTwoCoreQuotientEquiv hC
  let q := QuotientGroup.map (pCore 2 X) (sourceKernel M) (MonoidHom.id X) hO
  let r : actorImage C →* sourceImage M C :=
    (q.comp (actorImage C).subtype).codRestrict _ (by
      rintro ⟨x,k,hk,rfl⟩
      exact ⟨k,hk,rfl⟩)
  have hr : Function.Surjective r := by
    rintro ⟨x,k,hk,rfl⟩
    exact ⟨⟨QuotientGroup.mk' (pCore 2 X) k,k,hk,rfl⟩,rfl⟩
  exact ⟨r.comp eC.toMonoidHom,hr.comp eC.surjective⟩

/-- The source projective marking lifts to the intrinsic quotient, retaining the
special-linear alternative, including the exceptional coefficient field of order four. -/
theorem linear_diagram_component_quotient
    {M C : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hO : pCore 2 X ≤ sourceKernel M) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage M C ≃* PSL(3,F)) :
    ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL (C ⧸ pCore 2 C) 3 (2 ^ f) := by
  let Q := C ⧸ pCore 2 C
  let := hqs
  obtain ⟨v,hv⟩ := intrinsic_source_surjection hC hO
  let w := e.toMonoidHom.comp v
  have hw : Function.Surjective w := e.surjective.comp hv
  have hzP : center PSL(3,F) = ⊥ := Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)
  let a : Q ⧸ center Q ≃* PSL(3,F) :=
    (IsQuasisimple.centralQuotientEquiv w hw).trans
      ((QuotientGroup.quotientMulEquivOfEq hzP).trans QuotientGroup.quotientBot)
  by_cases hz : center Q = ⊥
  · exact Or.inl ⟨F,inferInstance,inferInstance,hF,
      ⟨QuotientGroup.quotientBot.symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans a)⟩⟩
  · have ho : Odd (Nat.card (center Q)) := by
      have hfit : center Q ≤ fittingSubgroup Q := le_sSup ⟨inferInstance,inferInstance⟩
      apply Nat.coprime_two_left.mp
      exact pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le
        (hfit.trans (fitting_le_pPrimeCore_of_pCore_eq_bot 2
          (pCore_quotient_pCore_eq_bot 2))))
    by_cases h4 : Nat.card F = 4
    · obtain ⟨_,j,_⟩ := Matrix.PSL3.BinaryOddCenterCover.nontrivial_center_recognition_four h4 a ho hz
      exact Or.inr ⟨F,inferInstance,inferInstance,hF,⟨j.symm⟩⟩
    · have h2 : Nat.card F ≠ 2 := by
        have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
        omega
      obtain ⟨_,_,_,j,_⟩ := Matrix.PSL3.OrdinaryCenterRecognition.nontrivial_center_recognition h2 h4 a hz
      exact Or.inr ⟨F,inferInstance,inferInstance,hF,⟨j.symm⟩⟩

/-- The genuine symplectic covering theorem removes the source central kernel. -/
theorem symplectic_diagram_component_quotient
    {M C : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hO : pCore 2 X ≤ sourceKernel M) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage M C ≃* Sp4Derived F) :
    ClassicalGroup.IsPSp (C ⧸ pCore 2 C) 2 (2 ^ f) := by
  let Q := C ⧸ pCore 2 C
  let := hqs
  have hlarge : 3 < Nat.card F := by
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
    omega
  let a := Theory.SpecificGroups.SymplecticFour.derivedEquivFull_of_card_gt_two
    (F := F) (by omega : 2 < Nat.card F)
  obtain ⟨v,hv⟩ := intrinsic_source_surjection hC hO
  let w := (a.toMonoidHom.comp e.toMonoidHom).comp v
  have hw : Function.Surjective w := a.surjective.comp (e.surjective.comp hv)
  let : IsQuasisimple (Theory.SpecificGroups.SymplecticFour.Sp F) :=
    Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.isQuasisimple hlarge
  let : IsSimpleGroup ((Theory.SpecificGroups.SymplecticFour.Sp F) ⧸
      center (Theory.SpecificGroups.SymplecticFour.Sp F)) := IsQuasisimple.simple
  let : Nontrivial (Theory.SpecificGroups.SymplecticFour.Sp F) :=
    Function.Surjective.nontrivial (QuotientGroup.mk'_surjective
      (center (Theory.SpecificGroups.SymplecticFour.Sp F)))
  have hk : w.ker ≤ center Q := by
    rcases IsQuasisimple.normal_le_center_or_eq_top w.ker with hk | hk
    · exact hk
    · have ht : (⊤ : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) = ⊥ := by
        rw [←map_top_of_surjective w hw,←hk]
        exact (map_eq_bot_iff w.ker).mpr le_rfl
      exact (top_ne_bot ht).elim
  let c : PerfectCentralCovering.Cover Q (Theory.SpecificGroups.SymplecticFour.Sp F) := {
    toMonoidHom := w
    surjective := hw
    isPerfect := inferInstance
    ker_le_center := hk }
  exact ⟨F,inferInstance,inferInstance,hF,
    ⟨(Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.coverEquiv hlarge c).trans
      Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv⟩⟩

/-- Every genuine diagram source row determines the intrinsic rank-two quotient
at its own marked field degree; no equality with n(H) is assumed. -/
theorem diagram_component_quotient
    {M C U : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hO : pCore 2 X ≤ sourceKernel M) (hf : 1 < f)
    (hm : DiagramModel M C U f) :
    ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL (C ⧸ pCore 2 C) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp (C ⧸ pCore 2 C) 2 (2 ^ f) := by
  rcases hm with ⟨F,_,_,_,_,hF,e,_,_⟩ | ⟨F,_,_,_,_,hF,e,_,_⟩
  · rcases linear_diagram_component_quotient hC hqs hO hf hF e with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (symplectic_diagram_component_quotient hC hqs hO hf hF e))

/-- The original component overlap is two-closed in both diagram rows. -/
theorem diagram_overlap_twoClosed
    (S : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    {C : Subgroup X} {f : ℕ}
    (hc : SingleClauses (ChapterB.minimalParabolicMax S hP) C S) (hf : 1 < f)
    (hm : DiagramModel (ChapterB.minimalParabolicMax S hP) C S f) :
    DiagramHall.CoveredBorelControl S hP C := by
  rcases hm with ⟨F,_,_,_,_,hF,e,he,_⟩ | ⟨F,_,_,_,_,hF,e,he,_⟩
  · exact DiagramHall.linear_coveredBorel hf hF S hP C hc e he
  · exact DiagramHall.symplectic_coveredBorel S hP hc hf hF e he

/-- The full residual Sylow intersection lies in the original maximal-subgroup two-core. -/
theorem diagram_residual_sylow_le_core
    (S : Sylow 2 X) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    {C : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hc : SingleClauses (ChapterB.minimalParabolicMax S hP) C S) (hf : 1 < f)
    (hm : DiagramModel (ChapterB.minimalParabolicMax S hP) C S f) :
    (S : Subgroup X) ⊓ pResidual 2 X ≤ (ChapterB.minimalParabolicMax S hP).pCoreIn 2 := by
  let M := ChapterB.minimalParabolicMax S hP
  let B := C.subgroupOf M
  let : C.Normal := DiagramHall.single_component_normal S hC hc
  have hb := diagram_overlap_twoClosed S hP hc hf hm
  let P : Sylow 2 B := pCore_isPGroup.toSylow hb.odd_index.not_two_dvd_nat
  have hn : (P : Subgroup B).Normal := inferInstanceAs (pCore 2 B).Normal
  have hSM := (ChapterB.minimalParabolicMax_spec S hP).2
  have hp : IsPGroup 2 (((S : Subgroup X) ⊓ C).subgroupOf M) :=
    (S.isPGroup'.to_le (show (S : Subgroup X) ⊓ C ≤ S from inf_le_left)).comap_subtype
  have hh := le_pCore_of_normalSylow (N := B) ⟨P,hn⟩ hp
    (show ((S : Subgroup X) ⊓ C).subgroupOf M ≤ B from fun _ hx => hx.2)
  have hh' := map_mono (f := M.subtype) hh
  rw [map_subgroupOf_eq_of_le (inf_le_left.trans hSM)] at hh'
  rw [DiagramHall.single_component_eq_twoResidual S hC hc]
  exact hh'

variable {G : Type*} [Group G] [Finite G]

/-- Source selection identifies the literal residual quotient in the diagram row. -/
theorem diagram_source_residual_quotient
    {T : Sylow 2 G} {L H : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f) :
    ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
      ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f) := by
  have hO : pCore 2 H ≤ sourceKernel ((normalizer (L : Set G)).subgroupOf H) := by
    apply Subgroup.normal_le_normalCore.mpr
    exact (pCore_isPGroup.le_sylow_of_normal (T.subtype hTH)).trans (comap_mono hTL)
  have he : C = pResidual 2 H :=
    (DiagramHall.single_component_eq_twoResidual (T.subtype hTH) hC hc).symm
  subst C
  exact diagram_component_quotient hC hqs hO hf hm

/-- The diagram row supplies the literal equality S ∩ K = T ∩ K used in the prime pair. -/
theorem diagram_sourceS_intersection_residual
    {T : Sylow 2 G} {L H : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    (hm : DiagramModel ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) f) :
    Global.sourceS L H ⊓ residual H = (T : Subgroup G) ⊓ residual H := by
  let S := T.subtype hH.1.1.2
  let M := (normalizer (L : Set G)).subgroupOf H
  have hP := hstar_minimalParabolic_of_generation_gt_one hTL hH hpar
  have hmax : ChapterB.minimalParabolicMax S hP = M := by
    let J := ChapterB.minimalParabolicMax S hP
    have hJ := ChapterB.minimalParabolicMax_spec S hP
    have hTJ : (T : Subgroup G) ≤ J.map H.subtype := by
      have hh := map_mono (f := H.subtype) hJ.2
      change ((T : Subgroup G).subgroupOf H).map H.subtype ≤ J.map H.subtype at hh
      rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
    have hJH : J.map H.subtype < H := by
      have hh := (map_lt_map_iff_of_injective H.subtype_injective).mpr hJ.1.lt_top
      simpa only [← MonoidHom.range_eq_map,range_subtype] using hh
    have hJM : J ≤ M := map_le_iff_le_comap.mp
      (Chapter3.HStar.proper_overgroup_le T hH hTJ hJH)
    have hn : M ≠ ⊤ := fun he => hH.1.2 (subgroupOf_eq_top.mp he)
    exact ((hJ.1.le_iff.mp hJM).resolve_left hn).symm
  have hh := diagram_residual_sylow_le_core S hP hC (hmax ▸ hc) hf (hmax ▸ hm)
  rw [hmax] at hh
  have hST : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hSM : (M.pCoreIn 2).map H.subtype = Global.sourceS L H := by
    rw [map_pCoreIn_of_injective 2 M H.subtype H.subtype_injective,subgroupOf_map_subtype]
    rfl
  have hh' := map_mono (f := H.subtype) hh
  rw [Subgroup.map_inf _ _ _ H.subtype_injective,hST,hSM] at hh'
  apply le_antisymm
    (inf_le_inf_right _ (Global.sourceS_le_sylow hTL hH.1.1.2))
  exact le_inf hh' inf_le_right

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
