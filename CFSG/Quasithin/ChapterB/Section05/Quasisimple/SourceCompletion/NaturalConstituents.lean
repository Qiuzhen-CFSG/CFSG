module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.Constituents
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.HalfRatio
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.SourceCatalogue
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.QuotientAction
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FourSpaceOffenders.ActorTransport

/-!
# Genuine natural constituents in the reducible B.5.1 branch

A faithful irreducible component submodule is an actual Irr⁺ member. B.1.5(3)
therefore makes it invariant under a minimal best offender. Its restriction to
the component/offender overgroup is faithful, irreducible on F*, and an
FF-module, so the full earlier B.4.2 theorem applies to that literal action.

At half ratio, one common minimal best offender retains the codimension bound
on every constituent, leaving precisely the natural SL3 and binary SL4/SL5
rows. The final application constructs the original LA-chief flag, selects its
smallest-ratio noncentral factor and supplies this natural decomposition on
its faithful component image. The actual central kernel remains present.

This establishes the selected factor's natural constituents from genuine
A.2.1, A.3.6 and B.4.2 inputs, independently of a B.5.1 classifier. Comparing
all factors and reconstructing the original socle are subsequent source steps.

Source: Aschbacher--Smith B.5.1, printed p.100, (+) through (**).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped BigOperators ENNReal IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A faithful irreducible component submodule is an actual Irr+ member. -/
theorem constituent_isIrrPlus (C : Subgroup G) [Nontrivial C]
    (W : Subrepresentation (ρ.comp C.subtype)) (hi : IsIrreducible W.toRepresentation)
    (hf : Function.Injective W.toRepresentation) : IsIrrPlus ρ C W.toSubmodule := by
  have hs : C ≤ subspaceStabilizer ρ W.toSubmodule := by
    apply le_subspaceStabilizer
    intro c hc v hv
    exact W.apply_mem_toSubmodule ⟨c, hc⟩ hv
  have hn : ¬ W.toSubmodule ≤ fixedSpace ρ C := by
    intro hz
    obtain ⟨c, hc⟩ := exists_ne (1 : C)
    apply hc
    apply hf
    ext v
    change ρ c v = ρ 1 v
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_one, Module.End.one_apply] using hz v.property c
  have ha : IsAtom W := (Subrepresentation.irreducible_iff_isAtom W).mp hi
  have hmin (J : Submodule (ZMod 2) V) (hJ : C ≤ subspaceStabilizer ρ J)
      (hJW : J ≤ W.toSubmodule) : J = W.toSubmodule ∨ J ≤ fixedSpace ρ C := by
    let Jrep := invariantSubspace ρ C J hJ
    rcases ha.le_iff.mp (show Jrep ≤ W from hJW) with hz | he
    · exact Or.inr ((congrArg Subrepresentation.toSubmodule hz).le.trans bot_le)
    · exact Or.inl (congrArg Subrepresentation.toSubmodule he)
  have hcomm : subspaceCommutator ρ W.toSubmodule C = W.toSubmodule := by
    let D := invariantSubspace ρ C (subspaceCommutator ρ W.toSubmodule C)
      (subspaceCommutator_invariant ρ W.toSubmodule C)
    rcases ha.le_iff.mp (show D ≤ W from subspaceCommutator_le_of_invariant ρ hs) with hz | he
    · exact (hn ((subspaceCommutator_eq_bot_iff ρ W.toSubmodule C).mp
        (congrArg Subrepresentation.toSubmodule hz))).elim
    · exact congrArg Subrepresentation.toSubmodule he
  exact isIrrPlus_of_minimal ρ hs hcomm hn hmin

/-- A minimal best offender stabilizes each faithful irreducible component
constituent, using B.1.5(3) with the actual quasisimple chief-factor hypotheses. -/
theorem constituent_stable [Finite G] [FiniteDimensional (ZMod 2) V]
    (C : Subgroup G) [IsQuasisimple C] (hfit : generalizedFitting G = C)
    (hcore : pCore 2 G = ⊥) (hfaith : Function.Injective ρ)
    {B : Subgroup G} (hB : IsMinimalBestOffender ρ B)
    (W : Subrepresentation (ρ.comp C.subtype)) (hi : IsIrreducible W.toRepresentation)
    (hf : Function.Injective W.toRepresentation) : B ≤ subspaceStabilizer ρ W.toSubmodule := by
  let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
  let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
  have hcomm : ⁅C, B⁆ = C := by
    have hq : IsQuasisimple (generalizedFitting G) := hfit.symm ▸ inferInstance
    simpa only [hfit] using QuasisimpleSections.commutator_fitting_eq hcore hq hB.1.1.1
      (hB.1.1.2.isPGroup 2 B)
  have hr : pResidual 2 C = ⊤ := by
    apply (pResidual_eq_top_iff 2 C).mpr
    intro N hN hp
    let := hN
    have hsub : Subsingleton (C ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (C ⧸ N) hp.isNilpotent
    apply top_unique
    intro c _
    exact (QuotientGroup.eq_one_iff c).mp (Subsingleton.elim _ _)
  have hchief : HasCentralPChiefFactors 2 C :=
    hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
      (⊥ : Subgroup C) (by simp)
      (IsQuasisimple.of_mulEquiv QuotientGroup.quotientBot.symm)
  exact source_lemma_B_1_5_3 ρ hfaith hB hr hcomm hchief
    (constituent_isIrrPlus ρ C W hi hf)

/-- The full earlier B.4.2 classification on a faithful irreducible
constituent, with the actual action of its component/offender overgroup. -/
theorem constituent_classification [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) {B : Subgroup G} (hB : IsMinimalBestOffender ρ B)
    (W : Subrepresentation (ρ.comp C.subtype)) (hi : IsIrreducible W.toRepresentation)
    (hf : Function.Injective W.toRepresentation) :
    ∃ hstable : C ⊔ B ≤ subspaceStabilizer ρ W.toSubmodule,
      let δ := (invariantSubspace ρ (C ⊔ B) W.toSubmodule hstable).toRepresentation
      SourceInduction.ProjectiveLine.IrreducibleActionCase δ
        (generalizedFitting ↥(C ⊔ B)) (offenderSubgroup δ) := by
  let : C.Normal := hfit ▸ generalizedFitting_normal (G := G)
  have hs : C ≤ subspaceStabilizer ρ W.toSubmodule := by
    apply le_subspaceStabilizer
    intro c hc v hv
    exact W.apply_mem_toSubmodule ⟨c, hc⟩ hv
  have hstable : C ⊔ B ≤ subspaceStabilizer ρ W.toSubmodule :=
    sup_le hs (constituent_stable ρ C hfit hcore hfaith hB W hi hf)
  refine ⟨hstable, ?_⟩
  let : FiniteDimensional (ZMod 2) W.toSubmodule := inferInstance
  let H := C ⊔ B
  let J := invariantSubspace ρ H W.toSubmodule hstable
  let δ := J.toRepresentation
  have hp : IsPGroup 2 B := hB.1.1.2.isPGroup 2 B
  have hcenter : center G ≤ C := by
    rw [← hfit]
    exact le_trans (show center G ≤ fittingSubgroup G from
      le_sSup ⟨inferInstance, inferInstance⟩) le_sup_left
  have hfit' : generalizedFitting G = C ⊔ center G := by rw [hfit, sup_of_le_left hcenter]
  have hfitH : generalizedFitting H = C.subgroupOf H :=
    IrreducibleBranch.local_generalizedFitting C B hfit' hcore hp
  have hfC : Function.Injective (δ.comp (C.subgroupOf H).subtype) :=
    hf.comp (subgroupOfEquivOfLe (show C ≤ H from le_sup_left)).injective
  have hfδ : Function.Injective δ := by
    apply IrreducibleBranch.faithful_of_fitting_restriction
    rwa [hfitH]
  have hiC : IsIrreducible (δ.comp (C.subgroupOf H).subtype) :=
    (irreducible_comp_surjective_iff
      (subgroupOfEquivOfLe (show C ≤ H from le_sup_left)).toMonoidHom
      (subgroupOfEquivOfLe (show C ≤ H from le_sup_left)).surjective W.toRepresentation).mpr hi
  have hiδ : IsIrreducible (δ.comp (generalizedFitting H).subtype) := by
    rwa [hfitH]
  let : IsQuasisimple (C.subgroupOf H) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show C ≤ H from le_sup_left)).symm
  have hq : IsQuasisimple (generalizedFitting H) := hfitH.symm ▸ inferInstance
  have hBo := ((hB.1.subgroupOf ρ (show B ≤ H from le_sup_right)).isOffender (ρ.comp H.subtype))
  have hoff : IsOffender δ (B.subgroupOf H) :=
    ⟨hBo.1, (fixedCodim_subrepresentation_le (ρ.comp H.subtype) J (B.subgroupOf H)).trans hBo.2⟩
  obtain ⟨A, _, hA⟩ := hoff.exists_bestOffender δ
  exact earlier H J.toSubmodule δ (IrreducibleBranch.local_sqtk hK C B hC hp)
    hq hfδ hiδ ⟨A, hA⟩

/-- The natural rows that survive the source half-ratio bound. -/
def SmallNaturalConstituent (C : Subgroup G) : Prop :=
  (∃ F : BinaryField, IsLinearNatural (ρ.comp C.subtype) F 3) ∨
    ∃ d, (d = 4 ∨ d = 5) ∧ IsLinearNatural (ρ.comp C.subtype) BinaryField.two d

/-- Every faithful irreducible constituent of a half-ratio minimal offender
is one of the actual SL3 or binary SL4/SL5 natural source actions. -/
theorem constituent_natural_of_half [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) {B : Subgroup G} (hB : IsMinimalBestOffender ρ B)
    (hhalf : 2 * fixedCodim ρ B ≤ rank B)
    (W : Subrepresentation (ρ.comp C.subtype)) (hi : IsIrreducible W.toRepresentation)
    (hf : Function.Injective W.toRepresentation) :
    ∃ hstable : C ⊔ B ≤ subspaceStabilizer ρ W.toSubmodule,
      SmallNaturalConstituent
        (invariantSubspace ρ (C ⊔ B) W.toSubmodule hstable).toRepresentation
        (generalizedFitting ↥(C ⊔ B)) := by
  obtain ⟨hs, hc⟩ := constituent_classification ρ hK earlier C hC hfit hcore hfaith hB W hi hf
  refine ⟨hs, hc.natural_of_ratio_le_half _ ?_⟩
  let H := C ⊔ B
  let J := invariantSubspace ρ H W.toSubmodule hs
  have hb := (hB.1.subgroupOf ρ (show B ≤ H from le_sup_right)).1
  have hq : IsQuadratic (ρ.comp H.subtype) (B.subgroupOf H) := by
    intro a ha b hb v
    exact hB.isQuadratic ρ a.val ha b.val hb v
  apply quadraticRatio_subrepresentation_le_half (ρ.comp H.subtype) J hb hq
  rwa [fixedCodim_subgroupOf ρ (show B ≤ H from le_sup_right),
    rank_subgroupOf (show B ≤ H from le_sup_right)]

/-- Genuine selection followed by the natural sieve: no constituent shape
or local B.5.1 classification is a premise. -/
theorem all_constituents_natural_of_half [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (C : Subgroup G) [IsQuasisimple C] (hC : IsSQTK K C)
    (hfit : generalizedFitting G = C) (hcore : pCore 2 G = ⊥)
    (hfaith : Function.Injective ρ) (hq : quadraticRatio ρ ≤ 1 / 2) :
    ∃ B, IsMinimalBestOffender ρ B ∧
      ∀ (W : Subrepresentation (ρ.comp C.subtype)), IsIrreducible W.toRepresentation →
        Function.Injective W.toRepresentation →
        ∃ hstable : C ⊔ B ≤ subspaceStabilizer ρ W.toSubmodule,
          SmallNaturalConstituent
            (invariantSubspace ρ (C ⊔ B) W.toSubmodule hstable).toRepresentation
            (generalizedFitting ↥(C ⊔ B)) := by
  obtain ⟨B, hB, hb⟩ := exists_minimal_half_ratio ρ hq
  exact ⟨B, hB, fun W hi hf =>
    constituent_natural_of_half ρ hK earlier C hC hfit hcore hfaith hB hb W hi hf⟩

/-- The actual constituent naturality attached to one common minimal offender. -/
def NaturalConstituentDecomposition (C : Subgroup G) : Prop :=
  ∃ B, IsMinimalBestOffender ρ B ∧
    ∃ (n : ℕ) (W : Fin n → Subrepresentation (ρ.comp C.subtype)),
      DirectSum.IsInternal (fun i => (W i).asSubmodule) ∧
        ∀ i, IsIrreducible (W i).toRepresentation ∧ Function.Injective (W i).toRepresentation ∧
          ∃ hstable : C ⊔ B ≤ subspaceStabilizer ρ (W i).toSubmodule,
            SmallNaturalConstituent
              (invariantSubspace ρ (C ⊔ B) (W i).toSubmodule hstable).toRepresentation
              (generalizedFitting ↥(C ⊔ B))

/-- Full faithful natural-constituent decomposition for a noncentral chief
image of half ratio. The earlier inputs are precisely A.2.1, A.3.6 and B.4.2. -/
theorem ChiefImage.natural_constituents [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L]
    (hL : IsSQTK K L) (hi : IsIrreducible ρ)
    (hn : subspaceCommutator ρ ⊤ L ≠ ⊥) (hq : IsPGroup 2 (G ⧸ L))
    (hhalf : quadraticRatio (imageRepresentation ρ) ≤ 1 / 2) :
    NaturalConstituentDecomposition (KernelQuotient.action ρ) (ChiefImage.component ρ L) := by
  let C := ChiefImage.component ρ L
  let : C.Normal := ChiefImage.component_normal ρ L
  let : IsQuasisimple C := ChiefImage.component_quasisimple ρ L hn
  have hsq := ChiefImage.component_sqtk ρ hsemisimple L hL hn
  have hr : quadraticRatio (KernelQuotient.action ρ) ≤ 1 / 2 := by
    change quadraticRatio ((imageRepresentation ρ).comp (KernelQuotient.equiv ρ).toMonoidHom) ≤ _
    rwa [NaturalExtensions.FourSpaceOffenders.reindex_ratio]
  obtain ⟨B, hB, hnat⟩ := all_constituents_natural_of_half (KernelQuotient.action ρ) hK earlier
    C hsq (ChiefImage.fitting_eq_component ρ L hi hn hq) (ChiefImage.twoCore_eq_bot ρ hi)
    (KernelQuotient.faithful ρ) hr
  obtain ⟨n, W, hd, hW⟩ := ChiefImage.faithful_constituents ρ hsemisimple h36 L hL hi hn
  exact ⟨B, hB, n, W, hd, fun i => ⟨(hW i).1, (hW i).2, hnat (W i) (hW i).1 (hW i).2⟩⟩

/-- Natural constituents on a literal chief quotient with its actual kernel. -/
def ChiefFactorNatural (L : Subgroup G) (U W : Subrepresentation ρ) : Prop :=
  let τ := sectionRepresentation ρ U W
  NaturalConstituentDecomposition (KernelQuotient.action τ) (ChiefImage.component τ L)

theorem half_flag_factor_natural [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hq : IsPGroup 2 (G ⧸ generalizedFitting G))
    (f : ReducibleChiefFlag ρ (generalizedFitting G)) {i : ℕ} (hi : i ∈ f.noncentral)
    (hhalf : quadraticRatio (imageRepresentation
      (sectionRepresentation ρ (f.chain i) (f.chain (i + 1)))) ≤ 1 / 2) :
    ChiefFactorNatural ρ (generalizedFitting G) (f.chain i) (f.chain (i + 1)) :=
  ChiefImage.natural_constituents _ hK hsemisimple h36 earlier (generalizedFitting G) hsq
    (f.irreducible ρ ((f.mem_noncentral i).mp hi).1) ((f.mem_noncentral i).mp hi).2 hq hhalf

/-- Source reduction through (**): the reducible original module has a
noncentral chief factor whose actual faithful component constituents are
natural SL3 or binary SL4/SL5 modules. No B.5.1 input is assumed. -/
theorem reducible_natural_factor [Finite G]
    {K : GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L)
    (hnot : ¬ IsIrrPlus ρ L (moved ρ L)) :
    ∃ A : Subgroup G, IsMinimalBestOffender ρ A ∧
      ∃ f : ReducibleChiefFlag (ρ.comp (L ⊔ A).subtype) (generalizedFitting ↥(L ⊔ A)),
        ∃ i ∈ f.noncentral,
          ChiefFactorNatural (ρ.comp (L ⊔ A).subtype) (generalizedFitting ↥(L ⊔ A))
            (f.chain i) (f.chain (i + 1)) := by
  let := h.finite_module
  let : IsQuasisimple L := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  obtain ⟨A, hA, f, hred⟩ := reducible_source_reduction ρ h hnot
  obtain ⟨k, hk, _, hkq, hqhalf⟩ := hred.2.2.2.2
  let H := L ⊔ A
  let σ := ρ.comp H.subtype
  have hp : IsPGroup 2 A := hA.1.1.2.isPGroup 2 A
  have hfit : generalizedFitting H = L.subgroupOf H :=
    IrreducibleBranch.local_generalizedFitting L A h.fitting h.twoCore hp
  let : IsQuasisimple (L.subgroupOf H) :=
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left)).symm
  let : IsQuasisimple (generalizedFitting H) := hfit.symm ▸ inferInstance
  have hsq : IsSQTK K (generalizedFitting H) := by
    rw [hfit]
    exact (IsSQTK.equiv (subgroupOfEquivOfLe (show L ≤ H from le_sup_left))).mpr h.sqtk
  have hq : IsPGroup 2 (H ⧸ generalizedFitting H) :=
    (IrreducibleBranch.local_quotient_isTwoGroup L A hp).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hfit.symm)
  exact ⟨A, hA, f, k, hk,
    half_flag_factor_natural σ hK hsemisimple h36 earlier hsq hq f hk (hkq.trans hqhalf)⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
