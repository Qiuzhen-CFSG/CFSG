module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.SpecificGroups.AlternatingFiveCore
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients

/-!
# The actual quotient inputs for the model comparison in 14.7.68

Restrict the original marking H → S₅ to K. Its image is A₅ and its kernel
is exactly O₂(K). Passing K through either local two-core retains this
A₅ quotient, and perfectness identifies its solvable radical with its
two-core. Thus the quotient local family, the radical quotient, strictness,
and the ambient SQTK condition required by A.3.14 are all verified.

Strictness follows because O₂(Gᵤ) and O₂(Lᵤ) lie in H whereas Lᵤ does not.
The C-component quotient is identified with its literal image in
Gᵤ/O₂(Gᵤ), with a formula on representatives. Separately, the full C.2.7
kernel bound controls the actual map Lᵤ/O₂(Lᵤ) → Lᵤ* and identifies the
quotients by their centers. The two quotients themselves are not identified.

These are the inputs of the comparison, not its classification conclusion.
The full A.3.14 implication belongs to qt-a03-embeddings / qt-a-03.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.14,
pp.49–50; C.2.7, pp.145–147; 14.7.68(2), pp.1071–1072.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- Restrict the given symmetric marking to the actual two-residual. -/
def KToAlternatingFive : K F →* alternatingGroup (Fin 5) :=
  ((MulEquiv.subgroupCongr d.K_image).toMonoidHom.comp
    (d.qH.subgroupMap ((K F).subgroupOf F.H))).comp
    (subgroupOfEquivOfLe (K_le_H F)).symm.toMonoidHom

/-- The restricted marking is the original qH on every element of K. -/
theorem KToAlternatingFive_apply (k : K F) :
    (d.KToAlternatingFive k : Equiv.Perm (Fin 5)) =
      d.qH ⟨(k : G), K_le_H F k.property⟩ := rfl

theorem KToAlternatingFive_surjective : Function.Surjective d.KToAlternatingFive :=
  (MulEquiv.subgroupCongr d.K_image).surjective.comp
    ((d.qH.subgroupMap_surjective _).comp
      (subgroupOfEquivOfLe (K_le_H F)).symm.surjective)

theorem KToAlternatingFive_ker_isTwoGroup : IsPGroup 2 d.KToAlternatingFive.ker := by
  have hH : IsPGroup 2 d.qH.ker := by
    rw [d.qH_ker]
    exact (isPGroup_pCoreIn 2 F.H).comap_subtype
  have hK : IsPGroup 2 (d.qH.subgroupMap ((K F).subgroupOf F.H)).ker := by
    rw [ker_subgroupMap]
    exact hH.comap_subtype
  have he : d.KToAlternatingFive.ker =
      (d.qH.subgroupMap ((K F).subgroupOf F.H)).ker.comap
        (subgroupOfEquivOfLe (K_le_H F)).symm.toMonoidHom := by
    ext x
    change (MulEquiv.subgroupCongr d.K_image)
      (d.qH.subgroupMap ((K F).subgroupOf F.H)
        ((subgroupOfEquivOfLe (K_le_H F)).symm x)) = 1 ↔ _
    rw [← (MulEquiv.subgroupCongr d.K_image).map_one,
      (MulEquiv.subgroupCongr d.K_image).injective.eq_iff]
    rfl
  rw [he]
  exact hK.comap_of_injective _ (subgroupOfEquivOfLe (K_le_H F)).symm.injective

/-- The kernel of this particular marking is exactly O₂(K). -/
theorem KToAlternatingFive_ker : d.KToAlternatingFive.ker = pCore 2 (K F) := by
  have he := d.KToAlternatingFive.comap_pCore_of_ker_isPGroup
    d.KToAlternatingFive_surjective d.KToAlternatingFive_ker_isTwoGroup
  simpa only [alternatingGroup.five_twoCore_eq_bot, MonoidHom.comap_bot] using he

/-- The A₅ marking is induced by qH and the actual two-core kernel. -/
def KCoreAlternatingFive : (K F ⧸ pCore 2 (K F)) ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq d.KToAlternatingFive_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.KToAlternatingFive
      d.KToAlternatingFive_surjective)

/-- Strictness in the local ambient group is inherited from K < Lᵤ. -/
theorem fixedComponent_strict_subgroupOf (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    (K F).subgroupOf (d.fixedCentralizer u) <
      Lu.subgroupOf (d.fixedCentralizer u) := by
  refine lt_of_le_of_ne (subgroupOf_mono _ h.larger.le) ?_
  intro he
  apply h.larger.ne
  have hm := congrArg (map (d.fixedCentralizer u).subtype) he
  simpa only [map_subgroupOf_eq_of_le h.le_centralizer,
    map_subgroupOf_eq_of_le (h.larger.le.trans h.le_centralizer)] using hm

/-- The literal K-image in the actual core quotient is proper. -/
theorem fixedComponent_core_K_image_lt_top (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    ((K F).subgroupOf Lu).map (QuotientGroup.mk' (pCore 2 Lu)) < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro he
  have hs : (K F).subgroupOf Lu ⊔ pCore 2 Lu = ⊤ := by
    have hc := congrArg (comap (QuotientGroup.mk' (pCore 2 Lu))) he
    simpa only [comap_map_eq, QuotientGroup.ker_mk', comap_top] using hc
  apply h.outside
  intro x hx
  have hmem : (⟨x, hx⟩ : Lu) ∈ (K F).subgroupOf Lu ⊔ pCore 2 Lu := by
    rw [hs]
    trivial
  have hh : (K F).subgroupOf Lu ⊔ pCore 2 Lu ≤ F.H.subgroupOf Lu := by
    refine sup_le (subgroupOf_mono _ (K_le_H F)) ?_
    intro k hk
    exact d.fixedComponent_core_le_H u h (mem_map_of_mem Lu.subtype hk)
  exact hh hmem

/-- The actual quotient marking agrees with the original qH on representatives. -/
theorem KCoreAlternatingFive_mk (k : K F) :
    d.KCoreAlternatingFive (QuotientGroup.mk' (pCore 2 (K F)) k) =
      d.KToAlternatingFive k := rfl

/-- Passing K through an ambient two-core does not change its A₅ core quotient. -/
def KImageCoreAlternatingFive (H : Subgroup G) (hKH : K F ≤ H) :
    ((((K F).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ⧸
      pCore 2 (((K F).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))) ≃*
        alternatingGroup (Fin 5) := by
  let A := (K F).subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 (q.subgroupMap A).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let e := subgroupOfEquivOfLe hKH
  exact ((q.subgroupMap A).pCoreQuotientEquiv (q.subgroupMap_surjective A) hk).symm.trans
    ((QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans d.KCoreAlternatingFive)

include d in
/-- A.3.14 uses the solvable radical; for the literal K-image it is the two-core. -/
theorem KImage_radical_eq_core (H : Subgroup G) (hKH : K F ≤ H) :
    solvableRadical (((K F).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) =
      pCore 2 (((K F).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) := by
  let := d.component.perfect
  let : Group.IsPerfect (K F) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (K_le_H F)).toMonoidHom)
    (subgroupOfEquivOfLe (K_le_H F)).surjective
  let : Group.IsPerfect ((K F).subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hKH).symm.surjective
  let : Group.IsPerfect (((K F).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) :=
    Group.IsPerfect.ofSurjective
      (f := (QuotientGroup.mk' (pCore 2 H)).subgroupMap ((K F).subgroupOf H))
      ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let := (d.KImageCoreAlternatingFive H hKH).isSimpleGroup
  exact PerfectCoreTwoExtension.radical_eq_core

/-- The A₅ quotient required by A.3.14, with its actual radical denominator. -/
def KImageRadicalAlternatingFive (H : Subgroup G) (hKH : K F ≤ H) :
    ((((K F).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) ⧸
      solvableRadical (((K F).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))) ≃*
        alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientMulEquivOfEq (d.KImage_radical_eq_core H hKH)).trans
    (d.KImageCoreAlternatingFive H hKH)

/-- The two-core of the fixed centralizer lies in H by the actual Sylow condition. -/
theorem fixedCentralizer_core_le_H (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) : (d.fixedCentralizer u).pCoreIn 2 ≤ F.H := by
  obtain ⟨S, hS⟩ := h.sylow
  exact (pCoreIn_le_sylow _ S).trans
    (hS ▸ (inf_le_left.trans (F.invariant 1)))

/-- Strictness also holds in Gᵤ/O₂(Gᵤ), the ambient group for A.3.14. -/
theorem fixedCentralizer_core_K_image_lt_component (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    ((K F).subgroupOf (d.fixedCentralizer u)).map
        (QuotientGroup.mk' (pCore 2 (d.fixedCentralizer u))) <
      (Lu.subgroupOf (d.fixedCentralizer u)).map
        (QuotientGroup.mk' (pCore 2 (d.fixedCentralizer u))) := by
  refine lt_of_le_of_ne (map_mono (subgroupOf_mono _ h.larger.le)) ?_
  intro he
  have hs := congrArg (comap (QuotientGroup.mk' (pCore 2 (d.fixedCentralizer u)))) he
  simp only [comap_map_eq, QuotientGroup.ker_mk'] at hs
  apply h.outside
  intro x hx
  have hmem : (⟨x, h.le_centralizer hx⟩ : d.fixedCentralizer u) ∈
      (K F).subgroupOf (d.fixedCentralizer u) ⊔ pCore 2 (d.fixedCentralizer u) := by
    rw [hs]
    exact (show Lu.subgroupOf (d.fixedCentralizer u) ≤
      Lu.subgroupOf (d.fixedCentralizer u) ⊔ pCore 2 (d.fixedCentralizer u) from
        le_sup_left) hx
  have hh : (K F).subgroupOf (d.fixedCentralizer u) ⊔ pCore 2 (d.fixedCentralizer u) ≤
      F.H.subgroupOf (d.fixedCentralizer u) := by
    refine sup_le (subgroupOf_mono _ (K_le_H F)) ?_
    intro k hk
    exact d.fixedCentralizer_core_le_H u h (mem_map_of_mem _ hk)
  exact hh hmem

/-- The actual quotient local-family hypothesis used by A.3.14. -/
theorem fixedCentralizer_core_K_local (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    ∃ S : Sylow 2 (d.fixedCentralizer u),
      (S : Subgroup (d.fixedCentralizer u)).map (d.fixedCentralizer u).subtype =
        d.fixedSylow u ∧
      ((K F).subgroupOf (d.fixedCentralizer u)).map
          (QuotientGroup.mk' (pCore 2 (d.fixedCentralizer u))) ∈
        ChapterA.Section03.localCComponents
          (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (d.fixedCentralizer u)))) := by
  obtain ⟨S, hS⟩ := h.sylow
  refine ⟨S, hS, ?_⟩
  have hloc : (K F).subgroupOf (d.fixedCentralizer u) ∈
      Chapter1.L (d.fixedCentralizer u) (S : Subgroup (d.fixedCentralizer u)) := by
    rw [← Chapter1.mem_L_map_iff (d.fixedCentralizer u).subtype
      (d.fixedCentralizer u).subtype_injective,
      map_subgroupOf_eq_of_le (d.K_le_fixedCentralizer u h.member), hS]
    exact d.K_mem_fixedLocalFamily u h.member h.fixed
  simpa only [Sylow.coe_mapSurjective] using
    Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hloc

open Chapter1.RadicalExclusions.ModelReduction

/-- Rᵤ normalizes Lᵤ because normality is relative to Gᵤ. -/
theorem fixedCore_normalizes_component (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) : d.fixedCore u ≤ normalizer (Lu : Set G) :=
  ((pCoreIn_le 2 _).trans inf_le_right).trans
    ((normal_subgroupOf_iff_le_normalizer h.le_centralizer).mp h.normal)

/-- C.2.7 controls the kernel of the literal core-to-star comparison. -/
theorem fixedComponent_coreToStar_ker_le_center (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    (c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) :
    (coreToStar (d.fixedCore_normalizes_component u h)).ker ≤
      center (Lu ⧸ pCore 2 Lu) :=
  FullSieve.coreToStar_ker_le_center_of_bound
    (d.fixedCore_normalizes_component u h) c27.kernel.upper

/-- The nontrivial star image is deduced from the source kernel bound. -/
theorem fixedComponent_starImage_ne_bot (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    (c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) :
    starImage Lu (d.fixedCore u) Lu ≠ ⊥ :=
  FullSieve.starImage_ne_bot_of_bound
    (d.fixedCore_normalizes_component u h) h.quotient c27.kernel.upper

/-- Only the central simple quotients are identified without a further center argument. -/
def fixedComponent_coreStarCenterEquiv (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    (c27 : FullSieve.SourceInterface.Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) :
    ((Lu ⧸ pCore 2 Lu) ⧸ center (Lu ⧸ pCore 2 Lu)) ≃*
      ((starImage Lu (d.fixedCore u) Lu) ⧸ center (starImage Lu (d.fixedCore u) Lu)) :=
  coreStarCenterEquiv (d.fixedCore_normalizes_component u h) h.quotient
    (d.fixedComponent_starImage_ne_bot u h c27)

/-- The component image in Gᵤ/O₂(Gᵤ) is the actual Lᵤ/O₂(Lᵤ). -/
def fixedComponent_coreEquivLocalImage (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    (Lu ⧸ pCore 2 Lu) ≃*
      (Lu.subgroupOf (d.fixedCentralizer u)).map
        (QuotientGroup.mk' (pCore 2 (d.fixedCentralizer u))) := by
  let e := subgroupOfEquivOfLe h.le_centralizer
  exact (QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans
    (cComponentTwoCoreQuotientEquiv h.component)

/-- The identification of the component quotient respects its original representatives. -/
theorem fixedComponent_coreEquivLocalImage_mk (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) (x : Lu) :
    (d.fixedComponent_coreEquivLocalImage u h
      (QuotientGroup.mk' (pCore 2 Lu) x) :
        d.fixedCentralizer u ⧸ pCore 2 (d.fixedCentralizer u)) =
      QuotientGroup.mk' (pCore 2 (d.fixedCentralizer u))
        ⟨(x : G), h.le_centralizer x.property⟩ := rfl

/-- All hypotheses at the reduced ambient boundary of A.3.14.

The smaller quotient is by its solvable radical. Both subgroups are literal
images under Gᵤ → Gᵤ/O₂(Gᵤ); their strictness is proved from escape from H.
This is input preparation, not the A.3.14 embedding classification.
-/
theorem fixedCentralizer_A314_inputs (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu) :
    let X := d.fixedCentralizer u ⧸ pCore 2 (d.fixedCentralizer u)
    let q := QuotientGroup.mk' (pCore 2 (d.fixedCentralizer u))
    let B := ((K F).subgroupOf (d.fixedCentralizer u)).map q
    let C := (Lu.subgroupOf (d.fixedCentralizer u)).map q
    IsSQTK KnownSimple.IsKnownSimple X ∧ pCore 2 X = ⊥ ∧
      ∃ S : Sylow 2 X, B ∈ ChapterA.Section03.localCComponents S ∧
        Nonempty ((B ⧸ solvableRadical B) ≃* alternatingGroup (Fin 5)) ∧
        B < C ∧ C.IsCComponent := by
  dsimp only
  refine ⟨d.fixedCentralizer_quotient_sqtk u h.nonidentity,
    pCore_quotient_pCore_eq_bot 2, ?_⟩
  obtain ⟨S, _, hloc⟩ := d.fixedCentralizer_core_K_local u h
  let := pCore_isNilpotent (p := 2) (G := d.fixedCentralizer u)
  exact ⟨S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 (d.fixedCentralizer u))),
    hloc, ⟨d.KImageRadicalAlternatingFive _ (d.K_le_fixedCentralizer u h.member)⟩,
    d.fixedCentralizer_core_K_image_lt_component u h, h.component.map_quotient _⟩

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
