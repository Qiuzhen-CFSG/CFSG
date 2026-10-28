module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SixFixedModel
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SixOriginalAction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore

/-!
# Passing the original A₆ core bound through its fixed subgroup

The fixed subgroup of the original moved module is normal in the actual
component--Sylow join and is a two-group. Quotienting by it therefore
preserves the embedded two-core of the component. The desired whole-core
bound is equivalent to the corresponding bound in this quotient; the
order-thirty-two central-cover case is retained.

The projected core bound remains an MS source obligation. Neither a
natural constituent nor its dimension supplies that bound. Normality of the
kernel does not assert descent of the MS characteristic condition.
Source: Aschbacher--Smith 13.6.22, printed pp.932--933.
-/

@[expose] public section
open Subgroup Representation Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
open LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G]

private theorem core_bound_iff_image {D : Type*} [Group D] [Finite D]
    (B U : Subgroup G) (f : G →* D) (hk : IsPGroup 2 f.ker) (hku : f.ker ≤ U) :
    ⁅B.pCoreIn 2,B⁆ ≤ U ↔ ⁅(B.map f).pCoreIn 2,B.map f⁆ ≤ U.map f := by
  rw [← map_pCoreIn_of_ker_isPGroup f hk B,← map_commutator]
  constructor
  · exact map_mono
  · intro h
    have hh := map_le_iff_le_comap.mp h
    rwa [comap_map_eq_self hku] at hh

/-- The actual K-fixed part of U_K inside K Tᵥ. -/
abbrev sixFixedInJoin (K L T : Subgroup G) (z v : G) : Subgroup ↥(K ⊔ Tv T v) :=
  (UK K L T z v).subgroupOf (K ⊔ Tv T v) ⊓
    centralizer (K.subgroupOf (K ⊔ Tv T v) : Set (K ⊔ Tv T v : Subgroup G))

omit [Finite G] in
/-- Both K and U_K are normal in the same join, so its fixed subgroup
can be used as an ambient quotient kernel. -/
theorem sixFixedInJoin_normal (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G)) :
    (sixFixedInJoin K L T z v).Normal := by
  let : (K.subgroupOf (K ⊔ Tv T v)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hn)
  let := joinUK_normal K L T z v hL hz hn
  exact inferInstance

/-- Exact component-core transport through the original fixed subgroup,
with an equivalence of the original and projected core-bound obligations. -/
theorem six_core_bound_iff_fixed_quotient
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    [IsElementaryAbelian 2 (WK K L T z v)] :
    let H := K ⊔ Tv T v
    let B := K.subgroupOf H
    let U := (UK K L T z v).subgroupOf H
    let C := sixFixedInJoin K L T z v
    let := sixFixedInJoin_normal K L T z v hL hz hn
    let q := QuotientGroup.mk' C
    IsPGroup 2 q.ker ∧
      (B.pCoreIn 2).map q = (B.map q).pCoreIn 2 ∧
      ((ChapterC.blockU K).map K.subtype ≤ UK K L T z v ↔
        ⁅(B.map q).pCoreIn 2,B.map q⁆ ≤ U.map q) := by
  let H := K ⊔ Tv T v
  let B := K.subgroupOf H
  let U := (UK K L T z v).subgroupOf H
  let C := sixFixedInJoin K L T z v
  let := sixFixedInJoin_normal K L T z v hL hz hn
  let q := QuotientGroup.mk' C
  have hUH : UK K L T z v ≤ H := (UK_le_WK K L T z v hL hz).trans hW
  let : IsElementaryAbelian 2 (UK K L T z v) :=
    IsElementaryAbelian.of_le (UK_le_WK K L T z v hL hz)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (show C ≤ U from inf_le_left)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact IsElementaryAbelian.isPGroup 2 C
  have he : (⁅B.pCoreIn 2,B⁆).map H.subtype = (ChapterC.blockU K).map K.subtype := by
    rw [map_commutator,map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
      map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),
      ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
    rfl
  refine ⟨hk,map_pCoreIn_of_ker_isPGroup q hk B,?_⟩
  rw [←core_bound_iff_image B U q hk (by
    rw [QuotientGroup.ker_mk']; exact inf_le_left)]
  constructor
  · intro h x hx
    exact h (he ▸ mem_map_of_mem H.subtype hx)
  · intro h x hx
    obtain ⟨y,hy,rfl⟩ := (he.symm ▸ hx)
    exact h hy

omit [Finite G] in
/-- The image of U_K in the quotient of the entire join is the same
natural group as its intrinsic quotient by the K-fixed subgroup. -/
theorem six_fixed_quotient_natural
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (m : ConjugationQuotientModel K (UK K L T z v)
      (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6))) :
    let H := K ⊔ Tv T v
    let U := (UK K L T z v).subgroupOf H
    let C := sixFixedInJoin K L T z v
    let := sixFixedInJoin_normal K L T z v hL hz hn
    ∃ E : (U.map (QuotientGroup.mk' C)) ≃*
      Multiplicative (BinaryPermutation.natural (Fin 6)),
      ∀ u : U, E ((QuotientGroup.mk' C).subgroupMap U u) =
        m.quotient ⟨((u : H) : G),u.property⟩ := by
  let H := K ⊔ Tv T v
  let U := (UK K L T z v).subgroupOf H
  let C := sixFixedInJoin K L T z v
  let := sixFixedInJoin_normal K L T z v hL hz hn
  let q := QuotientGroup.mk' C
  have hUH : UK K L T z v ≤ H := (UK_le_WK K L T z v hL hz).trans hW
  let e : U ≃* UK K L T z v := subgroupOfEquivOfLe hUH
  let f := m.quotient.comp e.toMonoidHom
  have hf : Function.Surjective f := m.surjective.comp e.surjective
  have hk : (q.subgroupMap U).ker = f.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk',←MonoidHom.comap_ker,m.kernel]
    ext u
    change (u.val ∈ U ∧ u.val ∈ centralizer (K.subgroupOf H : Set H)) ↔
      ((u.val : G) ∈ centralizer (K : Set G))
    constructor
    · rintro ⟨_,hc⟩ k hk
      exact congrArg Subtype.val (hc ⟨k,(show K ≤ H from le_sup_left) hk⟩ hk)
    · intro hc
      refine ⟨u.property,?_⟩
      intro k hk
      exact Subtype.ext (hc (k : G) hk)
  let e₁ := QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap U)
    (q.subgroupMap_surjective U)
  let E := (e₁.symm.trans (QuotientGroup.quotientMulEquivOfEq hk)).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨E,?_⟩
  intro u
  have hu : e₁.symm (q.subgroupMap U u) = QuotientGroup.mk' _ u := by
    apply e₁.injective
    rw [e₁.apply_symm_apply]
    rfl
  change (QuotientGroup.quotientKerEquivOfSurjective f hf)
    ((QuotientGroup.quotientMulEquivOfEq hk) (e₁.symm (q.subgroupMap U u))) = _
  rw [hu]
  rfl

variable {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The original A₆ source supplies the fixed quotient, its genuine natural
subgroup, and exact core transport. Only reconstruction of the projected
whole core remains as the displayed equivalent obligation. -/
theorem six_fixed_quotient_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      RankTwo.LocalApplication.SourceHypothesis S I →
        omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (eC : plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* alternatingGroup (Fin 6)) :
    let z := markedZ d.flag.module
    let v := markedV d.flag.module
    let H := K ⊔ Tv (T : Subgroup G) v
    let B := K.subgroupOf H
    let U := (UK K L (T : Subgroup G) z v).subgroupOf H
    let C := sixFixedInJoin K L (T : Subgroup G) z v
    ∃ hC : C.Normal,
      letI := hC
      let q := QuotientGroup.mk' C
      IsPGroup 2 q.ker ∧
      (B.pCoreIn 2).map q = (B.map q).pCoreIn 2 ∧
      (∃ m : ConjugationQuotientModel K (UK K L (T : Subgroup G) z v)
          (BinaryPermutation.alternatingNaturalRepresentation (Ω := Fin 6)),
        Function.Surjective m.actor ∧
        ∃ E : (U.map q) ≃* Multiplicative (BinaryPermutation.natural (Fin 6)),
          ∀ u : U, E (q.subgroupMap U u) = m.quotient ⟨((u : H) : G),u.property⟩) ∧
      ((ChapterC.blockU K).map K.subtype ≤ UK K L (T : Subgroup G) z v ↔
        ⁅(B.map q).pCoreIn 2,B.map q⁆ ≤ U.map q) := by
  obtain ⟨hW,hmoved⟩ := six_actionData_original_source d V₃ earlier standing hm hfusion
    h1332 h63 hK hL hz eC
  let := hW
  obtain ⟨m⟩ := hmoved
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  let := plusImage_K_normal K L (T : Subgroup G) (markedZ d.flag.module)
    (markedV d.flag.module) hL hz hK hn
  obtain ⟨a,ha⟩ := six_quotientModel_of_actionData K L (T : Subgroup G)
    (markedZ d.flag.module) (markedV d.flag.module) hL hz hK.1.1 m
  have hLK := (containment_and_noncontainment_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK hL hz (.symplectic ⟨eC.trans
      (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix
        (F := ZMod 2) (by simp)).symm⟩)).1
  have hWH := WK_le_join K L (T : Subgroup G) (markedZ d.flag.module)
    (markedV d.flag.module) hn hLK ((mem_omegaOneCenterAmbient_iff _ _).mp (markedZ_mem_Tv_omega d)).1
  obtain ⟨hk,hcore,hiff⟩ := six_core_bound_iff_fixed_quotient K L (T : Subgroup G)
    (markedZ d.flag.module) (markedV d.flag.module) hL hz hn hWH
  exact ⟨sixFixedInJoin_normal K L (T : Subgroup G) (markedZ d.flag.module)
    (markedV d.flag.module) hL hz hn,hk,hcore,⟨a,ha,
      six_fixed_quotient_natural K L (T : Subgroup G) (markedZ d.flag.module)
        (markedV d.flag.module) hL hz hn hWH a⟩,hiff⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
