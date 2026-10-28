module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalGeometry
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Components
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.QuadraticBound
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Offenders.PrimeCoreAction

/-!
# The original local quadratic action from guarded structural input

The abelian full point span makes each local span abelian. The original
seed transitivity makes intersecting conjugates commute. These facts and
the same-G,T structural input construct F.9.1 and its faithful bounded
quotient action on the literal U_I/V₁. No universal 12.2.2 or 12.2.13 is
needed for this construction.

The actual reduced local C T is then supplied by component uniqueness
and escape. The quadratic actor lies in the original point-parabolic
core and is faithful on that same component image. This is the local
action needed by the remaining Fitting and solvable-local reductions.
Source: Aschbacher–Smith F.9.1,16, pp.317–324; 14.7.30,47–48,
pp.1055,1063–1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
open Chapter12.Section08 CriticalFusion.Source
open Chapter12.Section09.NaturalSource
open Chapter13.Section08.SolvableExclusion.Three
open Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.ModuleBound
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem local_span_abelian (hab : IsMulCommutative F.U)
    (I : Subgroup G) (hIH : I ≤ F.H) : IsMulCommutative (F.UH I) := by
  let := hab
  have hi : F.UH I ≤ F.U := conjugateSpanBy_mono le_rfl hIH
  exact le_centralizer_iff_isMulCommutative.mp
    (hi.trans ((le_centralizer F.U).trans (Subgroup.centralizer_le hi)))

private theorem intersecting_seed_conjugates_commute
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U) :
    ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  obtain ⟨z,hz,he⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hh := F.abelian_U_iff_intersections_commute (by decide) z he hz (by
    intro x hx hx1
    obtain ⟨l,hl,hconj⟩ := h.vector_transitive
      (F.le_seed 1 (he ▸ mem_zpowers z)) hx hz hx1
    exact ⟨l,h.chosen.normalizes hl,hconj⟩)
  intro g hg
  have hc := (hh.mp hab) g⁻¹
  simpa only [conjugate,inv_inv] using hc (by simpa only [conjugate,inv_inv] using hg)

theorem local_f9_hypothesis_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) (hab : IsMulCommutative F.U)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    (naturalF9Setup F L J).Hypothesis := by
  let hf := local_f8_hypothesis_at h hab structural J hJ
  let D := naturalF9Setup F L J
  have hpoint : Nat.card (F.Vi 1) = 2 := by
    simpa using F.card 1 (by have := h.rank; omega)
  have hcent : F.H = centralizer (F.Vi 1 : Set G) :=
    le_antisymm (normalizer_le_centralizer_of_card_two _ hpoint)
      (Subgroup.centralizer_le_normalizer _)
  have hres : D.L₁ = (F.f8SourceSetup L J).L₁ := by
    change (pResidual 2 (L ⊓ centralizer (F.Vi 1 : Set G) : Subgroup G)).map
        (L ⊓ centralizer (F.Vi 1 : Set G)).subtype =
      (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype
    rw [hcent]
  have hvJ : V ≤ J := hf.V_le_T.trans (le_sup_right.trans hf.local_le)
  refine {
    elementary := hf.elementary
    residual := hf.residual
    normalizes_L := hf.T_normalizes_L
    characteristic_L := hf.characteristic_L
    V_le_LT := hf.V_le_LT
    reduced := hf.reduced
    sylow_centralizer := hf.centralizer_eq
    point_card := hpoint
    normalizes_point := F.invariant 1
    point_lt := lt_of_le_of_ne hf.point_le hf.quotient_nonzero
    plus_le := le_rfl
    H_centralizes := hJ.2.1.trans hcent.le
    local_le := by change D.L₁ ⊔ (T : Subgroup G) ≤ J; rw [hres]; exact hf.local_le
    characteristic_H := hf.characteristic_H
    kernel_core := ?_
    local_normalizes := ?_
    irreducible := ?_
    normalizer_control := le_rfl
    generated_core := hf.generated_core
    commutator_lifting := ?_ }
  · have he := (F.f8SourceSetup L J).quotientCentralizer_eq_intrinsic hf.H_le V hvJ
    rw [←he]
    exact hf.centralizer_core_le
  · change D.L₁ ⊔ (T : Subgroup G) ≤ normalizer (V : Set G)
    rw [hres,F.localKernel_L₁ L J]
    exact sup_le ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
      (h.sylow_normalizes_seed_at structural)
  · intro A ha hb hn
    apply hf.irreducible A ha hb
    change D.L₁ ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) at hn
    rwa [hres] at hn
  · intro g hg _ _ _
    let : IsMulCommutative (conjugateSpanBy V J) :=
      local_span_abelian hab J hJ.2.1
    let : IsMulCommutative (F.UH J) := inferInstanceAs
      (IsMulCommutative (conjugateSpanBy V J))
    have hv : V ≤ F.UH J := le_conjugateSpanBy _ _
    have hvg : V.map (MulAut.conj g).toMonoidHom ≤ F.UH J := by
      rintro _ ⟨v,hv,rfl⟩
      exact subset_closure ⟨g,hg,v,hv,rfl⟩
    have hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr
        (hv.trans ((le_centralizer (F.UH J)).trans (Subgroup.centralizer_le hvg)))
    exact ⟨hc,(commutator_comm _ _).trans hc⟩

/-- F.9.16(3) on the literal quotient of every original point overgroup. -/
theorem local_quadratic_bound_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) (hab : IsMulCommutative F.U)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    ∃ hU : IsElementaryAbelian 2 (F.UH J),
      let := hU
      ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
        quadraticRatio a.representation ≤ 2 := by
  let := h.chosen.elementary
  let : IsMulCommutative (conjugateSpanBy V J) :=
    local_span_abelian hab J hJ.2.1
  apply OriginalF916.original_bounded_action
    (SourceF91.ofF91 (local_f9_hypothesis_at h structural hab J hJ))
  · intro g hg
    exact intersecting_seed_conjugates_commute h hab g hg
  · intro x hx
    left
    rw [commutator_eq_bot_iff_le_centralizer,le_centralizer_iff]
    exact zpowers_le.mpr hx

/-- The original edge is L₁T, so the bound is witnessed in the literal R₁. -/
theorem local_quadratic_actor_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) (hab : IsMulCommutative F.U)
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G))) :
    ∃ hU : IsElementaryAbelian 2 (F.UH J),
      let := hU
      ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
        quadraticRatio a.representation ≤ 2 ∧
        ∃ B : Subgroup J,
          B ≤ (F.Ri L 1).subgroupOf J ∧
          IsElementaryTwo (B.map (QuotientGroup.mk' (pCore 2 J))) ∧
          IsQuadratic a.representation (B.map (QuotientGroup.mk' (pCore 2 J))) ∧
          fixedCodim a.representation (B.map (QuotientGroup.mk' (pCore 2 J))) ≤
            2 * rank (B.map (QuotientGroup.mk' (pCore 2 J))) := by
  obtain ⟨hU,a,ha⟩ := local_quadratic_bound_at h structural hab J hJ
  let : IsElementaryAbelian 2 (conjugateSpanBy V J) := hU
  let := h.chosen.elementary
  let : IsMulCommutative (conjugateSpanBy V J) :=
    local_span_abelian hab J hJ.2.1
  have hf := local_f9_hypothesis_at h structural hab J hJ
  have hres : (naturalF9Setup F L J).L₁ = F.Li L 1 :=
    hf.g2_L₁.symm.trans (F.localKernel_L₁ L J)
  have hedge : (L ⊔ (T : Subgroup G)) ⊓ J = F.Li L 1 ⊔ (T : Subgroup G) := by
    have he := hf.LT_inf_H_eq
    change (L ⊔ (T : Subgroup G)) ⊓ J =
      (naturalF9Setup F L J).L₁ ⊔ (T : Subgroup G) at he
    rwa [hres] at he
  refine ⟨hU,a,ha,?_⟩
  change ∃ B : Subgroup J,
    B ≤ ((F.Li L 1 ⊔ (T : Subgroup G)).pCoreIn 2).subgroupOf J ∧ _
  rw [←hedge]
  apply OriginalF916.original_witness
    (SourceF91.ofF91 (local_f9_hypothesis_at h structural hab J hJ))
  · intro g hg
    exact intersecting_seed_conjugates_commute h hab g hg
  · intro x hx
    left
    rw [commutator_eq_bot_iff_le_centralizer,le_centralizer_iff]
    exact zpowers_le.mpr hx


/-- A normal supplement makes the original quadratic actor faithful on
that supplement in the literal local star quotient. -/
theorem local_prime_supplement_quadratic_actor_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (X : Subgroup (HStar I)) [X.Normal]
    (hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I).map
      (QuotientGroup.mk' (pCore 2 I)) = ⊤) :
    ∃ hU : IsElementaryAbelian 2 (F.UH I),
      let := hU
      ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
        quadraticRatio a.representation ≤ 2 ∧
        ∃ A : Subgroup I,
          A ≤ (F.Ri L 1).subgroupOf I ∧
          IsElementaryTwo (A.map (QuotientGroup.mk' (pCore 2 I))) ∧
          IsQuadratic a.representation (A.map (QuotientGroup.mk' (pCore 2 I))) ∧
          fixedCodim a.representation (A.map (QuotientGroup.mk' (pCore 2 I))) ≤
            2 * rank (A.map (QuotientGroup.mk' (pCore 2 I))) ∧
          A.map (QuotientGroup.mk' (pCore 2 I)) ⊓ centralizer (X : Set (HStar I)) = ⊥ := by
  obtain ⟨hU,a,hq,A,hAR,hA,hquad,hcod⟩ :=
    local_quadratic_actor_at h structural hab I hI
  let := hU
  refine ⟨hU,a,hq,A,hAR,hA,hquad,hcod,?_⟩
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  let q := QuotientGroup.mk' (pCore 2 I)
  let B₀ := (B.subgroupOf I).map q
  let R₀ := ((F.Ri L 1).subgroupOf I).map q
  have hBR₀ : B.subgroupOf I ≤ normalizer ((F.Ri L 1).subgroupOf I : Set I) := by
    apply le_normalizer_iff.mpr
    intro b hb r hr
    exact le_normalizer_iff.mp (le_normalizer_pCoreIn 2 B) b hb r hr
  have hBR : B₀ ≤ normalizer (R₀ : Set (HStar I)) :=
    (map_mono hBR₀).trans (le_normalizer_map q)
  have hR2 : IsPGroup 2 R₀ := (isPGroup_pCoreIn 2 B).comap_subtype.map q
  have hfaith := centralizer_inf_eq_bot_of_supplement X B₀ R₀ hgen hR2 hBR
    (pCore_quotient_pCore_eq_bot 2)
  exact bot_unique ((inf_le_inf_right _ (map_mono hAR)).trans hfaith.le)


/-- The actual component reduction supplies the normal supplement and all
local-action premises internally at C T, with its original two-core map. -/
theorem local_component_quadratic_reduction_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    let A := C.map I.subtype
    let J := A ⊔ (T : Subgroup G)
    let KJ := A.subgroupOf J
    let q := QuotientGroup.mk' (pCore 2 J)
    J ≤ I ∧ J ∈ F.Hz L (normalizer (L : Set G)) ∧
      KJ.IsCComponent ∧ KJ.Normal ∧ IsQuasisimple (KJ ⧸ pCore 2 KJ) ∧
      ((q.comp KJ.subtype).ker = pCore 2 KJ) ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH J),
        let := hU
        ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
          quadraticRatio a.representation ≤ 2 ∧
          ∃ B : Subgroup J,
            B ≤ (F.Ri L 1).subgroupOf J ∧
            IsElementaryTwo (B.map q) ∧ IsQuadratic a.representation (B.map q) ∧
            fixedCodim a.representation (B.map q) ≤ 2 * rank (B.map q) ∧
            B.map q ⊓ centralizer (KJ.map q : Set (HStar J)) = ⊥ := by
  let A := C.map I.subtype
  let J := A ⊔ (T : Subgroup G)
  let KJ := A.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  have hJI : J ≤ I := sup_le (map_subtype_le _) (F.sylow_le_of_mem_Hz hI)
  have hJ := local_component_sylow_join_mem_Hz_at h structural source47 I hI C hC
  have hCI : (A.subgroupOf I).IsCComponent := by
    simpa only [A,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  have hKJ : KJ.IsCComponent := hCI.subgroupOf_of_le le_sup_left hJI
  let hn := local_component_normal_at h structural source47 J hJ KJ hKJ
  let : (KJ.map q).Normal := hn.map q (QuotientGroup.mk'_surjective _)
  have hs : A ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = J := by
    rw [←sup_assoc,sup_eq_left.mpr (source47 I hI C hC).1]
  have hg : KJ.map q ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J).map q = ⊤ := by
    rw [←Subgroup.map_sup,
      ←subgroupOf_sup (show A ≤ J from le_sup_left)
        (sup_le ((source47 I hI C hC).1.trans le_sup_left) le_sup_right),
      hs,subgroupOf_self,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  refine ⟨hJI,hJ,hKJ,hn,local_component_twoCore_of_earlier14747 source47 J hJ KJ hKJ,?_,?_⟩
  · rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hKJ.subnormal).symm
  · exact local_prime_supplement_quadratic_actor_at h hab structural J hJ (KJ.map q) hg

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
