module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Quotients
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Parabolics
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions
public import Theory.GroupTheory.EquivariantParabolicLift
public import Theory.GroupTheory.SylowNormalIntersectionIndex

/-!
# The original minimal parabolic in the graph branch of 14.7.51

The original point parabolic L₁T has Sylow index three. Restriction to
the normal component preserves that index, and its literal two-core
quotient preserves it again. Thus P = L₁(T ∩ K) is a minimal parabolic
in the same flag as the image of T ∩ K. The original Sylow normalizes
both factors of P, and its transported intrinsic quotient action preserves
the marked node. A noninner actor then forces degree four and the middle
node. That node is the actual point-hyperplane flag stabilizer.

Source: Aschbacher–Smith 14.7.51, printed p.1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.GraphMarking
open Chapter12.Section08 CriticalFusion.Source
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
/-- The literal component two-core quotient in the supplied linear marking. -/
@[expose] def componentLinearMap (K : Subgroup G) {m : ℕ}
    (eK : (K ⧸ pCore 2 K) ≃* LinearGroup (m + 1)) : K →* LinearGroup (m + 1) :=
  eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))

omit [Finite G] in
/-- The original Sylow conjugation on the intrinsic component quotient. -/
@[expose] def componentLinearAction (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) {m : ℕ}
    (eK : (K ⧸ pCore 2 K) ≃* LinearGroup (m + 1)) :
    (T : Subgroup G) →* MulAut (LinearGroup (m + 1)) :=
  (MulAut.congr eK).toMonoidHom.comp
    ((quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion hn)))

omit [Finite G] in
/-- The model action and quotient map retain the original conjugation formula. -/
theorem componentLinearAction_equivariant (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G)) {m : ℕ}
    (eK : (K ⧸ pCore 2 K) ≃* LinearGroup (m + 1)) (t : (T : Subgroup G)) (k : K) :
    componentLinearMap K eK (K.normalizerMonoidHom (inclusion hn t) k) =
      componentLinearAction K hn eK t (componentLinearMap K eK k) := by
  change eK (QuotientGroup.mk' (pCore 2 K) _) =
    eK (quotientAut (pCore 2 K) _ (eK.symm (eK (QuotientGroup.mk' (pCore 2 K) k))))
  rw [eK.symm_apply_apply,quotientAut_apply_mk]
  rfl

omit [Finite G] in
private theorem map_nested_subgroupOf (A I K : Subgroup G) (hKI : K ≤ I) :
    ((A.subgroupOf I).subgroupOf (K.subgroupOf I)).map
      (subgroupOfEquivOfLe hKI).toMonoidHom = A.subgroupOf K := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x,hKI x.property⟩,x.property⟩,hx,rfl⟩

private theorem component_point_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : I = K ⊔ (T : Subgroup G)) :
    ((T : Subgroup G).subgroupOf K).relIndex
      ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf K) = 3 := by
  let B := F.Li L 1 ⊔ (T : Subgroup G)
  have hTI := F.sylow_le_of_mem_Hz hI
  have hBI : B ≤ I := sup_le (F.Li_one_le_of_mem_Hz hI) hTI
  let : (K.subgroupOf I).Normal := (normal_subgroupOf_iff_le_normalizer hKI).mpr
    (by rw [hgen]; exact sup_le K.le_normalizer hn)
  have htop : K.subgroupOf I ⊔ (T : Subgroup G).subgroupOf I = ⊤ := by
    rw [←subgroupOf_sup hKI hTI,←hgen,subgroupOf_self]
  have hh := normal_intersection_relIndex ((T : Subgroup G).subgroupOf I)
    (B.subgroupOf I) (K.subgroupOf I) (subgroupOf_mono I le_sup_right)
    (by rw [htop]; exact le_top)
  have ht := relIndex_map_map_of_injective (f := (subgroupOfEquivOfLe hKI).toMonoidHom)
    (((T : Subgroup G).subgroupOf I).subgroupOf (K.subgroupOf I))
    ((B.subgroupOf I).subgroupOf (K.subgroupOf I))
    (subgroupOfEquivOfLe hKI).injective
  rw [map_nested_subgroupOf,map_nested_subgroupOf,hh] at ht
  have htI : ((T : Subgroup G).subgroupOf I).relIndex (B.subgroupOf I) =
      (T : Subgroup G).relIndex B := by
    rw [subgroupOf,relIndex_comap,map_subgroupOf_eq_of_le hBI]
  exact ht.trans (htI.trans (SymmetricThreeTwoCore.sylow_index_three
    (pointQuotientEquiv_at h structural)
    (T.subtype (show (T : Subgroup G) ≤ B from le_sup_right))))

omit [Finite G] in
private theorem component_point_eq_intersection
    (A K : Subgroup G) (hAK : A ≤ K)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G)) :
    A ⊔ ((T : Subgroup G) ⊓ K) = (A ⊔ (T : Subgroup G)) ⊓ K := by
  apply le_antisymm (le_inf (sup_le_sup_left inf_le_left A) (sup_le hAK inf_le_right))
  intro x hx
  have hm : x ∈ (A : Set G) * ((T : Subgroup G) : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left A (T : Subgroup G) hTA]
    exact hx.1
  obtain ⟨a,ha,t,ht,he⟩ := hm
  have he' : a * t = x := he
  have htK : t ∈ K := by
    apply (K.mul_mem_cancel_left (hAK ha)).mp
    rw [he']
    exact hx.2
  rw [←he']
  exact (A ⊔ ((T : Subgroup G) ⊓ K)).mul_mem (mem_sup_left ha) (mem_sup_right ⟨ht,htK⟩)

/-- The original component point parabolic is the literal omitted-cut
parabolic in its Sylow flag, preserved by the original Sylow quotient action. -/
theorem local_component_node_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : I = K ⊔ (T : Subgroup G)) (hLK : F.Li L 1 ≤ K)
    {m : ℕ} (eK : (K ⧸ pCore 2 K) ≃* LinearGroup (m + 1)) :
    ∃ (b : Basis m) (i : Fin m),
      let q := componentLinearMap K eK
      let P := F.Li L 1 ⊔ ((T : Subgroup G) ⊓ K)
      ((T : Subgroup G).subgroupOf K).map q = cutStabilizer b Set.univ ∧
      (P.subgroupOf K).map q = minimalParabolic b i ∧
      P.subgroupOf K = (minimalParabolic b i).comap q ∧
      (T : Subgroup G) ≤ normalizer (P : Set G) ∧
      ∀ t : (T : Subgroup G), (minimalParabolic b i).map
        (componentLinearAction K hn eK t).toMonoidHom = minimalParabolic b i := by
  let q := componentLinearMap K eK
  let P := F.Li L 1 ⊔ ((T : Subgroup G) ⊓ K)
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    change IsPGroup 2 (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))).ker
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hn
  have hSP : (S : Subgroup K) ≤ P.subgroupOf K := by
    rw [hS]
    intro x hx
    exact mem_sup_right ⟨hx,x.property⟩
  have hPE : P.subgroupOf K = (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf K := by
    change (F.Li L 1 ⊔ ((T : Subgroup G) ⊓ K)).subgroupOf K = _
    rw [component_point_eq_intersection _ K hLK (T_normalizes_L₁_at h structural)]
    ext x
    exact and_iff_left x.property
  have hi : (S : Subgroup K).relIndex (P.subgroupOf K) = 3 := by
    rw [hS,hPE]
    exact component_point_index h structural I K hI hKI hn hgen
  let S' := S.mapSurjective hq
  have hker : q.ker ≤ (S : Subgroup K) := hk.le_sylow_of_normal S
  have himage : (S' : Subgroup _).relIndex ((P.subgroupOf K).map q) = 3 := by
    change ((S : Subgroup K).map q).relIndex ((P.subgroupOf K).map q) = 3
    rw [relIndex_map_map,sup_eq_left.mpr hker,sup_eq_left.mpr (hker.trans hSP)]
    exact hi
  obtain ⟨b,i,hb,hP⟩ := InnerLinearExclusion.exists_marked_node S'
    ((P.subgroupOf K).map q) (map_mono hSP) himage
  have hPn : (T : Subgroup G) ≤ normalizer (P : Set G) :=
    (le_inf (T_normalizes_L₁_at h structural)
      ((le_inf (T : Subgroup G).le_normalizer hn).trans inf_normalizer_le_normalizer_inf)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  refine ⟨b,i,?_,hP,?_,hPn,?_⟩
  · exact hS ▸ hb
  · rw [←hP,comap_map_eq_self (hker.trans hSP)]
  · intro t
    have hh := EquivariantLift.map_invariant K q hn (componentLinearAction K hn eK)
      (componentLinearAction_equivariant K hn eK) hPn t
    rwa [hP] at hh

/-- A noninner original Sylow action forces the middle node in dimension four. -/
theorem local_graph_node_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : I = K ⊔ (T : Subgroup G)) (hLK : F.Li L 1 ≤ K)
    {m : ℕ} (hm : m = 3 ∨ m = 4)
    (eK : (K ⧸ pCore 2 K) ≃* LinearGroup (m + 1))
    (hout : ¬ ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K)) :
    m = 3 ∧ ∃ (b : Basis m) (i : Fin m), i.val = 1 ∧
      ((T : Subgroup G).subgroupOf K).map (componentLinearMap K eK) =
        cutStabilizer b Set.univ ∧
      ((F.Li L 1 ⊔ ((T : Subgroup G) ⊓ K)).subgroupOf K).map (componentLinearMap K eK) =
        minimalParabolic b i ∧
      ∀ t : (T : Subgroup G), (minimalParabolic b i).map
        (componentLinearAction K hn eK t).toMonoidHom = minimalParabolic b i := by
  classical
  obtain ⟨b,i,hb,hP,_,_,hinv⟩ := local_component_node_at h structural I K hI hKI hn hgen hLK eK
  push Not at hout
  obtain ⟨t,ht,hout⟩ := hout
  let a := componentLinearAction K hn eK ⟨t,ht⟩
  have ha : a ∉ MulAut.innerSubgroup _ := by
    intro ha
    rw [←MulAut.map_innerSubgroup_congr eK] at ha
    obtain ⟨β,hβ,hβa⟩ := ha
    have he : β = (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) :=
      (MulAut.congr eK).injective hβa
    exact hout (he ▸ hβ)
  obtain ⟨hdegree,hnode⟩ := outer_preserves_minimalParabolic_middle
    (by omega : 2 ≤ m) (by omega : m ≤ 4) b i a ha (hinv ⟨t,ht⟩)
  exact ⟨hdegree,b,i,by omega,hb,hP,hinv⟩

/-- The middle minimal parabolic in degree four is the point-hyperplane
flag stabilizer, with both subspaces in the same original basis. -/
theorem middle_node_eq_point_hyperplane (b : Basis 3) :
    minimalParabolic b (1 : Fin 3) =
      parabolic (cutSpace b (0 : Fin 3)) ⊓ parabolic (cutSpace b (2 : Fin 3)) := by
  ext g
  rw [minimalParabolic,mem_cutStabilizer,mem_inf]
  change (∀ j ∈ ({(1 : Fin 3)} : Set (Fin 3))ᶜ,
      ∀ v, g v ∈ cutSpace b j ↔ v ∈ cutSpace b j) ↔
    (∀ v, g v ∈ cutSpace b (0 : Fin 3) ↔ v ∈ cutSpace b (0 : Fin 3)) ∧
    (∀ v, g v ∈ cutSpace b (2 : Fin 3) ↔ v ∈ cutSpace b (2 : Fin 3))
  constructor
  · intro hg
    exact ⟨hg 0 (by decide),hg 2 (by decide)⟩
  · rintro ⟨h0,h2⟩ j hj
    fin_cases j
    · exact h0
    · exact (hj rfl).elim
    · exact h2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.GraphMarking
