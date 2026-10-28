module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointFixedLine
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorFusionSource
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.PrimeRankElementary

/-!
# The diagonal point residual enters the source component argument

The literal residual at a nonsingular tensor vector has A₅ quotient and is
normalized by its Sylow point centralizer. The point itself supplies the
nontrivial two-core in their join. Choose a Sylow of M ∩ C(v) above C_T(v). It contains J(T), so 3.2.10
upgrades it to an ambient Sylow centralizer; 1.2.4 then gives a normal
containing C-component, with no additional Sylow hypothesis.

These are the first reductions in Aschbacher–Smith 9.4.1, printed p.735.
The strict overcomponent's FF, cohomology and Xi exclusions are not asserted
here; they must show that the selected component equals the residual.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

private theorem alternatingFive_quasisimple : IsQuasisimple (alternatingGroup (Fin 5)) := {
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }

/-- The actual diagonal residual is a C-component in any group normalizing it. -/
theorem tensorPointResidual_cComponent (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {H : Subgroup G} (hLH : m.tensorPointResidual v ≤ H)
    (hHN : H ≤ normalizer (m.tensorPointResidual v : Set G)) :
    ((m.tensorPointResidual v).subgroupOf H).IsCComponent := by
  let B := (m.tensorPointResidual v).subgroupOf H
  let f : B ≃* m.tensorPointResidual v := subgroupOfEquivOfLe hLH
  let q := f.toMonoidHom.pCoreQuotientEquiv (p := 2) f.surjective
    (by rw [f.toMonoidHom.ker_eq_bot f.injective]; exact IsPGroup.of_bot)
  let : IsQuasisimple (alternatingGroup (Fin 5)) := alternatingFive_quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) :=
    IsQuasisimple.of_mulEquiv (q.trans (m.tensorPointResidualA5Equiv v hv)).symm
  have hn : B.Normal := normal_subgroupOf_of_le_normalizer hHN
  exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient hn.isSubnormal
    ((m.tensorPointResidual_isPPerfect v).of_surjective f.symm.toMonoidHom f.symm.surjective)

theorem tensorPoint_ne_one (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) : (v : G) ≠ 1 := by
  intro he
  have hv' : v = 1 := Subtype.ext he
  simp only [hv',map_one] at hv
  exact hv Matrix.det_zero

private theorem point_core_ne_bot (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {H : Subgroup G} (hvH : (v : G) ∈ H)
    (hH : H ≤ centralizer ({(v : G)} : Set G)) : H.pCoreIn 2 ≠ ⊥ := by
  have hp : IsPGroup 2 (zpowers (v : G)) :=
    T.isPGroup'.to_le (zpowers_le.mpr (m.fullModule_le_sylow v.property))
  have hn : H ≤ normalizer (zpowers (v : G) : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    exact hH
  have hle := le_pCoreIn_of_normalizes hp (zpowers_le.mpr hvH) hn
  intro he
  exact m.tensorPoint_ne_one v hv (mem_bot.mp (he ▸ hle (mem_zpowers (v : G))))

/-- The source Sylow point centralizer makes the diagonal residual local. -/
theorem tensorPointResidual_mem_local (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (centralizer ({(v : G)} : Set G))) :
    m.tensorPointResidual v ∈ Chapter1.L G
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) := by
  let R := (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)
  have hRX : R ≤ centralizer ({(v : G)} : Set G) := inf_le_right
  have hLX := m.tensorPointResidual_le_centralizer v
  refine ⟨m.tensorPointResidual_cComponent v hv le_sup_left
    (sup_le (m.tensorPointResidual v).le_normalizer (m.tensorPointResidual_sylow_normalized v)),
    hs.restrict le_sup_right (sup_le hLX hRX),?_⟩
  exact m.point_core_ne_bot v hv
    (mem_sup_right ⟨m.fullModule_le_sylow v.property,mem_centralizer_singleton_iff.mpr rfl⟩)
    (sup_le hLX hRX)

/-- Original 1.2.4 supplies a normal C-component containing the exact diagonal
residual; the only Sylow premise is the source choice inside M. -/
theorem tensorPointResidual_containing_component (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G))) :
    ∃ I : Subgroup G, m.tensorPointResidual v ≤ I ∧
      I ≤ centralizer ({(v : G)} : Set G) ∧
      (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent ∧
      centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G) := by
  let X := centralizer ({(v : G)} : Set G)
  let R := (T : Subgroup G) ⊓ X
  have hvX : (v : G) ∈ X := mem_centralizer_singleton_iff.mpr rfl
  have hLX := m.tensorPointResidual_le_centralizer v
  have hRX : R ≤ X := inf_le_right
  have hcoreX := m.point_core_ne_bot v hv hvX le_rfl
  have hSyl := m.tensor_centralizer_sylow v.property hs
  have hlocal := m.tensorPointResidual_mem_local v hv hSyl
  obtain ⟨P,hP⟩ := hSyl
  have hP' : (P : Subgroup X) = R.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hRX]
  have hlocalX : (m.tensorPointResidual v).subgroupOf X ∈ Chapter1.L X (P : Subgroup X) := by
    rw [hP']
    exact (Chapter1.mem_LIn_iff_subgroupOf hRX hLX).mp ⟨hLX,hlocal⟩
  have hPL : (P : Subgroup X) ≤ normalizer ((m.tensorPointResidual v).subgroupOf X : Set X) := by
    rw [hP',←subgroupOf_normalizer_eq hLX]
    exact comap_mono (m.tensorPointResidual_sylow_normalized v)
  obtain ⟨K,⟨hK,hLK,hKn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk D.simpleQTKE hcoreX) P hlocalX hPL
  let I := K.map X.subtype
  have hIX : I ≤ X := map_subtype_le K
  have he : I.subgroupOf X = K := comap_map_eq_self_of_injective X.subtype_injective K
  refine ⟨I,?_,hIX,he.symm ▸ hK,?_⟩
  · rw [←map_subgroupOf_eq_of_le hLX]
    exact map_mono hLK
  · exact (normal_subgroupOf_iff_le_normalizer hIX).mp (he.symm ▸ hKn)

/-- Failure of diagonal normality leaves a strictly larger normal component. -/
theorem tensorPointResidual_strict_component_of_not_normal (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (hn : ¬ centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G)) :
    ∃ I : Subgroup G, m.tensorPointResidual v < I ∧
      I ≤ centralizer ({(v : G)} : Set G) ∧
      (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent ∧
      centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G) := by
  obtain ⟨I,hLI,hIX,hI,hIN⟩ := m.tensorPointResidual_containing_component v hv hs
  refine ⟨I,lt_of_le_of_ne hLI ?_,hIX,hI,hIN⟩
  intro he
  exact hn (he.symm ▸ hIN)

/-- A containing component lying inside M is the original point residual. -/
theorem tensorPointResidual_eq_of_component_le_maximal (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hI : (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent)
    (hIM : I ≤ D.maximalLocal) : m.tensorPointResidual v = I := by
  have ht : (⊤ : Subgroup I).IsCComponent := by
    simpa only [subgroupOf_self] using hI.subgroupOf_of_le le_rfl hIX
  have hB := m.tensorPointResidual_cComponent v hv hLI
    ((le_inf hIM hIX).trans (m.tensorPointResidual_normalized v))
  exact le_antisymm hLI (subgroupOf_eq_top.mp (hB.eq_of_le ht le_top))

include m in
/-- There is a full ambient Sylow centralizer inside M normalizing the
literal residual, containing the original Sylow point centralizer. -/
theorem tensorPoint_exists_sylow (v : D.fullModule) :
    ∃ R : Subgroup G,
      (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G) ≤ R ∧
      R ≤ D.maximalLocal ⊓ centralizer ({(v : G)} : Set G) ∧
      Chapter1.IsSylowIn 2 R (centralizer ({(v : G)} : Set G)) := by
  let X := centralizer ({(v : G)} : Set G)
  let Y := D.maximalLocal ⊓ X
  let S := (T : Subgroup G) ⊓ X
  have hSY : S ≤ Y := inf_le_inf (le_normalizer_componentOrbit L T) le_rfl
  have hp : IsPGroup 2 S := T.isPGroup'.to_le inf_le_left
  obtain ⟨P,hP⟩ := (hp.comap_subtype : IsPGroup 2 (S.subgroupOf Y)).exists_le_sylow
  let R := (P : Subgroup Y).map Y.subtype
  have hSR : S ≤ R := by
    rw [←map_subgroupOf_eq_of_le hSY]
    exact map_mono hP
  have hRY : R ≤ Y := map_subtype_le _
  have hJR : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ R :=
    (le_inf (sSup_le fun _ h => h.1)
      (m.thompson_centralizes_fullModule.trans
        (centralizer_le (Set.singleton_subset_iff.mpr v.property)))).trans hSR
  exact ⟨R,hSR,hRY,
    source_sylow_in_of_thompson_le D m.thompson_centralizes_fullModule R X hJR ⟨P,rfl⟩⟩

/-- The diagonal residual belongs to the local family at any ambient Sylow
point centralizer inside its normalizer. -/
theorem tensorPointResidual_mem_local_at (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {R : Subgroup G}
    (hs : Chapter1.IsSylowIn 2 R (centralizer ({(v : G)} : Set G)))
    (hvR : (v : G) ∈ R) (hRN : R ≤ normalizer (m.tensorPointResidual v : Set G)) :
    m.tensorPointResidual v ∈ Chapter1.L G R := by
  have hRX := (Chapter1.isSylowIn_iff.mp hs).2.1
  have hLX := m.tensorPointResidual_le_centralizer v
  refine ⟨m.tensorPointResidual_cComponent v hv le_sup_left
    (sup_le (m.tensorPointResidual v).le_normalizer hRN),
    hs.restrict le_sup_right (sup_le hLX hRX),?_⟩
  exact m.point_core_ne_bot v hv (mem_sup_right hvR) (sup_le hLX hRX)

/-- The source 1.2.4 entrance for every original nonsingular tensor vector;
the local Sylow choice and the ambient Sylow passage are both discharged. -/
theorem tensorPointResidual_containing_component_source (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    ∃ I : Subgroup G, m.tensorPointResidual v ≤ I ∧
      I ≤ centralizer ({(v : G)} : Set G) ∧
      (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent ∧
      centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G) := by
  let X := centralizer ({(v : G)} : Set G)
  obtain ⟨R,hTR,hRM,hSyl⟩ := m.tensorPoint_exists_sylow v
  have hRX : R ≤ X := hRM.trans inf_le_right
  have hRN := hRM.trans (m.tensorPointResidual_normalized v)
  have hvR : (v : G) ∈ R :=
    hTR ⟨m.fullModule_le_sylow v.property,mem_centralizer_singleton_iff.mpr rfl⟩
  have hvX : (v : G) ∈ X := mem_centralizer_singleton_iff.mpr rfl
  have hLX := m.tensorPointResidual_le_centralizer v
  have hcoreX := m.point_core_ne_bot v hv hvX le_rfl
  have hlocal := m.tensorPointResidual_mem_local_at v hv hSyl hvR hRN
  obtain ⟨P,hP⟩ := hSyl
  have hP' : (P : Subgroup X) = R.subgroupOf X := by
    apply Subgroup.map_injective X.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hRX]
  have hlocalX : (m.tensorPointResidual v).subgroupOf X ∈ Chapter1.L X (P : Subgroup X) := by
    rw [hP']
    exact (Chapter1.mem_LIn_iff_subgroupOf hRX hLX).mp ⟨hLX,hlocal⟩
  have hPL : (P : Subgroup X) ≤ normalizer ((m.tensorPointResidual v).subgroupOf X : Set X) := by
    rw [hP',←subgroupOf_normalizer_eq hLX]
    exact comap_mono hRN
  obtain ⟨K,⟨hK,hLK,hKn⟩,_⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk D.simpleQTKE hcoreX) P hlocalX hPL
  let I := K.map X.subtype
  have hIX : I ≤ X := map_subtype_le K
  have he : I.subgroupOf X = K := comap_map_eq_self_of_injective X.subtype_injective K
  refine ⟨I,?_,hIX,he.symm ▸ hK,?_⟩
  · rw [←map_subgroupOf_eq_of_le hLX]
    exact map_mono hLK
  · exact (normal_subgroupOf_iff_le_normalizer hIX).mp (he.symm ▸ hKn)

/-- Failure of source9.4.1 gives a strict normal containing component
outside M, with no additional Sylow assumption. -/
theorem tensorPointResidual_strict_component_source (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hn : ¬ centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G)) :
    ∃ I : Subgroup G, m.tensorPointResidual v < I ∧
      I ≤ centralizer ({(v : G)} : Set G) ∧
      (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent ∧
      centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G) ∧
      ¬ I ≤ D.maximalLocal := by
  obtain ⟨I,hLI,hIX,hI,hIN⟩ := m.tensorPointResidual_containing_component_source v hv
  have hne : m.tensorPointResidual v ≠ I := fun he => hn (he.symm ▸ hIN)
  exact ⟨I,lt_of_le_of_ne hLI hne,hIX,hI,hIN,
    fun hIM => hne (m.tensorPointResidual_eq_of_component_le_maximal v hv hLI hIX hI hIM)⟩


/-- The original full module induces an elementary automorphism group of
rank at least six on a normal containing point component. -/
theorem tensorPoint_containing_automorphism_rank (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G)) :
    6 ≤ primeRank 2 (MulAut I) := by
  let : IsElementaryAbelian 2 D.fullModule := m.fullModule_elementary
  have hVV : D.fullModule ≤ centralizer (D.fullModule : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hVX : D.fullModule ≤ centralizer ({(v : G)} : Set G) :=
    hVV.trans
      (centralizer_le (Set.singleton_subset_iff.mpr v.property))
  let f : D.fullModule →* MulAut I :=
    I.normalizerMonoidHom.comp (inclusion (hVX.trans hIN))
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hk : f.ker = (D.fullModule ⊓ centralizer (I : Set G)).subgroupOf D.fullModule := by
    ext x
    constructor
    · intro hx
      have hx' : inclusion (hVX.trans hIN) x ∈ I.normalizerMonoidHom.ker := hx
      rw [normalizerMonoidHom_ker] at hx'
      exact ⟨x.property,hx'⟩
    · intro hx
      change inclusion (hVX.trans hIN) x ∈ I.normalizerMonoidHom.ker
      rw [normalizerMonoidHom_ker]
      exact hx.2
  have hker : Nat.card f.ker ≤ 4 := by
    rw [hk,Nat.card_congr (subgroupOfEquivOfLe (show
      D.fullModule ⊓ centralizer (I : Set G) ≤ D.fullModule from inf_le_left)).toEquiv]
    exact m.tensorPoint_containing_fixed_card_le v hv hLI
  by_contra hn
  have hr : primeRank 2 (MulAut I) ≤ 5 := by omega
  have hsmall : Nat.card f.range ≤ 32 :=
    (primeRank_le_iff_elementary_card_le (MulAut I)).mp hr f.range inferInstance
  have htotal := f.ker.index_mul_card
  rw [index_ker,m.card_fullModule] at htotal
  have hbound := Nat.mul_le_mul hsmall hker
  rw [htotal] at hbound
  omega

/-- All initial source9.4.1 marks on the actual strict overcomponent.
The remaining source exclusion must rule out this marked configuration. -/
theorem tensorPointResidual_strict_component_marks (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    (hn : ¬ centralizer ({(v : G)} : Set G) ≤ normalizer (m.tensorPointResidual v : Set G)) :
    ∃ I : Subgroup G, m.tensorPointResidual v < I ∧
      I ≤ centralizer ({(v : G)} : Set G) ∧
      (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent ∧
      centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G) ∧
      ¬ I ≤ D.maximalLocal ∧
      Nat.card (D.fullModule ⊓ centralizer (I : Set G) : Subgroup G) ≤ 4 ∧
      6 ≤ primeRank 2 (MulAut I) := by
  obtain ⟨I,hLI,hIX,hI,hIN,hIM⟩ := m.tensorPointResidual_strict_component_source v hv hn
  exact ⟨I,hLI,hIX,hI,hIN,hIM,m.tensorPoint_containing_fixed_card_le v hv hLI.le,
    m.tensorPoint_containing_automorphism_rank v hv hLI.le hIN⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
