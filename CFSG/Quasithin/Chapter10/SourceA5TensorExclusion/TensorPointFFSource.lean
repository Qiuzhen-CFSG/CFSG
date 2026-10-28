module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointNormalitySource
public import CFSG.Quasithin.Chapter1.Section02.ComponentDichotomy
public import Theory.GroupTheory.ReducedNormal.CentralSeedClosure
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# The exact Sylow-center orbit in the tensor point component

The original central involution in the diagonal moved subgroup gives the
nonquasisimple case of source 1.2.11 on I C_T(v). The point v supplies the
nontrivial two-core and its Sylow-centralizer bound; two-perfectness of the
literal diagonal residual supplies the relative residual in 1.2.11.

In characteristic two the actual orbit U=⟨Ω₁Z(T)^I⟩ is two-reduced.
The point-Sylow supplement fixes the seed, so it has the same orbit as I.
The source Sylow placement and concrete diagonal commutator mark remain
explicit. The later FF/cohomology image equality is a separate argument.

Source: Aschbacher--Smith 9.4.1, printed p.735, using 1.2.11 and B.2.14.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The diagonal moved subgroup is generated again by its commutators
with the literal two-perfect point residual. -/
theorem tensorPoint_moved_idempotent (v : D.fullModule) :
    ⁅⁅D.fullModule,m.tensorPointResidual v⁆,m.tensorPointResidual v⁆ =
      ⁅D.fullModule,m.tensorPointResidual v⁆ :=
  commutator_isPPerfect_idempotent _ _ (m.tensorPointResidual_isPPerfect v)
    (T.isPGroup'.to_le m.fullModule_le_sylow)
    ((m.tensorPointResidual_le_orbit v).trans m.sectionData.normalized)

include m in
/-- The original Sylow-center orbit is reduced in the characteristic-two
point-component join; the point Sylow does not enlarge the seed orbit. -/
theorem tensorPoint_centerOrbit_reduced (v : D.fullModule)
    {I : Subgroup G}
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (hs : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))))
    (hchar : I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) ∈ Chapter1.He G) :
    IsPReduced 2 ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I).subgroupOf
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let R := (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)
  let H := I ⊔ R
  have hZT : Z ≤ (T : Subgroup G) := fun _ hz =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZC : Z ≤ centralizer (T : Set G) := fun _ hz =>
    ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have hZR : Z ≤ R := by
    intro z hz
    refine ⟨hZT hz,mem_centralizer_singleton_iff.mpr ?_⟩
    exact (hZC hz v (m.fullModule_le_sylow v.property)).symm
  have hZH : Z ≤ H := hZR.trans le_sup_right
  have hRZ : R ≤ normalizer (Z : Set G) :=
    (inf_le_left.trans (le_centralizer_iff.mp hZC)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hRI : R ≤ normalizer (I : Set G) := inf_le_right.trans hIN
  have he : conjugateSpanBy Z H = conjugateSpanBy Z I :=
    conjugateSpanBy_sup_of_normalizes_seed Z I R hRZ hRI
  obtain ⟨P,hP⟩ := hs
  change (P : Subgroup H).map H.subtype = R at hP
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 (Z.subgroupOf H) := IsElementaryAbelian.subgroupOf hZH
  have hZP : Z.subgroupOf H ≤ (P : Subgroup H) := by
    intro z hz
    have hm : (z : G) ∈ (P : Subgroup H).map H.subtype := hP.symm ▸ hZR hz
    obtain ⟨a,ha,he⟩ := hm
    exact H.subtype_injective he ▸ ha
  have hc : Z.subgroupOf H ≤ centralizer (P : Set H) := by
    intro z hz p hp
    apply Subtype.ext
    have hpR : (p : G) ∈ R := hP ▸ mem_map_of_mem H.subtype hp
    exact hZC hz p hpR.1
  have hr := centralSeed_normalClosure_reduced P (Z.subgroupOf H)
    hZP hc (Chapter1.mem_He_iff.mp hchar)
  rwa [normalClosure_subgroupOf_eq_conjugateSpanBy Z H hZH,he] at hr

end CFSG.Quasithin.Chapter10.SourceA5TensorModel

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- Source 1.2.11 on the original nonquasisimple containing component.
The displayed elementary commutator is the concrete diagonal geometry mark. -/
theorem tensorPoint_join_mem_He_of_commutator (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hI : (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent)
    (hq : ¬ IsQuasisimple I)
    (hs : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAL : A ≤ m.tensorPointResidual v)
    (hLA : m.tensorPointResidual v ≤ normalizer (A : Set G))
    (z : G) (hz : orderOf z = 2)
    (hzt : z ∈ (T : Subgroup G))
    (hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hzm : z ∈ ⁅A,m.tensorPointResidual v⁆) :
    I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) ∈ Chapter1.He G := by
  let X := centralizer ({(v : G)} : Set G)
  let R := (T : Subgroup G) ⊓ X
  let H := I ⊔ R
  have hHX : H ≤ X := sup_le hIX inf_le_right
  have hLH : m.tensorPointResidual v ≤ H := hLI.trans le_sup_left
  have hAH : A ≤ H := hAL.trans hLH
  have hTH : (T : Subgroup G) ⊓ H = R :=
    le_antisymm (inf_le_inf le_rfl hHX) (le_inf inf_le_left le_sup_right)
  have hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ H) H := by
    rw [hTH]
    exact (m.tensor_centralizer_sylow v.property hs).restrict le_sup_right hHX
  have hvH : (v : G) ∈ H :=
    mem_sup_right ⟨m.fullModule_le_sylow v.property,mem_centralizer_singleton_iff.mpr rfl⟩
  have hp : IsPGroup 2 (zpowers (v : G)) :=
    T.isPGroup'.to_le (zpowers_le.mpr (m.fullModule_le_sylow v.property))
  have hn : H ≤ normalizer (zpowers (v : G) : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [zpowers_eq_closure,centralizer_closure]
    exact hHX
  have hvQ : (v : G) ∈ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes hp (zpowers_le.mpr hvH) hn (mem_zpowers _)
  have hH : H ∈ Chapter1.H G := by
    intro he
    exact m.tensorPoint_ne_one v hv (mem_bot.mp (he ▸ hvQ))
  have hIC : I ∈ Chapter1.cComponentsIn H :=
    ⟨le_sup_left,hI.subgroupOf_of_le le_sup_left hHX⟩
  have hzL : z ∈ m.tensorPointResidual v :=
    ((commutator_mono hAL le_rfl).trans (commutator_le_self _)) hzm
  have hsource : ∃ B : Subgroup G, B ≤ H ∧ IsElementaryAbelian 2 B ∧
      z ∈ ⁅B,(pResidual 2 (H ⊓ normalizer (B : Set G) : Subgroup G)).map
        (H ⊓ normalizer (B : Set G)).subtype⁆ := by
    refine ⟨A,hAH,hA,?_⟩
    let J := H ⊓ normalizer (A : Set G)
    have hLJ : m.tensorPointResidual v ≤ J := le_inf hLH hLA
    let f : (m.tensorPointResidual v).subgroupOf J ≃* m.tensorPointResidual v :=
      subgroupOfEquivOfLe hLJ
    have hpL : IsPPerfect 2 ((m.tensorPointResidual v).subgroupOf J) :=
      (m.tensorPointResidual_isPPerfect v).of_surjective f.symm.toMonoidHom f.symm.surjective
    have hle : m.tensorPointResidual v ≤ (pResidual 2 J).map J.subtype := by
      rw [←map_subgroupOf_eq_of_le hLJ]
      exact map_mono (le_pResidual_of_isPPerfect _ hpL)
    exact commutator_mono le_rfl hle hzm
  have hCT : (T : Subgroup G) ⊓ centralizer (H.pCoreIn 2 : Set G) ≤
      (T : Subgroup G) ⊓ H := by
    rw [hTH]
    intro t ht
    exact ⟨ht.1,mem_centralizer_singleton_iff.mpr (ht.2 v hvQ).symm⟩
  exact (Chapter1.lemma_1_2_11_involution D.simpleQTKE T H I z hH hSyl hIC hz
    (hLI hzL) ⟨hzt,hLH hzL⟩ hzc hsource hCT).resolve_left hq

/-- The nonquasisimple source branch constructs the literal reduced module
U=⟨Ω₁Z(T)^I⟩ from the original Sylow placement and diagonal commutator. -/
theorem tensorPoint_centerOrbit_reduced_of_commutator (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I)
    (hIX : I ≤ centralizer ({(v : G)} : Set G))
    (hI : (I.subgroupOf (centralizer ({(v : G)} : Set G))).IsCComponent)
    (hIN : centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G))
    (hq : ¬ IsQuasisimple I)
    (hs : Chapter1.IsSylowIn 2
      ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G))
      (D.maximalLocal ⊓ centralizer ({(v : G)} : Set G)))
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAL : A ≤ m.tensorPointResidual v)
    (hLA : m.tensorPointResidual v ≤ normalizer (A : Set G))
    (z : G) (hz : orderOf z = 2)
    (hzt : z ∈ (T : Subgroup G))
    (hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hzm : z ∈ ⁅A,m.tensorPointResidual v⁆) :
    IsPReduced 2 ((conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) I).subgroupOf
      (I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)))) := by
  have hHe := m.tensorPoint_join_mem_He_of_commutator v hv hLI hIX hI hq hs
    A hA hAL hLA z hz hzt hzc hzm
  have hSyl := (m.tensor_centralizer_sylow v.property hs).restrict
    (show (T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G) ≤
      I ⊔ ((T : Subgroup G) ⊓ centralizer ({(v : G)} : Set G)) from le_sup_right)
    (sup_le hIX inf_le_right)
  exact m.tensorPoint_centerOrbit_reduced v hIN hSyl hHe

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
