module
public import CFSG.Quasithin.Chapter10.SourceA5PointActionMarking
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.CComponent.RadicalKernel

/-!
# The original A5 section in the point action

The smaller component has a nonzero image in the actual point action.
Its action kernel is therefore a proper normal subgroup of a C-component,
hence solvable. Since the original perfect component has simple quotient
A5 by its two-core, that kernel is a two-group and the actual image retains
the original A5 two-core quotient. No centralization by the original
two-core is assumed. Source: Aschbacher–Smith 10.2.9, printed p.751.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterB.InternalThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The smaller image retains the original A5 two-core quotient. Its actual
kernel is proved to be a two-group, rather than assuming that O2(L) fixes VI. -/
theorem source_a5_point_small_image_twoCore
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    {v : G} (I : Subgroup G) (hLI : L ≤ I)
    (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hspan : ⁅D.fullModule,L⁆ ≤ conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := I ⊔ S
    let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)) I).subgroupOf H
    letI := hr.normal
    let K := L.subgroupOf H
    IsPGroup 2 ((actionMk U).subgroupMap K).ker ∧
      Nonempty (((K.map (actionMk U)) ⧸ pCore 2 (K.map (actionMk U))) ≃*
        alternatingGroup (Fin 5)) := by
  let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ S
  let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)) I).subgroupOf H
  let := hr.normal
  let K := L.subgroupOf H
  let f := (actionMk U).subgroupMap K
  have hLH : L ≤ H := hLI.trans le_sup_left
  let k : K ≃* L := subgroupOfEquivOfLe hLH
  have hL : (⊤ : Subgroup L).IsCComponent := by
    simpa only [subgroupOf_self] using D.maximal.1.1.subgroupOf_of_le
      (show L ≤ L from le_rfl) (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
  have hK : (⊤ : Subgroup K).IsCComponent := by
    simpa only [map_top_of_surjective k.symm.toMonoidHom k.symm.surjective] using hL.map_equiv k.symm
  let := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup K) ≃* K).toMonoidHom) topEquiv.surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ k (pCore_map_iso 2 k)).trans e
  let : IsSimpleGroup (K ⧸ pCore 2 K) := eK.isSimpleGroup
  have hproper : f.ker ≠ ⊤ := by
    intro he
    have hz : K.map (actionMk U) = ⊥ := by
      apply eq_bot_iff.mpr
      rintro _ ⟨a,ha,rfl⟩
      have hm : (⟨a,ha⟩ : K) ∈ f.ker := he ▸ mem_top _
      exact congrArg Subtype.val (show f ⟨a,ha⟩ = 1 from hm)
    exact (source_a5_point_action_marking D I hLI hout hCW hspan hr).2.2.1 hz
  have hkle : f.ker ≤ pCore 2 K := by
    rw [← PerfectCoreTwoExtension.radical_eq_core]
    exact kernel_le_solvableRadical_of_top_isCComponent hK f hproper
  have hk : IsPGroup 2 f.ker := pCore_isPGroup.of_injective
    (inclusion hkle) (inclusion_injective hkle)
  exact ⟨hk,⟨(f.pCoreQuotientEquiv ((actionMk U).subgroupMap_surjective K) hk).symm.trans eK⟩⟩
/-- The full containing component has a solvable action kernel. This is the
separate global-kernel premise in the marked A7 local-image theorem. -/
theorem source_a5_point_component_action_kernel_solvable
    {v : G} (I : Subgroup G) (hLI : L ≤ I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hout : ¬ I ≤ D.maximalLocal)
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hspan : ⁅D.fullModule,L⁆ ≤ conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I)
    (hr : IsPReduced 2 ((conjugateSpanBy
      (⁅D.fullModule,L⁆ ⊓ centralizer
        ((T : Subgroup G) ⊓ centralizer ({v} : Set G) : Set G)) I).subgroupOf
          (I ⊔ ((T : Subgroup G) ⊓ centralizer ({v} : Set G))))) :
    let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let H := I ⊔ S
    let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)) I).subgroupOf H
    letI := hr.normal
    Group.IsSolvable ((actionMk U).subgroupMap (I.subgroupOf H)).ker := by
  let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let H := I ⊔ S
  let U := (conjugateSpanBy (⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)) I).subgroupOf H
  let := hr.normal
  let K := I.subgroupOf H
  let f := (actionMk U).subgroupMap K
  have hK : K.IsCComponent := hI.subgroupOf_of_le le_sup_left (sup_le hIX inf_le_right)
  have hnonzero : K.map (actionMk U) ≠ ⊥ := by
    intro hz
    apply (source_a5_point_action_marking D I hLI hout hCW hspan hr).2.2.1
    exact eq_bot_iff.mpr (hz ▸ (map_mono (comap_mono hLI)))
  have hproper : f.ker ≠ ⊤ := by
    intro he
    apply hnonzero
    apply (Subgroup.eq_bot_iff_forall _).mpr
    rintro _ ⟨a,ha,rfl⟩
    have hm : (⟨a,ha⟩ : K) ∈ f.ker := he ▸ mem_top _
    exact congrArg Subtype.val (show f ⟨a,ha⟩ = 1 from hm)
  exact hK.isSolvable_of_subnormal_lt_top (inferInstance : f.ker.Normal).isSubnormal hproper

end CFSG.Quasithin.Chapter10
