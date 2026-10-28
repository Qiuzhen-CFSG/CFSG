module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupFF
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OldComponentLocalConsumer
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel
public import Theory.GroupTheory.CComponent.RadicalKernel
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The original local A₅ image in the tensor overgroup action

The old residual moves its tensor plane, so its image in the faithful action
on the omega orbit is nontrivial. Its proper action kernel lies in its two-core,
preserving the literal A₅ quotient. The image is proper in the new residual
image because the old residual fixes the tensor line whereas the original
component moves it. Restricting the original full Sylow and mapping it through
the new residual's solvable action kernel preserves local C-component membership.

Source: Aschbacher–Smith 9.3.7, printed p.734. The original tensor consumer
retains the source 9.2.7 quotient, 9.3.2 Sylow, and 9.3.5 movement inputs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open ChapterB.InternalThompsonAction ChapterA.Section03
variable {H : Type*} [Group H] [Finite H]

theorem source_tensor_overgroup_local_a5_image
    (P : Sylow 2 H) (K B L U W : Subgroup H) [K.Normal] [W.Normal]
    (hK : K.IsCComponent) (hB : B ∈ localCComponents P)
    (hBK : B ≤ K) (hLK : L ≤ K)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (hUW : U ≤ W) (hBU : B ≤ centralizer (U : Set H))
    (hmoveB : ¬ B ≤ centralizer (componentOrbit U L : Set H))
    (hmoveL : ¬ L ≤ centralizer (U : Set H)) :
    let q := actionMk W
    let BI := (B.map q).subgroupOf (K.map q)
    BI < ⊤ ∧ Nonempty ((BI ⧸ pCore 2 BI) ≃* alternatingGroup (Fin 5)) ∧
      Group.IsSolvable (q.subgroupMap K).ker ∧
      ∃ R : Sylow 2 K,
        (R : Subgroup K) = (P : Subgroup H).subgroupOf K ∧
        BI ∈ localCComponents (R.mapSurjective (q.subgroupMap_surjective K)) := by
  let q := actionMk W
  let BI := (B.map q).subgroupOf (K.map q)
  let f := q.subgroupMap K
  have hBW : componentOrbit U L ≤ W :=
    iSup_conjugates_le_of_le_normalizer U L W hUW le_normalizer_of_normal
  have hkerU : q.ker ≤ centralizer (U : Set H) := by
    simpa only [q,actionMk,QuotientGroup.ker_mk'] using centralizer_le hUW
  have hBnonzero : B.map q ≠ ⊥ := by
    intro hz
    have hc := (Subgroup.map_eq_bot_iff B).mp hz
    have hc' : B ≤ centralizer (W : Set H) := by
      simpa only [q,actionMk,QuotientGroup.ker_mk'] using hc
    exact hmoveB (hc'.trans (centralizer_le hBW))
  have hproperImage : B.map q < K.map q := by
    refine lt_of_le_of_ne (map_mono hBK) ?_
    intro he
    have hpre : K ≤ B ⊔ q.ker := by
      rw [←comap_map_eq]
      exact map_le_iff_le_comap.mp he.ge
    exact hmoveL (hLK.trans (hpre.trans (sup_le hBU hkerU)))
  have hBIproper : BI < ⊤ := lt_top_iff_ne_top.mpr (fun he => by
    have hh := congrArg (Subgroup.map (K.map q).subtype) he
    rw [map_subgroupOf_eq_of_le (map_mono hBK),←MonoidHom.range_eq_map,range_subtype] at hh
    exact hproperImage.ne hh)
  have hBtop : (⊤ : Subgroup B).IsCComponent := by
    simpa only [subgroupOf_self] using hB.subgroupOf_of_le
      (show B ≤ B from le_rfl) (show B ≤ B ⊔ (P : Subgroup H) from le_sup_left)
  let := hBtop.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup B) ≃* B).toMonoidHom) topEquiv.surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := eB.isSimpleGroup
  let b := q.subgroupMap B
  have hbker : b.ker ≠ ⊤ := by
    intro he
    apply hBnonzero
    apply (Subgroup.eq_bot_iff_forall _).mpr
    rintro _ ⟨a,ha,rfl⟩
    have hm : (⟨a,ha⟩ : B) ∈ b.ker := he ▸ mem_top _
    exact congrArg Subtype.val (show b ⟨a,ha⟩ = 1 from hm)
  have hbcore : b.ker ≤ pCore 2 B := by
    rw [← PerfectCoreTwoExtension.radical_eq_core]
    exact kernel_le_solvableRadical_of_top_isCComponent hBtop b hbker
  have hb2 : IsPGroup 2 b.ker := pCore_isPGroup.of_injective
    (inclusion hbcore) (inclusion_injective hbcore)
  let eImage : (B.map q ⧸ pCore 2 (B.map q)) ≃* alternatingGroup (Fin 5) :=
    (b.pCoreQuotientEquiv (q.subgroupMap_surjective B) hb2).symm.trans eB
  let i : BI ≃* B.map q := subgroupOfEquivOfLe (map_mono hBK)
  let eBI : (BI ⧸ pCore 2 BI) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ i (pCore_map_iso 2 i)).trans eImage
  have hfk : f.ker ≠ ⊤ := by
    intro he
    apply hBnonzero
    apply eq_bot_iff.mpr
    intro x hx
    obtain ⟨a,ha,rfl⟩ := hx
    have hm : (⟨a,hBK ha⟩ : K) ∈ f.ker := he ▸ mem_top _
    exact congrArg Subtype.val (show f ⟨a,hBK ha⟩ = 1 from hm)
  let : Group.IsSolvable f.ker := hK.isSolvable_of_subnormal_lt_top
    (inferInstance : f.ker.Normal).isSubnormal hfk
  refine ⟨hBIproper,⟨eBI⟩,inferInstance,?_⟩
  obtain ⟨R,hR,hBR⟩ := SourceEmbeddings.exists_local_sylow_restriction P hB hBK
    (inferInstance : K.Normal).isSubnormal
  have hlocal := Chapter1.Section02.localCComponents_map_of_solvable_ker hBR f
  have himage : (B.subgroupOf K).map f = BI := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact mem_map.mpr ⟨a,ha,rfl⟩
    · rintro ⟨a,ha,hax⟩
      exact ⟨⟨a,hBK ha⟩,ha,Subtype.ext hax⟩
  refine ⟨R,hR,?_⟩
  simpa only [himage,Sylow.coe_mapSurjective] using hlocal

end CFSG.Quasithin.Chapter10

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB.InternalThompsonAction ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}

theorem old_residual_action_image_data (m : SourceA5TensorModel D e)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G))
      ((pResidual 2 H).map H.subtype ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))))
    (M₀ : Subgroup G) (hcore : pCore 2 M₀ ≠ ⊥)
    (hgen : M₀ = (L ⊔ (pResidual 2 H).map H.subtype) ⊔
      ((T : Subgroup G) ⊓ normalizer (L : Set G)))
    (hKU : (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorLine : Set G))
    (hmove : ¬ (pResidual 2 H).map H.subtype ≤ centralizer (m.tensorPlane : Set G))
    (W : Subgroup M₀) [W.Normal] (hUW : m.tensorLine.subgroupOf M₀ ≤ W) :
    let K := pResidual 2 M₀
    let q := actionMk W
    let BI := (((pResidual 2 H).map H.subtype).subgroupOf M₀).map q |>.subgroupOf (K.map q)
    BI < ⊤ ∧ Nonempty ((BI ⧸ pCore 2 BI) ≃* alternatingGroup (Fin 5)) ∧
      Group.IsSolvable (q.subgroupMap K).ker ∧
      ∃ R : Sylow 2 K,
        (R : Subgroup K) = (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf M₀).subgroupOf K ∧
        BI ∈ localCComponents (R.mapSurjective (q.subgroupMap_surjective K)) := by
  let B := (pResidual 2 H).map H.subtype
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hLH : L ≤ M₀ := hgen ▸ le_sup_of_le_left le_sup_left
  have hBH : B ≤ M₀ := hgen ▸ le_sup_of_le_left le_sup_right
  have hSH : S ≤ M₀ := hgen ▸ le_sup_right
  have hout : ¬ M₀ ≤ D.maximalLocal := by
    intro hh
    exact source_hstar_residual_not_le (le_normalizer_componentOrbit L T) hH (hBH.trans hh)
  have hUS : m.tensorLine ≤ S := by
    apply m.tensorLine_le_fullModule.trans
    rw [←m.module_eq]
    exact le_inf D.module_le_sylow
      (D.module_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hUH : m.tensorLine ≤ M₀ := hUS.trans hSH
  obtain ⟨hK,hLK,hBK,_⟩ := m.old_residual_component_product hn hH eK hSyl M₀ hcore hgen hKU hmove
  obtain ⟨P,hP⟩ := source_a5_local_outside_overgroup_sylow D e hn hcore hLH hSH hout
  have hPS : (P : Subgroup M₀) = S.subgroupOf M₀ := by
    apply map_injective M₀.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le hSH]
  have hBlocal : B.subgroupOf M₀ ∈ localCComponents P := by
    rw [hPS]
    exact SourceEmbeddings.local_restrict
      (m.old_residual_mem_local_at_stabilizer hn hH eK hSyl).1 hBH
  let b : B.subgroupOf M₀ ≃* B := subgroupOfEquivOfLe hBH
  let eB : (B.subgroupOf M₀ ⧸ pCore 2 (B.subgroupOf M₀)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans eK
  have hBU : B.subgroupOf M₀ ≤ centralizer (m.tensorLine.subgroupOf M₀ : Set M₀) := by
    intro b hb u hu
    exact Subtype.ext (hKU hb u hu)
  have horbit : (componentOrbit (m.tensorLine.subgroupOf M₀) (L.subgroupOf M₀)).map M₀.subtype =
      m.tensorPlane := by
    rw [map_componentOrbit,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hLH]
    rfl
  have hmoveB : ¬ B.subgroupOf M₀ ≤ centralizer
      (componentOrbit (m.tensorLine.subgroupOf M₀) (L.subgroupOf M₀) : Set M₀) := by
    intro hc
    apply hmove
    intro b hb w hw
    obtain ⟨w',hw',rfl⟩ := horbit ▸ hw
    exact congrArg M₀.subtype (hc (show (⟨b,hBH hb⟩ : M₀) ∈ B.subgroupOf M₀ from hb) w' hw')
  have hmoveL : ¬ L.subgroupOf M₀ ≤ centralizer (m.tensorLine.subgroupOf M₀ : Set M₀) := by
    intro hc
    have hc' : m.tensorLine ≤ centralizer (L : Set G) := by
      intro u hu l hl
      exact (congrArg M₀.subtype
        (hc (show (⟨l,hLH hl⟩ : M₀) ∈ L.subgroupOf M₀ from hl)
          ⟨u,hUH hu⟩ hu)).symm
    exact m.tensorLine_ne_bot (le_bot_iff.mp
      (m.fullModule_component_fixed_eq_bot ▸ (le_inf m.tensorLine_le_fullModule hc')))
  obtain ⟨hp,he,hker,R,hR,hlocal⟩ := source_tensor_overgroup_local_a5_image P
    (pResidual 2 M₀) (B.subgroupOf M₀) (L.subgroupOf M₀) (m.tensorLine.subgroupOf M₀) W
    hK hBlocal hBK hLK eB hUW hBU hmoveB hmoveL
  exact ⟨hp,he,hker,R,hR.trans (congrArg (fun X : Subgroup M₀ => X.subgroupOf (pResidual 2 M₀)) hPS),hlocal⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
