module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearContainment
public import CFSG.Quasithin.ChapterB.Section02.DoubledPointBaumann
public import Stellmacher.BaumannMap
public import Theory.ElementaryAbelian.Injective

/-!
# The doubled component's reciprocal Baumann subgroup

The original fixed-line generator is a nonzero point of the moved orbit,
up to a component-fixed factor. Restricting the original Sylow subgroup to K
makes that point Sylow-fixed. The doubled-natural point theorem therefore
identifies both J(O₂(K ∩ N_G(L))) and Baum(O₂(K ∩ N_G(L))) with the
corresponding subgroups of O₂(K). All transports retain the actual K action,
its two-core quotient and the five-dimensional marking of the original L.

In particular K normalizes this reciprocal Baumann subgroup, so its ambient
normalizer escapes N_G(L). This establishes the component-side point-radical
calculation used in 13.4.10(4). The source radical O₂(L₁T) is larger in general;
its comparison with this reciprocal radical is not assumed or asserted here.
That comparison and the augmentation form of 13.2.2(7), the remaining row
exclusions and the comparison/commutator/graph assembly remain with
qt-d-1341-nonsolvable-source. Earlier-source inputs retain their existing
producers and final discharge with qt-d-1341-fixed-core-source. Universal
nonsolvability is still required separately at both escaping weights.

Source: Aschbacher–Smith 13.4.10(2–4), printed pp.908–909, and
13.2.2(7), printed pp.877–878.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

private theorem component_sylow_in_original
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G)) :
    ∃ S : Sylow 2 K, (S : Subgroup K).map K.subtype ≤ (T : Subgroup G) := by
  let X := K ⊔ (T : Subgroup G)
  let N := K.subgroupOf X
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  obtain ⟨Q,hQ⟩ := (T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)).exists_sylow_map_eq_inf_of_normal N
  let e : N ≃* K := subgroupOfEquivOfLe (show K ≤ X from le_sup_left)
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((Q : Subgroup N).map e.toMonoidHom).map K.subtype ≤ _
  have he : ((Q : Subgroup N).map e.toMonoidHom).map K.subtype =
      ((Q : Subgroup N).map N.subtype).map X.subtype := by
    rw [map_map,map_map]
    rfl
  rw [he,hQ]
  exact (map_mono inf_le_left).trans (by
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ X from le_sup_right)])

/-- On the original selected component the reciprocal point centralizer has
exactly the Baumann subgroup of O₂(K). No shortness or minimality is assumed. -/
theorem doubled_reciprocal_baumann
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (e : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ : Subgroup G) ≃*
      Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector))
    (he : let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
      ∀ (k : K) (v : U), (e (k • v)).toAdd =
        (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
          (eK (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) :
    elementaryAbelianMaxJ ((K ⊓ normalizer (L : Set G)).pCoreIn 2) =
        elementaryAbelianMaxJ (K.pCoreIn 2) ∧
      ChapterB.baumann ((K ⊓ normalizer (L : Set G)).pCoreIn 2) =
        ChapterB.baumann (K.pCoreIn 2) ∧
      ¬ normalizer (ChapterB.baumann ((K ⊓ normalizer (L : Set G)).pCoreIn 2) : Set G) ≤
        normalizer (L : Set G) := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let X := K ⊔ (T : Subgroup G)
  have hUK : U ≤ K := (component_moved_le_twoCore h₀ hzT hz1 hKz hTK).trans (pCoreIn_le 2 K)
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  let := hred.elementary
  let : IsElementaryAbelian 2 U := by
    have hh : IsElementaryAbelian 2 ((U.subgroupOf X).map X.subtype) := IsElementaryAbelian.map _
    rwa [map_subgroupOf_eq_of_le (hUK.trans le_sup_left)] at hh
  let Ui := U.subgroupOf K
  let : Ui.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_right _ _)
  let : IsElementaryAbelian 2 Ui := IsElementaryAbelian.comap_of_injective K.subtype K.subtype_injective U
  let ei : Ui ≃* U := subgroupOfEquivOfLe hUK
  let eU := ei.trans e
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eK.injective,QuotientGroup.ker_mk']
  have heU (k : K) (v : Ui) : (eU (MulAut.conjNormal k v)).toAdd =
      (BinaryLinearThree.W.prod BinaryLinearThree.W) (q k) (eU v).toAdd := by
    change (e (ei (MulAut.conjNormal k v))).toAdd = _
    have hei : ei (MulAut.conjNormal k v) =
        U.normalizerMonoidHom ⟨k.val,normalizer_commutator_ge_right _ _ k.property⟩ (ei v) :=
      Subtype.ext rfl
    rw [hei]
    exact he k (ei v)
  obtain ⟨w,hw,hC⟩ := component_fixed_generator_point h₀ h structural m hzT hz1 hKz hTK hKM
  let wi : Ui := ei.symm w
  obtain ⟨S,hS⟩ := component_sylow_in_original hTK
  have hSw : (S : Subgroup K) ≤ centralizer ({wi.val} : Set K) := by
    intro k hkS
    have hkT : k.val ∈ (T : Subgroup G) := hS (mem_map_of_mem K.subtype hkS)
    have hkd : k.val ∈ centralizer ({m.constant.val} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      exact (mem_omegaOneCenterAmbient_iff _ _).mp
        (m.constant_mem_central_four h structural).2 |>.2.2 k.val hkT
    have hkw := (hC.le ⟨k.property,hkd⟩).2
    exact mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp hkw))
  have hwi : wi ≠ 1 := fun hh => hw (by simpa [wi] using congrArg ei hh)
  have hb := ChapterB.doubled_point_baumann Ui q hq hk eU heU wi hwi S hSw
  let C := centralizer ({wi.val} : Set K)
  have hCm : C.map K.subtype = K ⊓ normalizer (L : Set G) := by
    rw [←fixed_generator_centralizer h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh)),hC]
    ext k
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩
    · rintro ⟨hk,hc⟩
      exact ⟨⟨k,hk⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  have hm := congrArg (fun A : Subgroup K => A.map K.subtype) hb.2.1
  change (ChapterB.baumann (C.pCoreIn 2)).map K.subtype = (ChapterB.baumann (pCore 2 K)).map K.subtype at hm
  dsimp only [ChapterB.baumann,ChapterB.thompsonAlpha] at hm
  rw [baumann_map_injective K.subtype K.subtype_injective,
    baumann_map_injective K.subtype K.subtype_injective,
    map_pCoreIn_of_injective 2 C K.subtype K.subtype_injective,hCm] at hm
  have hj := congrArg (fun A : Subgroup K => A.map K.subtype) hb.1
  change (elementaryAbelianMaxJ (C.pCoreIn 2)).map K.subtype =
    (elementaryAbelianMaxJ (pCore 2 K)).map K.subtype at hj
  rw [←elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective,
    ←elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective,
    map_pCoreIn_of_injective 2 C K.subtype K.subtype_injective,hCm] at hj
  change ChapterB.baumann ((K ⊓ normalizer (L : Set G)).pCoreIn 2) =
    ChapterB.baumann (K.pCoreIn 2) at hm
  refine ⟨hj,hm,?_⟩
  rw [hm]
  intro hbound
  exact hKM ((K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))).trans
      ((normalizer_le_normalizer_baumann (K.pCoreIn 2)).trans hbound))
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
