module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixAutomizer
public import Theory.GroupTheory.PResidual.NormalizedImageCover
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# Lifting the original component from its full module image

Inside the unchanged KT, the two-residual is K. The prescribed hexacode
chart identifies the kernel on K with its actual two-core. If that core
normalizes an actual subgroup inducing the entire automizer, residual
generation and a normalized two-group supplement put K in that subgroup.
The full ambient action kernel is unrestricted.

Source: the argument of G.2.3 used after Aschbacher--Smith12.7.18,
printed pp.333 and845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Lift a full original action image through only the actual K-kernel. -/
theorem original_tripleSix_component_le_of_full_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (I : Subgroup G) (hI : I ≤ K ⊔ (T : Subgroup G))
    (hQI : K.pCoreIn 2 ≤ normalizer (I : Set G))
    (himage : inducedAutomizer U I = ⊤) : K ≤ I := by
  let M := K ⊔ (T : Subgroup G)
  let A := K.subgroupOf M
  let B := I.subgroupOf M
  let Q := (K.pCoreIn 2).subgroupOf M
  have hKN : K ≤ normalizer (U : Set G) := D.normalizes
  have hTN : (T : Subgroup G) ≤ normalizer (U : Set G) :=
    ((structural K h).2.2 U D).1
  have hMN : M ≤ normalizer (U : Set G) := sup_le hKN hTN
  let α := U.normalizerMonoidHom.rangeRestrict.comp (inclusion hMN)
  obtain ⟨f0, _, hfk, _, _⟩ := original_tripleSix_full_automizer h structural D a
  let f := f0.comp α
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer D.sylow_normalizes_component)
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ M from le_sup_left)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ M from le_sup_left)).symm.surjective
  have hpA : IsPPerfect 2 A := by
    intro J hJ hq
    let := hJ
    by_contra hne
    let : Nontrivial (A ⧸ J) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (A ⧸ J) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective J)
    let : Group.IsNilpotent (A ⧸ J) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (A ⧸ J) inferInstance
  have hgen : A ⊔ (T : Subgroup G).subgroupOf M = ⊤ := by
    rw [← subgroupOf_sup (show K ≤ M from le_sup_left)
      (show (T : Subgroup G) ≤ M from le_sup_right)]
    exact subgroupOf_self M
  have hres : pResidual 2 M = A := pResidual_eq_of_isPPerfect_sup A _ hpA
    T.isPGroup'.comap_subtype hgen
  have hker : pResidual 2 M ⊓ f.ker ≤ Q := by
    rintro x ⟨hx, hxf⟩
    rw [hres] at hx
    let k : K := ⟨x.val, hx⟩
    have he : f x = (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val := hfk k
    have hq : QuotientGroup.mk' (pCore 2 K) k = 1 := by
      apply a.groupEquiv.injective
      apply Subtype.ext
      exact he.symm.trans (hxf.trans (congrArg Subtype.val (map_one a.groupEquiv)).symm)
    exact mem_map_of_mem K.subtype ((QuotientGroup.eq_one_iff k).mp hq)
  have hcover : (pResidual 2 M).map f ≤ B.map f := by
    rintro _ ⟨x, _, rfl⟩
    have hx : α x ∈ inducedAutomizer U I := himage.symm ▸ mem_top _
    obtain ⟨n, hn, hnx⟩ := hx
    let y : M := ⟨n.val, hI hn⟩
    refine ⟨y, hn, ?_⟩
    exact congrArg f0 hnx
  have hn : Q ≤ normalizer (B : Set M) := by
    intro x hx
    exact (le_normalizer_comap M.subtype) (hQI hx)
  have hle := pResidual_le_of_normalized_image_cover f B Q
    (isPGroup_pCoreIn 2 K).comap_subtype hn hker hcover
  rw [hres] at hle
  intro x hx
  exact hle (show (⟨x, mem_sup_left hx⟩ : M) ∈ A from hx)

end CFSG.Quasithin.Chapter12.Section07
