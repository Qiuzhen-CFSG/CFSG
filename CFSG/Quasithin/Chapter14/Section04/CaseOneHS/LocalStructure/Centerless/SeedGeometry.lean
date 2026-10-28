module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.FaithfulComponent
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Geometry
public import Theory.Representation.NormalElementaryQuotient.OriginalAction
public import Theory.Representation.ConjugationFixedQuotient

/-!
# The marked central hyperplane in the seed exclusion

For the original flag, Z(U) intersect U^g is centralized by Z(U)^g.
Its index in Z(U) equals the order of the literal Z(U)^g image on
U/Z(U): conjugation carries the central intersection to that action's
kernel, using the original parabolic-center identity. An image of order
two therefore moves at most one dimension on any normal elementary
subgroup of H contained in Z(U), including the reduced test module VH.

These are the shared transvection bounds for both branches of 14.3.25.
They retain the original plane conjugator, action map and Sylow geometry;
no centerlessness or later natural S₅ recognition is assumed.

Source: Aschbacher--Smith, 12.8.10(6) and 14.3.25, printed pp.853,1001.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original center intersection and exact dotted-image index. -/
theorem source_center_axis (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (F.ZU ⊓ conjugate F.U g).relIndex F.ZU =
      Nat.card (F.uhatAction.comp
        (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range ∧
    F.ZU ⊓ conjugate F.U g ≤ centralizer (conjugate F.ZU g : Set G) := by
  let := chosen.elementary
  let f := F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)
  obtain ⟨hi,haxis,hker⟩ := source_center_intersections d earlier hq chosen structural alternatives
    F hne g hgP hgH
  have ha := (source_parabolic_action d earlier hq chosen structural alternatives F hne g hgP hgH).2.1
  have hk : f.ker = (F.U).subgroupOf (conjugate F.ZU g) := by
    ext z
    change F.uhatAction (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP z) = 1 ↔ (z:G) ∈ F.U
    constructor
    · intro he
      have hz : (z:G) ∈ F.xHatKernel g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) :=
        (F.mem_xHatKernel _ _ _).mpr ⟨F.conjugate_ZU_le_X g z.property,
          (F.mem_uhatAction_ker_iff _).mp he⟩
      rw [ha] at hz
      exact hz.1.1
    · intro hz
      have h := higherRankHypothesis d earlier hq chosen
      have hc := (F.localKernel_commutator_squares d.qtke L
        (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
        (h.sylow_normalizes structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
        (h.flag_escape F alternatives)).1
      exact (F.mem_uhatAction_ker_iff _).mpr fun u hu =>
        F.point_le_ZU (by decide) (hc (commutator_mem_commutator hz hu))
  have hD : g ∈ normalizer (Chapter12.Section08.centerIn (F.I₂ L) : Set G) :=
    (normalizer_le_normalizer_characteristic_image (F.I₂ L) (center (F.I₂ L)))
      (le_normalizer_conjugateSpanBy F.U (F.P L) hgP)
  have hconj : conjugate (F.ZU ⊓ conjugate F.U g) g = conjugate F.ZU g ⊓ F.U := by
    rw [haxis, show conjugate (Chapter12.Section08.centerIn (F.I₂ L) ⊔ F.Vi 1) g =
      conjugate (Chapter12.Section08.centerIn (F.I₂ L)) g ⊔ conjugate (F.Vi 1) g from map_sup _ _ _,
      (conjugate_eq_iff _ _).mpr hD, hker]
  refine ⟨?_, ?_⟩
  · rw [← index_ker, hk]
    change _ = (F.U).relIndex (conjugate F.ZU g)
    rw [← inf_relIndex_left (conjugate F.ZU g) F.U, ← hconj]
    exact (relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective).symm
  · apply inf_le_right.trans
    apply le_centralizer_iff.mp
    change conjugate (Chapter12.Section08.centerIn F.U) g ≤ _
    rw [← centerIn_conjugate]
    rintro z ⟨c,hc,rfl⟩ u hu
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨u,hu⟩)

/-- The original conjugate-center actor has rank at most one on any elementary
normal subgroup lying in the center, when its dotted image has order two. -/
theorem source_seed_center_displacement (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hcard : Nat.card (F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range = 2)
    (A : Subgroup F.H) [A.Normal] [IsElementaryAbelian 2 A]
    (hAZ : A.map F.H.subtype ≤ F.ZU)
    (a : F.H) (ha : (a:G) ∈ conjugate F.ZU g) :
    Module.finrank (ZMod 2)
      (NormalElementaryQuotient.originalAction A a - LinearMap.id).range ≤ 1 := by
  obtain ⟨hi,hc⟩ := source_center_axis d earlier hq chosen structural alternatives F hne g hgP hgH
  rw [hcard] at hi
  let C := centralizer ({(a:G)} : Set G)
  have haxis : F.ZU ⊓ conjugate F.U g ≤ C := by
    intro z hz
    exact mem_centralizer_singleton_iff.mpr (hc hz a ha).symm
  have hidx : C.relIndex (A.map F.H.subtype) ≤ 2 := by
    exact (relIndex_le_of_le_right (H := C) hAZ (show C.relIndex F.ZU ≠ 0 from index_ne_zero_of_finite)).trans
      ((relIndex_le_of_le_left (L := F.ZU) haxis (by rw [hi]; decide)).trans hi.le)
  have he : centralizer (zpowers a : Set F.H) = C.comap F.H.subtype := by
    rw [zpowers_eq_closure, centralizer_closure]
    ext x
    simp only [mem_centralizer_singleton_iff, mem_comap, C]
    exact Subtype.ext_iff
  have hb := NormalElementaryQuotient.original_fixed_index A (zpowers a)
  rw [inf_relIndex_left, he, relIndex_comap] at hb
  rw [hb] at hidx
  have hn : fixedCodim (NormalElementaryQuotient.originalAction A) (zpowers a) ≤ 1 := by
    have hp : 2 ^ fixedCodim (NormalElementaryQuotient.originalAction A) (zpowers a) ≤ 2 ^ 1 := by
      simpa using hidx
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
  rwa [fixedCodim_zpowers_eq_displacement_rank] at hn

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
