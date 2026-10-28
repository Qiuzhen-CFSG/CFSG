module

public import CFSG.Quasithin.Chapter10.SourceA5PointLocalMathieu
public import Theory.Mathieu.M22.Properties.LocalA5Shape

/-!
# The M22 point alternative from the original local hypotheses

The prescribed quotient Sylow normalizes the literal central image of L.
Native M22 involution centralizers and the faithful Sylow action on A5 force
its two-core to be elementary of order sixteen. The proved local placement
then supplies the original quasisimple marking, and the existing dispatcher
returns the point-component alternative. This removes both independent
core-shape hypotheses while retaining the same component, quotient and
original moved subgroup.

Source: Aschbacher--Smith A.3.14(6) and 10.2.9, printed pp.49 and 750--751.
-/

public section
open Subgroup Theory.GroupTheory
open Sporadic.Mathieu MathieuCode Sporadic.Mathieu.M22ChapterH
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] {L I : Subgroup G}

/-- The native shape theorem applies to the literal central image and the
same full quotient Sylow that normalizes it. -/
theorem source_a5_m22_normalized_image_core_shape
    (eI : I ⧸ center I ≃* M22) (S : Sylow 2 (I ⧸ center I))
    (hS : (S : Subgroup (I ⧸ center I)) ≤ normalizer
      ((L.subgroupOf I).map (QuotientGroup.mk' (center I)) : Set (I ⧸ center I)))
    (eB : ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ⧸
      pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I))) ≃*
      alternatingGroup (Fin 5)) :
    IsElementaryAbelian 2
      (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) ∧
    Nat.card (pCore 2 ((L.subgroupOf I).map (QuotientGroup.mk' (center I)))) = 16 := by
  let B := (L.subgroupOf I).map (QuotientGroup.mk' (center I))
  let C := B.map eI.toMonoidHom
  let : Finite (I ⧸ center I) := Finite.of_injective eI eI.injective
  let T := S.mapSurjective (f := eI.toMonoidHom) eI.surjective
  have hT : (T : Subgroup M22) ≤ normalizer (C : Set M22) :=
    (map_mono hS).trans (le_normalizer_map eI.toMonoidHom)
  let e := eI.subgroupMap B
  let eq : B ⧸ pCore 2 B ≃* C ⧸ pCore 2 C :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  obtain ⟨hE, h16⟩ := M22LocalA5Shape.core_shape_of_normalized T C hT (eq.symm.trans eB)
  let ec : pCore 2 B ≃* pCore 2 C :=
    (e.subgroupMap (pCore 2 B)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  let : IsElementaryAbelian 2 (pCore 2 C) := hE
  exact ⟨IsElementaryAbelian.of_surjective ec.symm.toMonoidHom ec.symm.surjective,
    (Nat.card_congr ec.toEquiv).trans h16⟩

variable [Finite G] {T : Sylow 2 G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- Original point-local membership and normalization supply the M22 marking,
including the elementary core and its order. -/
theorem source_a5_point_m22_quasisimple_marking_of_local
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (eI : I ⧸ center I ≃* M22) :
    SourceA5PointQuasisimpleMarking.{u,0} L I := by
  obtain ⟨S, _, _, hl, hS, _, ⟨eB⟩, _⟩ :=
    source_a5_point_center_quotient_local_embedding D e hn hvL hv0 hs hLI hIX hI
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (center I))
  obtain ⟨hE, h16⟩ := source_a5_m22_normalized_image_core_shape eI Sbar hS eB
  obtain ⟨f, hf⟩ := source_a5_m22_local_image_exists_marking eI Sbar hl hE h16 eB
  exact .mathieu22 f hf

/-- The original M22/3.M22 point alternative needs no separate marking or
core-shape hypothesis. -/
theorem source_a5_point_m22_local_alternative_of_local
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (t : G) {v : G}
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (eI : I ⧸ center I ≃* M22) :
    SourceA5PointComponentAlternative D e t I :=
  source_a5_point_alternative_of_quasisimple_marking D e t I hLI.le hv hNI hcross
    (source_a5_point_m22_quasisimple_marking_of_local
      D e hn (hcross hv) hv0 hs hLI hIX hI eI)

end CFSG.Quasithin.Chapter10
