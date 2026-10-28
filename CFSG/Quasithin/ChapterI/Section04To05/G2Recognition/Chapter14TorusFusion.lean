module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.TorusFusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour

/-!
# The torus rotation in the dimension-four source branch

The genuine SourceLocalData supply the original two SL₂(3) factors and
their common marked Klein four. Its full ambient normalizer induces all
six automorphisms, its centralizer has order prime to three, and an actual
element of order three rotates its three involutions. The conjugation
formulas retain the original central involution and outer involution.

This supplies the torus rotation used after Fong–Wong §3A and before
§4A (Nagoya Math. J.36 (1969), pp.155,163) for Aschbacher–Smith I.4.5,
printed p.417. The exceptional cubic-core exclusions and the recognition
callback remain with `qt-i45-g2-recognition`. The existing independent
owner `qt-d-14414-g2-source` constructs SourceLocalData; this result leaves
that source premise explicit.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour Chapter14.Section04.DimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original source torus has the full normalizer action and an actual
cubic rotation, without any assumption on the ambient three-part. -/
theorem source_torus_rotation (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hcard : Nat.card F.U = 32)
    (localData : SourceLocalData L F) :
    ∃ (c : G2ThreeConfiguration G) (t : CubicTorus c),
      IsKleinFour (t.torus.map c.H.subtype) ∧
      Function.Surjective (t.torus.map c.H.subtype).normalizerMonoidHom ∧
      (centralizer (t.torus.map c.H.subtype : Set G)).relIndex
        (normalizer (t.torus.map c.H.subtype : Set G))=6 ∧
      ¬ 3 ∣ Nat.card (centralizer (t.torus.map c.H.subtype : Set G)) ∧
      ∃ g : G, orderOf g=3 ∧ g ∈ normalizer (t.torus.map c.H.subtype : Set G) ∧
        MulAut.conj g (t.z:G)=(t.n:G) ∧
        MulAut.conj g (t.n:G)=(t.z:G)*(t.n:G) := by
  obtain ⟨c⟩ := configuration_of_source_local d earlier hq chosen structural alternatives
    F hne hZ hcard localData
  obtain ⟨t⟩ := exists_cubic_torus c
  let := t.ambient_torus_kleinFour
  exact ⟨c,t,t.ambient_torus_kleinFour,kleinFour_normalizer_action_surjective c _,
    t.ambient_torus_normalizer_index,t.three_not_dvd_torus_centralizer,
    t.exists_cubic_rotation⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
