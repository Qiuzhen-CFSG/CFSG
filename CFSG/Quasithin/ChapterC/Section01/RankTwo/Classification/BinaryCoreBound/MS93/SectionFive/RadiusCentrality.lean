module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalAction

/-!
# Radius centrality and the three-subgroup deduction

For critical distance greater than four, the radius-two subgroup is abelian,
so its commutator with the neighborhood kernel centralizes it. Given this
centrality at any distance greater than two, the three-subgroup lemma puts
the derived subgroup in the elementary center of the kernel. The endpoint
triple-commutator in MS93 (5.2)(iii) follows by subgroup containment.

Failure of centrality can therefore occur only at distance four. This module
does not prove the chief-factor argument needed for that remaining case.

Source: Meierfrankenfeld--Stellmacher (1993), (5.2), printed pp.914--915.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive
open DistanceEight.PathCentrality
variable {M : Type*} [Group M] (R : Subgroup M) (geometry : Geometry R)

theorem radius_commutator_central_of_four_lt
    (hb : 4 < geometry.b R) {a : Vertex R} (ha : color R a = false) :
    ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
  have hn : Q R a ≤ normalizer (V R a : Set (FreeAmalgam R)) :=
    (show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans
      (DistanceEight.V_normalized R a)
  have hc := le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt R ha hb)
  exact (le_normalizer_iff_commutator_le_left.mp hn).trans hc

theorem radius_derived_le_X
    (hb : 2 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    (hc : ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R))) :
    ⁅V R a,V R a⁆ ≤ X R a := by
  have hVQ : V R a ≤ Q R a := V_le_Q R ha hb
  have hVQV : ⁅⁅V R a,Q R a⁆,V R a⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr hc
  have hQVV : ⁅⁅Q R a,V R a⁆,V R a⁆ = ⊥ := by
    rw [commutator_comm (Q R a) (V R a)]
    exact hVQV
  have hVVQ : ⁅⁅V R a,V R a⁆,Q R a⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hVQV hQVV
  have hcenter : ⁅V R a,V R a⁆ ≤ (center (Q R a)).map (Q R a).subtype := by
    intro x hx
    refine ⟨⟨x,hVQ (commutator_le_self _ hx)⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext ((commutator_eq_bot_iff_le_centralizer.mp hVVQ) hx y y.property)
  exact DistanceEight.commutator_le_omegaCenter_of_omegaOne_eq_self
    (V R a) (V R a) (Q R a) hVQ (DistanceEight.VBall_omegaOne R a 2) hcenter

theorem radius_triple_commutator
    {a : Vertex R}
    (hc : ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)))
    (A B : Subgroup (FreeAmalgam R)) (hA : A ≤ Q R a) (hB : B ≤ V R a) :
    ⁅⁅A,B⁆,B⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  have hAB : ⁅A,B⁆ ≤ ⁅V R a,Q R a⁆ := by
    rw [commutator_comm A B]
    exact commutator_mono hB hA
  exact (hAB.trans hc).trans (centralizer_le hB)

theorem critical_radius_triple_commutator
    {a a' c : Vertex R}
    (hc : ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R))) :
    ⁅⁅X R a' ⊓ Q R a,V R a ⊓ Q R c⁆,V R a ⊓ Q R c⁆ = ⊥ :=
  radius_triple_commutator R hc _ _ inf_le_right inf_le_left

theorem distance_eq_four_of_radius_commutator_not_central
    (hb : 2 < geometry.b R) {a : Vertex R} (ha : color R a = false)
    (hn : ¬ ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R))) :
    geometry.b R = 4 := by
  have hle : geometry.b R ≤ 4 := by
    by_contra hnle
    exact hn (radius_commutator_central_of_four_lt R geometry (by omega) ha)
  have he : Even (geometry.b R) := geometry.even (alpha R) rfl
  rw [Nat.even_iff] at he
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.SectionFive
