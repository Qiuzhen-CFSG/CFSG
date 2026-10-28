module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Intersection.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Intersection.Models
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Intersection.Movement
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.Semilinear

/-!
# H-star intersection normalization in the chosen Sp₄ and G₂ rows

A hypothetical moving intersection gives L = [L,J(T)]. On the faithful
full orbit, B.2.7 and the complete B.5 theorems then make the original seed
all of that orbit: the only reducible component alternatives are excluded
by the actual group orders. The resulting normalizer invariance contradicts
the moving intersection. Both the fixed-free and nonsplit central branches
are retained, with M = N_G(L) and the original H-star convention.

This proves Aschbacher--Smith 11.0.3(5), printed p.760, for the actual
chosen-natural input used by the Section 12.2 reduction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

private theorem centerfree_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hh : e x ∈ center B := (centerCongr e ⟨x,hx⟩).property
  rw [hz, mem_bot] at hh
  exact e.map_eq_one_iff.mp hh

include D S

theorem fullModule_eq_of_thompson_sp4
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hcomm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    componentOrbit V (normalizer (L : Set G)) = V := by
  apply fullModule_eq_of_thompson_of_not_linear D S hcomm
  · exact centerfree_of_equiv m.groupEquiv
      (Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot (F := S.field.Carrier))
  · intro hn
    have hm := SourceCompletion.NaturalActor.of_equiv m.groupEquiv.symm hn
    rcases hm with ⟨K, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
    · exact IntersectionModels.no_sp4_linearThree S.field K e
    · exact SourceCompletion.no_symplectic_binary_equiv S.field hd e

theorem fullModule_eq_of_thompson_g2
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (hcomm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    componentOrbit V (normalizer (L : Set G)) = V := by
  apply fullModule_eq_of_thompson_of_not_linear D S hcomm
  · apply centerfree_of_equiv m.groupEquiv
    apply Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot
    rw [S.field.card_eq]
    exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) S.nonbinary
  · intro hn
    have hm := SourceCompletion.NaturalActor.of_equiv m.groupEquiv.symm hn
    rcases hm with ⟨K, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
    · exact IntersectionModels.no_g2_linearThree S.field K e
    · exact IntersectionModels.no_g2_binary S.field S.nonbinary hd e

/-- Source 11.0.3(5), for the actual marked Sp₄ and G₂ rows and every original
H-star comparison subgroup. No fixed-space, FF-classification or invariance
premise remains. -/
theorem intersection_normalizes
    (hnatural : Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) ∨
      Nonempty (ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))))
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    H ⊓ normalizer (L : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (V : Set G) := by
  apply le_inf inf_le_right
  by_contra hmove
  have hcomm := thompson_commutator_of_intersection_moves D S hH hmove
  have he : componentOrbit V (normalizer (L : Set G)) = V := by
    rcases hnatural with hm | hm
    · obtain ⟨m⟩ := hm
      exact fullModule_eq_of_thompson_sp4 D S m hcomm
    · obtain ⟨m⟩ := hm
      exact fullModule_eq_of_thompson_g2 D S m hcomm
  have hn := le_normalizer_componentOrbit V (normalizer (L : Set G))
  rw [he] at hn
  exact hmove (inf_le_right.trans hn)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
