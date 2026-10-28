module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Symplectic.CommutingProducts
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Thompson

/-!
# The fixed-line involution and its commuting products

The literal fixed-line centralizer identifies its generator with a
nonidentity central element of the first vertex. The faithful marking
therefore maps it to the transvection at the original base point. The
intrinsic chamber-pair theorem then supplies the exact commuting-product
premise of the Burnside-fusion and characteristic-two recognition argument,
transported through the original generated subgroup and common Sylow.

The final application removes that premise from the previous endpoint.
The local-product/chamber construction and involution representatives in
the plane core remain to be proved by this solvable-branch owner. Earlier
source normality and the overgroup supplement retain their original
producers and final discharge with the fixed-core assembly owner.

Source: Aschbacher–Smith 13.4.9, printed pp.906–907.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher Quasithin.I5 Quasithin.I5.C3Recognition
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem fixed_line_point_center
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (a : C.system.family 0)
    (hd : a.val.val ∈ V ⊓ centralizer (L : Set G)) (hd1 : a.val.val ≠ 1) :
    a ∈ center (C.system.family 0) := by
  rw [mem_center_iff]
  intro b
  apply Subtype.ext
  apply Subtype.ext
  have hb : b.val.val ∈ normalizer (L : Set G) := by
    exact C.first.le b.property
  exact mem_centralizer_singleton_iff.mp
    ((fixed_generator_centralizer h structural D m hd hd1).symm ▸ hb)

/-- Every original fixed-line generator is the transvection at the marked base point. -/
theorem fixed_line_transvection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (mark : SymplecticMark C.system) (a : C.system.family 0)
    (hd : a.val.val ∈ V ⊓ centralizer (L : Set G)) (hd1 : a.val.val ≠ 1) :
    mark.hom a.val = Matrix.PSp4Three.transvection (mark.point C.system.basePoint) 1 :=
  mark.point_center_transvection (fixed_line_point_center h structural D m z H₀ C a hd hd1)
    (fun hh => hd1 (congrArg (fun x : C.system.family 0 => x.val.val) hh))

/-- The marked point-center calculation supplies the actual source product premise. -/
theorem fixed_line_commuting_product
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (d : G) (hd : d ∈ V ⊓ centralizer (L : Set G)) (hd1 : d ≠ 1)
    (e : G) (he : e ∈ generated (normalizer (L : Set G)) z H₀)
    (hconj : ∃ c ∈ generated (normalizer (L : Set G)) z H₀, MulAut.conj c d = e)
    (hcomm : Commute d e) (hne : e ≠ d) :
    ∃ c ∈ generated (normalizer (L : Set G)) z H₀,
      (T : Subgroup G) ≤ centralizer ({MulAut.conj c (d * e)} : Set G) := by
  let E := generated (normalizer (L : Set G)) z H₀
  have hME : normalizer (L : Set G) ≤ E := first_le_generated _ _ _
  have hTE : (T : Subgroup G) ≤ E := D.sylow_normalizes_component.trans hME
  have hdM : d ∈ normalizer (L : Set G) := D.sylow_normalizes_component (D.le_sylow hd.1)
  let a : C.system.family 0 := ⟨⟨d, hME hdM⟩, by rw [C.first]; exact hdM⟩
  have ha := fixed_line_point_center h structural D m z H₀ C a hd hd1
  have ha1 : a ≠ 1 := fun hh => hd1 (congrArg (fun x : C.system.family 0 => x.val.val) hh)
  have hac : IsConj a.val (⟨e, he⟩ : E) := by
    obtain ⟨c, hc, hce⟩ := hconj
    apply isConj_iff.mpr
    exact ⟨⟨c, hc⟩, Subtype.ext hce⟩
  have habc : Commute a.val (⟨e, he⟩ : E) := Subtype.ext hcomm.eq
  have habn : (⟨e, he⟩ : E) ≠ a.val := fun hh => hne (congrArg Subtype.val hh)
  obtain ⟨c, hc⟩ := point_center_commuting_product C.system ha ha1 _ hac habc habn
  refine ⟨c.val, c.property, ?_⟩
  intro t ht
  have ht' : (⟨t, hTE ht⟩ : E) ∈ C.system.T := by rw [C.chamber]; exact ht
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hc ht')))

open scoped Pointwise in
/-- The genuine marked geometry now discharges the commuting-product input. -/
theorem isPSp_of_source_thompson_representatives
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (hnormal : H₀ ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (supplement : ∀ X : Subgroup G, X ∈ Chapter1.HOver G (H₀ : Set G) →
      (X : Set G) = (H₀ : Set G) *
        (X ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H₀ : Set G) : Subgroup G))
    (hr : ∀ a ∈ generated (normalizer (L : Set G)) z H₀,
      BenderSuzuki.PFAppendixIII.IsInvolution a →
      ∃ c ∈ generated (normalizer (L : Set G)) z H₀,
        MulAut.conj c a ∈ H₀.pCoreIn 2) : ClassicalGroup.IsPSp G 3 2 := by
  apply isPSp_of_source_thompson_data h₀ h structural D m z H₀ C hnormal supplement hr
  exact fixed_line_commuting_product h structural D m z H₀ C
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
