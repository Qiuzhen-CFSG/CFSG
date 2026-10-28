module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Thompson
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Products

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Symplectic.CommutingProducts
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Thompson

/-!
# The fixed-line involution and its commuting products: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/Products` proof for the local step.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Subgroup Theory.GroupTheory Stellmacher Quasithin.I5 Quasithin.I5.C3Recognition
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem fixed_line_point_center_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
    ((fixed_generator_centralizer_at h structural D m hd hd1).symm ▸ hb)

/-- The marked point-center calculation supplies the actual source product premise. -/
theorem fixed_line_commuting_product_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  have ha := fixed_line_point_center_at h structural D m z H₀ C a hd hd1
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
theorem isPSp_of_source_thompson_representatives_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
  apply isPSp_of_source_thompson_data_at h₀ h structural D m z H₀ C hnormal supplement hr
  exact fixed_line_commuting_product_at h structural D m z H₀ C
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
