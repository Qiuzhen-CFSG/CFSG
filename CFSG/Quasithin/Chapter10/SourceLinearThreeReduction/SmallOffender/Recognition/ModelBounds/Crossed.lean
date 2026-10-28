module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietAction
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerResidual
public import CFSG.Quasithin.Chapter10.SourceA5WeakClosureLowerBound
public import Theory.Representation.BinaryConjugationSection.TrivialCommutant

/-!
# Crossed centralization from a trivial invertible commutant

The two original components commute modulo the orbit two-core, which
centralizes the full module. Thus the opposite component centralizes the
marked action on the moved central quotient. A trivial invertible commutant
makes this action trivial; full commutator generation removes the central
kernel and gives the literal crossed-centralization conclusion.

Source: Aschbacher--Smith 10.1.1--2 and 10.2.12, pp.741--742,754--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 PointControl.Selection.ModuleChoice
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem opposite_commutator_centralizes_fullModule
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ⁅L.map (MulAut.conj t).toMonoidHom,L⁆ ≤ centralizer (D.fullModule : Set G) := by
  let R := localOrbit T L
  obtain ⟨q,hq,hker,hleft,hright⟩ := original_component_product_quotient D
    (fun hn => htn (hn ht)) ht htn
  apply commutator_le.mpr
  intro b hb l hl
  obtain ⟨k,hk,rfl⟩ := hb
  let aR : R := ⟨l,le_componentOrbit L T hl⟩
  let bR : R := originalConjugateOrbitInclusion ht ⟨k,hk⟩
  have hh : ⁅bR,aR⁆ ∈ q.ker := by
    change q ⁅bR,aR⁆ = 1
    rw [map_commutatorElement,hright,
      show q aR = (QuotientGroup.mk' _ (⟨l,hl⟩ : L),1) from hleft ⟨l,hl⟩]
    simp [commutatorElement_def]
  rw [hker] at hh
  exact source_fullModule_orbit_core_centralizes D (mem_map_of_mem R.subtype hh)

theorem crossed_of_trivial_commutant
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) J V)
    (e : (L ⧸ pCore 2 L) ≃* J)
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (htriv : ∀ f : V ≃ₗ[ZMod 2] V, (∀ j v, f (σ j v) = σ j (f v)) →
      f = LinearEquiv.refl _ _)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  let Q := L.map (MulAut.conj t).toMonoidHom
  let W := ⁅D.fullModule,L⁆
  let := source_full_moved_elementary D
  have hQR : Q ≤ localOrbit T L := by
    rintro _ ⟨l,hl,rfl⟩
    exact (originalConjugateOrbitInclusion ht ⟨l,hl⟩).property
  have hQL : Q ≤ normalizer (L : Set G) :=
    hQR.trans (source_nonnormal_orbit_le_normalizer D (fun hn => htn (hn ht)))
  have hQV : Q ≤ normalizer (D.fullModule : Set G) :=
    (hQR.trans (localOrbit T L).le_normalizer).trans D.maximalLocal_normalizes_fullModule
  have hQW : Q ≤ normalizer (W : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.fullModule,L⁆).map (MulAut.conj x).toMonoidHom = ⁅D.fullModule,L⁆
    have hV : D.fullModule.map (MulAut.conj x).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (hQV hx)
    have hL : L.map (MulAut.conj x).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp (hQL hx)
    rw [map_commutator,hV,hL]
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hQWc : Q ≤ centralizer (W : Set G) :=
    c.centralizes_of_trivial_commutant (by
      intro f hf
      apply htriv f
      intro j v
      obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) j
      exact hf l v) Q hQL hQW
      ((opposite_commutator_centralizes_fullModule D ht htn).trans (centralizer_le hWV))
      (source_full_moved_eq_commutator D)
  exact crossed_of_opposite_centralization D ht htn (le_centralizer_iff.mp hQWc)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
