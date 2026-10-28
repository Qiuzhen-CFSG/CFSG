module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.ModelBounds.Crossed
public import Theory.Representation.BinaryConjugationSection.PerfectScalarCommutant
/-!
# Crossed centralization for scalar marked components

The opposite component is perfect and commutes with the original component
on the full module. Its induced action on the moved central quotient is
scalar, hence trivial. Full commutator generation removes the fixed kernel
and gives crossed centralization on the literal moved subgroup.

Source: Aschbacher--Smith 10.1.1--2 and 10.2.12, pp.741--742,754--755.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 PointControl.Selection.ModuleChoice
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem crossed_of_scalar_commutant
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {F J V : Type*} [Field F] [Group J] [AddCommGroup V]
    [Module (ZMod 2) V] [Module F V]
    (σ : Representation (ZMod 2) J V)
    (e : (L ⧸ pCore 2 L) ≃* J)
    (c : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (hs : ∀ f : V →ₗ[ZMod 2] V, (∀ j v, f (σ j v) = σ j (f v)) →
      ∃ a : F, ∀ v, f v = a • v)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  let Q := L.map (MulAut.conj t).toMonoidHom
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect Q := Group.IsPerfect.map (MulAut.conj t).toMonoidHom
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
    c.centralizes_of_perfect_scalar_commutant (by
      intro f hf
      apply hs f
      intro j v
      obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) j
      exact hf l v) Q hQL hQW
      ((opposite_commutator_centralizes_fullModule D ht htn).trans (centralizer_le hWV))
      (source_full_moved_eq_commutator D)
  exact crossed_of_opposite_centralization D ht htn (le_centralizer_iff.mp hQWc)

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
