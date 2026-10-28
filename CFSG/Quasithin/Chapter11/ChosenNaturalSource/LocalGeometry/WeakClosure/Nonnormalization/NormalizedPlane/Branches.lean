module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.Symmetry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Central

/-!
# The strict-commutator reduction in source 11.2.4

If the commutator has the full natural quotient but misses the marked plane,
the original central kernel is nontrivial. The SL₃ vanishing theorem and the
preceding G₂ exclusion then force a genuine Sp₄ action marking. Reciprocal
Sylow transport gives corank 2n for both actions, even for nonsplit covers.
Finally, containing the marked first preimage absorbs the entire central
kernel and makes the commutator equal to the plane. The actual plane-alignment
consumer below then supplies the abelian-span contradiction.

The missing source step is to establish that first-preimage containment from
the reciprocal transvection exclusion and the two commuting roots. It is not
assumed to be a source theorem here. The parabolic result is used uniformly
only to apply it to the reciprocal pair after Sylow conjugacy.

Source: Aschbacher--Smith, 11.2.4, printed pp.769--770.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- Failure of equality can only occur in a nontrivial original central cover. -/
theorem centralizer_ne_bot_of_strict {A : Subgroup G}
    (hp : ParabolicGeometry f A) (hne : ⁅V, A⁆ ≠ f.Vi 1) :
    V ⊓ centralizer (L : Set G) ≠ ⊥ := by
  intro hz
  apply hne
  simpa only [hz, sup_bot_eq] using hp.quotient_plane

/-- The strict branch retains the original coordinates, not an unrelated
group-family label or an independently chosen module equivalence. -/
theorem strict_symplectic_coordinates {A : Subgroup G}
    (hp : ParabolicGeometry f A) (hne : ⁅V, A⁆ ≠ f.Vi 1)
    (hG2 : ¬ Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))) :
    V ⊓ centralizer (L : Set G) ≠ ⊥ ∧
      ∃ m : ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)),
        c = Coordinates.sp4 m := by
  have hc := centralizer_ne_bot_of_strict f hp hne
  refine ⟨hc, ?_⟩
  cases c with
  | sl3 m => exact (hc (Preliminary.sl3_centralizer_eq_bot D S m)).elim
  | sp4 m => exact ⟨m, rfl⟩
  | g2 m => exact (hG2 ⟨m⟩).elim

/-- The genuine earlier G₂ weak-closure conclusion excludes the G₂ marking
already from this one noncommuting conjugate in T. -/
theorem strict_symplectic_of_g2_weakClosure
    (hG2 : Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) →
      Source.weakClosureZero (T : Subgroup G) V ≤
        (T : Subgroup G) ⊓ centralizer (V : Set G))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hp : ParabolicGeometry f (V.map (MulAut.conj g).toMonoidHom))
    (hstrict : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ f.Vi 1) :
    V ⊓ centralizer (L : Set G) ≠ ⊥ ∧
      ∃ m : ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)),
        c = Coordinates.sp4 m := by
  have hA : V.map (MulAut.conj g).toMonoidHom ≤ Source.weakClosureZero (T : Subgroup G) V :=
    le_sSup ⟨g, rfl, hg⟩
  have hW : ⁅V, Source.weakClosureZero (T : Subgroup G) V⁆ ≠ ⊥ := by
    intro hz
    exact hne (bot_unique ((commutator_mono le_rfl hA).trans_eq hz))
  exact strict_symplectic_coordinates f hp hstrict (not_g2_of_noncentral_zero D S hG2 hW)

/-- Containing V₁ absorbs C_V(L); the quotient-plane equality then lifts
to an equality inside the original V, without a splitting hypothesis. -/
theorem commutator_eq_of_point_le {A : Subgroup G}
    (hp : ParabolicGeometry f A) (hpoint : f.Vi 0 ≤ ⁅V, A⁆) :
    ⁅V, A⁆ = f.Vi 1 := by
  apply le_antisymm (le_sup_left.trans_eq hp.quotient_plane)
  rw [← hp.quotient_plane]
  exact sup_le le_rfl ((f.centralizer_le_Vi 0).trans hpoint)

/-- Both literal actions have corank 2n in the Sp₄ row. The actor kernel
is the actual C_A(V), rather than the kernel of an unrelated model action. -/
theorem symplectic_action_coranks
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (Coordinates.sp4 m))
    (hp : ∀ k : G, V.map (MulAut.conj k).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ≠ ⊥ →
      ParabolicGeometry f (V.map (MulAut.conj k).toMonoidHom))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G)) =
      2 * S.field.degree ∧
    subgroupCorank V (V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) =
      2 * S.field.degree := by
  simpa only [sp4_plane_corank] using action_coranks_equal f hp g hg hne hn

/-- Actual application of the remaining root output to the normalized-pair
plane-alignment argument. The root output is still an explicit obligation. -/
theorem alignment_of_point_le
    (hp : ∀ k : G, V.map (MulAut.conj k).toMonoidHom ≤ T →
      ⁅V, V.map (MulAut.conj k).toMonoidHom⁆ ≠ ⊥ →
      ParabolicGeometry f (V.map (MulAut.conj k).toMonoidHom))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hn : V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hpoint : f.Vi 0 ≤ ⁅V, V.map (MulAut.conj g).toMonoidHom⁆) :
    Alignment (f.Vi 1) V g :=
  alignment_of_equal_commutator f hp g hne hn (commutator_eq_of_point_le f (hp g hg hne) hpoint)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane
