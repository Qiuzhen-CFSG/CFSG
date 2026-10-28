module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Doubling.Multiplicity
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Intersection

/-!
# The literal doubled natural module in 11.2.1

The full normalizer orbit has at most two copies of the original marked
natural SL₃ action when L=[L,J(T)]. A single copy would have the same
order as the original seed, so strict enlargement forces exactly two.
The resulting binary conjugation section is on V_M itself, has trivial
kernel and intertwines the original map L → L/O₂(L) with the same full
SL₃ marking. No center or quotient is discarded.

The H-star application discharges both the doubled-module recognition and
the preceding other-row normalization premise. The exact odd-kernel
normalizer contract and the automizer bounds remain explicit; their final
discharge stays with the generation assembly owner.
Source: Aschbacher--Smith, 11.0.3(5) and 11.2.1, printed pp.760,766--767.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Doubling
open Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Actual coordinates on the full subgroup, with zero kernel and literal
ambient conjugation under the unchanged natural marking. -/
theorem section_of_copies
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (h : FullModuleNaturalCopies D S m 2) :
    Nonempty (BinaryConjugationSection L
      (Source.conjugateSpan (normalizer (L : Set G)) V) ⊥
      ((repeated (linearNatural S.field 3) 2).comp
        (m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  let := fullModule_elementary D S
  let U := componentOrbit V (normalizer (L : Set G))
  obtain ⟨e,he⟩ := h
  let q : U →* Multiplicative (Fin 2 → Fin 3 → S.field.Carrier) :=
    e.toLinearMap.toAddMonoidHom.toMultiplicative
  have hUM : U ≤ normalizer (L : Set G) :=
    iSup_conjugates_le_of_le_normalizer V _ _
      (D.le_sylow.trans D.sylow_normalizes_component) (normalizer (L : Set G)).le_normalizer
  refine ⟨{
    section_le := ?_
    kernel_le := bot_le
    normalized := L.le_normalizer.trans (le_normalizer_componentOrbit V _)
    coordinates := q
    onto := e.surjective
    kernel_eq := ?_
    equivariant := ?_
  }⟩
  · change U ≤ L
    exact (fullModule_eq_commutator D S).le.trans
      (le_normalizer_iff_commutator_le_right.mp hUM)
  · rw [bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff q).mpr e.injective
  · intro l v
    exact he l (Additive.ofMul v)

/-- Strict enlargement excludes one copy. The supplied marking itself is
retained in both natural summands, for every nonbinary field degree. -/
theorem doubled_section_of_thompson
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hcomm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    (hproper : V ≠ Source.conjugateSpan (normalizer (L : Set G)) V) :
    Nonempty (BinaryConjugationSection L
      (Source.conjugateSpan (normalizer (L : Set G)) V) ⊥
      ((repeated (linearNatural S.field 3) 2).comp
        (m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) := by
  obtain ⟨s,hs,h⟩ := fullModule_sl3_natural_copies D S m
  have hb := copies_le_two_of_thompson D S m hcomm hs h
  have htwo : s = 2 := by
    by_contra hn
    have hone : s = 1 := by omega
    subst s
    exact hproper (h.eq_seed D S).symm
  subst s
  exact section_of_copies D S m h

/-- The complete representation-theoretic step of 11.2.1, with no FF,
multiplicity, fixed-space or coordinate premise left to discharge. -/
theorem doublingStep : DoublingStep D S := by
  rintro ⟨m⟩ hcomm hproper
  exact ⟨m,doubled_section_of_thompson D S m hcomm hproper⟩

/-- The literal H-star generation alternative now needs only the exact
odd-kernel normalizer and two automizer bounds. The earlier normalization
clause and the doubled action have been proved on the original D and S. -/
theorem conclusion_of_automizer_bounds
    (hcontrol : OddKernelNormalizer (T := T) (L := L) (V := V))
    (hbounds : AutomizerBounds D S) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Conclusion D S H := by
  apply conclusion_of_source_steps D S ?_ hcontrol hbounds (doublingStep D S) hH
  intro K hK hrows
  exact (intersection_normalizes D S hrows K hK).trans inf_le_right

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Doubling
