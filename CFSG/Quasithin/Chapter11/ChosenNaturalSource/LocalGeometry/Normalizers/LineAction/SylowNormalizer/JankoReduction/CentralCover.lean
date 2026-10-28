module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.SylowModels
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms

/-!
# Sylow automorphism stabilizers of central covers

Automorphisms of a perfect central cover descend faithfully through its
actual center quotient. A Sylow stabilizer therefore embeds in the stabilizer
of the projected Sylow. A two-group stabilizer downstairs excludes the
nontrivial odd action of the moved component upstairs, even though its center
may have odd order. In particular this removes the triple cover of A₇ from
the actual component catalogue.

Source: Aschbacher--Smith A.3.12 and the argument (**) in 3.3.12, pp.47--48,589.
The remaining recognition and source assembly belong to
qt-d-1222-natural-line-action.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

private theorem cover_sylow_stabilizer_two {H M : Type*} [Group H] [Group M] [Finite H]
    (q : PerfectCentralCovering.Cover H M) (hq : q.toMonoidHom.ker = center H)
    (hM : ∀ P : Sylow 2 M,
      IsPGroup 2 (MulAction.stabilizer (MulAut M) (P : Subgroup M))) (P : Sylow 2 H) :
    IsPGroup 2 (MulAction.stabilizer (MulAut H) (P : Subgroup H)) := by
  let R := P.mapSurjective q.surjective
  let B := MulAction.stabilizer (MulAut H) (P : Subgroup H)
  let C := MulAction.stabilizer (MulAut M) (R : Subgroup M)
  have hp (a : B) : q.autMap hq a.val ∈ C := by
    change (R : Subgroup M).map (q.autMap hq a.val).toMonoidHom = (R : Subgroup M)
    have he : (q.autMap hq a.val).toMonoidHom.comp q.toMonoidHom =
        q.toMonoidHom.comp a.val.toMonoidHom := by
      ext x
      exact q.autMap_apply hq a.val x
    change ((P : Subgroup H).map q.toMonoidHom).map _ = _
    rw [map_map,he,←map_map]
    have ha : (P : Subgroup H).map a.val.toMonoidHom = (P : Subgroup H) := a.property
    rw [ha]
    rfl
  let j : B →* C := ((q.autMap hq).comp B.subtype).codRestrict C hp
  apply (hM R).of_injective j
  intro a b hab
  apply Subtype.ext
  exact q.autMap_injective hq (congrArg Subtype.val hab)

private theorem alternating_seven_stabilizer_two
    (P : Sylow 2 (alternatingGroup (Fin 7))) :
    IsPGroup 2 (MulAction.stabilizer (MulAut (alternatingGroup (Fin 7))) (P : Subgroup (alternatingGroup (Fin 7)))) := by
  apply MulAut.isPGroup_sylow_stabilizer_of_self_normalizing P
    (AlternatingSevenSylow.sylow_normalizer_eq_self P)
  let A := alternatingGroup (Fin 7)
  have hc : Nat.card (Equiv.Perm (Fin 7) ⧸ A) = 2^1 := by
    rw [← A.index_eq_card]
    exact alternatingGroup.index_eq_two
  apply (IsPGroup.of_card hc).of_surjective (MulAut.outerAction A)
  intro x
  obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup A) x
  obtain ⟨s,rfl⟩ :=
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide)).surjective a
  exact ⟨QuotientGroup.mk' A s,rfl⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- A center quotient with two-group Sylow stabilizers excludes the literal
perfect component, without discarding its center in the original action. -/
theorem false_of_central_quotient_stabilizers {M : Type*} [Group M]
    (e : ((E.component ⧸ pCore 2 E.component) ⧸
      center (E.component ⧸ pCore 2 E.component)) ≃* M)
    (hM : ∀ P : Sylow 2 M,
      IsPGroup 2 (MulAction.stabilizer (MulAut M) (P : Subgroup M))) : False := by
  let H := E.component ⧸ pCore 2 E.component
  let : Group.IsPerfect (⊤ : Subgroup H) := E.componentQuotient_isCComponent.perfect
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective
    (f := (topEquiv : (⊤ : Subgroup H) ≃* H).toMonoidHom) topEquiv.surjective
  let q : PerfectCentralCovering.Cover H M := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center H))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk'] }
  have hq : q.toMonoidHom.ker = center H := by
    change (e.toMonoidHom.comp (QuotientGroup.mk' (center H))).ker = _
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨P,hP⟩ := E.quotientSylow_isSylow
  apply E.quotientSylow_stabilizer_not_twoGroup
  rw [←hP]
  exact cover_sylow_stabilizer_two q hq hM P

/-- The actual A₇ central quotient is excluded at every central-cover degree. -/
theorem quotient_center_not_alternating_seven :
    ¬ Nonempty (((E.component ⧸ pCore 2 E.component) ⧸
      center (E.component ⧸ pCore 2 E.component)) ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  exact E.false_of_central_quotient_stabilizers e alternating_seven_stabilizer_two

/-- In particular the A.3.6 triple-cover row is impossible. -/
theorem quotient_not_alternating_seven_cover :
    ¬ Chapter1.Section02.LocalModels.IsAlternatingCover
      (E.component ⧸ pCore 2 E.component) 7 :=
  fun h => E.quotient_center_not_alternating_seven h.2.2
end MovedComponent

/-- The original escape consumer retains the same literal component and action. -/
theorem exists_moved_component_not_alternating_seven_cover
    (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      ¬ Chapter1.Section02.LocalModels.IsAlternatingCover
        (E.component ⧸ pCore 2 E.component) 7 := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,E.quotient_not_alternating_seven_cover⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
