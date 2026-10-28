module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.CentralCover
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable

/-!
# Excluding the alternating-six central-cover row

The inclusion fixing the seventh letter sends a Sylow two-subgroup of A₆
onto a Sylow two-subgroup of A₇: both have order eight. Thus self-normalization
in A₇ gives self-normalization in A₆. Since Out(A₆) has order four, its Sylow
automorphism stabilizers are two-groups. Faithful descent through the actual
center quotient then excludes the A.3.6 triple-cover row for the moved component.

The application uses the original normalizer escape and component quotient.
The remaining J₁ recognition belongs to qt-d-1222-natural-line-action.
Source: Aschbacher--Smith A.3.12 and 3.3.12, printed pp.47--48,589.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer

private def sixSeven : alternatingGroup (Fin 6) →* alternatingGroup (Fin 7) := by
  let s : Finset (Fin 7) := Finset.univ.erase 6
  let e : Fin 6 ≃ s := Fintype.equivOfCardEq (by decide)
  exact (alternatingGroup.ofSubtype s).comp e.altCongrHom.toMonoidHom

private theorem sixSeven_injective : Function.Injective sixSeven := by
  unfold sixSeven
  exact alternatingGroup.ofSubtype_injective.comp (Equiv.altCongrHom _).injective

private theorem alternating_six_sylow_self_normalizing
    (P : Sylow 2 (alternatingGroup (Fin 6))) :
    normalizer (P : Set (alternatingGroup (Fin 6))) =
      (P : Subgroup (alternatingGroup (Fin 6))) := by
  obtain ⟨Q,hQ⟩ := P.exists_comap_eq_of_injective sixSeven_injective
  have hPcard : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    decide +kernel
  have hQcard : Nat.card Q = 8 := by
    rw [Q.card_eq_multiplicity, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    decide +kernel
  have he : (P : Subgroup (alternatingGroup (Fin 6))).map sixSeven =
      (Q : Subgroup (alternatingGroup (Fin 7))) := by
    apply eq_of_le_of_card_ge
    · exact map_le_iff_le_comap.mpr hQ.ge
    · rw [card_map_of_injective sixSeven_injective,hPcard,hQcard]
  apply le_antisymm _ (P : Subgroup (alternatingGroup (Fin 6))).le_normalizer
  intro g hg
  have hm : sixSeven g ∈ normalizer
      ((P : Subgroup (alternatingGroup (Fin 6))).map sixSeven : Set _) :=
    (P : Subgroup (alternatingGroup (Fin 6))).le_normalizer_map sixSeven
      (mem_map_of_mem sixSeven hg)
  rw [he] at hm
  change sixSeven g ∈ normalizer (Q : Set (alternatingGroup (Fin 7))) at hm
  rw [AlternatingSevenSylow.sylow_normalizer_eq_self Q] at hm
  rw [←hQ]
  exact hm

private theorem alternating_six_stabilizer_two
    (P : Sylow 2 (alternatingGroup (Fin 6))) :
    IsPGroup 2 (MulAction.stabilizer (MulAut (alternatingGroup (Fin 6)))
      (P : Subgroup (alternatingGroup (Fin 6)))) := by
  apply MulAut.isPGroup_sylow_stabilizer_of_self_normalizing P
    (alternating_six_sylow_self_normalizing P)
  exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}
namespace MovedComponent
variable (E : MovedComponent S f A)

/-- Faithful descent excludes the literal A₆ center quotient. -/
theorem quotient_center_not_alternating_six :
    ¬ Nonempty (((E.component ⧸ pCore 2 E.component) ⧸
      center (E.component ⧸ pCore 2 E.component)) ≃* alternatingGroup (Fin 6)) := by
  rintro ⟨e⟩
  exact E.false_of_central_quotient_stabilizers e alternating_six_stabilizer_two

/-- The actual triple cover of A₆ is excluded without replacing the original quotient. -/
theorem quotient_not_alternating_six_cover :
    ¬ Chapter1.Section02.LocalModels.IsAlternatingCover
      (E.component ⧸ pCore 2 E.component) 6 :=
  fun h => E.quotient_center_not_alternating_six h.2.2
end MovedComponent

/-- Apply the exclusion to the component produced by the original escape. -/
theorem exists_moved_component_not_alternating_six_cover
    (f : InvariantFlag c) (A : OddSupplement T)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    ∃ E : MovedComponent S f A,
      ¬ Chapter1.Section02.LocalModels.IsAlternatingCover
        (E.component ⧸ pCore 2 E.component) 6 := by
  obtain ⟨E⟩ := exists_movedComponent f A hescape
  exact ⟨E,E.quotient_not_alternating_six_cover⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
