module

public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue.ElementaryThompson
public import Stellmacher.ElementaryAbelianMaxJ

/-!
# The elementary Thompson clause of H.9.3(3)

For the specified Sylow subgroup T₀ of Aut(GL₄(2)), A₀ is the unique elementary
subgroup of largest order in T₀ ∩ Inn(GL₄(2)). Thus the supremum defining the
elementary Thompson subgroup is exactly A₀. Sylow conjugacy supplies an actual
automorphism taking the corresponding subgroup for any Sylow T to this A₀.

The order bound and uniqueness are proved in the intrinsic permutation model;
there are no classification or maximality premises left to discharge here.
This uses the elementary-abelian maximal-rank convention of section 0.6.1,
printed p.8, rather than the all-abelian Thompson subgroup.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(3),
printed pp.391–392, PDF pp.402–403. This is its Thompson identification clause;
the exhaustive three-orbit assertion belongs to the catalogue assembly.
-/

public section

namespace CFSG.Quasithin.ChapterH.NaturalDual.FourActors
open BinaryNaturalDual.FourActors BinaryNaturalDual.FourActors.PermutationCatalogue

/-- The maximal elementary family in the chosen inner Sylow consists only of A₀. -/
theorem T0_inner_maximal_elementary_family :
    Stellmacher.elementaryAbelianMaxSubgroups ((T0 : Subgroup M) ⊓ inner) = {A0} := by
  ext E
  change (E ≤ (T0 : Subgroup M) ⊓ inner ∧ IsElementaryAbelian 2 E ∧
    ∀ B : Subgroup M, B ≤ (T0 : Subgroup M) ⊓ inner → IsElementaryAbelian 2 B →
      Nat.card B ≤ Nat.card E) ↔ E = A0
  constructor
  · rintro ⟨hE, he, hm⟩
    let := he
    apply T0_inner_elementary_eq_A0_of_card_ge E hE
    simpa only [A0_card] using hm A0 A0_le_T0_inner A0_elementary
  · rintro rfl
    refine ⟨A0_le_T0_inner, A0_elementary, ?_⟩
    intro B hB he
    let := he
    rw [A0_card]
    exact T0_inner_elementary_card_le B hB

/-- H.9.3(3): A₀ is the elementary Thompson subgroup of the chosen Sylow intersection. -/
theorem elementaryThompson_T0_inner :
    Stellmacher.elementaryAbelianMaxJ ((T0 : Subgroup M) ⊓ inner) = A0 := by
  rw [Stellmacher.elementaryAbelianMaxJ, T0_inner_maximal_elementary_family, sSup_singleton]

/-- The marked equality is realized by an actual Sylow subgroup, without extra premises. -/
theorem exists_sylow_elementaryThompson_eq_A0 : ∃ T : Sylow 2 M,
    Stellmacher.elementaryAbelianMaxJ ((T : Subgroup M) ⊓ inner) = A0 :=
  ⟨T0, elementaryThompson_T0_inner⟩

/-- An actual conjugator transports both an arbitrary Sylow and its elementary Thompson subgroup. -/
theorem exists_conj_elementaryThompson_eq_A0 (T : Sylow 2 M) : ∃ a : M,
    (T : Subgroup M).map (MulAut.conj a).toMonoidHom = (T0 : Subgroup M) ∧
    (Stellmacher.elementaryAbelianMaxJ ((T : Subgroup M) ⊓ inner)).map
      (MulAut.conj a).toMonoidHom = A0 := by
  obtain ⟨a, hT, hi⟩ := exists_conj_sylow_inner_eq_T0 T
  refine ⟨a, hT, ?_⟩
  rw [← Stellmacher.elementaryAbelianMaxJ_map_equiv, hi, elementaryThompson_T0_inner]

end CFSG.Quasithin.ChapterH.NaturalDual.FourActors
