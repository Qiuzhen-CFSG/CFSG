module

public import Theory.Representation.BinaryNaturalDual.FiveActors.Classification.Geometry
public import Theory.Representation.BinaryNaturalDual.FiveActors.Classification.Transport
public import Theory.Representation.BinaryNaturalDual.FiveActors.Classification.PairModel
public import Theory.Representation.BinaryNaturalDual.FiveActors.Classification.PairNormalForm
public import Theory.Representation.BinaryNaturalDual.FiveActors.Classification.PairCentralizer
public import Theory.GroupTheory.QuasithinBasic
public import Theory.ElementaryAbelian.Quotient

/-!
# Conjugate placement of large elementary inner actors

For a nonquadratic elementary subgroup, choose commuting involutions with
nonzero product of displacement operators. The pair normal form conjugates
this pair to the regular four-plus-one model, so the elementary subgroup
embeds in that model's common centralizer. Its proved two-rank bound of
four excludes this case.
The quadratic case lies in a radical at its displacement span; dimension
counting and inverse transpose then give an actual conjugator into the
radical at any prescribed three-space.

The final placement theorem discharges both pair-calculation premises
using `PairNormalForm` and `PairCentralizer`. It constructs an actual
automorphism conjugating the given actor into the radical at any prescribed
three-space, with a specialization to the marked radical `A₀`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.2(3),
printed pp.390–391 (PDF pp.401–402). This is an alternative to the source's
`K₁/K₂` and `J(T)` argument. The innerness hypothesis remains explicit,
as intended for the independent H.9.2(2) producer.
-/

@[expose] public section

open BinaryLinear BinaryLinear.OuterCyclic Theory.GroupTheory
open scoped IsMulCommutative
namespace BinaryNaturalDual.FiveActors.Classification

theorem quadratic_of_regular_pair_analysis
    (pair_normal_form : ∀ s t : G, s ^ 2 = 1 → t ^ 2 = 1 → s * t = t * s →
      (∃ x : X, s (t x - x) ≠ t x - x) →
      ∃ g : G, MulAut.conj g s = regularS ∧ MulAut.conj g t = regularT)
    (pair_centralizer_rank : primeRank 2 regularCentralizer ≤ 4)
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : 5 ≤ primeRank 2 E) :
    Quadratic E := by
  intro s hs t ht x
  by_contra hx
  have hst : s * t = t * s :=
    congrArg Subtype.val (mul_comm (⟨s, hs⟩ : E) ⟨t, ht⟩)
  obtain ⟨g, hgs, hgt⟩ := pair_normal_form s t
    (elemPow_eq_one_of_isElementaryAbelian s hs)
    (elemPow_eq_one_of_isElementaryAbelian t ht) hst ⟨x, hx⟩
  let F := E.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  have hS : regularS ∈ F := ⟨s, hs, hgs⟩
  have hT : regularT ∈ F := ⟨t, ht, hgt⟩
  have hle : F ≤ regularCentralizer := by
    intro a ha
    apply Subgroup.mem_centralizer_iff.mpr
    intro b hb
    have hbF : b ∈ F := by
      rcases Set.mem_insert_iff.mp hb with rfl | hb
      · exact hS
      · exact Set.mem_singleton_iff.mp hb ▸ hT
    exact congrArg Subtype.val (mul_comm (⟨b, hbF⟩ : F) ⟨a, ha⟩)
  have hrank : primeRank 2 E = primeRank 2 F :=
    primeRank_equiv 2 (E.equivMapOfInjective _ (MulAut.conj g).injective)
  have hbound := (primeRank_le_of_injective 2 (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)).trans pair_centralizer_rank
  omega

theorem inner_image_placement_of_quadratic
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : 5 ≤ primeRank 2 E)
    (hq : Quadratic E) (U : Submodule (ZMod 2) X)
    (hU : Module.finrank (ZMod 2) U = 3) :
    ∃ a : M, (E.map MulAut.conj).map (MulAut.conj a).toMonoidHom ≤ radicalActor U := by
  obtain ⟨a, ha⟩ := exists_map_radical_le (displacementSpan E) U
    (radical_dimension E hq hE) hU
  refine ⟨a, ?_⟩
  rw [inner_image_map_conj]
  exact Subgroup.map_mono ((Subgroup.map_mono (le_radical_displacementSpan E hq)).trans ha)

theorem placement_of_regular_pair_analysis
    (pair_normal_form : ∀ s t : G, s ^ 2 = 1 → t ^ 2 = 1 → s * t = t * s →
      (∃ x : X, s (t x - x) ≠ t x - x) →
      ∃ g : G, MulAut.conj g s = regularS ∧ MulAut.conj g t = regularT)
    (pair_centralizer_rank : primeRank 2 regularCentralizer ≤ 4)
    (A : Subgroup M) [IsElementaryAbelian 2 A] (hinner : A ≤ L)
    (hA : 5 ≤ primeRank 2 A) (U : Submodule (ZMod 2) X)
    (hU : Module.finrank (ZMod 2) U = 3) :
    ∃ a : M, A.map (MulAut.conj a).toMonoidHom ≤ radicalActor U := by
  let E := A.comap (MulAut.conj : G →* M)
  have himage : E.map MulAut.conj = A := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      exact hg
    · intro a ha
      obtain ⟨g, hg⟩ := hinner ha
      exact ⟨g, by change MulAut.conj g ∈ A; rwa [hg], hg⟩
  let e : E ≃* A :=
    (E.equivMapOfInjective _
      (MulAut.conj_injective_of_center_eq_bot center_eq_bot)).trans
        (MulEquiv.subgroupCongr himage)
  let : IsElementaryAbelian 2 E :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hE : 5 ≤ primeRank 2 E := by rw [primeRank_equiv 2 e]; exact hA
  have hq := quadratic_of_regular_pair_analysis pair_normal_form pair_centralizer_rank E hE
  simpa only [himage] using inner_image_placement_of_quadratic E hE hq U hU

/-- A large elementary subgroup of the actual `GL₅(2)` acts quadratically
on its natural module. The pair classification and centralizer bound are
proved inputs, with no additional classification premise. -/
theorem quadratic_of_primeRank_ge_five
    (E : Subgroup G) [IsElementaryAbelian 2 E] (hE : 5 ≤ primeRank 2 E) :
    Quadratic E :=
  quadratic_of_regular_pair_analysis regular_pair_normal_form
    regularCentralizer_primeRank_le_four E hE

/-- Every elementary inner actor of rank at least five is conjugate, by an
actual automorphism of `GL₅(2)`, into the radical at any given three-space.
This is the exhaustive placement step of H.9.2(3); H.9.2(2) supplies the
explicit innerness premise in the source assembly. -/
theorem exists_conjugate_le_radicalActor
    (A : Subgroup M) [IsElementaryAbelian 2 A] (hinner : A ≤ L)
    (hA : 5 ≤ primeRank 2 A) (U : Submodule (ZMod 2) X)
    (hU : Module.finrank (ZMod 2) U = 3) :
    ∃ a : M, A.map (MulAut.conj a).toMonoidHom ≤ radicalActor U :=
  placement_of_regular_pair_analysis regular_pair_normal_form
    regularCentralizer_primeRank_le_four A hinner hA U hU

/-- The source's marked Sylow-invariant three-space gives the marked
radical representative for every elementary inner actor of rank at least five. -/
theorem exists_conjugate_le_A₀
    (A : Subgroup M) [IsElementaryAbelian 2 A] (hinner : A ≤ L)
    (hA : 5 ≤ primeRank 2 A) :
    ∃ a : M, A.map (MulAut.conj a).toMonoidHom ≤ A₀ :=
  exists_conjugate_le_radicalActor A hinner hA U₀ finrank_U₀

end BinaryNaturalDual.FiveActors.Classification
