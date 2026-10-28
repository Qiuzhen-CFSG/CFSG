module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Blocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.BlockObstructions
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Endpoints
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Geometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.Projection
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.CentralizerGeometry
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.ParabolicPairs
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.RelativeBlocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.FourIntersection

/-!
# Binary linear component refinement

Source: Aschbacher–Smith 2.3.9(7), combined manuscript, printed pp.525–526.

The literal inner action supplied by 1.1.5(3)(a) determines an involution
projection in the actual PSL model. Its centrality in the component Sylow
intersection supplies rank-one coordinates, with no geometric premise left
to the caller.

In degree five, or degree four with trivial Dynkin action, two invariant
flag stabilizers generate the component. Joining them with all of S gives
overgroups in HeOver(S), inside ⟨L,S⟩. The source local block decomposition
then supplies an escaping block, contradicting the complete relative block
calculation. This excludes L₅(2) and forces nontrivial Dynkin action in L₄(2).
The action is expressed through conjugation of actual transported subspace
stabilizers of different dimensions by N_S(L); S may permute components.

For L₄(2), the proved proper-overgroup geometry and diagram exchange identify
L ∩ M with the projection centralizer, completing the binary conclusion (g).
All coordinate, flag, block and intersection premises are discharged here.
The no-two-invariant-parabolics reduction and assembly of all Lie families
remain in the parent module.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

open Subgroup

variable {G : Type*} [Group G] {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem excluded_case_false {n : ℕ} [NeZero n]
    (h : LocalSetup H L M S z) (e : L ≃* PSL n)
    (hn : n = 5 ∨ n = 4 ∧
      ¬ NontrivialDynkinAction e ((S : Subgroup H).map H.subtype))
    {t : L} (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) : False := by
  have hn45 : n = 4 ∨ n = 5 := hn.elim Or.inr (fun hn => Or.inl hn.1)
  obtain ⟨c⟩ := projection_transvectionCoordinates h hn45 e ht ht2
  obtain ⟨F, hF, hinv, hSF, _, B, hB, hout, hmoved⟩ :=
    exists_escapingBlock_in_flagOvergroup h e hn ht ht2
  exact hout (blockObstruction_of_excluded_flag h ht c F hF hinv hSF B hB hmoved)

/-- The two invariant parabolics and their relative block obstructions exclude
PSL₅(2), using the actual involution projection from 1.1.5(3)(a). -/
theorem not_five_of_projection (h : LocalSetup H L M S z) (e : L ≃* PSL 5)
    {t : L} (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) : False :=
  excluded_case_false h e (Or.inl rfl) ht ht2

/-- In degree four, trivial action on the transported binary subspace geometry
would give the same impossible pair of block obstructions. -/
theorem four_nontrivialDynkinAction_of_projection
    (h : LocalSetup H L M S z) (e : L ≃* PSL 4)
    {t : L} (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    NontrivialDynkinAction e ((S : Subgroup H).map H.subtype) := by
  by_contra hd
  exact excluded_case_false h e (Or.inr ⟨rfl, hd⟩) ht ht2

/-- The L₄(2) intersection clause of 2.3.9(7)(g). Both the transvection
coordinates and nontrivial diagram action are consequences of the local setup
and the supplied involution projection. -/
theorem four_intersection_eq_centralizer
    (h : LocalSetup H L M S z) (e : L ≃* PSL 4)
    {t : L} (ht : IsConjugationProjection L z t) (ht2 : orderOf t = 2) :
    L ⊓ M = L ⊓ centralizer ({(t : G)} : Set G) := by
  obtain ⟨c⟩ := projection_transvectionCoordinates h (Or.inl rfl) e ht ht2
  exact FourIntersection.intersection_eq_centralizer h e ht ht2 c
    (four_nontrivialDynkinAction_of_projection h e ht ht2)

private theorem involution_projection_of_inner {n : ℕ} [NeZero n]
    (h : LocalSetup H L M S z) (e : L ≃* PSL n)
    (hinner : ∃ u : L, IsConjugationProjection L z u) :
    ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 := by
  obtain ⟨u, hu⟩ := hinner
  obtain ⟨t, ht, _⟩ := exists_unique_projection h e (MulAut.conj u)
    (fun x => (hu x).symm) ⟨u, rfl⟩
  exact ⟨t, ht⟩

/-- PSL₅(2) is excluded from the actual inner-action case of 1.1.5(3)(a).
The implementing element is not assumed to have order two; this follows from
the centerless model and the source's nontrivial involutory action. -/
theorem not_five (h : LocalSetup H L M S z) (e : L ≃* PSL 5)
    (hinner : ∃ u : L, IsConjugationProjection L z u) : False := by
  obtain ⟨t, ht, ht2⟩ := involution_projection_of_inner h e hinner
  exact not_five_of_projection h e ht ht2

/-- The complete binary surviving alternative 2.3.9(7)(g), from the actual
PSL₄(2) equivalence and literal inner action supplied by 1.1.5(3)(a).
No projection-order, coordinate, diagram-action or intersection premise remains. -/
theorem four_refinement (h : LocalSetup H L M S z) (e : L ≃* PSL 4)
    (hinner : ∃ u : L, IsConjugationProjection L z u) :
    NontrivialDynkinAction e ((S : Subgroup H).map H.subtype) ∧
      ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 ∧
        L ⊓ M = L ⊓ centralizer ({(t : G)} : Set G) := by
  obtain ⟨t, ht, ht2⟩ := involution_projection_of_inner h e hinner
  exact ⟨four_nontrivialDynkinAction_of_projection h e ht ht2,
    t, ht, ht2, four_intersection_eq_centralizer h e ht ht2⟩

/-- The degree-five exclusion for a supplied automorphism implementing literal
ambient conjugation, with innerness expressed by the actual conjugation map. -/
theorem not_five_of_inner_action (h : LocalSetup H L M S z) (e : L ≃* PSL 5)
    (α : MulAut L) (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) : False := by
  obtain ⟨t, ⟨ht, ht2⟩, _⟩ := exists_unique_projection h e α hα hinner
  exact not_five_of_projection h e ht ht2

/-- Apply conclusion (g) directly to the inner automorphism in 1.1.5(3)(a),
preserving its equality with the ambient conjugation action of z. -/
theorem four_refinement_of_inner_action (h : LocalSetup H L M S z)
    (e : L ≃* PSL 4) (α : MulAut L)
    (hα : ∀ x : L, (α x : G) = z * (x : G) * z⁻¹)
    (hinner : α ∈ (MulAut.conj (G := L)).range) :
    NontrivialDynkinAction e ((S : Subgroup H).map H.subtype) ∧
      ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 ∧
        L ⊓ M = L ⊓ centralizer ({(t : G)} : Set G) := by
  obtain ⟨t, ⟨ht, ht2⟩, _⟩ := exists_unique_projection h e α hα hinner
  exact ⟨four_nontrivialDynkinAction_of_projection h e ht ht2,
    t, ht, ht2, four_intersection_eq_centralizer h e ht ht2⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
