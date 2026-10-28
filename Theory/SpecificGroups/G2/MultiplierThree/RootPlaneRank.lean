module
public import Theory.SpecificGroups.G2.MultiplierOrdinary.PositiveRelations.CommutingLifts
public import Theory.Quasithin.CentralThreeLocalRank

/-!
# An ordinary rank-three subgroup in a ternary G₂ central cover

The A/B positive-root pair has distinct torus characters over F₃. Normalized
additive sections therefore commute in every central extension, and the
actual unipotent coordinates make the projected pair injective. Adjoining a
nontrivial central three-group gives ordinary three-rank at least three.
This uses the A/B pair and imposes no splitting of the obstructed B/D pair.

The application is the exceptional ternary endpoint of Aschbacher–Smith
A.2.17, printed p.39, using the ordinary rank assertion of I.2.1. The root
lifting convention and orthogonal defect are GLS3 §6.3, printed pp.319–320.
-/

open Subgroup
namespace Atlas.G2
open MultiplierOrdinary MultiplierOrdinary.RootSections

private theorem rootAB_injective : Function.Injective
    (fun a : Multiplicative (ZMod 3) × Multiplicative (ZMod 3) =>
      rootA a.1.toAdd * rootB a.2.toAdd) := by
  intro a b h
  have hu : unipotentProduct ![a.1.toAdd,a.2.toAdd,0,0,0,0] =
      unipotentProduct ![b.1.toAdd,b.2.toAdd,0,0,0,0] := by
    simpa only [unipotentProduct, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, rootC_zero, rootD_zero, rootE_zero, rootF_zero, mul_one] using h
  have ht := unipotentProduct_injective hu
  apply Prod.ext
  · exact Multiplicative.toAdd.injective (by simpa using congrFun ht 0)
  · exact Multiplicative.toAdd.injective (by simpa using congrFun ht 1)

/-- Any central extension of the ternary model has an elementary nine
lifting the literal A/B root pair injectively. -/
public theorem exists_ternary_root_nine_lift {E : Type*} [Group E]
    (f : E →* Model (ZMod 3)) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) :
    ∃ j : Multiplicative (ZMod 3) × Multiplicative (ZMod 3) →* E,
      Function.Injective (f.comp j) := by
  obtain ⟨L, hL⟩ := prime_torusEquivariant_sections (p := 3) (by simp) (by decide) f hf hk
  have hb (s t : ZMod 3) : L.x 1 s * L.x 0 t = L.x 0 t * L.x 1 s :=
    L.commute_of_torus_separates hL hf hk 1 0 (-1) 1 (by decide) (by decide)
      (model_collectionRelations (F := ZMod 3)).toCommutingRelations.ba s t
  let j := (L.root 0).noncommCoprod (L.root 1) (fun a b => (hb b.toAdd a.toAdd).symm)
  refine ⟨j, ?_⟩
  intro a b hab
  apply rootAB_injective
  change f (L.x 0 a.1.toAdd * L.x 1 a.2.toAdd) =
    f (L.x 0 b.1.toAdd * L.x 1 b.2.toAdd) at hab
  simpa only [map_mul, L.project_x, positiveRoot, Matrix.cons_val_zero,
    Matrix.cons_val_one] using hab

/-- A nontrivial central three-group adds one ordinary rank to the lifted
A/B roots. This does not assert a rank-three involution centralizer. -/
public theorem three_le_primeRank_of_ternary_central_quotient
    {E : Type*} [Group E] [Finite E]
    (iso : E ⧸ center E ≃* Model (ZMod 3))
    (hZ : IsPGroup 3 (center E)) (hne : center E ≠ ⊥) : 3 ≤ primeRank 3 E := by
  let f := iso.toMonoidHom.comp (QuotientGroup.mk' (center E))
  have hf : Function.Surjective f := iso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker ≤ center E := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center E) x = 1
    exact iso.map_eq_one_iff.mp (MonoidHom.mem_ker.mp hx)
  obtain ⟨j, hj⟩ := exists_ternary_root_nine_lift f hf hk
  have hqj : Function.Injective ((QuotientGroup.mk' (center E)).comp j) := by
    intro a b hab
    apply hj
    exact congrArg iso hab
  have hh := Theory.Quasithin.three_le_primeRank_normalizer_of_injective_central_projection
    hZ hne (⊥ : Subgroup E) j hqj
    (fun _ => by rw [Subgroup.normalizer_eq_top]; trivial)
    (fun a => by
      apply Prod.ext
      · change (3 • a.1.toAdd) = 0
        simp only [nsmul_eq_mul]; exact zero_mul _
      · change (3 • a.2.toAdd) = 0
        simp only [nsmul_eq_mul]; exact zero_mul _)
    (by change Nat.card (ZMod 3 × ZMod 3) = _; rw [Nat.card_prod]; norm_num)
  exact hh.trans (Theory.GroupTheory.primeRank_le_of_injective 3
    (normalizer ((⊥ : Subgroup E) : Set E)).subtype Subtype.val_injective)
end Atlas.G2
