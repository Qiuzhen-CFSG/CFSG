module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
public import Theory.GroupTheory.ElementaryEightFixedPointOrder24
public import Theory.Representation.BinaryGroupAction
/-!
# Full point-fixer action on the binary natural hyperplane

The literal A₆ stabilizer of the duad {4,5} acts faithfully on its
perpendicular hyperplane. Its order is 24, equal to the full automorphism
stabilizer of the distinguished nonzero vector in an elementary eight.
Faithfulness uses only three duad classes, while the cardinal bound uses
its action on the four complementary planes.

Source: Aschbacher--Smith, §B.3 and 13.5.5, printed pp.83--85 and 916.
-/

@[expose] public section

open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointAction
open NaturalGeometry NaturalPairing
private theorem card_L1 : Nat.card L1 = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem fixes_three_duads (g : S) (hg : g ∈ L1)
    (h01 : pair (g 0) (g 1) = pair 0 1)
    (h02 : pair (g 0) (g 2) = pair 0 2)
    (h03 : pair (g 0) (g 3) = pair 0 3) : g = 1 := by
  have cert : ∀g:Equiv.Perm (Fin 6), ((pair 4 5).image g = pair 4 5 ∧ Equiv.Perm.sign g = 1) → pair (g 0) (g 1) = pair 0 1 →
    pair (g 0) (g 2) = pair 0 2 → pair (g 0) (g 3) = pair 0 3 → g = 1 := by
    decide +kernel
  exact cert g hg h01 h02 h03
noncomputable abbrev Hyperplane := form.orthogonal canonicalLine
private theorem pair_perp (i j : Ω) (hi : i ≠ 4 ∧ i ≠ 5) (hj : j ≠ 4 ∧ j ≠ 5) :
    pairVector i j ∈ Hyperplane := by
  intro x hx
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
  have h : form (pairVector 4 5) (pairVector i j) = 0 := by
    let a : core Ω := ⟨Pi.single 4 1 + Pi.single 5 1, by
      simp [mem_core]; decide⟩
    let b : core Ω := ⟨Pi.single i 1 + Pi.single j 1, by
      simp [mem_core]; decide +revert⟩
    have hh := naturalPairing_apply_core Ω a b
    change form (pairVector 4 5) (pairVector i j) = _ at hh
    rw [hh]
    simp [a,b,Fin.sum_univ_six,Ne.symm hi.1,Ne.symm hi.2,
      Ne.symm hj.1,Ne.symm hj.2]
  simp [h]
private theorem stable (g : L1) (v : Hyperplane) :
    naturalRepresentation Ω g.val v.val ∈ Hyperplane := by
  change naturalRepresentation Ω g.val v.val ∈ form.orthogonal canonicalLine
  rw [← orthogonal_invariant canonicalLine g.val (canonicalLine_map_of_mem g.property.1)]
  exact Submodule.mem_map_of_mem v.property
noncomputable def action (g : L1) : Hyperplane ≃ₗ[ZMod 2] Hyperplane where
  toFun v := ⟨naturalRepresentation Ω g.val v.val,by exact stable g v⟩
  invFun v := ⟨naturalRepresentation Ω g.val⁻¹ v.val,by exact stable g⁻¹ v⟩
  left_inv v := by
    apply Subtype.ext
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv v := by
    apply Subtype.ext
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  map_add' v w := Subtype.ext (map_add _ _ _)
  map_smul' c v := Subtype.ext (map_smul _ _ _)
noncomputable def actionHom : L1 →* MulAut (Multiplicative Hyperplane) where
  toFun g := (action g).toAddEquiv.toMultiplicative
  map_one' := by
    ext x : 1
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact LinearMap.congr_fun (map_one _) _
  map_mul' g h := by
    ext x : 1
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact LinearMap.congr_fun (map_mul _ _ _) _
theorem actionHom_injective : Function.Injective actionHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro g hg
  have hv (v : Hyperplane) : naturalRepresentation Ω g.val v.val = v.val := by
    have hh := congrArg (fun a : MulAut (Multiplicative Hyperplane) => a (Multiplicative.ofAdd v)) hg
    exact congrArg (fun v : Multiplicative Hyperplane => v.toAdd.val) hh
  have hpair (j : Ω) (hj : j ≠ 4 ∧ j ≠ 5) (hj0 : (0:Ω) ≠ j) :
      pair (g.val 0) (g.val j) = pair 0 j := by
    have hh := hv ⟨pairVector 0 j,pair_perp 0 j (by decide) hj⟩
    rw [pairVector_map] at hh
    exact (pairVector_eq_iff (g.val.injective.ne hj0) hj0).mp hh
  exact Subtype.ext (fixes_three_duads g.val g.property
    (hpair 1 (by decide) (by decide)) (hpair 2 (by decide) (by decide))
    (hpair 3 (by decide) (by decide)))

noncomputable def point : Multiplicative Hyperplane := Multiplicative.ofAdd
  ⟨pairVector 4 5, by
    intro y hy
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp [form_alt (pairVector 4 5)]⟩
theorem point_ne_one : point ≠ 1 := by
  intro h
  exact pairVector45_ne_zero (congrArg (fun v : Multiplicative Hyperplane => v.toAdd.val) h)
theorem action_fixes_point (g : L1) : actionHom g point = point := by
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  change naturalRepresentation Ω g.val (pairVector 4 5) = pairVector 4 5
  rw [pairVector_map]
  apply (pairVector_eq_iff (g.val.injective.ne (by decide)) (by decide)).mpr
  have h := g.property.1
  change (pair 4 5).image g.val = pair 4 5 at h
  simpa only [pair, Finset.image_insert, Finset.image_singleton] using h

theorem hyperplane_card : Nat.card (Multiplicative Hyperplane) = 8 := by
  classical
  let := Fintype.ofFinite Hyperplane
  change Nat.card Hyperplane = 8
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
  have hd : Module.finrank (ZMod 2) Hyperplane = 3 := by
    rw [Hyperplane, LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      finrank_natural_even Ω (by decide), canonicalLine_finrank]
    rfl
  rw [hd]
  decide

theorem range_eq_point_stabilizer : actionHom.range =
    MulAction.stabilizer (MulAut (Multiplicative Hyperplane)) point := by
  let : IsElementaryAbelian 2 (Multiplicative Hyperplane) := Representation.BinaryGroupAction.elementary
  have hle : actionHom.range ≤ MulAction.stabilizer (MulAut (Multiplicative Hyperplane)) point := by
    rintro _ ⟨g,rfl⟩
    exact action_fixes_point g
  apply Subgroup.eq_of_le_of_card_ge hle
  have hc : Nat.card actionHom.range = 24 := by
    change Nat.card (Set.range actionHom) = 24
    rw [Nat.card_range_of_injective actionHom_injective,card_L1]
  rw [hc]
  apply Nat.le_of_dvd (by decide)
  exact elementaryEight_fixed_point_image_card_dvd_twentyfour hyperplane_card point point_ne_one
    (MulAction.stabilizer (MulAut (Multiplicative Hyperplane)) point) (fun a => a.property)

theorem exists_action (a : MulAut (Multiplicative Hyperplane)) (ha : a point = point) :
    ∃g:L1, actionHom g = a := by
  have h : a ∈ MulAction.stabilizer (MulAut (Multiplicative Hyperplane)) point := ha
  rw [← range_eq_point_stabilizer] at h
  exact h
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointAction
