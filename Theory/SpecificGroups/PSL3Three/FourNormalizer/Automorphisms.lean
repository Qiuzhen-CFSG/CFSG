module

public import Theory.SpecificGroups.PSL3Three.FourNormalizer
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.SpecificGroups.PSL3Three.GraphWitnesses.EightCentralizers.GraphModel
public import Theory.GroupAction.AutomorphismFixerTransport

/-!
# Full automorphism fixers of four-subgroups in PSL₃(3)

Inverse transpose fixes the diagonal four pointwise. Every automorphism is
inner or inner times inverse transpose; an inner factor fixes that four
exactly when its conjugating element belongs to the four. The graph actor
is outer, so these give precisely eight distinct automorphisms. Simultaneous
diagonalization and the canonical SL-to-PSL equivalence transport the count
to every four-subgroup and every equivalent carrier.

Source: Aschbacher--Smith, quasithin manuscript, Lemma 2.5.8(5), pp.556--557.
This is the concrete full-automorphism pointwise-fixer calculation used in
the source Sylow-containment argument.
-/

public section
namespace Matrix.PSL3Three.FourGeometry
open Subgroup Matrix.PSL3.OuterSolvable
open GraphWitnesses.EightCentralizers GraphWitnesses.EightCentralizers.GraphModel
local notation "τ" => graph (ZMod 3)

private theorem diagonal_elementary : IsElementaryAbelian 2 diagonalFour := by
  refine { toIsMulCommutative := (le_centralizer_iff_isMulCommutative.mp
      (le_of_eq centralizer_diagonalFour.symm)), exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  rintro ⟨x, i, rfl⟩
  apply Subtype.ext
  have h : ∀ i : Fin 4, diagonalElement i ^ 2 = 1 := by decide
  exact h i

private noncomputable abbrev D : Subgroup PSL := diagonalFour.map equiv.toMonoidHom

private theorem card_D : Nat.card D = 4 := by
  rw [Subgroup.card_map_of_injective equiv.injective, card_diagonalFour]

private theorem centralizer_D : centralizer (D : Set PSL) = D := by
  let : IsElementaryAbelian 2 diagonalFour := diagonal_elementary
  exact centralizer_four D (IsElementaryAbelian.map equiv.toMonoidHom) card_D

private theorem graph_fixes (x : PSL) (hx : x ∈ D) : τ x = x := by
  obtain ⟨s, ⟨i, rfl⟩, rfl⟩ := hx
  have h : ∀ i : Fin 4, graphSL (ZMod 3) (diagonalElement i) = diagonalElement i := by
    decide
  change τ (equiv (diagonalElement i)) = equiv (diagonalElement i)
  rw [equiv_apply]
  change project (graphSL (ZMod 3) (diagonalElement i)) = project (diagonalElement i)
  rw [h]

private def fixerParameter (p : D × Bool) : fixingSubgroup (MulAut PSL) (D : Set PSL) :=
  ⟨MulAut.conj p.1.val * (if p.2 then τ else 1), by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    change (MulAut.conj p.1.val * (if p.2 then τ else 1)) y = y
    have hfix : (if p.2 then τ else (1 : MulAut PSL)) y = y := by
      cases p.2 <;> simp only [Bool.false_eq_true, ↓reduceIte, MulAut.one_apply,
        graph_fixes y hy]
    rw [MulAut.mul_apply, hfix, MulAut.conj_apply]
    have hc := (show p.1.val ∈ centralizer (D : Set PSL) from
      by rw [centralizer_D]; exact p.1.property) y hy
    rw [← hc, mul_inv_cancel_right]⟩

private theorem inner_ne_inner_graph (x y : PSL) :
    MulAut.conj x ≠ MulAut.conj y * τ := by
  intro h
  apply graph_not_inner
  refine ⟨y⁻¹ * x, ?_⟩
  rw [map_mul, map_inv, h, inv_mul_cancel_left]

private theorem fixerParameter_injective : Function.Injective fixerParameter := by
  rintro ⟨x, b⟩ ⟨y, c⟩ he
  have h := congrArg Subtype.val he
  change MulAut.conj x.val * (if b then τ else 1) =
    MulAut.conj y.val * (if c then τ else 1) at h
  have hbc : b = c := by
    cases b <;> cases c
    · rfl
    · exact (inner_ne_inner_graph x.val y.val (by simpa only [Bool.false_eq_true, ↓reduceIte, mul_one] using h)).elim
    · exact (inner_ne_inner_graph y.val x.val (by simpa only [Bool.false_eq_true, ↓reduceIte, mul_one] using h.symm)).elim
    · rfl
  subst c
  have hxy : x = y := Subtype.ext
    (MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot (mul_right_cancel h))
  exact Prod.ext hxy rfl

private theorem fixerParameter_surjective : Function.Surjective fixerParameter := by
  intro a
  obtain ⟨x, hx | hx⟩ := automorphism_inner_or_inner_graph a.val
  · have hc : x ∈ centralizer (D : Set PSL) := by
      intro y hy
      have h := (mem_fixingSubgroup_iff _).mp a.property y hy
      change a.val y = y at h
      rw [hx, MulAut.conj_apply] at h
      exact ((mul_inv_eq_iff_eq_mul).mp h).symm
    refine ⟨(⟨x, centralizer_D ▸ hc⟩, false), ?_⟩
    apply Subtype.ext
    change MulAut.conj x * 1 = a.val
    simpa only [mul_one] using hx.symm
  · have hc : x ∈ centralizer (D : Set PSL) := by
      intro y hy
      have h := (mem_fixingSubgroup_iff _).mp a.property y hy
      change a.val y = y at h
      rw [hx, MulAut.mul_apply, graph_fixes y hy, MulAut.conj_apply] at h
      exact ((mul_inv_eq_iff_eq_mul).mp h).symm
    exact ⟨(⟨x, centralizer_D ▸ hc⟩, true), Subtype.ext hx.symm⟩

private theorem card_diagonal_fixer :
    Nat.card (fixingSubgroup (MulAut PSL) (D : Set PSL)) = 8 := by
  rw [← Nat.card_congr (Equiv.ofBijective fixerParameter
    ⟨fixerParameter_injective, fixerParameter_surjective⟩), Nat.card_prod, card_D]
  simp [Nat.card_eq_fintype_card]

/-- The actual full automorphism group of PSL₃(3) has order 11232. -/
theorem card_fullAutomorphismGroup : Nat.card (MulAut PSL) = 11232 := by
  let f : PSL × Bool → MulAut PSL := fun p =>
    MulAut.conj p.1 * (if p.2 then τ else 1)
  have hi : Function.Injective f := by
    rintro ⟨x, b⟩ ⟨y, c⟩ h
    change MulAut.conj x * (if b then τ else 1) =
      MulAut.conj y * (if c then τ else 1) at h
    have hbc : b = c := by
      cases b <;> cases c
      · rfl
      · exact (inner_ne_inner_graph x y
          (by simpa only [Bool.false_eq_true, ↓reduceIte, mul_one] using h)).elim
      · exact (inner_ne_inner_graph y x
          (by simpa only [Bool.false_eq_true, ↓reduceIte, mul_one] using h.symm)).elim
      · rfl
    subst c
    exact Prod.ext (MulAut.conj_injective_of_center_eq_bot psl_center_eq_bot
      (mul_right_cancel h)) rfl
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨x, hx | hx⟩ := automorphism_inner_or_inner_graph a
    · exact ⟨(x, false), by simpa [f] using hx.symm⟩
    · exact ⟨(x, true), by simpa [f] using hx.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hi, hs⟩), Nat.card_prod, card_PSL]
  simp [Nat.card_eq_fintype_card]

end Matrix.PSL3Three.FourGeometry

namespace Matrix.PSL3Three
open Subgroup FourGeometry

/-- In the full automorphism group, every elementary four has pointwise fixer of order eight. -/
theorem card_four_fixer (F : Subgroup PSL)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    Nat.card (fixingSubgroup (MulAut PSL) (F : Set PSL)) = 8 := by
  let : IsElementaryAbelian 2 F := hF
  let A := F.map equiv.symm.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map equiv.symm.toMonoidHom
  obtain ⟨g, hg⟩ := exists_conj_diagonalFour A
    (by rw [Subgroup.card_map_of_injective equiv.symm.injective, hc])
  let e : PSL ≃* PSL := (equiv.symm.trans (MulAut.conj g)).trans equiv
  have he : F.map e.toMonoidHom = diagonalFour.map equiv.toMonoidHom := by
    change F.map (equiv.toMonoidHom.comp
      ((MulAut.conj g).toMonoidHom.comp equiv.symm.toMonoidHom)) = _
    rw [← Subgroup.map_map, ← Subgroup.map_map, hg]
  have hecard := MulAut.card_fixingSubgroup_map e F
  rw [he] at hecard
  exact hecard.symm.trans card_diagonal_fixer

/-- The full automorphism fixer count on any carrier identified with PSL₃(3). -/
theorem card_four_fixer_of_equiv {K : Type*} [Group K]
    (e : K ≃* PSL) (F : Subgroup K)
    (hF : IsElementaryAbelian 2 F) (hc : Nat.card F = 4) :
    Nat.card (fixingSubgroup (MulAut K) (F : Set K)) = 8 := by
  let : IsElementaryAbelian 2 F := hF
  rw [← MulAut.card_fixingSubgroup_map e F]
  exact card_four_fixer (F.map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective e.injective, hc])

end Matrix.PSL3Three
