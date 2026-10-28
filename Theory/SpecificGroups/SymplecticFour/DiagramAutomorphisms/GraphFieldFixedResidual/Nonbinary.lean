module

public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Residuals and Sylow indices after a Suzuki matrix identification

For a nondegenerate Suzuki matrix group, simplicity and nonsolvability force
both the commutator and the two-residual to be the whole group. Restricting
an actual equivalence therefore identifies its source's two-residual with
the Suzuki commutator, retaining the elementwise map.

A two-subgroup embedded in the Suzuki carrier has order at most `q²`, by
the existing root Sylow subgroup. Sylow two-subgroups of Sp₄(q) have order
`q⁴`, giving index at least `q²` for their intersections with any subgroup
actually equivalent to the Suzuki carrier. This bounds the intersection
with the full subgroup, not merely its two-residual.

These are conditional consequences of a genuine carrier identification;
no fixed-group identification is asserted here. The binary parameter is
excluded and must be computed on Sp₄(2)′ separately.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 16.1.4(7) and 16.1.8, printed pp.1171–1173. The
concrete Suzuki model facts come from Huppert--Blackburn III, XI.3.1–3.6.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative

/-- The nondegenerate concrete Suzuki carrier is perfect. -/
theorem suzuki_commutator_eq_top (m : ℕ) (hm : 0 < m) :
    commutator (SuzukiMatrixGroup m) = ⊤ := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (commutator (SuzukiMatrixGroup m)) inferInstance with h | h
  · let := (commutator_eq_bot_iff _).mp h
    exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm inferInstance).elim
  · exact h

/-- The nondegenerate concrete Suzuki carrier has no nontrivial two-group quotient. -/
theorem suzuki_twoResidual_eq_top (m : ℕ) (hm : 0 < m) :
    pResidual 2 (SuzukiMatrixGroup m) = ⊤ := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (pResidual 2 (SuzukiMatrixGroup m)) inferInstance with h | h
  · have hp := Subgroup.isPGroup_quotient_pResidual (G := SuzukiMatrixGroup m) 2
    have hpG := hp.of_equiv ((QuotientGroup.quotientMulEquivOfEq h).trans
      QuotientGroup.quotientBot)
    let := hpG.isNilpotent
    exact (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm inferInstance).elim
  · exact h

/-- The residual is the commutator for positive Suzuki parameter. -/
theorem suzuki_twoResidual_eq_commutator (m : ℕ) (hm : 0 < m) :
    pResidual 2 (SuzukiMatrixGroup m) = commutator (SuzukiMatrixGroup m) := by
  rw [suzuki_twoResidual_eq_top m hm, suzuki_commutator_eq_top m hm]

/-- Restrict a specified Suzuki equivalence to the actual two-residual. -/
def residualEquivOfSuzuki {G : Type*} [Group G] (m : ℕ) (hm : 0 < m)
    (e : G ≃* SuzukiMatrixGroup m) :
    pResidual 2 G ≃* commutator (SuzukiMatrixGroup m) :=
  ((pResidual 2 G).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr
      ((Subgroup.map_pResidual 2 e).trans (suzuki_twoResidual_eq_commutator m hm)))

@[simp] theorem residualEquivOfSuzuki_coe {G : Type*} [Group G]
    (m : ℕ) (hm : 0 < m) (e : G ≃* SuzukiMatrixGroup m) (x : pResidual 2 G) :
    (residualEquivOfSuzuki m hm e x : SuzukiMatrixGroup m) = e x := rfl

private theorem card_le_suzuki_sylow {X : Type*} [Group X] [Finite X]
    (m : ℕ) (hm : 0 < m) (hX : IsPGroup 2 X)
    (f : X →* SuzukiMatrixGroup m) (hf : Function.Injective f) :
    Nat.card X ≤ (2 ^ (2 * m + 1)) ^ 2 := by
  obtain ⟨Q, hQ⟩ := (hX.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  obtain ⟨R, hR⟩ := suzukiRootSubgroup_isSylow m hm
  calc
    Nat.card X = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
    _ ≤ Nat.card Q := Nat.card_le_card_of_injective (Subgroup.inclusion hQ)
      (Subgroup.inclusion_injective hQ)
    _ = Nat.card R := by rw [Q.card_eq_multiplicity, R.card_eq_multiplicity]
    _ = (2 ^ (2 * m + 1)) ^ 2 := by
      rw [hR, suzukiRootSubgroup_card m hm]

variable {F : Type*} [Field F] [Finite F]

/-- The order of every Sylow two-subgroup of the ambient symplectic group. -/
theorem sylow_card (m : ℕ) (hF : Nat.card F = 2 ^ (2 * m + 1))
    (P : Sylow 2 (Sp F)) : Nat.card P = (2 ^ (2 * m + 1)) ^ 4 := by
  calc
    Nat.card P = Nat.card (unipotentSylow hF (by omega)) := by
      rw [P.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    _ = (2 ^ (2 * m + 1)) ^ 4 := by
      change Nat.card (unipotent (F := F)) = _
      rw [card_unipotent, hF]

/-- An actual Suzuki subgroup meets every ambient Sylow two-subgroup in index at least q². -/
theorem suzuki_subgroup_sylow_index (m : ℕ) (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m + 1)) (H : Subgroup (Sp F))
    (e : H ≃* SuzukiMatrixGroup m) (P : Sylow 2 (Sp F)) :
    (2 ^ (2 * m + 1)) ^ 2 ≤ H.relIndex P := by
  let N := H.subgroupOf (P : Subgroup (Sp F))
  let f : N →* H := {
    toFun x := ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : H => (z : Sp F)) h))
  have hc : Nat.card N ≤ (2 ^ (2 * m + 1)) ^ 2 :=
    card_le_suzuki_sylow m hm (P.isPGroup'.to_subgroup N)
      (e.toMonoidHom.comp f) (e.injective.comp hf)
  have hmul := N.card_mul_index
  rw [sylow_card m hF P] at hmul
  change (2 ^ (2 * m + 1)) ^ 2 ≤ N.index
  have hbound := Nat.mul_le_mul_right N.index hc
  rw [hmul] at hbound
  have hpow : (2 ^ (2 * m + 1)) ^ 4 =
      (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1)) ^ 2 := by ring
  rw [hpow] at hbound
  exact Nat.le_of_mul_le_mul_left hbound (by positivity)

/-- The strict bound used in the component-centralizer argument. -/
theorem suzuki_subgroup_sylow_index_gt_two (m : ℕ) (hm : 0 < m)
    (hF : Nat.card F = 2 ^ (2 * m + 1)) (H : Subgroup (Sp F))
    (e : H ≃* SuzukiMatrixGroup m) (P : Sylow 2 (Sp F)) :
    2 < H.relIndex P := by
  have hq : 2 ≤ 2 ^ (2 * m + 1) := by
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 1 ≤ 2 * m + 1 by omega)
    simpa using h
  have hi := suzuki_subgroup_sylow_index m hm hF H e P
  nlinarith

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.GraphFieldFixedResidual
