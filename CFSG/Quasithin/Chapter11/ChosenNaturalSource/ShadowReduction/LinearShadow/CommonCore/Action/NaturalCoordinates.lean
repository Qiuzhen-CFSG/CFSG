module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Kernel

/-!
# Marked natural summands and their split-torus fixed points

A natural-summand marking specifies a surjective map from the original V_H
onto actual copies of the natural plane, its exact K-fixed kernel, and the
intertwining equation for the original conjugation action. It allows a nonsplit
central extension. This is an output specification for the G.1.6 argument,
not an assertion that that argument has been established.

A nonidentity split diagonal fixes no vector in these copies. Thus an actual
subgroup containing a lift of that diagonal has the same fixed points as K.
The last theorem specializes this to the literal source D₀ and Z. The source
producer must construct both the marking and the diagonal lift.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.3.7, natural-summand and Cartan paragraph, printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] (T : Sylow 2 G) (H : Subgroup G)

/-- Actual equivariant natural coordinates on V_H/C_{V_H}(K), allowing a
central kernel on V_H. Existence is a separate mathematical theorem. -/
structure NaturalQuotientMarking (F : BinaryField) where
  multiplicity : ℕ
  positive : 0 < multiplicity
  quotientEquiv : (outsideResidual H ⧸ pCore 2 (outsideResidual H)) ≃*
    SpecialLinearGroup (Fin 2) F.Carrier
  coordinates : omegaClosure T H →* Multiplicative (Fin multiplicity → Fin 2 → F.Carrier)
  surjective : Function.Surjective coordinates
  kernel : coordinates.ker =
    (centralizer (outsideResidual H : Set G)).subgroupOf (omegaClosure T H)
  intertwines : ∀ (k : outsideResidual H) (v : omegaClosure T H) (i : Fin multiplicity),
    (coordinates (residualAction T H k v)).toAdd i =
      mulVec (quotientEquiv (QuotientGroup.mk' _ k)).val ((coordinates v).toAdd i)

variable {T H} {F : BinaryField}

private theorem diagonal_fixed_zero (a : F.Carrier) (ha : a ≠ 1)
    (w : Fin 2 → F.Carrier)
    (hw : mulVec !![a,0;0,a⁻¹] w = w) : w = 0 := by
  have h₀ : a * w 0 = w 0 := by
    simpa [mulVec,dotProduct,Fin.sum_univ_two] using congrFun hw 0
  have h₁ : a⁻¹ * w 1 = w 1 := by
    simpa [mulVec,dotProduct,Fin.sum_univ_two] using congrFun hw 1
  have hz₀ : w 0 = 0 := by
    have hz : (a - 1) * w 0 = 0 := by rw [sub_mul,one_mul,h₀,sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)
  have hz₁ : w 1 = 0 := by
    have hz : (a⁻¹ - 1) * w 1 = 0 := by rw [sub_mul,one_mul,h₁,sub_self]
    exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr (inv_ne_one.mpr ha))
  ext j
  fin_cases j <;> assumption

/-- The original lifted diagonal has exactly the global fixed kernel. -/
theorem NaturalQuotientMarking.fixed_eq_of_diagonal
    (c : NaturalQuotientMarking T H F) (B : Subgroup G)
    (hBK : B ≤ outsideResidual H) (d : outsideResidual H) (hd : (d : G) ∈ B)
    (a : F.Carrier) (ha : a ≠ 1)
    (hdiag : (c.quotientEquiv (QuotientGroup.mk' _ d)).val = !![a,0;0,a⁻¹]) :
    omegaClosure T H ⊓ centralizer (B : Set G) =
      omegaClosure T H ⊓ centralizer (outsideResidual H : Set G) := by
  apply le_antisymm
  · rintro v ⟨hv,hc⟩
    refine ⟨hv,?_⟩
    have hfix : residualAction T H d ⟨v,hv⟩ = ⟨v,hv⟩ := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hc d hd)
    have hz : c.coordinates ⟨v,hv⟩ = 1 := by
      change (c.coordinates ⟨v,hv⟩).toAdd = 0
      funext i
      have he := c.intertwines d ⟨v,hv⟩ i
      rw [hfix,hdiag] at he
      exact diagonal_fixed_zero a ha _ he.symm
    have hk : (⟨v,hv⟩ : omegaClosure T H) ∈ c.coordinates.ker := hz
    rw [c.kernel] at hk
    exact hk
  · exact inf_le_inf_left _ (centralizer_le hBK)

/-- The same computation on the source omega-center, with its original embedding. -/
theorem NaturalQuotientMarking.omega_fixed_eq_of_diagonal
    (c : NaturalQuotientMarking T H F) (B : Subgroup G)
    (hBK : B ≤ outsideResidual H) (d : outsideResidual H) (hd : (d : G) ∈ B)
    (a : F.Carrier) (ha : a ≠ 1)
    (hdiag : (c.quotientEquiv (QuotientGroup.mk' _ d)).val = !![a,0;0,a⁻¹]) :
    omegaCenter T ⊓ centralizer (B : Set G) =
      omegaCenter T ⊓ centralizer (outsideResidual H : Set G) := by
  have he := c.fixed_eq_of_diagonal B hBK d hd a ha hdiag
  apply le_antisymm
  · rintro v ⟨hv,hc⟩
    exact ⟨hv,(he.le ⟨omegaCenter_le_closure T H hv,hc⟩).2⟩
  · exact inf_le_inf_left _ (centralizer_le hBK)

/-- The literal odd Hall subgroup D_H supplies D₀; no unrelated torus tag is used. -/
theorem source_oddCartan_omega_fixed
    (c : NaturalQuotientMarking T H F) (D_H : Subgroup G)
    (hDK : oddCartanPart D_H ≤ outsideResidual H)
    (d : outsideResidual H) (hd : (d : G) ∈ oddCartanPart D_H)
    (a : F.Carrier) (ha : a ≠ 1)
    (hdiag : (c.quotientEquiv (QuotientGroup.mk' _ d)).val = !![a,0;0,a⁻¹]) :
    omegaCenter T ⊓ centralizer (oddCartanPart D_H : Set G) =
      omegaCenter T ⊓ centralizer (outsideResidual H : Set G) :=
  c.omega_fixed_eq_of_diagonal _ hDK d hd a ha hdiag


/-- Every subgroup extracted from the odd Hall group remains inside that group. -/
theorem oddCartanPart_le (D_H : Subgroup G) : oddCartanPart D_H ≤ D_H :=
  map_subtype_le _

/-- The actual odd Hall group lies in O²(H), so its source subgroup D₀ does too.
This needs no identification of the odd Hall group with a model torus. -/
theorem oddCartanPart_le_residual_of_hall [Finite G] (M D_H : Subgroup G)
    (hDH : D_H ≤ H ⊓ M)
    (hHall : IsHallSubgroup OddHall.oddPrimes (D_H.subgroupOf (H ⊓ M))) :
    oddCartanPart D_H ≤ outsideResidual H := by
  have ho : Odd (Nat.card D_H) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv]
    exact OddHall.odd_hall_odd hHall
  have hoH : Odd (Nat.card (D_H.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hDH.trans inf_le_left)).toEquiv]
    exact ho
  have hr : D_H.subgroupOf H ≤ pResidual 2 H :=
    OddHall.odd_subgroup_le (pResidual 2 H) _ (isPGroup_quotient_pResidual 2) hoH
  apply (oddCartanPart_le D_H).trans
  intro d hd
  exact ⟨⟨d,(hDH hd).1⟩,hr hd,rfl⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
