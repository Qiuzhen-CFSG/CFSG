module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MatrixOrbit

/-!
# The literal rank-one determinant subgroup

The two marked point stabilizers generate exactly the left SL₂ factor
and the right point involution. The cubic word supplies the reverse
inclusion, while the right-factor condition supplies the forward one.
This is the finite image calculation for J=⟨U,Uʸ⟩ in 15.3.56.
-/

@[expose] public noncomputable section
open Matrix Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MatrixOrbit
open ClassicalOrthogonal.FourPlusMatrix
open ClassicalOrthogonal.FourPlusMatrix.PrimeFieldTwo
abbrev P := PairSL (F := ZMod 2)

def rightProjection : P →* P :=
  { toFun := fun a => (1, a.2)
    map_one' := rfl
    map_mul' := fun _ _ => by ext <;> simp }

def rankOne (X : M) : Subgroup P := (stabilizer X).comap rightProjection

private theorem stabilizer_right_fix (X : M) (hX : X ≠ 0) (hs : X.det = 0)
    (a : P) (ha : matrixAction a X = X) : matrixAction (1, a.2) X = X := by
  exact (show ∀ X : M, X ≠ 0 → X.det = 0 → ∀ a : P,
    matrixAction a X = X → matrixAction (1, a.2) X = X by decide +kernel) X hX hs a ha

/-- Exact generation by the source pair of point stabilizers. -/
theorem rankOne_generated (X : M) (hX : X ≠ 0) (hs : X.det = 0) :
    stabilizer X ⊔ (stabilizer X).map (MulAut.conj leftCubic⁻¹).toMonoidHom =
      rankOne X := by
  let J := stabilizer X ⊔ (stabilizer X).map (MulAut.conj leftCubic⁻¹).toMonoidHom
  have hS : stabilizer X ≤ rankOne X := by
    intro a ha
    exact stabilizer_right_fix X hX hs a ha
  have hconj (u : P) : (MulAut.conj leftCubic⁻¹ u).2 = u.2 := by
    change ((1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))⁻¹ * u.2) *
      (1⁻¹)⁻¹ = u.2
    simp
  have hJ : J ≤ rankOne X := by
    apply sup_le hS
    rintro _ ⟨u, hu, rfl⟩
    change matrixAction (1, (MulAut.conj leftCubic⁻¹ u).2) X = X
    rw [hconj]
    exact hS hu
  have hc : leftCubic ∈ J := by
    obtain ⟨u, hu, he⟩ := cubic_word X hX hs
    have huJ : u ∈ J := (show stabilizer X ≤ J from le_sup_left) hu
    have huc : leftCubic⁻¹ * u * leftCubic ∈ J := by
      apply (show (stabilizer X).map (MulAut.conj leftCubic⁻¹).toMonoidHom ≤ J
        from le_sup_right)
      refine ⟨u, hu, ?_⟩
      change leftCubic⁻¹ * u * (leftCubic⁻¹)⁻¹ = leftCubic⁻¹ * u * leftCubic
      rw [inv_inv]
    have hword := J.pow_mem (J.mul_mem huJ huc) 2
    exact he ▸ hword
  apply le_antisymm hJ
  intro a ha
  obtain ⟨k, u, hu, rfl⟩ := rank_one_words X hX hs a ha
  exact J.mul_mem (J.pow_mem hc k.val) (mem_sup_left hu)

/-- The image has the source order twelve, before taking its plane kernel. -/
theorem rankOne_card (X : M) (hX : X ≠ 0) (hs : X.det = 0) : Nat.card (rankOne X) = 12 := by
  change Nat.card {a : P // matrixAction (1, a.2) X = X} = 12
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact (show ∀ X : M, X ≠ 0 → X.det = 0 →
    (Finset.univ.filter (fun a : P => matrixAction (1, a.2) X = X)).card = 12
    by decide +kernel) X hX hs

/-- The full left factor is the plane actor; all its matrices lift literally. -/
def rankOneLeft (X : M) : rankOne X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  (MonoidHom.fst _ _).comp (rankOne X).subtype

theorem rankOneLeft_surjective (X : M) : Function.Surjective (rankOneLeft X) := by
  intro a
  refine ⟨⟨(a, 1), ?_⟩, rfl⟩
  change matrixAction (1, 1) X = X
  change matrixHom (1 : P) X = X
  rw [map_one]
  rfl

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MatrixOrbit
