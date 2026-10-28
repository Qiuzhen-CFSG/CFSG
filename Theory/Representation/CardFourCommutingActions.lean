module

public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Commuting actions on the four-point elementary abelian group

A faithful group of order three acting on an elementary abelian group of
order four is a Sylow `3`-subgroup of `GL₂(2)`.  Its centralizer in
`GL₂(2)` has order three: it contains that cyclic subgroup, while a larger
centralizer would make it central, contradicting the trivial center of
`GL₂(2)`.  Hence the image of a commuting order-two action has order
dividing both two and three and is trivial.

This is the finite two-dimensional calculation used for the local `SL₂(2)`
coordinates in Stellmacher's Lemma (1.6), journal p. 17.
-/

namespace Representation

open scoped Pointwise
open scoped IsMulCommutative

universe uD uQ uU

private theorem glTwoTwo_center_eq_bot :
    Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = ⊥ := by
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  ext A
  constructor
  · rintro ⟨x, rfl⟩
    have hx : x = 1 := Subsingleton.elim _ _
    simp [hx]
  · intro hA
    have hAone : A = 1 := by simpa using hA
    subst A
    exact ⟨1, by simp⟩

/-- An order-two group acting on the four-point elementary abelian group and
commuting with a faithful order-three action acts trivially. -/
public theorem actsTrivially_card_four_of_commuting_card_three_action
    {D : Type uD} {Q : Type uQ} {U : Type uU}
    [Group D] [Group Q] [Group U] [Finite D] [Finite Q] [Finite U]
    [IsElementaryAbelian 2 U]
    [MulDistribMulAction D U] [MulDistribMulAction Q U]
    (hUcard : Nat.card U = 4)
    (hDcard : Nat.card D = 3)
    (hDfaith : Function.Injective
      (ofElementaryAbelianAction (A := D) (G := U) (p := 2)).asGroupHom)
    (hQcard : Nat.card Q = 2)
    (hcomm : ∀ d : D, ∀ q : Q, ∀ u : U,
      d • (q • u) = q • (d • u)) :
    ActsTrivially (A := Q) (G := U) := by
  let nU := Module.finrank (ZMod 2) (Additive U)
  have hnU : nU = 2 := by
    have hc : Nat.card (Additive U) = 4 := by
      calc
        Nat.card (Additive U) = Nat.card U := Nat.card_congr Additive.toMul
        _ = 4 := hUcard
    rw [@Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive U)] at hc
    norm_num at hc
    change 2 ^ nU = 2 ^ 2 at hc
    exact Nat.pow_right_injective (by omega) hc
  let b : Module.Basis (Fin 2) (ZMod 2) (Additive U) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive U) hnU
  let ρD := ofElementaryAbelianAction (A := D) (G := U) (p := 2)
  let ρQ := ofElementaryAbelianAction (A := Q) (G := U) (p := 2)
  let φD : D →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρD.asGroupHom
  let φQ : Q →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρQ.asGroupHom
  have hφDinj : Function.Injective φD :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hDfaith
  have hGLcard :
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = 6 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  have hφDcard : Nat.card φD.range = 3 := by
    calc
      Nat.card φD.range = Nat.card D :=
        Nat.card_congr
          (Equiv.ofBijective φD.rangeRestrict
            ⟨fun x y hxy => hφDinj (congrArg Subtype.val hxy),
              φD.rangeRestrict_surjective⟩).symm
      _ = 3 := hDcard
  have hρcomm (d : D) (q : Q) : Commute (ρD.asGroupHom d) (ρQ.asGroupHom q) := by
    apply Units.ext
    apply LinearMap.ext
    intro u
    exact congrArg Additive.ofMul (hcomm d q (Additive.toMul u))
  have hφcomm (d : D) (q : Q) : Commute (φD d) (φQ q) := by
    change (Matrix.GeneralLinearGroup.toLin' b).symm (ρD.asGroupHom d) *
        (Matrix.GeneralLinearGroup.toLin' b).symm (ρQ.asGroupHom q) =
      (Matrix.GeneralLinearGroup.toLin' b).symm (ρQ.asGroupHom q) *
        (Matrix.GeneralLinearGroup.toLin' b).symm (ρD.asGroupHom d)
    rw [← map_mul, (hρcomm d q).eq, map_mul]
  let C := Subgroup.centralizer (φD.range : Set
    (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)))
  let hthree : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fact (Nat.Prime 3) := hthree
  let hφDcyclic : IsCyclic φD.range := isCyclic_of_prime_card hφDcard
  let _ : IsMulCommutative φD.range := hφDcyclic.isMulCommutative
  have hφDleC : φD.range ≤ C := by
    simpa only [C] using Subgroup.le_centralizer φD.range
  have hthree_dvd_C : 3 ∣ Nat.card C := by
    simpa only [hφDcard] using Subgroup.card_dvd_of_le hφDleC
  have hC_dvd_six : Nat.card C ∣ 6 := by
    simpa only [hGLcard] using Subgroup.card_subgroup_dvd_card C
  have hCcard : Nat.card C = 3 := by
    have hCpos : 0 < Nat.card C := Nat.card_pos
    have hCle : Nat.card C ≤ 6 := Nat.le_of_dvd (by norm_num) hC_dvd_six
    obtain ⟨k, hk⟩ := hthree_dvd_C
    have hcases : Nat.card C = 3 ∨ Nat.card C = 6 := by
      omega
    rcases hcases with hthree | hsix
    · exact hthree
    · have hCtop : C = ⊤ :=
        Subgroup.eq_top_of_card_eq C (by rw [hGLcard]; exact hsix)
      have hcenter :
          Subgroup.center
              (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) = ⊥ :=
        glTwoTwo_center_eq_bot
      have hφDcenter : φD.range ≤ Subgroup.center
          (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)) := by
        exact (Subgroup.centralizer_eq_top_iff_subset.mp (by
          simpa only [C] using hCtop))
      rw [hcenter] at hφDcenter
      have hφDbot : φD.range = ⊥ := le_antisymm hφDcenter bot_le
      have hcardOne : Nat.card φD.range = 1 := by rw [hφDbot]; simp
      omega
  have hφQleC : φQ.range ≤ C := by
    rintro x ⟨q, rfl⟩
    change φQ q ∈ Subgroup.centralizer (φD.range : Set
      (Matrix.GeneralLinearGroup (Fin 2) (ZMod 2)))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hy with ⟨d, rfl⟩
    exact (hφcomm d q).eq
  have hφQ_dvd_three : Nat.card φQ.range ∣ 3 := by
    simpa only [hCcard] using Subgroup.card_dvd_of_le hφQleC
  have hφQ_dvd_two : Nat.card φQ.range ∣ 2 := by
    simpa only [hQcard] using Subgroup.card_range_dvd φQ
  have hφQcard : Nat.card φQ.range = 1 := by
    exact Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 2)
      hφQ_dvd_three hφQ_dvd_two
  have hφQbot : φQ.range = ⊥ := Subgroup.card_eq_one.mp hφQcard
  intro q u
  have hφQone : φQ q = 1 := by
    have hmem : φQ q ∈ φQ.range := ⟨q, rfl⟩
    rw [hφQbot] at hmem
    simpa using hmem
  have hρQone : ρQ.asGroupHom q = 1 := by
    apply (Matrix.GeneralLinearGroup.toLin' b).symm.injective
    change φQ q = (Matrix.GeneralLinearGroup.toLin' b).symm 1
    simpa only [map_one] using hφQone
  have happ := congrArg
    (fun f : LinearMap.GeneralLinearGroup (ZMod 2) (Additive U) =>
      LinearMap.GeneralLinearGroup.toLinearEquiv f (Additive.ofMul u)) hρQone
  change ρQ q (Additive.ofMul u) = Additive.ofMul u at happ
  apply Additive.ofMul.injective
  simpa [ρQ] using happ

end Representation
