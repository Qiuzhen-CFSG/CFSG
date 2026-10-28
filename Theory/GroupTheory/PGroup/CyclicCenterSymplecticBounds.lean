module

public import Theory.GroupTheory.PGroup.RankTwoSymplecticBounds

/-!
# Small symplectic two-groups with cyclic center

A non-Hall symplectic two-group with cyclic center is nonabelian and has
order at least sixteen. For the lower bound, a hypothetical group of order
at most eight automatically satisfies the elementary rank bound: an
elementary eight would be the entire group. Thus the existing small-model
argument applies without a rank hypothesis on the original group.

Source: Hall's central-product theorem, as used in Janko–Thompson (1970),
§4, printed pp.389–393.
-/

open Subgroup

namespace IsBinarySymplecticType

/-- Cyclic center and exclusion of the cyclic Hall case force noncommutativity. -/
public theorem not_isMulCommutative_of_cyclic_center_not_hall
    {P : Type*} [Group P] [IsCyclic (center P)]
    (hnot : ¬ IsBinaryHallFactor P) : ¬ IsMulCommutative P := by
  intro hcomm
  let e : center P ≃* P :=
    (MulEquiv.subgroupCongr (center_eq_top_iff.mpr hcomm)).trans topEquiv
  exact hnot (Or.inl (e.isCyclic.mp inferInstance))

/-- No rank assumption is needed for the lower bound when the center is cyclic. -/
public theorem sixteen_le_card_of_cyclic_center_not_hall
    {P : Type*} [Group P] [Finite P] [IsCyclic (center P)]
    (hP : IsPGroup 2 P) (hsymp : IsBinarySymplecticType P)
    (hnot : ¬ IsBinaryHallFactor P) : 16 ≤ Nat.card P := by
  by_contra hbound
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hnle : n ≤ 3 := by
    by_contra h
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show 4 ≤ n by omega)
    rw [← hn] at hp
    norm_num at hp
    omega
  have hsmall : Nat.card P ≤ 8 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) hnle
  have hrank (U : Subgroup P) (hU : IsElementaryAbelian 2 U) : Nat.card U < 8 := by
    by_contra! hlarge
    have htop : U = ⊤ := U.eq_top_of_card_eq (by
      have := U.card_le_card_group
      omega)
    let : IsMulCommutative U := hU.toIsMulCommutative
    have hcomm : IsMulCommutative P := by
      rw [htop] at hU
      let : IsElementaryAbelian 2 (⊤ : Subgroup P) := hU
      exact isMulCommutative_iff.mpr (fun x y => congrArg Subtype.val
        ((isMulCommutative_iff.mp hU.toIsMulCommutative)
          (⟨x, mem_top x⟩ : (⊤ : Subgroup P)) ⟨y, mem_top y⟩))
    exact not_isMulCommutative_of_cyclic_center_not_hall hnot hcomm
  exact hbound (hsymp.sixteen_le_card_of_not_hall hP hrank hnot)

end IsBinarySymplecticType
