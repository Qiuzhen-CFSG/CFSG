module

public import Theory.SpecificGroups.Suzuki.SylowOmegaGeometry
public import Theory.SpecificGroups.Suzuki.RootSquareFibers

/-!
# Nonidentity squares in a prescribed Suzuki Sylow subgroup

The root center has order q>1 and every central element is a square.
An equivalence adjusted by Sylow conjugacy therefore supplies a nonidentity
square in any prescribed Sylow two-subgroup of an actual Suzuki carrier.

Source: Huppert--Blackburn III, XI.3.1. The symplectic Borel-placement
consumer uses this square to recover the original ambient unipotent group.
-/

public section
open Subgroup
namespace BenderSuzuki.MatrixGroups

/-- Every prescribed Suzuki Sylow contains an element with nonidentity
square, retaining the actual matrix-model equivalence. -/
theorem suzukiSylow_exists_nontrivial_square
    {G : Type*} [Group G] [Finite G] {m : ℕ} (hm : 0<m)
    (e : G ≃* SuzukiMatrixGroup m) (S : Sylow 2 G) :
    ∃x : S, x^2≠1 := by
  obtain ⟨f,hS,_⟩ := suzukiSylow_aligned_equiv hm e S
  let a : SuzukiRootSubgroup m ≃* S :=
    ((SuzukiRootSubgroup m).equivMapOfInjective f.toMonoidHom f.injective).trans
      (MulEquiv.subgroupCongr hS)
  have hc : 1 < Nat.card (center (SuzukiRootSubgroup m)) := by
    rw [suzukiRootSubgroup_center_card m hm]
    exact Nat.one_lt_pow (by omega) (by decide)
  let : Nontrivial (center (SuzukiRootSubgroup m)) :=
    Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨z,hz⟩ := exists_ne (1 : center (SuzukiRootSubgroup m))
  obtain ⟨x,hx⟩ := suzukiRootSubgroup_square_surjective m hm z
  refine ⟨a x,?_⟩
  intro h
  have hh : x^2=1 := a.map_eq_one_iff.mp (by simpa only [map_pow] using h)
  exact hz (Subtype.ext (hx.symm.trans hh))

end BenderSuzuki.MatrixGroups
