module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Enlarging a point stabilizer on an elementary group of order 32

Automorphisms of an elementary abelian two-group act transitively on its
nonidentity elements: an isomorphism between the corresponding lines extends
to the whole binary vector space. In order 32 the point stabilizer therefore
has prime index 31 and order 322560. Any overgroup that moves the marked point
is the full automorphism group.
-/

namespace MulAut

open scoped IsMulCommutative

private theorem exists_map_nonidentity
    {E : Type*} [Group E] [IsElementaryAbelian 2 E]
    (x y : E) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : MulAut E, a x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Additive E)
    (Additive.ofMul x) hx
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Additive E)
    (Additive.ofMul y) hy
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨MulEquiv.toAdditive.symm g.toAddEquiv, ?_⟩
  change g (Additive.ofMul x) = Additive.ofMul y
  have h := hg (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  have hx1 : (ex 1 : Additive E) = Additive.ofMul x :=
    congrArg Subtype.val (LinearEquiv.toSpanNonzeroSingleton_one
      (ZMod 2) (Additive E) (Additive.ofMul x) hx)
  have hy1 : (ey 1 : Additive E) = Additive.ofMul y :=
    congrArg Subtype.val (LinearEquiv.toSpanNonzeroSingleton_one
      (ZMod 2) (Additive E) (Additive.ofMul y) hy)
  exact (congrArg g hx1).symm.trans (h.symm.trans hy1)

/-- The full point stabilizer on an elementary group of order 32 has index 31. -/
public theorem index_stabilizer_of_elementary_thirtyTwo
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (z : E) (hz : z ≠ 1) :
    (MulAction.stabilizer (MulAut E) z).index = 31 := by
  have horbit : MulAction.orbit (MulAut E) z = ({1} : Set E)ᶜ := by
    ext w
    constructor
    · rintro ⟨a, rfl⟩ he
      exact hz (a.injective (he.trans (map_one a).symm))
    · intro hw
      obtain ⟨a, ha⟩ := exists_map_nonidentity z w hz hw
      exact MulAction.mem_orbit_iff.mpr ⟨a, ha⟩
  rw [MulAction.index_stabilizer, horbit, Set.ncard_compl, hE,
    Set.ncard_singleton]

/-- The full point stabilizer on an elementary group of order 32 has order 322560. -/
public theorem card_stabilizer_of_elementary_thirtyTwo
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (z : E) (hz : z ≠ 1) :
    Nat.card (MulAction.stabilizer (MulAut E) z) = 322560 := by
  have h := (MulAction.stabilizer (MulAut E) z).card_mul_index
  rw [index_stabilizer_of_elementary_thirtyTwo hE z hz,
    SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E 5
      (by simpa using hE)] at h
  norm_num [Fin.prod_univ_succ] at h
  change Nat.card (MulAction.stabilizer (MulAut E) z) * 31 = 9999360 at h
  omega

/-- A full point stabilizer and an automorphism moving its point force the whole
automorphism group of the given elementary group of order 32. -/
public theorem eq_top_of_elementaryThirtyTwo_stabilizer_of_moves
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 32) (A : Subgroup (MulAut E)) (z : E) (hz : z ≠ 1)
    (hSA : MulAction.stabilizer (MulAut E) z ≤ A)
    (hmoves : ∃ a ∈ A, a z ≠ z) : A = ⊤ := by
  have hindex := index_stabilizer_of_elementary_thirtyTwo hE z hz
  have hdvd : A.index ∣ 31 := hindex ▸ Subgroup.index_dvd_of_le hSA
  rcases (show Nat.Prime 31 by decide).eq_one_or_self_of_dvd _ hdvd with h | h
  · exact Subgroup.index_eq_one.mp h
  · have hrel := Subgroup.relIndex_mul_index hSA
    rw [h, hindex] at hrel
    have hAS : A ≤ MulAction.stabilizer (MulAut E) z :=
      Subgroup.relIndex_eq_one.mp (by omega)
    obtain ⟨a, ha, hmove⟩ := hmoves
    exact (hmove (hAS ha)).elim

end MulAut
