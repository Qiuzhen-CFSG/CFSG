module

public import Theory.SpecificGroups.PSL3Three.MaximalClassification
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Theory.PGroupCore

/-!
# Three-cores of subgroups of order 432 in PSL₃(3)

The concrete subgroup cover puts a subgroup of order 432 in a conjugate of a
line stabilizer, plane stabilizer, monomial group or Singer normalizer. Given
the candidate orders 432, 432, 24 and 39, Lagrange's theorem excludes the last
two and gives equality in the first two cases. Actual subgroup equivalences
then transport the intrinsic three-cores.

The candidate orders and the two parabolic core orders remain explicit
premises. In particular these results do not substitute the smaller pointwise
fixing groups for the full parabolics or assert an unproved local calculation.

Source: GLS III, Theorem 6.5.3(a–c), as proved for the concrete matrix
subgroups in `MaximalClassification`; application to Aschbacher–Smith,
combined 1 March 2004 manuscript, proof of Proposition 1.3.4, printed p.511.
-/

@[expose] public section

open Subgroup
namespace Matrix.PSL3Three

private theorem core_card_congr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    Nat.card (pCore 3 G) = Nat.card (pCore 3 H) := by
  rw [← pCore_map_iso 3 e, card_map_of_injective e.injective]

/-- A subgroup of order 432 is isomorphic to an actual parabolic, once the
four concrete candidate orders have been computed. The subgroup cover supplies
an inclusion in a conjugate, and equality follows from the orders. -/
theorem parabolic_equiv_of_card_eq_432
    (hline : Nat.card lineStabilizer = 432)
    (hplane : Nat.card planeStabilizer = 432)
    (hmono : Nat.card monomial = 24)
    (hsinger : Nat.card singerNormalizer = 39)
    (H : Subgroup PSL) (hH : Nat.card H = 432) :
    Nonempty (H ≃* lineStabilizer) ∨ Nonempty (H ≃* planeStabilizer) := by
  have hproper : H ≠ ⊤ := by
    intro he
    rw [he, Subgroup.card_top, card_PSL] at hH
    norm_num at hH
  obtain ⟨g, hg⟩ := proper_subgroup_le_conjugate_PSL H hproper
  have close (K : Subgroup PSL) (hK : Nat.card K = 432)
      (hle : H ≤ K.map (MulAut.conj g).toMonoidHom) : Nonempty (H ≃* K) := by
    have he : H = K.map (MulAut.conj g).toMonoidHom :=
      eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective, hK, hH])
    exact ⟨(MulEquiv.subgroupCongr he).trans ((MulAut.conj g).subgroupMap K).symm⟩
  rcases hg with hh | hh | hh | hh
  · exact Or.inl (close _ hline hh)
  · exact Or.inr (close _ hplane hh)
  · have hd := card_dvd_of_le hh
    rw [hH, card_map_of_injective (MulAut.conj g).injective, hmono] at hd
    norm_num at hd
  · have hd := card_dvd_of_le hh
    rw [hH, card_map_of_injective (MulAut.conj g).injective, hsinger] at hd
    norm_num at hd

/-- The order-nine three-core calculation for all subgroups of order 432
reduces to the two concrete full parabolics and the four candidate orders.
Every numerical premise is explicit; this does not assert those computations. -/
theorem threeCore_card_of_card_eq_432_of_parabolic_calculations
    (hline : Nat.card lineStabilizer = 432)
    (hplane : Nat.card planeStabilizer = 432)
    (hmono : Nat.card monomial = 24)
    (hsinger : Nat.card singerNormalizer = 39)
    (hlineCore : Nat.card (pCore 3 lineStabilizer) = 9)
    (hplaneCore : Nat.card (pCore 3 planeStabilizer) = 9)
    (H : Subgroup PSL) (hH : Nat.card H = 432) :
    Nat.card (pCore 3 H) = 9 := by
  rcases parabolic_equiv_of_card_eq_432 hline hplane hmono hsinger H hH with he | he
  · obtain ⟨e⟩ := he
    exact (core_card_congr e).trans hlineCore
  · obtain ⟨e⟩ := he
    exact (core_card_congr e).trans hplaneCore


end Matrix.PSL3Three
