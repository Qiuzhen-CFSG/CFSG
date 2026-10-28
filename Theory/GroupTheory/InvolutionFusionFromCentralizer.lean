module
public import Mathlib.GroupTheory.Sylow

/-!
# Global involution fusion from an involution centralizer

If every involution commuting with an involution `j` in a finite group is
conjugate to `j`, then every involution of the group is conjugate to `j`.
This is the reduction in Brauer, *On finite Desarguesian planes I*, (2A),
article page 119. Brauer obtains the local hypothesis from his postulates
(I) and (III); the reduction itself only needs the hypothesis stated here.

Choose a Sylow 2-subgroup containing `j`. Its nontrivial center contains an
involution `z`, by the p-group center theorem and Cauchy's theorem. The local
hypothesis conjugates `z` to `j`. Any other involution is conjugate into the
same Sylow subgroup and hence commutes with `z`; transporting this commuting
pair and applying the local hypothesis again proves the result.

The theorem supports the involution-based incidence geometry in Brauer's
recognition of PSL₃(q), which ABG uses for its Third Main Theorem. It is
independent of that recognition theorem and of the ABG campaign.
-/

open scoped Pointwise

namespace Theory.GroupTheory

private theorem exists_sylow_mem_involution {G : Type*} [Group G] [Finite G]
    {x : G} (hx : orderOf x = 2) : ∃ S : Sylow 2 G, x ∈ S := by
  have hp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by simpa only [Nat.card_zpowers, pow_one] using hx)
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  exact ⟨S, hS (Subgroup.mem_zpowers x)⟩

private theorem exists_isConj_mem_sylow {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) {x : G} (hx : orderOf x = 2) :
    ∃ y : S, orderOf y = 2 ∧ IsConj x (y : G) := by
  obtain ⟨T, hxT⟩ := exists_sylow_mem_involution hx
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  have hy : (MulAut.conj g) x ∈ S := by
    rw [← hg]
    change (MulAut.conj g) • x ∈ (MulAut.conj g) • (T : Set G)
    exact Set.smul_mem_smul_set hxT
  refine ⟨⟨(MulAut.conj g) x, hy⟩, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx]
  · exact isConj_iff.mpr ⟨g, rfl⟩

private theorem exists_central_involution {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) [Nontrivial S] :
    ∃ z : S, z ∈ Subgroup.center S ∧ orderOf z = 2 := by
  let : Nontrivial (Subgroup.center S) := S.isPGroup'.center_nontrivial
  have hZ := S.isPGroup'.to_subgroup (Subgroup.center S)
  obtain ⟨n, hn, hcard⟩ := hZ.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.ne_of_gt hn)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  exact ⟨z, z.property, by simpa only [Subgroup.orderOf_coe] using hz⟩

/-- Fusion of all involutions in the centralizer of `j` into its global class
forces all involutions of the finite group into that class. -/
public theorem isConj_of_involution_of_centralizer_fusion
    {G : Type*} [Group G] [Finite G] {j : G} (hj : orderOf j = 2)
    (hlocal : ∀ y : G, orderOf y = 2 → Commute y j → IsConj y j)
    {x : G} (hx : orderOf x = 2) : IsConj x j := by
  obtain ⟨S, hjS⟩ := exists_sylow_mem_involution hj
  let jS : S := ⟨j, hjS⟩
  have hjne : j ≠ 1 := by
    intro h
    simp [h] at hj
  let : Nontrivial S := ⟨⟨jS, 1, fun h => hjne (congrArg Subtype.val h)⟩⟩
  obtain ⟨z, hzC, hz⟩ := exists_central_involution S
  have hzG : orderOf (z : G) = 2 := by simpa only [Subgroup.orderOf_coe] using hz
  have hzj : Commute (z : G) j := by
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hzC jS).symm)
  obtain ⟨g, hg⟩ := isConj_iff.mp (hlocal z hzG hzj)
  obtain ⟨y, hy, hxy⟩ := exists_isConj_mem_sylow S hx
  have hyz : Commute (y : G) (z : G) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hzC y)
  have hconj : Commute ((MulAut.conj g) (y : G)) j := by
    simpa only [MulAut.conj_apply, hg] using hyz.map (MulAut.conj g)
  have hyG : orderOf ((MulAut.conj g) (y : G)) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hy]
  exact hxy.trans ((isConj_iff.mpr ⟨g, rfl⟩).trans (hlocal _ hyG hconj))

end Theory.GroupTheory
