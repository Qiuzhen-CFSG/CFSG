module

public import GorensteinWalter.BrauerSuzukiWallDefs
public import FeitThompson.BGsection1.theorem_1_13

/-!
# Dihedral involution centralizers: the I.4.1 hypotheses

This is the exact local input of Aschbacher–Smith, *The Classification of
Quasithin Groups*, I.4.1, printed p. 415. The parameter `n` is the exponent
of the centralizer order, so the dihedral model has rotation order
`2 ^ (n - 1)`. No simplicity assumption is imposed.

A central involution of a Sylow subgroup is conjugate to the distinguished
involution. Conjugating the whole Sylow subgroup into its centralizer shows
that the centralizer itself is Sylow. This adapts the two-primary argument
in `GorensteinWalter.BrauerSuzukiWallHall` without assuming the remaining
Brauer–Suzuki–Wall configuration data.
-/

open scoped Pointwise

namespace CFSG.Quasithin

open GorensteinWalter

/-- The hypotheses of I.4.1, with centralizer order `2 ^ n`. -/
public structure DihedralInvolutionCentralizerHypotheses
    (G : Type*) [Group G] [Finite G] (n : ℕ) where
  two_le : 2 ≤ n
  z : G
  involution : IsInvolution z
  involutions_conjugate : ∀ u : G, IsInvolution u → ∃ g : G, g * u * g⁻¹ = z
  centralizer_equiv : Nonempty
    (Subgroup.centralizer ({z} : Set G) ≃* DihedralGroup (2 ^ (n - 1)))

namespace DihedralInvolutionCentralizerHypotheses
variable {G : Type*} [Group G] [Finite G] {n : ℕ}

/-- The centralizer has the order prescribed in the source. -/
public theorem centralizer_card (h : DihedralInvolutionCentralizerHypotheses G n) :
    Nat.card (Subgroup.centralizer ({h.z} : Set G)) = 2 ^ n := by
  calc
    _ = Nat.card (DihedralGroup (2 ^ (n - 1))) :=
      Nat.card_congr h.centralizer_equiv.some.toEquiv
    _ = 2 * 2 ^ (n - 1) := DihedralGroup.nat_card
    _ = 2 ^ n := by
      rw [mul_comm, ← pow_succ]
      congr 1
      have := h.two_le
      omega

/-- The distinguished involution centralizer is a two-group. -/
public theorem centralizer_isPGroup (h : DihedralInvolutionCentralizerHypotheses G n) :
    IsPGroup 2 (Subgroup.centralizer ({h.z} : Set G)) :=
  IsPGroup.of_card h.centralizer_card


/-- The involution centralizer is an ambient Sylow two-subgroup. -/
public theorem centralizer_isSylow (h : DihedralInvolutionCentralizerHypotheses G n) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = Subgroup.centralizer ({h.z} : Set G) := by
  classical
  obtain ⟨Q, hCQ⟩ := IsPGroup.exists_le_sylow h.centralizer_isPGroup
  have hzQ : h.z ∈ (Q : Subgroup G) := hCQ (by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have : y = h.z := by simpa using hy
    subst y
    rfl)
  let : Fact (IsPGroup 2 Q) := ⟨Q.isPGroup'⟩
  have : Nontrivial Q := by
    refine ⟨⟨⟨h.z, hzQ⟩, 1, ?_⟩⟩
    intro heq
    exact h.involution.1 (congrArg Subtype.val heq)
  obtain ⟨t, _, htCenter, htNe, htSq⟩ :=
    exists_nontrivial_mem_center_of_normal_p_subgroup
      (G := Q) (p := 2) (⊤ : Subgroup Q) top_ne_bot
  have htI : IsInvolution (t : G) := by
    refine ⟨?_, congrArg Subtype.val htSq⟩
    intro htOne
    exact htNe (Subtype.ext htOne)
  obtain ⟨g, hgt⟩ := h.involutions_conjugate (t : G) htI
  let S : Sylow 2 G := g • Q
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer ({h.z} : Set G) := by
    intro x hx
    change x ∈ ((g • Q : Sylow 2 G) : Subgroup G) at hx
    rw [Sylow.coe_subgroup_smul] at hx
    rcases Set.mem_smul_set.mp hx with ⟨q, hqQ, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyz : y = h.z := by simpa using hy
    rw [hyz, ← hgt]
    have hcomm : q * (t : G) = (t : G) * q :=
      congrArg Subtype.val ((Subgroup.mem_center_iff.mp htCenter) ⟨q, hqQ⟩)
    calc
      (g * (t : G) * g⁻¹) * (g * q * g⁻¹) =
          g * ((t : G) * q) * g⁻¹ := by group
      _ = g * (q * (t : G)) * g⁻¹ := by rw [hcomm]
      _ = (g * q * g⁻¹) * (g * (t : G) * g⁻¹) := by group
  exact ⟨S, (S.is_maximal' h.centralizer_isPGroup hSC).symm⟩

/-- All Sylow two-subgroups have the prescribed dihedral type. -/
public theorem hasDihedralSylowTwo (h : DihedralInvolutionCentralizerHypotheses G n) :
    HasDihedralSylowTwo G := by
  obtain ⟨S, hS⟩ := h.centralizer_isSylow
  intro T
  refine ⟨n - 1, by have := h.two_le; omega, ?_⟩
  exact ⟨(Sylow.equiv T S).trans
    ((MulEquiv.subgroupCongr hS).trans h.centralizer_equiv.some)⟩

end DihedralInvolutionCentralizerHypotheses
end CFSG.Quasithin
