module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddTwoPrimary.LocalModel
public import Theory.GroupTheory.PerfectCentralCoverSquareObstruction
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.Reduction

/-!
# Eliminating the diagonal defect in the odd G₂ local cover

In a central double extension, lift both SL₂ factors using their proved
two-primary splitting theorem. Perfectness makes their lifts commute.
Fusion of the outer generator with a scalar involution extends the lift to
the semidirect product. Its only possible descent defect is the diagonal
scalar involution. The paired order-four element squares to this defect,
whereas fusion to a scalar involution forces its lift to have square one.
Thus the lift descends to a section of the actual odd-index image.

Transfer excludes double covers. The prime-order quotient theorem then
excludes two from arbitrary finite perfect central kernels. The concrete
local homomorphism and the two conjugacies are still explicit inputs.

Source: the local covering calculation for Aschbacher–Smith I.1.1–I.1.4,
printed pp.407–408, and GLS III §6.1.
-/

public section

namespace Atlas.G2.MultiplierOrdinary.OddTwoPrimary
open PerfectCentralCovering Subgroup

private theorem rankOne_perfect {p : ℕ} [Fact p.Prime] (hp : 3 < p) :
    Group.IsPerfect (RankOne p) := by
  have h2 : (2 : ZMod p) ≠ 0 := fun h =>
    Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  have hsq : (2 : ZMod p) ^ 2 ≠ 1 := by
    intro h
    have h3 : (3 : ZMod p) = 0 := by linear_combination h
    exact Nat.not_dvd_of_pos_of_lt (by decide) hp
      ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
  exact ⟨Matrix.SL2.commutator_eq_top h2 hsq⟩

namespace LocalModel
variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] (m : LocalModel p G)

/-- The marked local map is injective on each individual SL₂ factor. -/
theorem left_injective : Function.Injective
    ((m.inclusion.comp SemidirectProduct.inl).comp
      (MonoidHom.inl (RankOne p) (RankOne p))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  rcases (m.kernel _).mp hx with h | h
  · exact congrArg (fun x : m.Domain => x.left.1) h
  · exact (congrArg (fun x : m.Domain => x.left.1) h).trans
      (congrArg (fun x : m.Domain => x.left.2) h).symm

/-- The second rank-one factor also has trivial intersection with the
diagonal kernel. -/
theorem right_injective : Function.Injective
    ((m.inclusion.comp SemidirectProduct.inl).comp
      (MonoidHom.inr (RankOne p) (RankOne p))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  rcases (m.kernel _).mp hx with h | h
  · exact congrArg (fun x : m.Domain => x.left.2) h
  · exact (congrArg (fun x : m.Domain => x.left.2) h).trans
      (congrArg (fun x : m.Domain => x.left.1) h).symm

/-- The diagonal central-product defect vanishes in a double extension
once its square-root element fuses to the marked scalar involution. -/
theorem diagonal_lift_eq_one
    {E : Type*} [Group E] (f : E →* G) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2)
    (t : m.Domain →* E) (ht : f.comp t = m.inclusion)
    (hpair : IsConj (m.inclusion m.scalar) (m.inclusion m.paired)) :
    t m.diagonal = 1 := by
  have ht' (x : m.Domain) : f (t x) = m.inclusion x := DFunLike.congr_fun ht x
  have hexp (k : E) (h : k ∈ f.ker) : k ^ 2 = 1 := by
    have he := pow_card_eq_one' (x := (⟨k, h⟩ : f.ker))
    rw [hk] at he
    exact congrArg Subtype.val he
  obtain ⟨g, hg⟩ := isConj_iff.mp hpair
  obtain ⟨a, ha⟩ := hf g
  have he : f (t m.paired) = f (a * t m.scalar * a⁻¹) := by
    rw [map_mul, map_mul, map_inv, ha, ht', ht']
    exact hg.symm
  rw [← m.paired_sq, map_pow,
    square_eq_of_map_eq_of_kernel_exponent_two f hc hexp he,
    conj_pow, ← map_pow, m.scalar_sq, map_one]
  simp

/-- The two actual fusion identities split every finite central double
extension over the specified odd-index image. -/
theorem exists_section_of_double_kernel (hp : 3 < p)
    (houter : IsConj (m.inclusion m.scalar) (m.inclusion m.outer))
    (hpair : IsConj (m.inclusion m.scalar) (m.inclusion m.paired))
    {E : Type*} [Group E] [Finite E]
    (f : E →* G) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hk : Nat.card f.ker = 2) :
    ∃ s : m.inclusion.range →* E, f.comp s = m.inclusion.range.subtype := by
  let : Group.IsPerfect (RankOne p) := rankOne_perfect hp
  let : Group.IsPerfect (RankOne p × RankOne p) := ⟨by
    change ⁅(⊤ : Subgroup (RankOne p × RankOne p)), ⊤⁆ = ⊤
    rw [← top_prod_top, commutator_prod_prod]
    change (commutator (RankOne p)).prod (commutator (RankOne p)) =
      (⊤ : Subgroup (RankOne p)).prod ⊤
    simp⟩
  have hkp : IsPGroup 2 f.ker := IsPGroup.of_card (n := 1) (by simpa using hk)
  let j := m.inclusion.comp SemidirectProduct.inl
  obtain ⟨sl, hsl⟩ := exists_lift_of_splits_central_pGroup
    (fun _ _ _ q hq hqc hqk =>
      Matrix.SpecialLinearGroup.exists_section_of_central_two_kernel hp q hq hqc hqk)
    f hf hc hkp (j.comp (MonoidHom.inl _ _)) m.left_injective
  obtain ⟨sr, hsr⟩ := exists_lift_of_splits_central_pGroup
    (fun _ _ _ q hq hqc hqk =>
      Matrix.SpecialLinearGroup.exists_section_of_central_two_kernel hp q hq hqc hqk)
    f hf hc hkp (j.comp (MonoidHom.inr _ _)) m.right_injective
  obtain ⟨s, hs⟩ := exists_product_lift_of_factor_lifts f hc j sl sr hsl hsr
  obtain ⟨t, ht⟩ := exists_lift_semidirect_of_involution_fusion
    f hf hc m.action m.inclusion s hs (-1, 1) (by ext <;> simp) houter
  have hd := m.diagonal_lift_eq_one f hf hc hk t ht hpair
  have hker : m.inclusion.ker ≤ t.ker := by
    intro x hx
    rcases (m.kernel x).mp hx with rfl | rfl
    · exact map_one t
    · exact hd
  let q := QuotientGroup.lift m.inclusion.ker t hker
  let e := QuotientGroup.quotientKerEquivRange m.inclusion
  refine ⟨q.comp e.symm.toMonoidHom, ?_⟩
  ext x
  obtain ⟨a, ha⟩ := x.property
  have hx : x = m.inclusion.rangeRestrict a := Subtype.ext ha.symm
  rw [hx]
  have he : e.symm (m.inclusion.rangeRestrict a) =
      QuotientGroup.mk' m.inclusion.ker a := e.symm_apply_eq.mpr rfl
  change f (q (e.symm (m.inclusion.rangeRestrict a))) = m.inclusion a
  rw [he]
  exact DFunLike.congr_fun ht a

/-- Prime-order central quotient reduction and the local section exclude
two from every finite perfect central kernel. -/
theorem not_two_dvd_kernel [Finite G] (hp : 3 < p)
    (houter : IsConj (m.inclusion m.scalar) (m.inclusion m.outer))
    (hpair : IsConj (m.inclusion m.scalar) (m.inclusion m.paired))
    {E : Type*} [Group E] [Finite E] (f : Cover E G) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  intro hdiv
  obtain ⟨D, hD, hDf, g, hg⟩ := PrimaryReduction.exists_prime_order_quotient f hdiv
  let := hD
  let := hDf
  obtain ⟨s, hs⟩ := m.exists_section_of_double_kernel hp houter hpair
    g.toMonoidHom g.surjective g.ker_le_center hg
  exact not_dvd_card_kernel_of_section g m.inclusion.range
    m.odd_index.not_two_dvd_nat s hs (hg ▸ dvd_rfl)

end LocalModel
end Atlas.G2.MultiplierOrdinary.OddTwoPrimary

end
