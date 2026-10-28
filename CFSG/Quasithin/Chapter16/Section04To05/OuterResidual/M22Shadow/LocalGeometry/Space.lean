module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.Reductions
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The elementary shadow space

Once the preparatory argument has established R₀ = 1, Q ≅ E₁₆ and
outer symmetry, the marked r and z are independent of Q. They commute
with Q and each other. Two internal direct-product calculations therefore
give |Q⟨r,z⟩| = 64, and the commuting-join theorem gives exponent two.
The needed preparation remains explicit; these lemmas do not assert it.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.7, printed p.1186.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

private theorem disjoint_zpowers_of_order_two (A : Subgroup G) {x : G}
    (hx : orderOf x = 2) (hnot : x ∉ A) : Disjoint A (zpowers x) := by
  classical
  apply Subgroup.disjoint_def.mpr
  intro a ha hx'
  rw [mem_zpowers_iff_mem_range_orderOf, hx] at hx'
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hx'
  have hn2 := Finset.mem_range.mp hn
  interval_cases n
  · simpa using he.symm
  · exact (hnot (by simpa only [← he, pow_one] using ha)).elim

/-- The original marked involution centralizes Q. -/
theorem residualCore_zpowers_centralize (h : IntersectionSetup T z L g R) :
    zpowers z ≤ centralizer (residualCore L r : Set G) := by
  apply zpowers_le.mpr
  intro q hq
  exact (mem_centralizer_singleton_iff.mp
    (residualCore_le_original_centralizer h hq))

omit [Finite G] in
/-- The residual defining Q is inside the centralizer of r. -/
theorem residualCore_zpowers_r_centralize :
    zpowers r ≤ centralizer (residualCore L r : Set G) := by
  apply zpowers_le.mpr
  intro q hq
  exact (mem_centralizer_singleton_iff.mp
    (residualCore_le_centralizer L r hq))

/-- Both marked elements lie in the Sylow group centralized by z. -/
theorem marked_involutions_commute (h : IntersectionSetup T z L g R) (hr : r ∈ R) :
    Commute r z := by
  exact (mem_centralizer_singleton_iff.mp (h.sylow_centralizes (h.le_sylow hr)))

/-- The actual ambient join is elementary once its residual core is. -/
theorem shadowSpace_elementary (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (hr2 : orderOf r = 2) [IsElementaryAbelian 2 (residualCore L r)] :
    IsElementaryAbelian 2 (shadowSpace L r z) := by
  let : IsElementaryAbelian 2 (zpowers r) :=
    .zpowers_of_pow_eq_one (hr2 ▸ pow_orderOf_eq_one r)
  let : IsElementaryAbelian 2 (zpowers z) :=
    .zpowers_of_pow_eq_one (h.involution ▸ pow_orderOf_eq_one z)
  have he : zpowers z ≤ centralizer (zpowers r : Set G) := by
    apply zpowers_le.mpr
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact ((marked_involutions_commute h hr).zpow_left n).eq
  let : IsElementaryAbelian 2 ↥(zpowers r ⊔ zpowers z) :=
    .sup_of_le_centralizer he
  exact IsElementaryAbelian.sup_of_le_centralizer
    (sup_le residualCore_zpowers_r_centralize (residualCore_zpowers_centralize h))

omit [Finite G] in
/-- Placement in L′ and the outer action of z separate z from Q. -/
theorem residualCore_not_mem_z_of_outer_symmetry
    (hQ : residualCore L r ≤ L.conjBy g)
    (hz : z ∈ normalizer (L.conjBy g : Set G))
    (hout : (L.conjBy g).normalizerMonoidHom ⟨z, hz⟩ ∉
      MulAut.innerSubgroup (L.conjBy g)) : z ∉ residualCore L r := by
  intro hzQ
  apply hout
  refine ⟨⟨z, hQ hzQ⟩, ?_⟩
  ext x
  rfl

/-- Trivial inner part separates r from Q⟨z⟩. -/
theorem marked_r_not_mem_core_z (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥) :
    r ∉ residualCore L r ⊔ zpowers z := by
  have hzK : z ∈ centralizer (L : Set G) := by
    intro x hx
    exact (mem_centralizer_singleton_iff.mp (h.component.1 hx))
  have hle : residualCore L r ⊔ zpowers z ≤ L ⊔ centralizer (L : Set G) :=
    sup_le ((residualCore_le_component L r).trans le_sup_left)
      ((zpowers_le.mpr hzK).trans le_sup_right)
  intro hrQ
  have hm : r ∈ innerPart L R := ⟨hr, hle hrQ⟩
  have hr1 : r = 1 := by rwa [hinner, mem_bot] at hm
  simp [hr1] at hr2

/-- Internal direct-product coordinates, retaining multiplication of the
three specified ambient factors. This is a group equivalence, not yet an
equivariant decomposition for either local normalizer. -/
theorem shadowSpace_product (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hzQ : z ∉ residualCore L r) :
    ∃ e : (residualCore L r × zpowers z) × zpowers r ≃* shadowSpace L r z,
      ∀ q a b, (e ((q, a), b) : G) = (q : G) * (a : G) * (b : G) := by
  have hQz := residualCore_zpowers_centralize (r := r) h
  have hQr := residualCore_zpowers_r_centralize (L := L) (r := r)
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (residualCore L r) (zpowers z)
    (disjoint_zpowers_of_order_two _ h.involution hzQ)
    (le_centralizer_iff.mp hQz)
  have hcomm : residualCore L r ⊔ zpowers z ≤ centralizer (zpowers r : Set G) := by
    apply sup_le (le_centralizer_iff.mp hQr)
    apply zpowers_le.mpr
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
    exact ((marked_involutions_commute h hr).zpow_left n).eq
  obtain ⟨f, hf⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (residualCore L r ⊔ zpowers z) (zpowers r)
    (disjoint_zpowers_of_order_two _ hr2 (marked_r_not_mem_core_z h hr hr2 hinner)) hcomm
  have heq : shadowSpace L r z = (residualCore L r ⊔ zpowers z) ⊔ zpowers r := by
    simp only [shadowSpace, sup_assoc, sup_comm (zpowers z) (zpowers r)]
  refine ⟨((e.prodCongr (MulEquiv.refl _)).trans f).trans
    (MulEquiv.subgroupCongr heq.symm), ?_⟩
  intro q a b
  change (f (e (q, a), b) : G) = _
  rw [hf, he]

/-- The two independent marked involutions enlarge E₁₆ to order 64. -/
theorem shadowSpace_card (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hzQ : z ∉ residualCore L r) (hcard : Nat.card (residualCore L r) = 16) :
    Nat.card (shadowSpace L r z) = 64 := by
  obtain ⟨e, _⟩ := shadowSpace_product h hr hr2 hinner hzQ
  rw [← Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_prod,
    Nat.card_zpowers, Nat.card_zpowers, hcard, hr2, h.involution]

/-- The second local hyperplane Q⟨r⟩ excludes the first marked vector z. -/
theorem marked_z_not_mem_core_r (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (hinner : innerPart L R = ⊥)
    (hzQ : z ∉ residualCore L r) : z ∉ residualCore L r ⊔ zpowers r := by
  classical
  intro hz
  have hn : zpowers r ≤ normalizer (residualCore L r : Set G) :=
    residualCore_zpowers_r_centralize.trans (centralizer_le_normalizer _)
  change z ∈ ((residualCore L r ⊔ zpowers r : Subgroup G) : Set G) at hz
  rw [coe_mul_of_right_le_normalizer_left _ _ hn] at hz
  obtain ⟨q, hq, b, hb, he⟩ := hz
  change b ∈ zpowers r at hb
  rw [mem_zpowers_iff_mem_range_orderOf, hr2] at hb
  obtain ⟨n, hn, hb⟩ := Finset.mem_image.mp hb
  have hn2 := Finset.mem_range.mp hn
  interval_cases n
  · have hb1 : b = 1 := by simpa using hb.symm
    apply hzQ
    have hqz : q = z := by simpa only [hb1, mul_one] using he
    exact hqz ▸ hq
  · have hbr : b = r := by simpa using hb.symm
    have her : r = q⁻¹ * z := by rw [← he, hbr]; simp
    apply marked_r_not_mem_core_z h hr hr2 hinner
    have hm := (residualCore L r ⊔ zpowers z).mul_mem
      ((show residualCore L r ≤ residualCore L r ⊔ zpowers z from le_sup_left)
        ((residualCore L r).inv_mem hq))
      ((show zpowers z ≤ residualCore L r ⊔ zpowers z from le_sup_right) (mem_zpowers z))
    rwa [← her] at hm

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow
