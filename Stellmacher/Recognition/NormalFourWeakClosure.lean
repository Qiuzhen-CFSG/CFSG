module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Stellmacher.Recognition.NormalFourWeakClosureLocal
public import Stellmacher.Recognition.NormalFourWeakClosureHall
public import Stellmacher.Recognition.SimpleInvolutionFusion
public import Theory.GroupTheory.PGroup.NormalFourFusion
public import Theory.GroupTheory.PGroup.RankTwoNormalFourTransfer
public import Theory.GroupTheory.WeakClosureOvergroups

/-!
# The weak-closure obstruction for the unique normal four

Let `E` be a normal four-group in a Sylow two-subgroup whose central first
omega has order two. If every Sylow conjugate of a central involution lies
in `E`, Z-star supplies a distinct conjugate in `E`. Conjugation inside the
Sylow interchanges the other two involutions of `E`, so all three are fused.
Thompson transfer then shows that every Sylow involution lies in `E`.

For the unique normal four, weak closure gives this central-class containment
by the square-root and centralizer argument in `NormalFourWeakClosureLocal`.
The Hall 14.4.1 argument in `NormalFourWeakClosureHall` then contradicts
containment of every Sylow involution in the four. Thus some conjugate of
the four returns to the Sylow subgroup and differs from the original four.
This handles both fusion cases of Janko–Thompson, Math. Z. 113 (1970),
§6, p.395: Z-star excludes the separated case, and Hall transfer excludes
the fused case.

The obstruction does not require the N₂ hypothesis, noncommutativity as a
separate assumption, or normality of the odd-core quotient image. The image
retains its definition from `NormalFourOddCoreSetup`; in particular no
normality before quotienting is assumed.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

open Subgroup
open scoped IsMulCommutative

/-- Once central-involution conjugates stay in the normal four, its three
involutions are fused. This excludes the separated fusion case by Z-star. -/
public theorem involutions_fused_of_central_class_mem_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hclass : ∀ z t : S, z ∈ center S → orderOf z = 2 →
      IsConj (z : G) (t : G) → t ∈ E)
    (u v : S) (hu : u ∈ E) (hv : v ∈ E)
    (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) :
    IsConj (u : G) (v : G) := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 := (orderOf_coe (w : center S)).trans
    ((orderOf_coe w).trans hw)
  have hzC : z ∈ center S := (w : center S).property
  have hzE : z ∈ E := omega_one_center_le_four_of_elementary_card_lt_eight
    (elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G)) E hE
      (mem_map_of_mem (center S).subtype w.property)
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  obtain ⟨t, htz, hzt⟩ := exists_distinct_isConj_in_sylow hns S z hz
  have htE : t ∈ E := hclass z t hzC hz hzt
  have ht1 : t ≠ 1 := by
    intro h
    have hzG : (z : G) = 1 := isConj_one_left.mp (by simpa [h] using hzt)
    exact hz1 (Subtype.ext hzG)
  have hnc : ¬ E ≤ center S := four_not_le_center_of_card_omega_one_center_eq_two hZ E hE
  have hfused (a : S) (ha : a ∈ E) (ha2 : orderOf a = 2) :
      IsConj (z : G) (a : G) := by
    by_cases haz : a = z
    · exact haz ▸ IsConj.refl (z : G)
    have ha1 : a ≠ 1 := by intro h; simp [h] at ha2
    exact hzt.trans ((S : Subgroup G).subtype.map_isConj
      (isConj_of_mem_normal_four_of_ne_central_involution E hE hnc z t a
        hzE hzC hz1 htE ha ht1 ha1 htz haz))
  exact (hfused u hu hu2).symm.trans (hfused v hv hv2)

private theorem no_normal_index_two
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  intro N hN hi
  rcases hN.eq_bot_or_eq_top with hbot | htop
  · have hcard : Nat.card G = 2 := by simpa [hbot] using hi
    let : IsCyclic G := isCyclic_of_prime_card hcard
    exact hns (Group.isSolvable_of_comm (fun a b => mul_comm a b))
  · simp [htop] at hi

/-- Class containment for the central involution, together with Thompson
transfer, confines every Sylow involution to the normal four. -/
public theorem involution_mem_four_of_central_class_mem_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hclass : ∀ z t : S, z ∈ center S → orderOf z = 2 →
      IsConj (z : G) (t : G) → t ∈ E)
    (t : S) (ht : orderOf t = 2) : t ∈ E := by
  obtain ⟨u, hu, htu⟩ := S.exists_isConj_mem_normal_four_of_elementary_card_lt_eight
    (no_normal_index_two hns) hrank hZ E hE t ht
  have hu1 : u ≠ 1 := by
    intro h
    have ht1 : t = 1 := Subtype.ext (isConj_one_left.mp (by simpa [h] using htu))
    simp [ht1] at ht
  have hu2 : orderOf u = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu) hu1
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  let z : S := (w : center S)
  have hz : orderOf z = 2 := (orderOf_coe (w : center S)).trans
    ((orderOf_coe w).trans hw)
  have hzC : z ∈ center S := (w : center S).property
  have hzE : z ∈ E := hclass z z hzC hz (IsConj.refl _)
  have hzu := involutions_fused_of_central_class_mem_four hns hrank S hZ E hE
    hclass z u hzE hu hz hu2
  exact hclass z t hzC hz (hzu.trans htu.symm)

/-- The unique normal four cannot be weakly closed in a Sylow two-subgroup
with central first omega of order two in a nonsolvable finite simple group
under the elementary rank bound. -/
public theorem false_of_weakly_closed
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hweak : ∀ g : G,
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G) →
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom =
        E.map (S : Subgroup G).subtype) : False := by
  have hclass := central_class_mem_four_of_weakly_closed hrank S E hE hunique hweak
  exact false_of_weakly_closed_of_involutions_mem hns S hZ E hE hweak
    (involution_mem_four_of_central_class_mem_four hns hrank S hZ E hE hclass)

/-- Some ambient conjugate of the unique normal four returns to the Sylow
subgroup and differs from the four. This is the weak-closure obstruction
used in the normal odd-core quotient-image branch. -/
public theorem exists_distinct_conjugate_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E) :
    ∃ g : G,
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≤
        (S : Subgroup G) ∧
      (E.map (S : Subgroup G).subtype).map (MulAut.conj g).toMonoidHom ≠
        E.map (S : Subgroup G).subtype := by
  classical
  by_contra h
  apply false_of_weakly_closed hns hrank S hZ E hE hunique
  intro g hg
  by_contra hne
  exact h ⟨g, hg, hne⟩

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
