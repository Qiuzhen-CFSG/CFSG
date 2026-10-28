module

public import Theory.GroupTheory.QuaternionCentralProductCubicRestriction
public import Theory.GroupTheory.QuaternionCentralProductCubicStabilizer
public import Theory.GroupTheory.ElementaryEightPlanePoint
public import Mathlib.GroupTheory.IndexNormal

/-!
# Point stabilizers from quaternion central products

The center of a central product of two quaternion eights has order two.
If the product lies in an order-64 subgroup, it has index two there, so
that subgroup fixes its unique central involution. For a self-centralizing
elementary eight, this involution belongs to the elementary subgroup.
A cubic normalizer actor fixing the same point then supplies an order-24
point stabilizer in the actual automizer. The census of elementary eights
supplies a nonidentity independent cubic actor normalizing the given eight;
faithful restriction makes its induced action have order three.

This is the intrinsic point-stabilizer step of Stellmacher (8.6)(a),
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Subgroup

private theorem normalizer_fixes_center_of_card_two
    {G : Type*} [Group G] (Q : Subgroup G)
    (hZ : Nat.card (center Q) = 2) (z : center Q)
    (g : normalizer (Q : Set G)) :
    g * ((z : Q) : G) * (g : G)⁻¹ = ((z : Q) : G) := by
  let e := centerCongr (Q.normalizerMonoidHom g)
  have he : e z = z := by
    by_cases hz : z = 1
    · simp [hz]
    · obtain ⟨w, _, hw⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp hZ
      have hez : e z ≠ 1 := fun h => hz (e.injective (h.trans e.map_one.symm))
      exact (hw (e z) hez).trans (hw z hz).symm
  exact congrArg (fun w : center Q => ((w : Q) : G)) he

/-- The unique central involution of an index-two subgroup lies in a
self-centralizing subgroup and is fixed by every normalizer of the former. -/
public theorem exists_common_fixed_point_of_center_card_two
    {G : Type*} [Group G] [Finite G] (Q S U : Subgroup G)
    (hQ : Nat.card Q = 32) (hS : Nat.card S = 64)
    (hQS : Q ≤ S) (hUQ : U ≤ Q)
    (hcentral : S ⊓ centralizer (U : Set G) = U)
    (hZ : Nat.card (center Q) = 2) :
    ∃ z : U, z ≠ 1 ∧
      (∀ s : S, (s : G) * z * (s : G)⁻¹ = z) ∧
      ∀ g : normalizer (Q : Set G), (g : G) * z * (g : G)⁻¹ = z := by
  have hi : (Q.subgroupOf S).index = 2 := by
    have h := (Q.subgroupOf S).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv, hQ, hS] at h
    omega
  have hSN : S ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hQS).mp (normal_of_index_eq_two hi)
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : center Q)).mp hZ
  have hzU : ((z : Q) : G) ∈ U := by
    rw [← hcentral]
    refine ⟨hQS (z : Q).property, ?_⟩
    intro u hu
    exact congrArg Subtype.val (mem_center_iff.mp z.property (⟨u, hUQ hu⟩ : Q))
  refine ⟨⟨((z : Q) : G), hzU⟩, ?_, ?_, ?_⟩
  · intro h
    have hG : ((z : Q) : G) = 1 := congrArg (fun u : U => (u : G)) h
    exact hz (Subtype.ext (Subtype.ext hG))
  · intro s
    exact normalizer_fixes_center_of_card_two Q hZ z ⟨s, hSN s.property⟩
  · exact normalizer_fixes_center_of_card_two Q hZ z

/-- A cubic actor normalizing both the central product and its elementary
eight supplies the full point stabilizer. The Sylow hypothesis on the
order-64 subgroup is unnecessary for this implication. -/
public theorem quaternion_central_product_point_image_of_cubic
    {G : Type*} [Group G] [Finite G] (B C U S : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (hUQ : U ≤ B ⊔ C) (hS : Nat.card S = 64) (hQS : B ⊔ C ≤ S)
    (hSN : S ≤ normalizer (U : Set G))
    (hcentral : S ⊓ centralizer (U : Set G) = U)
    (g : normalizer (U : Set G))
    (hgQ : (g : G) ∈ normalizer ((B ⊔ C : Subgroup G) : Set G))
    (hg : orderOf (U.normalizerMonoidHom g) = 3) :
    Nonempty (ElementaryEightPointImage U) := by
  have hBcard : Nat.card B = 8 := by
    obtain ⟨e⟩ := hB
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hCcard : Nat.card C = 8 := by
    obtain ⟨e⟩ := hC
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hCn : C ≤ normalizer (B : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro c hc b hb
    exact hcomm b hb c hc
  have hQ : Nat.card (B ⊔ C : Subgroup G) = 32 := by
    have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes B C hCn
    rw [hBcard, hCcard, hinter] at h
    omega
  obtain ⟨z, hz, hfixS, hfixQ⟩ := exists_common_fixed_point_of_center_card_two
    (B ⊔ C) S U hQ hS hQS hUQ hcentral
    (quaternion_central_product_center_card B C hB hC hinter hcomm)
  exact elementaryEight_point_image_of_cubic U S hU hS hSN hcentral z hz
    (fun s => Subtype.ext (hfixS s)) g hg (Subtype.ext (hfixQ ⟨g, hgQ⟩))

/-- Any nonidentity member of the independent cubic group that normalizes
the supplied elementary eight supplies its point-stabilizer image. -/
public theorem QuaternionIndependentCubics.point_image_of_nontrivial_normalizing_actor
    {G : Type*} [Group G] [Finite G] {B C : Subgroup G}
    (actors : QuaternionIndependentCubics B C) (U S : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (hUQ : U ≤ B ⊔ C) (hS : Nat.card S = 64) (hQS : B ⊔ C ≤ S)
    (hSN : S ≤ normalizer (U : Set G))
    (hcentral : S ⊓ centralizer (U : Set G) = U)
    (a : actors.A) (ha : a ≠ 1) (haU : (a : G) ∈ normalizer (U : Set G)) :
    Nonempty (ElementaryEightPointImage U) := by
  exact quaternion_central_product_point_image_of_cubic B C U S hB hC hinter hcomm
    hU hUQ hS hQS hSN hcentral ⟨a, haU⟩ (actors.le_normalizer a.property)
    (actors.orderOf_restriction_eq_three U hB hC hinter hcomm hU hUQ a ha haU)

/-- Independent cubic actors on the quaternion factors supply a point-stabilizer
image on every elementary eight that is self-centralizing in an order-64
normalizing overgroup. Once the actors are supplied, neither a Sylow condition
on that overgroup nor an ambient centralizer bound on the product is needed. -/
public theorem QuaternionIndependentCubics.point_image
    {G : Type*} [Group G] [Finite G] {B C : Subgroup G}
    (actors : QuaternionIndependentCubics B C) (U S : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8)
    (hUQ : U ≤ B ⊔ C) (hS : Nat.card S = 64) (hQS : B ⊔ C ≤ S)
    (hSN : S ≤ normalizer (U : Set G))
    (hcentral : S ⊓ centralizer (U : Set G) = U) :
    Nonempty (ElementaryEightPointImage U) := by
  obtain ⟨a, ha, haU⟩ :=
    actors.exists_nontrivial_normalizing hB hC hinter hcomm U hU hUQ
  exact actors.point_image_of_nontrivial_normalizing_actor U S hB hC hinter hcomm
    hU hUQ hS hQS hSN hcentral a ha haU

end Subgroup
