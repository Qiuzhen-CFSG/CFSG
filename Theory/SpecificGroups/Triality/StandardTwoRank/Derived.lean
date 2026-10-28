module

public import Theory.SpecificGroups.Triality.StandardTwoRank.Perfectness
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer
public import Theory.SpecificGroups.Triality.BinaryCenter
public import Theory.SpecificGroups.Triality.TwoLocalCover.Hexagon
public import Theory.SpecificGroups.Triality.TwoLocalCover.ApartmentStabilizer

/-!
# Simplicity of genuine binary triality

For every positive binary exponent, the original elementary graph-field
carrier modulo its own center is nonabelian simple, including at q = 2.
The shared perfectness and actual commutator equivalence are re-exported
from `Perfectness`; their root-generation proof is not duplicated here.

For an ambient normal subgroup K, Bruhat theory puts the Borel overgroup
KB either in a proper root parabolic or in the whole group. In the first
case, K fixes all vertices of one type in the genuine parabolic hexagon.
The unique two-edge path between two such vertices forces it to fix a
vertex of the other type, putting K in the Borel. Opposition puts K in
the torus. Its commutators with the positive subgroup lie in the trivial
torus intersection, so K centralizes the Borel. The rank-one Bruhat
witnesses show that the Borel normally generates the carrier; its proved
centerlessness now gives K = 1. In the second case, the quotient by K is
a solvable image of the Borel, and shared perfectness gives K = G.

Source: GLS3, Theorem 2.2.7(a,b) and the root/Bruhat structure in §§2.3–2.6,
`refs/KGroup/GLS3/chapter2.tex`. Triality at q = 2 is not among the eight
exceptions. The parabolics and quotient are those of `StandardModel`.
-/

public section


open scoped Pointwise commutatorElement
open Subgroup
open Theory.AlgebraicGroup
namespace Triality.Standard.TwoRank.Derived
open Parabolics ConcreteBruhat
noncomputable section

private theorem normal_eq_top_of_borel_le {G : Type*} [Group G]
    (T : TitsSystem (X := G)) (H : Subgroup G) [H.Normal] (hB : T.B ≤ H) : H = ⊤ := by
  apply top_unique
  rw [← T.standardParabolic_S]
  apply T.standardParabolic_le _ hB
  intro s hs
  obtain ⟨ns, b, hns, hb, hcell⟩ := T.exists_rankOne_witness hs
  have hsquare : (ns : G) * ns ∈ T.B := by
    have h := (T.representative_sq_mem_intersection hs ns hns).1
    change (ns : G) ^ 2 ∈ T.B at h
    simpa only [pow_two] using h
  apply T.bruhatCell_subset_of_mem H hB hcell
  have hc := (inferInstance : H.Normal).conj_mem b (hB hb) (ns : G)
  simpa only [mul_assoc, inv_mul_cancel_left] using H.mul_mem hc (hB hsquare)

/-- The actual torus is commutative, through its two field-unit coordinates. -/
theorem torus_isMulCommutative (P : Parameters) (hp : P.prime = 2) :
    IsMulCommutative (torus P) := by
  apply IsMulCommutative.of_comm
  intro a b
  apply (TorusCoordinates.torusMulEquiv P hp).symm.injective
  simp only [map_mul, mul_comm]

/-- The actual Borel is solvable: its normal positive two-subgroup has an
abelian torus supplement. -/
theorem borel_isSolvable (n : ℕ) (hn : 0 < n) :
    Group.IsSolvable (borel (binaryParameters n hn)) := by
  let P := binaryParameters n hn
  let U := (unipotent P).subgroupOf (borel P)
  let : U.Normal := unipotent_normal_in_borel P rfl
  let : Group.IsNilpotent (unipotent P) := (unipotent_isPGroup_binary P rfl).isNilpotent
  let : IsMulCommutative (torus P) := torus_isMulCommutative P rfl
  let : Group.IsSolvable (torus P) := Group.isSolvable_of_comm (mul_comm' · ·)
  let q := QuotientGroup.mk' U
  let i := Subgroup.inclusion (torus_le_borel P)
  have hsurj : Function.Surjective (q.comp i) := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective U y
    have hb : b.val ∈ (unipotent P : Set (Carrier P)) * torus P :=
      (borel_eq_mul P rfl) ▸ b.property
    obtain ⟨u, hu, t, ht, he⟩ := hb
    refine ⟨⟨t, ht⟩, ?_⟩
    apply (QuotientGroup.eq_iff_div_mem).mpr
    change t / b.val ∈ unipotent P
    rw [← he]
    simpa using (unipotent P).inv_mem hu
  let : Group.IsSolvable ((borel P) ⧸ U) := Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_ker_le_range (Subgroup.inclusion (unipotent_le_borel P)) q
    (by simp [q, U, P])

/-- Every ambient normal subgroup inside the Borel is trivial. Opposition
puts it in the torus; normality and the disjoint positive subgroup force
centralization of the Borel, whose conjugates generate the whole carrier. -/
theorem normal_eq_bot_of_le_borel (n : ℕ) (hn : 0 < n)
    (K : Subgroup (BinaryCarrier n hn)) [K.Normal]
    (hK : K ≤ borel (binaryParameters n hn)) : K = ⊥ := by
  let P := binaryParameters n hn
  have hKT : K ≤ torus P := by
    intro x hx
    apply TwoLocalGeometry.ApartmentStabilizer.borel_opposition_intersection n hn (hK hx)
    exact hK (by simpa only [inv_inv] using
      (inferInstance : K.Normal).conj_mem x hx (weylRepresentative P rfl (.r 3))⁻¹)
  have hKU : ⁅K, unipotent P⁆ = ⊥ := by
    apply le_bot_iff.mp
    apply le_trans _ (disjoint_unipotent_torus P rfl).le_bot
    apply le_inf
    · exact Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hK.trans (borel_le_normalizer_unipotent P rfl))
    · exact (Subgroup.commutator_le_left K (unipotent P)).trans hKT
  have hUT : unipotent P ≤ centralizer (K : Set (Carrier P)) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hKU
  have hTT : torus P ≤ centralizer (K : Set (Carrier P)) := by
    let : IsMulCommutative (torus P) := torus_isMulCommutative P rfl
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact congrArg Subtype.val (mul_comm' (⟨k, hKT hk⟩ : torus P) ⟨t, ht⟩)
  have hBC : borel P ≤ centralizer (K : Set (Carrier P)) := by
    intro b hb
    have hb' : b ∈ (unipotent P : Set (Carrier P)) * torus P := (borel_eq_mul P rfl) ▸ hb
    obtain ⟨u, hu, t, ht, rfl⟩ := hb'
    exact Subgroup.mul_mem _ (hUT hu) (hTT ht)
  have hC : centralizer (K : Set (Carrier P)) = ⊤ :=
    normal_eq_top_of_borel_le (titsSystem n hn) _ hBC
  have hZ : K ≤ center (BinaryCarrier n hn) := by
    rw [← Subgroup.commutator_top_left_eq_bot_iff_le_center,
      Subgroup.commutator_eq_bot_iff_le_centralizer, hC]
  exact le_bot_iff.mp (hZ.trans (binaryCarrier_center_eq_bot n hn).le)
end
end Triality.Standard.TwoRank.Derived


open Subgroup SimpleGraph
namespace Triality.Standard.TwoRank.Derived
open Parabolics ConcreteBruhat TwoLocalGeometry GroupAction.EvenPolygon

/-- Normal subgroups contained in either vertex stabilizer fix both ends of
a two-edge path. Hexagon girth forces its middle vertex to be fixed as well. -/
theorem normal_le_borel_of_le_parabolic (n : ℕ) (hn : 0 < n)
    (K : Subgroup (BinaryCarrier n hn)) [K.Normal] (a : Node)
    (hK : K ≤ parabolic (binaryParameters n hn) a) :
    K ≤ borel (binaryParameters n hn) := by
  let P := binaryParameters n hn
  obtain ⟨b, hab, hinter⟩ : ∃ b : Node, a ≠ b ∧
      parabolic P a ⊓ parabolic P b = borel P := by
    cases a with
    | arms => exact ⟨.central, by decide, parabolic_inf_binary P rfl⟩
    | central => exact ⟨.arms, by decide, by rw [inf_comm]; exact parabolic_inf_binary P rfl⟩
  let v := CosetGeometry.base (parabolic P) a
  let w := CosetGeometry.base (parabolic P) b
  let s := simpleRepresentative P rfl b
  have hsP : s ∈ parabolic P b := simpleRepresentative_mem_parabolic P rfl b
  have hsB : s ∉ borel P := by
    intro h
    have he : relativeReflection b = 1 :=
      (RelativeNormalizer.representative_mem_borel_iff n hn _).mp
        ((weylRepresentative_simple P rfl b).symm ▸ h)
    exact (relativeReflection_involution b).1 he
  have hsw : s • w = w := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [CosetGeometry.stabilizer_base]
    exact hsP
  have hsv : s • v ≠ v := by
    intro h
    have hsa : s ∈ parabolic P a := by
      rw [← CosetGeometry.stabilizer_base (parabolic P) a]
      exact h
    exact hsB (hinter ▸ (show s ∈ parabolic P a ⊓ parabolic P b from ⟨hsa, hsP⟩))
  have h1 : (incidenceGraph n hn).Adj v w :=
    ⟨hab, CosetGeometry.incident_base _ a b⟩
  have h2 : (incidenceGraph n hn).Adj w (s • v) := by
    simpa only [hsw] using (smul_adj s h1).symm
  let p : (incidenceGraph n hn).Walk v (s • v) := .cons h1 (.cons h2 .nil)
  have hp : p.IsPath := by
    simp [p, h2.ne, h1.ne, hsv.symm]
  have hv : v ∈ fixedVertices K := by
    intro k hk
    apply MulAction.mem_stabilizer_iff.mp
    rw [CosetGeometry.stabilizer_base]
    exact hK hk
  have hsvfix : s • v ∈ fixedVertices K :=
    normalizer_smul_mem_fixedVertices K
      (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _) hv
  have hw : w ∈ fixedVertices K :=
    short_path_fixed ((hexagonGeometry n hn).toEvenPolygonAction
      (apartmentTranslates n hn) (standardApartment_fixer_odd n hn)) K hv hsvfix hp
      (by change 2 < 2 * 3; decide) w (by simp [p])
  have hKb : K ≤ parabolic P b := by
    intro k hk
    rw [← CosetGeometry.stabilizer_base (parabolic P) b]
    exact hw k hk
  exact hinter ▸ le_inf hK hKb
end Triality.Standard.TwoRank.Derived

open Subgroup Theory.AlgebraicGroup
namespace Triality.Standard.TwoRank.Derived
open Parabolics ConcreteBruhat

/-- The rank-two Bruhat system places every proper Borel overgroup in one of
the two original root parabolics. -/
theorem le_parabolic_of_borel_le (n : ℕ) (hn : 0 < n)
    (H : Subgroup (BinaryCarrier n hn)) (hB : borel (binaryParameters n hn) ≤ H)
    (hH : H ≠ ⊤) : ∃ a, H ≤ parabolic (binaryParameters n hn) a := by
  classical
  let T := titsSystem n hn
  let I := T.simpleIndices H
  have hclass : H = T.standardParabolic I := T.subgroup_eq_standardParabolic_simpleIndices H hB
  have hnot : ¬ (simpleReflection n hn .arms ∈ I ∧ simpleReflection n hn .central ∈ I) := by
    rintro ⟨ha, hc⟩
    apply hH
    have hI : I = T.S := by
      apply Set.Subset.antisymm (T.simpleIndices_subset H)
      intro s hs
      rcases (mem_titsSystem_S_iff n hn s).mp hs with rfl | rfl
      · exact ha
      · exact hc
    rw [hclass, hI, T.standardParabolic_S]
  by_cases ha : simpleReflection n hn .arms ∈ I
  · refine ⟨.arms, ?_⟩
    rw [hclass, parabolic_eq_standardParabolic]
    apply T.standardParabolic_mono
    intro s hs
    rcases (mem_titsSystem_S_iff n hn s).mp (T.simpleIndices_subset H hs) with rfl | rfl
    · exact Set.mem_singleton _
    · exact (hnot ⟨ha, hs⟩).elim
  · refine ⟨.central, ?_⟩
    rw [hclass, parabolic_eq_standardParabolic]
    apply T.standardParabolic_mono
    intro s hs
    rcases (mem_titsSystem_S_iff n hn s).mp (T.simpleIndices_subset H hs) with rfl | rfl
    · exact (ha hs).elim
    · exact Set.mem_singleton _

/-- A normal subgroup supplemented by the solvable Borel is the whole
perfect carrier. -/
theorem normal_eq_top_of_sup_borel (n : ℕ) (hn : 0 < n)
    (K : Subgroup (BinaryCarrier n hn)) [K.Normal]
    (hK : K ⊔ borel (binaryParameters n hn) = ⊤) : K = ⊤ := by
  let P := binaryParameters n hn
  let q := QuotientGroup.mk' K
  have hmapK : K.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact (QuotientGroup.ker_mk' K).ge
  have hsurj : Function.Surjective (q.comp (borel P).subtype) := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    have h := congrArg (Subgroup.map q) hK
    simpa only [Subgroup.map_sup, hmapK, bot_sup_eq,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective K)] using h
  let : Group.IsSolvable (borel P) := borel_isSolvable n hn
  let : Group.IsSolvable (BinaryCarrier n hn ⧸ K) := Group.isSolvable_of_surjective hsurj
  have hs : Subsingleton (BinaryCarrier n hn ⧸ K) := by
    by_contra! hnontrivial
    exact Group.IsPerfect.not_isSolvable (BinaryCarrier n hn ⧸ K) inferInstance
  exact QuotientGroup.subgroup_eq_top_of_subsingleton K hs

/-- The genuine binary triality carrier is simple, including exponent one. -/
instance binaryCarrier_isSimpleGroup (n : ℕ) (hn : 0 < n) :
    IsSimpleGroup (BinaryCarrier n hn) := by
  let P := binaryParameters n hn
  have hnontrivial : Nontrivial (BinaryCarrier n hn) := by
    by_contra! htriv
    apply parabolic_ne_top_binary P rfl .arms
    exact Subsingleton.elim _ _
  refine { eq_bot_or_eq_top_of_normal := ?_ }
  intro K hnormal
  let := hnormal
  by_cases hsup : K ⊔ borel P = ⊤
  · exact Or.inr (normal_eq_top_of_sup_borel n hn K hsup)
  · obtain ⟨a, ha⟩ := le_parabolic_of_borel_le n hn (K ⊔ borel P) le_sup_right hsup
    exact Or.inl (normal_eq_bot_of_le_borel n hn K
      (normal_le_borel_of_le_parabolic n hn K a (le_sup_left.trans ha)))
end Triality.Standard.TwoRank.Derived

namespace Triality.Standard.TwoRank

export Perfectness (binaryCarrier_isPerfect binary_commutator_eq_top
  binaryCommutatorEquiv binaryCommutatorEquiv_apply)
export Derived (binaryCarrier_isSimpleGroup)

/-- The actual derived subgroup is simple through its inclusion equivalence. -/
instance binaryCommutator_isSimpleGroup (n : ℕ) (hn : 0 < n) :
    IsSimpleGroup (commutator (BinaryCarrier n hn)) :=
  (Perfectness.binaryCommutatorEquiv n hn).isSimpleGroup

/-- The model input used by the smaller-field and seven-component inductions. -/
theorem binaryCarrier_simple_and_perfect (n : ℕ) (hn : 0 < n) :
    IsSimpleGroup (BinaryCarrier n hn) ∧ Group.IsPerfect (BinaryCarrier n hn) :=
  ⟨inferInstance, inferInstance⟩

/-- The simple binary carriers are nonabelian, with no exception at q = 2. -/
theorem binaryCarrier_nonabelian (n : ℕ) (hn : 0 < n) :
    ¬ IsMulCommutative (BinaryCarrier n hn) :=
  Group.IsPerfect.not_isMulCommutative _

/-- The same simplicity statement for any original characteristic-two parameter. -/
theorem carrier_isSimpleGroup (P : Parameters) (hp : P.prime = 2) :
    IsSimpleGroup (Carrier P) := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  exact binaryCarrier_isSimpleGroup n hn

end Triality.Standard.TwoRank
