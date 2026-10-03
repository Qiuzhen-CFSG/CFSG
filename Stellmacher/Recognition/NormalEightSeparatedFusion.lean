module

public import Theory.GroupTheory.PGroup.NormalEightFour
public import Theory.GroupTheory.NormalFourFusion
public import Theory.GroupTheory.FourGroupCrossActionFusion
public import Theory.GroupTheory.CoprimeCentralizerSupplement
public import Theory.PPrimeCore
public import Mathlib.GroupTheory.Sylow

/-!
# The separated fusion case for a normal four

Without a normal elementary eight, central omega lies in every normal four.
When central omega has order two, the four is noncentral, and its other two
involutions are already conjugate in the Sylow subgroup. Thus either all three
involutions fuse in the ambient group, or the central involution has no other
ambient conjugate in the four.

The local centralizer control and the cross-action configuration below are
explicit interfaces for the two remaining steps of the separated case. They
are not asserted to exist here. A cross-action configuration contradicts
separation by the proved four-group cross-action theorem.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemmas 2.1, 3.1–3.2 and §6,
printed pp.386–389 and 395.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedFusion

open Subgroup

variable {G : Type*} [Group G]

/-- The central involution has no distinct ambient conjugate in the four. -/
public abbrev Separated (S : Sylow 2 G) (W : Subgroup S) (z : S) : Prop :=
  ∀ t : S, t ∈ W → IsConj (z : G) (t : G) → t = z

/-- Janko–Thompson 3.1, expressed inside each involution centralizer. -/
public abbrev CentralizerFactorization (S : Sylow 2 G) (W : Subgroup S) : Prop :=
  ∀ i : S, i ∈ W → orderOf i = 2 → i ∉ center S →
    let C := centralizer ({(i : G)} : Set G)
    centralizer ((W.map (S : Subgroup G).subtype).subgroupOf C : Set C) ⊔
      pPrimeCore 2 C = ⊤

/-- The conclusion of Janko–Thompson 3.2 for the noncentral involutions of
the normal four. The overgroup is an actual ambient two-subgroup. -/
public abbrev LocalCentralizerControl (S : Sylow 2 G) (W : Subgroup S) : Prop :=
  ∀ i : S, i ∈ W → orderOf i = 2 → i ∉ center S →
    ∀ V : Subgroup G, IsPGroup 2 V → W.map (S : Subgroup G).subtype ≤ V →
      V ≤ centralizer ({(i : G)} : Set G) →
      V ≤ centralizer (W.map (S : Subgroup G).subtype : Set G)

/-- The geometric output needed to apply Janko–Thompson 2.1 to `W`.
The elementary-abelian witnesses are fields rather than hidden assumptions. -/
public structure CrossAction (W : Subgroup G) where
  V : Subgroup G
  V₁ : Subgroup G
  W₁ : Subgroup G
  elementaryV : IsElementaryAbelian 2 V
  elementaryV₁ : IsElementaryAbelian 2 V₁
  elementaryW₁ : IsElementaryAbelian 2 W₁
  cardV : Nat.card V = 4
  cardV₁ : Nat.card V₁ = 4
  cardW₁ : Nat.card W₁ = 4
  normalizes : V ⊔ V₁ ≤ normalizer ((W ⊔ W₁ : Subgroup G) : Set G)
  centralizes : V ≤ centralizer (W : Set G)
  centralizes₁ : V₁ ≤ centralizer (W₁ : Set G)
  commute : W ≤ centralizer (W₁ : Set G)
  disjoint : W ⊓ W₁ = ⊥
  cross : ∀ v ∈ V, v ≠ 1 → ∀ w ∈ W₁, w ≠ 1 → ¬ Commute v w
  cross₁ : ∀ v ∈ V₁, v ≠ 1 → ∀ w ∈ W, w ≠ 1 → ¬ Commute v w

variable [Finite G]

/-- The odd-core factorization gives the two-subgroup control of Lemma 3.2. -/
public theorem localCentralizerControl_of_factorization
    (S : Sylow 2 G) (W : Subgroup S) [IsElementaryAbelian 2 W]
    (hfactor : CentralizerFactorization S W) : LocalCentralizerControl S W := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro i hi hi2 hiC V hV hWV hVC
  let C := centralizer ({(i : G)} : Set G)
  let W₀ := W.map (S : Subgroup G).subtype
  have hWC : W₀ ≤ C := hWV.trans hVC
  have hsub : W₀.subgroupOf C ≤ V.subgroupOf C := fun _ hx => hWV hx
  have hc := le_centralizer_of_isPGroup_of_coprime_supplement
    (W₀.subgroupOf C) (pPrimeCore 2 C) (V.subgroupOf C)
    pPrimeCore_coprime_card (hfactor i hi hi2 hiC) hV.comap_subtype hsub
  intro v hv w hw
  exact congrArg Subtype.val
    (hc (show (⟨v, hVC hv⟩ : C) ∈ V.subgroupOf C from hv)
      (⟨w, hWC hw⟩ : C) hw)

/-- Central omega supplies a central involution in the normal four using
only the bound on normal elementary subgroups. -/
public theorem exists_central_involution_mem_four
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) :
    ∃ z : S, z ∈ W ∧ z ∈ center S ∧ orderOf z = 2 := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  refine ⟨(w : center S), ?_, (w : center S).property, ?_⟩
  · exact omega_one_center_le_normal_four_of_no_normal_eight hno W hW
      (mem_map_of_mem (center S).subtype w.property)
  · exact (orderOf_coe (w : center S)).trans ((orderOf_coe w).trans hw)

/-- Failure of fusion separates the central involution from the other two.
No elementary-rank bound is used. -/
public theorem separated_of_not_fused
    (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4)
    (z : S) (hzW : z ∈ W) (hzC : z ∈ center S) (hz : orderOf z = 2)
    (hnot : ¬ ∀ u v : S, u ∈ W → v ∈ W → orderOf u = 2 → orderOf v = 2 →
      IsConj (u : G) (v : G)) : Separated S W z := by
  intro t ht hzt
  by_contra htz
  have hz1 : z ≠ 1 := by intro h; simp [h] at hz
  have ht1 : t ≠ 1 := by
    intro h
    exact hz1 (Subtype.ext (isConj_one_left.mp (by simpa [h] using hzt)))
  have hf := normal_four_fusion_of_central_isConj W hW
    (four_not_le_center_of_card_omega_one_center_eq_two hZ W hW)
    ⟨z, hzW⟩ hzC (fun h => hz1 (congrArg Subtype.val h))
    (S : Subgroup G).subtype ⟨t, ht⟩
    (fun h => ht1 (congrArg Subtype.val h))
    (fun h => htz (congrArg Subtype.val h)) hzt
  apply hnot
  intro u v hu hv hu2 hv2
  exact hf ⟨u, hu⟩ ⟨v, hv⟩
    (by intro h; have h' : u = 1 := congrArg Subtype.val h; simp [h'] at hu2)
    (by intro h; have h' : v = 1 := congrArg Subtype.val h; simp [h'] at hv2)

/-- A constructed cross action fuses the involutions of the intrinsic four. -/
public theorem CrossAction.involutions_fused
    (S : Sylow 2 G) (W : Subgroup S) [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (c : CrossAction (W.map (S : Subgroup G).subtype))
    (u v : S) (hu : u ∈ W) (hv : v ∈ W)
    (hu2 : orderOf u = 2) (hv2 : orderOf v = 2) : IsConj (u : G) (v : G) := by
  let W₀ := W.map (S : Subgroup G).subtype
  let : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 c.V := c.elementaryV
  let : IsElementaryAbelian 2 c.V₁ := c.elementaryV₁
  let : IsElementaryAbelian 2 c.W₁ := c.elementaryW₁
  apply isConj_of_four_group_cross_action c.V c.V₁ W₀ c.W₁
    c.cardV c.cardV₁
    ((card_map_of_injective (S : Subgroup G).subtype_injective).trans hW)
    c.cardW₁ c.normalizes c.centralizes c.centralizes₁ c.commute c.disjoint
    c.cross c.cross₁ (u : G) (v : G)
    (mem_map_of_mem _ hu) (mem_map_of_mem _ hv)
  · intro h
    have h' : u = 1 := Subtype.ext h
    simp [h'] at hu2
  · intro h
    have h' : v = 1 := Subtype.ext h
    simp [h'] at hv2

end Stellmacher.Recognition.NormalEightSeparatedFusion
