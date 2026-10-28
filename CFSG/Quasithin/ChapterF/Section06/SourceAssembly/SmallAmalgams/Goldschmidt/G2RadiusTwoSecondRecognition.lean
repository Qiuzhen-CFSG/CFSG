module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.G2RadiusTwoQuotient
public import Theory.GroupTheory.NormalSixteenC4SquareRecognition
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SecondRecognition

/-!
# The actual second radius-two parabolic

The S₄ quotient and the faithful permutation of the three neighboring labels
force the source group to have trivial center. Its branch-action kernel has
order sixteen, a central four-group and an element of order four. Existing
normal-subgroup recognition identifies this kernel with C₄ × C₄. Its
self-centralization and S₃ quotient then recognize the whole source group as
the literal second parabolic of the derived binary G₂ model.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.9),
printed pp.400–401.
-/

@[expose] public section
open Subgroup SimpleGraph
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoSixLabels
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}
namespace Frame
variable {β : RankTwo.Vertex F} {f : BranchFrame F β} (r : Frame f)
variable (c : CanonicalLabelSetup F s) (hr : c.radius = 2) (hs : 4 ≤ s)
variable (h : CubicTreeAction F) (hβ : β.type ≠ c.side)
include r c hr hs h hβ

omit r in
/-- All nonidentity elements of the neighboring four-group are the three labels. -/
theorem neighbor_cases {g : G} (hg : g ∈ c.neighborLabelGroup β) :
    g = 1 ∨ ∃ i : Fin 3, g = c.label (f.e i).val := by
  classical
  let := c.radiusTwo_neighborLabelGroup_isKleinFour hr (by omega) h β hβ
  let : Finite (c.neighborLabelGroup β) := Nat.finite_of_card_ne_zero
    (by rw [IsKleinFour.card_four]; decide)
  let : Fintype (c.neighborLabelGroup β) := Fintype.ofFinite _
  let z : Fin 3 → c.neighborLabelGroup β := fun i =>
    ⟨c.label (f.e i).val, subset_closure ⟨(f.e i).val, (f.e i).property, rfl⟩⟩
  have hz (i : Fin 3) : z i ≠ 1 := by
    intro he
    have he' : c.label (f.e i).val = 1 := congrArg Subtype.val he
    have ho := c.order_two (f.e i).val (branch_type c hβ i)
    simp only [he', orderOf_one] at ho
    omega
  have h01 : z 0 ≠ z 1 := by
    intro he
    have hi : (0 : Fin 3) = 1 := branch_labels_injective c hβ (congrArg Subtype.val he)
    contradiction
  have hprod : z 0 * z 1 = z 2 := by
    apply Subtype.ext
    have hne {i j : Fin 3} (hi : i ≠ j) : (f.e i).val ≠ (f.e j).val :=
      fun he => hi (f.e.injective (Subtype.ext he))
    have he := c.neighbor_product β (f.e 0).val (f.e 1).val (f.e 2).val
      (f.e 0).property (f.e 1).property (f.e 2).property
      (hne (by decide)) (hne (by decide)) (hne (by decide)) (branch_type c hβ 0)
    exact (mul_eq_one_iff_eq_inv.mp he).trans (c.label_inv (branch_type c hβ 2))
  have hm := Finset.mem_univ (⟨g,hg⟩ : c.neighborLabelGroup β)
  rw [← IsKleinFour.eq_finset_univ (hz 0) (hz 1) h01, hprod] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with he | he | he | he
  · exact Or.inr ⟨2, congrArg Subtype.val he⟩
  · exact Or.inr ⟨0, congrArg Subtype.val he⟩
  · exact Or.inr ⟨1, congrArg Subtype.val he⟩
  · exact Or.inl (congrArg Subtype.val he)

omit r h in
/-- A branch-kernel element centralizes each of the three neighboring labels. -/
theorem action_ker_centralizes_neighbor (g : c.radiusTwoSecondGroup β)
    (hg : g ∈ (c.radiusTwoSecondAction hr (by omega) f).ker) :
    g.val ∈ centralizer (c.neighborLabelGroup β : Set G) := by
  have hk : f.branchAction (Subgroup.inclusion
      (c.radiusTwo_second_le_stabilizer hr (by omega) β) g) = 1 := hg
  rw [CanonicalLabelSetup.neighborLabelGroup, centralizer_closure]
  apply mem_centralizer_iff.mpr
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨j,hj⟩ := f.e.surjective ⟨w,hw⟩
  have hjv : (f.e j).val = w := congrArg Subtype.val hj
  rw [← hjv]
  have hfix := f.branchAction_eval (Subgroup.inclusion
    (c.radiusTwo_second_le_stabilizer hr (by omega) β) g) j
  rw [hk, Equiv.Perm.one_apply] at hfix
  change (f.e j).val = g.val • (f.e j).val at hfix
  have he := c.conjugate g.val (f.e j).val (branch_type c hβ j)
  rw [← hfix] at he
  change c.label (f.e j).val * g.val = g.val * c.label (f.e j).val
  calc
    _ = (g.val * c.label (f.e j).val * g.val⁻¹) * g.val := congrArg (fun z => z*g.val) he
    _ = _ := by group


omit r c hr hs h hβ in
private theorem permutation_four_center_trivial :
    ∀ p : Equiv.Perm (Fin 4), (∀ q, q*p=p*q) → p = 1 := by decide +kernel

/-- The original order-ninety-six source group has trivial center. -/
theorem second_center_eq_bot : center (c.radiusTwoSecondGroup β) = ⊥ := by
  let : (four c hr hs h hβ (β := β)).Normal :=
    c.radiusTwo_neighborLabelGroup_normal hr (by omega) h hβ
  obtain ⟨e, _⟩ := r.reflection_quotient_symmetric_four c hr hs h hβ
  let q := QuotientGroup.mk' (four c hr hs h hβ (β := β))
  apply bot_unique
  intro z hz
  have hqz : q z = 1 := by
    apply e.injective
    rw [map_one]
    apply permutation_four_center_trivial
    intro p
    obtain ⟨w,rfl⟩ := e.surjective p
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (four c hr hs h hβ (β := β)) w
    simpa only [map_mul] using congrArg (fun x => e (q x)) (mem_center_iff.mp hz g)
  have hzN' : z ∈ four c hr hs h hβ := (QuotientGroup.eq_one_iff z).mp hqz
  have hzN : z.val ∈ c.neighborLabelGroup β := hzN'
  rcases neighbor_cases c hr hs h hβ (f := f) hzN with hz1 | ⟨i,hi⟩
  · exact Subtype.ext hz1
  · obtain ⟨j,hj⟩ := (by decide : ∀ i : Fin 3,
      ∃ j : Fin 3, Equiv.swap (j+1) (j+2) i ≠ i) i
    let g : c.radiusTwoSecondGroup β := ⟨_,r.mem_second c h hβ (j,0)⟩
    have hc := congrArg Subtype.val (mem_center_iff.mp hz g)
    change c.label (r.u (j,0)) * z.val = z.val * c.label (r.u (j,0)) at hc
    rw [hi] at hc
    have hv := f.branchAction_eval (Subgroup.inclusion
      (c.radiusTwo_second_le_stabilizer hr (by omega) β) g) i
    change (f.e (c.radiusTwoSecondAction hr (by omega) f g i)).val =
      c.label (r.u (j,0)) • (f.e i).val at hv
    have hact : c.radiusTwoSecondAction hr (by omega) f g = Equiv.swap (j+1) (j+2) :=
      r.label_branch_action c hr hs h hβ (j,0)
    rw [hact] at hv
    have he := c.conjugate (c.label (r.u (j,0))) (f.e i).val (branch_type c hβ i)
    rw [← hv, hc, mul_assoc, mul_inv_cancel, mul_one] at he
    exact (hj (branch_labels_injective c hβ he)).elim

/-- The kernel of the actual action on the three branches has order sixteen. -/
theorem second_action_ker_card :
    Nat.card (c.radiusTwoSecondAction hr (by omega) f).ker = 16 := by
  let q := c.radiusTwoSecondAction hr (by omega) f
  have hsurj := c.radiusTwoSecondAction_surjective hr hs h hβ f
  let e := QuotientGroup.quotientKerEquivOfSurjective q hsurj
  have hquot : Nat.card (c.radiusTwoSecondGroup β ⧸ q.ker) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  change Nat.card q.ker = 16
  have hc := q.ker.card_mul_index
  rw [Subgroup.index_eq_card, hquot, r.second_card c hr hs h hβ] at hc
  omega


omit r in
/-- The original neighboring four-group lies in the actual branch kernel. -/
theorem neighbor_le_action_ker :
    (c.neighborLabelGroup β).subgroupOf (c.radiusTwoSecondGroup β) ≤
      (c.radiusTwoSecondAction hr (by omega) f).ker := by
  let := c.radiusTwo_neighborLabelGroup_isKleinFour hr (by omega) h β hβ
  intro n hn
  change f.branchAction (Subgroup.inclusion
    (c.radiusTwo_second_le_stabilizer hr (by omega) β) n) = 1
  apply Equiv.ext
  intro j
  apply branch_labels_injective c hβ (f := f)
  change c.label (f.e (f.branchAction (Subgroup.inclusion
    (c.radiusTwo_second_le_stabilizer hr (by omega) β) n) j)).val = c.label (f.e j).val
  rw [f.branchAction_eval, Subgroup.coe_inclusion]
  have hzN : c.label (f.e j).val ∈ c.neighborLabelGroup β :=
    subset_closure ⟨(f.e j).val, (f.e j).property,rfl⟩
  have hc := congrArg Subtype.val
    ((IsKleinFour.isMulCommutative (G := c.neighborLabelGroup β)).is_comm.comm
      ⟨n.val,hn⟩ ⟨c.label (f.e j).val,hzN⟩)
  change n.val * c.label (f.e j).val = c.label (f.e j).val * n.val at hc
  rw [c.conjugate n.val (f.e j).val (branch_type c hβ j),
    hc, mul_assoc, mul_inv_cancel, mul_one]

/-- The branch kernel has a center containing the actual neighboring four-group. -/
theorem second_action_ker_center_card :
    4 ≤ Nat.card (center (c.radiusTwoSecondAction hr (by omega) f).ker) := by
  let : Finite (c.radiusTwoSecondGroup β) := Nat.finite_of_card_ne_zero
    (by rw [r.second_card c hr hs h hβ]; decide)
  let N := (c.neighborLabelGroup β).subgroupOf (c.radiusTwoSecondGroup β)
  let K := (c.radiusTwoSecondAction hr (by omega) f).ker
  have hNK : N ≤ K := neighbor_le_action_ker c hr hs h hβ
  have hNZ : N.subgroupOf K ≤ center K := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (action_ker_centralizes_neighbor c hr hs hβ y.val y.property)
      (x.val : G) hx).symm
  have hcard : Nat.card (N.subgroupOf K) = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hNK).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (c.radiusTwo_neighborLabelGroup_le_second h hβ)).toEquiv]
    let := c.radiusTwo_neighborLabelGroup_isKleinFour hr (by omega) h β hβ
    exact IsKleinFour.card_four
  rw [← hcard]
  exact Nat.card_le_card_of_injective (Subgroup.inclusion hNZ) (Subgroup.inclusion_injective hNZ)

/-- The branch kernel retains the source paired element of order four. -/
theorem second_action_ker_order_four :
    ∃ p : (c.radiusTwoSecondAction hr (by omega) f).ker, orderOf p = 4 := by
  let a : c.radiusTwoSecondGroup β := ⟨_,r.mem_second c h hβ (0,0)⟩
  let b : c.radiusTwoSecondGroup β := ⟨_,r.mem_second c h hβ (0,1)⟩
  let q := c.radiusTwoSecondAction hr (by omega) f
  have hk : a*b ∈ q.ker := by
    have ha : q a = Equiv.swap (1 : Fin 3) 2 := r.label_branch_action c hr hs h hβ (0,0)
    have hb : q b = Equiv.swap (1 : Fin 3) 2 := r.label_branch_action c hr hs h hβ (0,1)
    change q (a*b) = 1
    rw [map_mul,ha,hb,Equiv.swap_mul_self]
  let p : q.ker := ⟨a*b,hk⟩
  refine ⟨p,?_⟩
  have hsq := (r.pair_product_structure c hr hs h hβ 0 0 1 (by decide)).1
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · intro he
    have he' := congrArg (fun x : q.ker => (x.val : G)) he
    change (c.label (r.u (0,0)) * c.label (r.u (0,1))) ^ 2 = 1 at he'
    have hz := c.order_two (f.e 0).val (branch_type c hβ 0)
    rw [← hsq, he', orderOf_one] at hz
    omega
  · apply Subtype.ext
    apply Subtype.ext
    change (c.label (r.u (0,0)) * c.label (r.u (0,1))) ^ 4 = 1
    rw [show 4 = 2*2 from rfl, pow_mul, hsq, pow_two,
      c.label_mul_self (branch_type c hβ 0)]

/-- The actual branch kernel is the homocyclic core C₄ × C₄. -/
theorem second_action_ker_equiv_c4_square :
    Nonempty ((c.radiusTwoSecondAction hr (by omega) f).ker ≃*
      (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  let : Finite (c.radiusTwoSecondGroup β) := Nat.finite_of_card_ne_zero
    (by rw [r.second_card c hr hs h hβ]; decide)
  exact nonempty_mulEquiv_c4_square_of_normal_order_sixteen _
    (r.second_center_eq_bot c hr hs h hβ) (r.second_action_ker_card c hr hs h hβ)
    (r.second_action_ker_center_card c hr hs h hβ) (r.second_action_ker_order_four c hr hs h hβ)


omit r in
/-- The literal branch kernel is self-centralizing in the second source group. -/
theorem second_action_ker_self_centralizing :
    centralizer ((c.radiusTwoSecondAction hr (by omega) f).ker :
      Set (c.radiusTwoSecondGroup β)) ≤ (c.radiusTwoSecondAction hr (by omega) f).ker := by
  intro g hg
  change f.branchAction (Subgroup.inclusion
    (c.radiusTwo_second_le_stabilizer hr (by omega) β) g) = 1
  apply Equiv.ext
  intro j
  apply branch_labels_injective c hβ (f := f)
  change c.label (f.e (f.branchAction (Subgroup.inclusion
    (c.radiusTwo_second_le_stabilizer hr (by omega) β) g) j)).val = c.label (f.e j).val
  rw [f.branchAction_eval, Subgroup.coe_inclusion]
  let z : c.radiusTwoSecondGroup β := ⟨c.label (f.e j).val,
    c.neighbor_label_mem_radiusTwoSecondGroup h (f.e j).property (branch_type c hβ j)⟩
  have hzN : z ∈ (c.neighborLabelGroup β).subgroupOf (c.radiusTwoSecondGroup β) :=
    subset_closure ⟨(f.e j).val, (f.e j).property,rfl⟩
  have hzK := neighbor_le_action_ker c hr hs h hβ (f := f) hzN
  have hc := congrArg Subtype.val (mem_centralizer_iff.mp hg z hzK).symm
  change g.val * c.label (f.e j).val = c.label (f.e j).val * g.val at hc
  rw [c.conjugate g.val (f.e j).val (branch_type c hβ j),
    hc, mul_assoc, mul_inv_cancel, mul_one]

/-- The original distance-three group is the concrete second derived G₂ parabolic. -/
theorem second_equiv_derivedSecond :
    Nonempty (c.radiusTwoSecondGroup β ≃* Atlas.G2.BinaryParabolicPair.derivedSecond) := by
  let : Finite (c.radiusTwoSecondGroup β) := Nat.finite_of_card_ne_zero
    (by rw [r.second_card c hr hs h hβ]; decide)
  obtain ⟨e⟩ := r.second_action_ker_equiv_c4_square c hr hs h hβ
  exact Atlas.G2.BinaryParabolicPair.equiv_derivedSecond_of_c4_square _ e
    (r.second_card c hr hs h hβ) (second_action_ker_self_centralizing c hr hs h hβ)
    (QuotientGroup.quotientKerEquivOfSurjective _
      (c.radiusTwoSecondAction_surjective hr hs h hβ f))

end Frame
end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.RadiusTwoSixLabels
