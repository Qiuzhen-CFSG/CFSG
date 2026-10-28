module
public import CFSG.Quasithin.Chapter15.Section01.CaseI.MarkedMovementTransport
public import Theory.GroupTheory.PResidual.PrimeToTransport
public import Theory.GroupTheory.PResidual.TwoThreeComparison
public import Theory.GroupTheory.PResidual.OrderSix

/-!
# The actual cubic residual in Case I

A marked point stabilizer of order six has the same two-residual and
prime-to-three residual. Surjective image transport identifies the action
of the original O^{3'}(C_M(Z1)) with that cubic. Every two-perfect subgroup
whose action is nontrivial therefore has the full same image, moves the
same V2, and has centralizer index three on V2.

Source: Aschbacher--Smith15.1.24(3), printed p.1101, with the original
marked source maps retained.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem marked_six_twoThree {D : Type*} [Group D] [Finite D]
    (hc : Nat.card D = 6) : IsPiGroup twoThreePrimes D := by
  apply (IsPiGroup_iff _ _).mpr
  intro p hp
  rw [hc] at hp
  have h := p.property.dvd_mul.mp (show (p : ℕ) ∣ 2*3 from hp)
  rcases h with h | h
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left p.property.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left p.property.ne_one)

/-- The original prime-to-three residual has the same cubic action as the
marked centralizer's two-residual. -/
theorem marked_primeToResidual_action_image
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (v : Additive V) (K : Subgroup (internalActionImage M V hn))
    (hK : ∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v)
    (hc : Nat.card K = 6) :
    let C := M ⊓ centralizer (zpowers (v.toMul : G) : Set G)
    let Y := (primeToResidual 3 C).map C.subtype
    let hYM : Y ≤ M := (map_subtype_le _).trans inf_le_left
    let a : Y →* internalActionImage M V hn :=
      (actionHom M V hn).rangeRestrict.comp (inclusion hYM)
    a.range = (pResidual 2 K).map K.subtype := by
  dsimp only
  let C := M ⊓ centralizer (zpowers (v.toMul : G) : Set G)
  let Y := (primeToResidual 3 C).map C.subtype
  let hYM : Y ≤ M := (map_subtype_le _).trans inf_le_left
  let f := (actionHom M V hn).rangeRestrict
  let a := f.comp (inclusion hYM)
  obtain ⟨q,hq,hker,hcoord⟩ := vector_stabilizer_projection M V hn v K hK
  have he : (primeToResidual 3 C).map q = pResidual 2 K := by
    rw [map_primeToResidual_of_surjective 3 q hq,
      ← twoResidual_eq_primeToResidual_three (marked_six_twoThree hc)]
  change a.range = _
  rw [← he, map_map]
  ext d
  constructor
  · rintro ⟨r,rfl⟩
    obtain ⟨c,hc,hcr⟩ := r.property
    refine ⟨c,hc,?_⟩
    change (q c : internalActionImage M V hn) = f (inclusion hYM r)
    rw [hcoord]
    congr 1
    exact Subtype.ext hcr
  · rintro ⟨c,hc,rfl⟩
    refine ⟨⟨c,mem_map_of_mem C.subtype hc⟩,?_⟩
    change f ⟨(c:G),c.property.1⟩ = (q c : internalActionImage M V hn)
    exact (hcoord c).symm

/-- The prime-to-three residual moves exactly the same original subgroup V2. -/
theorem marked_primeToResidual_commutator
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (v : Additive V) (K : Subgroup (internalActionImage M V hn))
    (hK : ∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v)
    (hc : Nat.card K = 6) :
    let C := M ⊓ centralizer (zpowers (v.toMul : G) : Set G)
    let Y := (primeToResidual 3 C).map C.subtype
    let R := (pResidual 2 C).map C.subtype
    ⁅V,Y⁆ = ⁅V,R⁆ := by
  intro C Y R
  let hYM : Y ≤ M := (map_subtype_le _).trans inf_le_left
  let a : Y →* internalActionImage M V hn :=
    (actionHom M V hn).rangeRestrict.comp (inclusion hYM)
  have hh := commutator_image_eq (imageRepresentation M V hn) V V Y
    (hYM.trans hn) le_rfl a (MonoidHom.id V) (fun _ _ => rfl) ⊤ (by
      ext x
      simp [binarySubgroup])
  rw [map_id, marked_primeToResidual_action_image M V hn v K hK hc] at hh
  have he : ⁅V,Y⁆.subgroupOf V = ⁅V,R⁆.subgroupOf V :=
    hh.trans (marked_residual_commutator_image M V hn v K hK).symm
  have hYV : ⁅V,Y⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp (hYM.trans hn)
  have hRV : ⁅V,R⁆ ≤ V := (marked_residual_movement hn _).1
  simpa only [map_subgroupOf_eq_of_le hYV,map_subgroupOf_eq_of_le hRV] using
    congrArg (map V.subtype) he

/-- Every noncentral two-perfect subgroup of the literal cubic actor moves
all of the same V2. This is the subgroup quantifier of source15.1.24(3). -/
theorem marked_cubic_subgroup_movement
    (M V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G))
    (v : Additive V) (K : Subgroup (internalActionImage M V hn))
    (hK : ∀ d, d ∈ K ↔ imageRepresentation M V hn d v = v)
    (hc : Nat.card K = 6) :
    let C := M ⊓ centralizer (zpowers (v.toMul : G) : Set G)
    let Y := (primeToResidual 3 C).map C.subtype
    let R := (pResidual 2 C).map C.subtype
    ∀ (Y0 : Subgroup G), Y0 ≤ Y → IsPPerfect 2 Y0 →
      ¬ Y0 ≤ centralizer (V : Set G) →
      ⁅V,Y0⁆ = ⁅V,R⁆ ∧ ⁅⁅V,R⁆,Y0⁆ = ⁅V,R⁆ ∧
      (centralizer ((⁅V,R⁆ : Subgroup G) : Set G)).relIndex Y0 = 3 := by
  intro C Y R Y0 hY0 hp hncen
  let hYM : Y ≤ M := (map_subtype_le _).trans inf_le_left
  let hY0M : Y0 ≤ M := hY0.trans hYM
  let f := (actionHom M V hn).rangeRestrict
  let a : Y →* internalActionImage M V hn := f.comp (inclusion hYM)
  let a0 : Y0 →* internalActionImage M V hn := f.comp (inclusion hY0M)
  let B := (pResidual 2 K).map K.subtype
  have ha : a.range = B := marked_primeToResidual_action_image M V hn v K hK hc
  have hle : a0.range ≤ B := by
    rw [←ha]
    rintro _ ⟨y,rfl⟩
    exact ⟨⟨y,hY0 y.property⟩,rfl⟩
  have hne : a0.range ≠ ⊥ := by
    intro hb
    apply hncen
    intro y hy w hw
    have he : a0 ⟨y,hy⟩ = 1 := by
      have hh : a0 ⟨y,hy⟩ ∈ a0.range := ⟨⟨y,hy⟩,rfl⟩
      rw [hb,mem_bot] at hh
      exact hh
    have hh := congrArg (fun d =>
      ((imageRepresentation M V hn d (Additive.ofMul (⟨w,hw⟩ : V))).toMul : G)) he
    change y*w*y⁻¹ = w at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hcard : Nat.card B = 3 := by
    rw [card_map_of_injective K.subtype_injective,card_twoResidual_of_card_six hc]
  have heq : a0.range = B := by
    let : Fact (Nat.card B).Prime := ⟨hcard ▸ Nat.prime_three⟩
    rcases (a0.range.subgroupOf B).eq_bot_or_eq_top_of_prime_card with hb | ht
    · have hh := congrArg (map B.subtype) hb
      rw [map_subgroupOf_eq_of_le hle,Subgroup.map_bot] at hh
      exact (hne hh).elim
    · have hh := congrArg (map B.subtype) ht
      simpa only [map_subgroupOf_eq_of_le hle,←MonoidHom.range_eq_map,range_subtype] using hh
  have hh := commutator_image_eq (imageRepresentation M V hn) V V Y0
    (hY0M.trans hn) le_rfl a0 (MonoidHom.id V) (fun _ _ => rfl) ⊤ (by
      ext x
      simp [binarySubgroup])
  rw [map_id,heq] at hh
  have hh' : ⁅V,Y0⁆.subgroupOf V = ⁅V,R⁆.subgroupOf V :=
    hh.trans (marked_residual_commutator_image M V hn v K hK).symm
  have hYV : ⁅V,Y0⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp (hY0M.trans hn)
  have hRV : ⁅V,R⁆ ≤ V := (marked_residual_movement hn _).1
  have he : ⁅V,Y0⁆ = ⁅V,R⁆ := by
    simpa only [map_subgroupOf_eq_of_le hYV,map_subgroupOf_eq_of_le hRV] using
      congrArg (map V.subtype) hh'
  have hmove : ⁅⁅V,R⁆,Y0⁆ = ⁅V,R⁆ := by
    rw [←he]
    exact commutator_isPPerfect_idempotent Y0 V hp
      (IsElementaryAbelian.isPGroup 2 V) (hY0M.trans hn)
  refine ⟨he,hmove,?_⟩
  have hker : a0.ker = (centralizer (V : Set G)).subgroupOf Y0 := by
    ext y
    change f (inclusion hY0M y) = 1 ↔ (y:G) ∈ centralizer (V : Set G)
    constructor
    · intro hy
      have hh : (inclusion hY0M y) ∈ (actionHom M V hn).ker := congrArg Subtype.val hy
      rw [actionHom_ker] at hh
      exact hh
    · intro hy
      have hh : (inclusion hY0M y) ∈ (actionHom M V hn).ker := by
        rw [actionHom_ker]
        exact hy
      exact Subtype.ext hh
  have hcV : (centralizer (V : Set G)).relIndex Y0 = 3 := by
    change ((centralizer (V : Set G)).subgroupOf Y0).index = 3
    rw [←hker]
    have hh := relIndex_ker (⊤ : Subgroup Y0) a0
    simpa only [relIndex_top_right,←MonoidHom.range_eq_map,heq,hcard] using hh
  have hd := relIndex_dvd_of_le_left Y0 (centralizer_le hRV)
  rw [hcV] at hd
  apply (Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left
  intro hi
  have hz : ⁅⁅V,R⁆,Y0⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr (relIndex_eq_one.mp hi)
  have hzV : ⁅V,Y0⁆ = ⊥ := he.trans (hmove.symm.trans hz)
  exact hncen (commutator_eq_bot_iff_le_centralizer.mp
    ((commutator_comm Y0 V).trans hzV))

end CFSG.Quasithin.Chapter15.Section01
