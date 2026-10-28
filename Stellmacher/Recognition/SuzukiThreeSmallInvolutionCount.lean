module

public import Stellmacher.Recognition.SuzukiThreeCentralizerCount
import Mathlib.Tactic

/-!
# The nine involutions in a Suzuki point stabilizer

The cyclic two-point stabilizer of order eight is a Sylow 2-subgroup of the
point stabilizer of order 216. Its unique involution therefore represents all
involutions of the point stabilizer. Root–torus coordinates identify its
centralizer there with the product of its root centralizer and the torus.
In the centralizing-swap branch this has order 3 · 8 = 24, giving 216 / 24 = 9
involutions.

Source: Suzuki (1965), Section II, Lemmas 1–3.
-/

namespace Stellmacher.Recognition.SuzukiThreeHypotheses

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω]
    {a : Ω} {Q : Subgroup (stabilizer G a)} [Q.Normal]
    (h : SuzukiThreeHypotheses G Ω a Q)

include h

/-- Root–torus coordinates for the centralizer inside a point stabilizer. -/
public theorem stabilizer_centralizer_card (b : Ω) (hb : b ≠ a)
    (k : stabilizer (stabilizer G a) b) :
    Nat.card (Subgroup.centralizer ({(k : stabilizer G a)} : Set (stabilizer G a))) =
      Nat.card (rootCentralizer (Q := Q) b k) * 8 := by
  let P := rootCentralizer (Q := Q) b k
  let K := stabilizer (stabilizer G a) b
  let C := Subgroup.centralizer ({(k : stabilizer G a)} : Set (stabilizer G a))
  let f : P × K → C := fun p => ⟨p.1.val.val * p.2.val, by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact ((h.commute_root_torus_iff b hb k p.2 p.1.val).mpr
      ((mem_rootCentralizer b k p.1.val).mp p.1.property)).symm.eq⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q he
      have he' := (h.root_torus_bijective b hb).injective
        (a₁ := (p.1.val, p.2)) (a₂ := (q.1.val, q.2))
        (congrArg Subtype.val he)
      exact Prod.ext (Subtype.ext (congrArg Prod.fst he')) (congrArg (fun z : Q × K => z.2) he')
    · intro x
      obtain ⟨⟨u, l⟩, he⟩ := (h.root_torus_bijective b hb).surjective x.val
      have hx : Commute ((k : stabilizer G a) : G) (x.val : G) := by
        exact congrArg (fun z : stabilizer G a => (z : G))
          (Subgroup.mem_centralizer_singleton_iff.mp x.property).symm
      have heG : ((u : stabilizer G a) : G) * ((l : stabilizer G a) : G) =
          (x.val : G) := congrArg (fun z : stabilizer G a => (z : G)) he
      have hu : u ∈ P := (mem_rootCentralizer b k u).mpr
        ((h.commute_root_torus_iff b hb k l u).mp (heG.symm ▸ hx))
      exact ⟨(⟨u, hu⟩, l), Subtype.ext he⟩
  have hc := (Nat.card_congr (Equiv.ofBijective f hf)).symm
  rw [Nat.card_prod, h.twoPoint_card b hb] at hc
  exact hc

/-- Sylow conjugacy fuses all point-stabilizer involutions into the torus. -/
public theorem stabilizer_involution_isConj [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (j : stabilizer (stabilizer G a) b)
    (hj : orderOf (j : G) = 2) (x : stabilizer G a) (hx : orderOf x = 2) :
    IsConj x (j : stabilizer G a) := by
  let : Finite G := h.finite_group
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := stabilizer (stabilizer G a) b
  have hK : IsPGroup 2 K := IsPGroup.of_card (n := 3) (h.twoPoint_card b hb)
  have hidx : K.index = 27 := by
    have hc := K.card_mul_index
    rw [h.twoPoint_card b hb, h.stabilizer_card] at hc
    omega
  let S : Sylow 2 (stabilizer G a) := hK.toSylow (by rw [hidx]; decide)
  have hxP : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx]; rfl)
  obtain ⟨R, hR⟩ := hxP.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_smul_eq (stabilizer G a) R S
  have hxR : x ∈ R := hR (Subgroup.mem_zpowers x)
  have hxK : g * x * g⁻¹ ∈ K := by
    have hz := (R.equivSMul g ⟨x, hxR⟩).property
    change g * x * g⁻¹ ∈ (g • R : Sylow 2 (stabilizer G a)) at hz
    rw [hg] at hz
    exact hz
  let k : K := ⟨g * x * g⁻¹, hxK⟩
  have hk : orderOf (k : G) = 2 := by
    have hc := (MulAut.conj g).orderOf_eq x
    change orderOf (g * x * g⁻¹) = orderOf x at hc
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact (Subgroup.orderOf_coe k).symm.trans (hc.trans hx)
  obtain ⟨j₀, _, huniq⟩ := h.twoPoint_exists_unique_involution b hb
  have he : k = j := (huniq k hk).trans (huniq j hj).symm
  exact isConj_iff.mpr ⟨g, congrArg Subtype.val he⟩

/-- In the centralizing-swap branch, the point stabilizer has nine involutions. -/
public theorem stabilizer_involution_card [FaithfulSMul G Ω]
    (b : Ω) (hb : b ≠ a) (t : G) (_ht : t ^ 2 = 1)
    (hta : t • a = b) (htb : t • b = a)
    (htK : ∀ k : stabilizer (stabilizer G a) b,
      Commute t ((k : stabilizer G a) : G)) :
    Nat.card {x : G // orderOf x = 2 ∧ x ∈ stabilizer G a} = 9 := by
  let : Finite G := h.finite_group
  obtain ⟨j, hj, _⟩ := h.twoPoint_exists_unique_involution b hb
  let J := (ConjClasses.mk (j : stabilizer G a)).carrier
  have hcent : Nat.card
      (Subgroup.centralizer ({(j : stabilizer G a)} : Set (stabilizer G a))) = 24 := by
    rw [h.stabilizer_centralizer_card b hb j,
      h.rootCentralizer_involution_card b hb t hta htb j hj (htK j).symm]
  have hclass : Nat.card J = 9 := by
    have hc := ConjClasses.nat_card_carrier_mul_card_centralizer (j : stabilizer G a)
    rw [hcent, h.stabilizer_card] at hc
    change Nat.card J * 24 = 216 at hc
    omega
  let f : {x : G // orderOf x = 2 ∧ x ∈ stabilizer G a} → J := fun x =>
    ⟨⟨x.val, x.property.2⟩, ConjClasses.mem_carrier_iff_mk_eq.mpr
      (ConjClasses.mk_eq_mk_iff_isConj.mpr
        (h.stabilizer_involution_isConj b hb j hj ⟨x.val, x.property.2⟩
          (by
            rw [← Subgroup.orderOf_coe]
            exact x.property.1)))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      exact Subtype.ext (congrArg (fun z : J => (z.val : G)) he)
    · intro x
      have hxconj : IsConj x.val (j : stabilizer G a) :=
        ConjClasses.mk_eq_mk_iff_isConj.mp
          (ConjClasses.mem_carrier_iff_mk_eq.mp x.property)
      obtain ⟨g, hg⟩ := isConj_iff.mp hxconj
      have hx : orderOf (x.val : G) = 2 := by
        have hc := (MulAut.conj g).orderOf_eq x.val
        change orderOf (g * x.val * g⁻¹) = orderOf x.val at hc
        rw [hg] at hc
        simpa only [Subgroup.orderOf_coe] using hc.symm.trans
          (show orderOf (j : stabilizer G a) = 2 by
            simpa only [Subgroup.orderOf_coe] using hj)
      exact ⟨⟨x.val, hx, x.val.property⟩, Subtype.ext (Subtype.ext rfl)⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).trans hclass

end Stellmacher.Recognition.SuzukiThreeHypotheses
