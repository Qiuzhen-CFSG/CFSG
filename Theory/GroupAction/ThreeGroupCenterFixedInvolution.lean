module

public import Theory.GroupTheory.PGroup.AbelianIndexThreeStructure
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Center-fixing involutions of finite three-groups

An involutive automorphism fixing the center of a finite nonabelian three-group
preserves every abelian subgroup of index three. The identity automorphism is
included, and the center can have arbitrary order.

If an abelian index-three subgroup were moved, it and its image would force the
center to have index nine. Every proper subgroup containing the center is then
abelian, since its quotient by the center has order at most three. Apply this to
the fixed subgroup. A fixed element commutes with an inverted element: their
central commutator is both fixed and inverted, hence trivial in odd order.
The fixed/inverted factorization therefore identifies the fixed subgroup with
the center. The same factorization shows that every subgroup containing the
center is preserved, giving the contradiction.

This supplies the abstract involution input in the three-core argument for
GLS4, Chapter 4, Lemma 3.11(a), `refs/KGroup/GLS4/Chapter4.tex`, lines 585–603.
The degree-three subgroup context is Aschbacher–Smith A.3.21(c), printed
pp.55–56 of `refs/quasithin.pdf`. The fixed/inverted argument also appears in
`Theory.GroupAction.Extraspecial27InvolutionFixed`; here no extraspecial or
order-27 assumption is required.
-/

open Subgroup
open scoped commutatorElement

namespace MulAut
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem abelian_of_proper_of_center_index_nine
    (hindex : (center G).index = 9) (C : Subgroup G)
    (hZC : center G ≤ C) (hne : C ≠ ⊤) : IsMulCommutative C := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let Z := (center G).subgroupOf C
  have hm : Z.index * C.index = 9 := by
    exact (relIndex_mul_index hZC).trans hindex
  have hdvd : Z.index ∣ 3 ^ 2 := by
    exact ⟨C.index, by simpa using hm.symm⟩
  obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hdvd
  have hnlt : n < 2 := by
    by_contra hh
    have hn2 : n = 2 := by omega
    rw [hn2] at he
    have hci : C.index = 1 := by rw [he] at hm; omega
    exact hne (index_eq_one.mp hci)
  have hsmall : Nat.card (C ⧸ Z) ∣ 3 := by
    change Z.index ∣ 3
    interval_cases n <;> simp [he]
  let : IsCyclic (C ⧸ Z) := isCyclic_of_card_dvd_prime hsmall
  apply (QuotientGroup.mk' Z).isMulCommutative_of_isCyclic_of_ker_le_center
  rw [QuotientGroup.ker_mk']
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact mem_center_iff.mp hx y.val

private theorem fixed_eq_center_of_center_index_nine_involution
    (hodd : Odd (Nat.card G)) (hindex : (center G).index = 9)
    (α : MulAut G) (hα : Function.Involutive α) (hne : α ≠ 1)
    (hZ : ∀ z ∈ center G, α z = z) : fixedSubgroup α = center G := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let C := fixedSubgroup α
  have hZC : center G ≤ C := fun z hz => (mem_fixedSubgroup α z).mpr (hZ z hz)
  have hCne : C ≠ ⊤ := by
    intro he
    apply hne
    ext x
    exact (mem_fixedSubgroup α x).mp (he.ge (mem_top x))
  let : IsMulCommutative C := abelian_of_proper_of_center_index_nine hindex C hZC hCne
  let : IsMulCommutative (G ⧸ center G) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by
      change (center G).index = 3 ^ 2
      exact hindex)
  have hcommcenter (x y : G) : ⁅x,y⁆ ∈ center G := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (center G)) ⁅x,y⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (IsMulCommutative.is_comm.comm _ _)
  have hfixed_inverted (c v : G) (hc : α c = c) (hv : α v = v⁻¹) : Commute c v := by
    have hcentral := hcommcenter c v
    have hh : α ⁅c,v⁆ = ⁅c,v⁆⁻¹ := by
      rw [map_commutatorElement, hc, hv, commutatorElement_inv_right, ← commutatorElement_inv]
      rw [mem_center_iff.mp ((center G).inv_mem hcentral) v⁻¹,
        mul_assoc, inv_mul_cancel, mul_one]
    rw [hZ _ hcentral] at hh
    have hsquare : ⁅c,v⁆ ^ 2 = 1 := by
      rw [pow_two]
      calc
        ⁅c,v⁆ * ⁅c,v⁆ = ⁅c,v⁆⁻¹ * ⁅c,v⁆ := congrArg (fun x => x * ⁅c,v⁆) hh
        _ = 1 := inv_mul_cancel _
    have hc1 : ⁅c,v⁆ = 1 := hodd.coprime_two_right.pow_left_bijective.injective
      (hsquare.trans (one_pow 2).symm)
    exact commutatorElement_eq_one_iff_commute.mp hc1
  apply le_antisymm
  · intro c hc
    rw [mem_center_iff]
    intro x
    obtain ⟨⟨u,v⟩, ⟨hu,hv,huv⟩, _⟩ :=
      Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hodd α hα x
    have hcu : Commute c u := setLike_mul_comm (s := C) hc ((mem_fixedSubgroup α u).mpr hu)
    have hcv : Commute c v := hfixed_inverted c v ((mem_fixedSubgroup α c).mp hc) hv
    rw [← huv]
    exact (hcu.mul_right hcv).eq.symm
  · exact hZC

/-- A center-fixing involutive automorphism of a finite nonabelian three-group
preserves every abelian subgroup of index three, including when the automorphism
is the identity. -/
public theorem map_eq_self_of_abelian_index_three_of_center_fixed_involution
    (hG : IsPGroup 3 G) (hn : ¬ IsMulCommutative G)
    (α : MulAut G) (hα : Function.Involutive α)
    (hZ : ∀ z ∈ center G, α z = z)
    (A : Subgroup G) (ha : IsMulCommutative A) (hi : A.index = 3) :
    A.map α.toMonoidHom = A := by
  classical
  by_contra hne
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsMulCommutative A := ha
  have hb : IsMulCommutative (A.map α.toMonoidHom) := inferInstance
  have hj : (A.map α.toMonoidHom).index = 3 := (index_map_equiv A α).trans hi
  have hindex : (center G).index = 9 :=
    center_index_eq_nine_of_distinct_abelian_index_three hG hn A
      (A.map α.toMonoidHom) ha hb hi hj (fun he => hne he.symm)
  have hαne : α ≠ 1 := by
    intro he
    apply hne
    subst α
    exact A.map_id
  have hodd : Odd (Nat.card G) := by
    obtain ⟨n, he⟩ := hG.exists_card_eq
    rw [he]
    exact (by decide : Odd 3).pow
  have hfixed := fixed_eq_center_of_center_index_nine_involution hodd hindex α hα hαne hZ
  have hZA := center_le_of_abelian_index_three hG hn A ha hi
  have hstable : ∀ x ∈ A, α x ∈ A := by
    intro x hx
    obtain ⟨⟨u,v⟩, ⟨hu,hv,huv⟩, _⟩ :=
      Theory.GroupTheory.existsUnique_fixed_inverted_mul_of_odd_card hodd α hα x
    have huA : u ∈ A := hZA (hfixed ▸ (mem_fixedSubgroup α u).mpr hu)
    have hvA : v ∈ A := by
      have hh := A.mul_mem (A.inv_mem huA) hx
      simpa [← huv] using hh
    rw [← huv, map_mul, hu, hv]
    exact A.mul_mem huA (A.inv_mem hvA)
  apply hne
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hstable x hx
  · intro x hx
    exact ⟨α x, hstable x hx, hα x⟩

end MulAut
