module
public import Theory.GroupTheory.CubicCentralizerCount
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.IndexNormal
public import Theory.GroupTheory.CentralDisplacementOddIndex
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Small residuals from an involution with small fixed index

An involutory automorphism fixing a subgroup of index at most two has
central displacement. If a cubic element is inverted by such an involution,
the cubic is a product of two conjugate involutions, so its displacement
on a normal subgroup is central as well. The displacement homomorphism
identifies the cubic commutator order with its fixed-subgroup index, which
the existing centralizer intersection bound makes at most four.

The final theorem supplies the literal commutator inside the two-core of a
finite symmetric-three extension. Its source consumer is Goldschmidt,
*Automorphisms of trivalent graphs* (1980), (4.2), printed pp.392--393.
This bypasses the quaternion intermediate case by using the original
involution's index-two condition directly.
-/

open Subgroup
namespace MulAut
variable {P : Type*} [Group P] [Finite P]

private theorem displacement_central_of_fixed_index_le_two (a : MulAut P)
    (ha : a ^ 2 = 1) (hi : a.fixedSubgroup.index ≤ 2) (x : P) :
    a x * x⁻¹ ∈ center P := by
  let C := a.fixedSubgroup
  have hfix {y : P} (hy : y ∈ C) : a y = y := (mem_fixedSubgroup a y).mp hy
  have haa (y : P) : a (a y) = y := by
    have h := congrArg (fun f : MulAut P => f y) ha
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using h
  by_cases ht : C.index = 1
  · have htop := index_eq_one.mp ht
    rw [hfix (htop ▸ mem_top x), mul_inv_cancel]
    exact one_mem _
  have hi2 : C.index = 2 := by
    have hp : 0 < C.index := Nat.pos_of_ne_zero C.index_ne_zero_of_finite
    change C.index ≤ 2 at hi
    omega
  let _ : C.Normal := normal_of_index_eq_two hi2
  have hxax : a x * x⁻¹ ∈ C := by
    rw [C.mul_mem_iff_of_index_two hi2, C.inv_mem_iff]
    simp only [C, mem_fixedSubgroup, haa]
    exact eq_comm
  have hd2 : (a x * x⁻¹) ^ 2 = 1 := by
    have hh := hfix hxax
    rw [map_mul, map_inv, haa] at hh
    have hh' : (a x * x⁻¹)⁻¹ = a x * x⁻¹ := by
      simpa only [mul_inv_rev, inv_inv] using hh
    rw [pow_two]
    calc
      _ = (a x * x⁻¹)⁻¹ * (a x * x⁻¹) :=
        congrArg (fun d => d * (a x * x⁻¹)) hh'.symm
      _ = 1 := inv_mul_cancel _
  have hdx : Commute (a x * x⁻¹) x := by
    have hh := hfix (C.mul_self_mem_of_index_two hi2 x)
    rw [map_mul] at hh
    have hs : (a x * x⁻¹)⁻¹ = a x * x⁻¹ :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hd2)
    change a x * x⁻¹ * x = x * (a x * x⁻¹)
    calc
      _ = a x := by group
      _ = x * (a x * x⁻¹)⁻¹ := by
        rw [mul_inv_rev, inv_inv, ← mul_assoc]
        apply (eq_mul_inv_iff_mul_eq).mpr
        exact hh
      _ = x * (a x * x⁻¹) := by rw [hs]
  have hdc (c : P) (hc : c ∈ C) : Commute (a x * x⁻¹) c := by
    have hm := Subgroup.Normal.conj_mem (inferInstance : C.Normal) c hc x⁻¹
    have hh := hfix hm
    simp only [map_mul, map_inv, hfix hc, inv_inv] at hh
    change a x * x⁻¹ * c = c * (a x * x⁻¹)
    calc
      _ = a x * (x⁻¹ * c * x) * x⁻¹ := by group
      _ = a x * ((a x)⁻¹ * c * a x) * x⁻¹ := by rw [hh]
      _ = c * (a x * x⁻¹) := by group
  rw [mem_center_iff]
  intro y
  by_cases hy : y ∈ C
  · exact (hdc y hy).symm.eq
  by_cases hx : x ∈ C
  · rw [hfix hx, mul_inv_cancel, one_mul, mul_one]
  have hyx : y * x⁻¹ ∈ C := (C.mul_mem_iff_of_index_two hi2).mpr (by
    simp only [C.inv_mem_iff, hy, hx])
  have hh := (hdc (y * x⁻¹) hyx).mul_right hdx
  simpa only [inv_mul_cancel_right] using hh.symm.eq

private theorem right_displacement_central_of_fixed_index_le_two (a : MulAut P)
    (ha : a ^ 2 = 1) (hi : a.fixedSubgroup.index ≤ 2) (x : P) :
    x⁻¹ * a x ∈ center P := by
  have h := Subgroup.Normal.conj_mem (inferInstance : (center P).Normal) _
    (displacement_central_of_fixed_index_le_two a ha hi x) x⁻¹
  simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] using h

omit [Finite P] in
private theorem cyclic_commutator_card_eq_fixed_index_of_central
    (a : MulAut P) (hc : ∀ x : P, x⁻¹ * a x ∈ center P) :
    Nat.card (commutatorAction (zpowers a) P) = a.fixedSubgroup.index := by
  let δ := centralDisplacement (center P) le_rfl a hc
  let f : P →* P := (center P).subtype.comp δ
  have hf (x : P) : f x = x⁻¹ * a x := rfl
  have hker : f.ker = a.fixedSubgroup := by
    ext x
    rw [MonoidHom.mem_ker, mem_fixedSubgroup, hf, inv_mul_eq_one, eq_comm]
  have heq : commutatorAction (zpowers a) P = f.range := by
    apply le_antisymm
    · let K : Subgroup (MulAut P) := {
        carrier := {b | ∀ x : P, x⁻¹ * b x ∈ f.range}
        one_mem' := by intro x; simp
        mul_mem' := by
          intro b c hb hc x
          have h := f.range.mul_mem (hc x) (hb (c x))
          change x⁻¹ * b (c x) ∈ f.range
          simpa only [mul_assoc, mul_inv_cancel_left] using h
        inv_mem' := by
          intro b hb x
          have h := f.range.inv_mem (hb (b⁻¹ x))
          simpa only [MulAut.apply_inv_self, mul_inv_rev, inv_inv] using h }
      have hk : zpowers a ≤ K := zpowers_le.mpr (fun x => ⟨x, rfl⟩)
      rw [commutatorAction_eq_closure, closure_le]
      rintro x ⟨b,y,rfl⟩
      exact hk b.property y
    · rintro x ⟨y,rfl⟩
      rw [commutatorAction_eq_closure]
      exact subset_closure ⟨⟨a, mem_zpowers a⟩, y, rfl⟩
  rw [heq, ← index_ker, hker]
end MulAut

namespace Theory.GroupTheory.SmallInvolutionResidual
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem fixed_conjNormal (Q : Subgroup G) [Q.Normal] (z : G) :
    (MulAut.conjNormal z : MulAut Q).fixedSubgroup =
      (centralizer ({z} : Set G)).subgroupOf Q := by
  ext q
  rw [MulAut.mem_fixedSubgroup, mem_subgroupOf]
  change (MulAut.conjNormal z : MulAut Q) q = q ↔
    (q : G) ∈ centralizer ({z} : Set G)
  rw [Subtype.ext_iff, MulAut.conjNormal_apply,
    mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]

public theorem cubic_commutator_card_le_four (Q : Subgroup G) [Q.Normal]
    {z x : G} (hz : z ^ 2 = 1) (hx : x ^ 3 = 1)
    (hinv : MulAut.conj z x = x⁻¹)
    (hi : (centralizer ({z} : Set G)).relIndex Q ≤ 2) :
    Nat.card (⁅Q,zpowers x⁆ : Subgroup G) ≤ 4 := by
  let y := MulAut.conj x z
  have hy : y ^ 2 = 1 := by dsimp only [y]; rw [← map_pow, hz, map_one]
  have hmap : Q.map (MulAut.conj x).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; trivial)
  have hiy : (centralizer ({y} : Set G)).relIndex Q ≤ 2 := by
    rw [show (centralizer ({y} : Set G)).relIndex Q =
      (centralizer ({z} : Set G)).relIndex Q from
      centralizer_relIndex_equiv Q (MulAut.conj x) z hmap]
    exact hi
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hz)
  have hxx : x⁻¹ * x⁻¹ = x := by
    apply inv_injective
    simp only [mul_inv_rev, inv_inv]
    apply eq_inv_of_mul_eq_one_left
    simpa only [pow_succ, pow_zero, one_mul] using hx
  have hprod : z * y = x := by
    change z * (x * z * x⁻¹) = x
    have hinv' : z * x * z = x⁻¹ := by simpa only [MulAut.conj_apply, hzi] using hinv
    rw [← mul_assoc, ← mul_assoc, hinv', hxx]
  let a : MulAut Q := MulAut.conjNormal z
  let b : MulAut Q := MulAut.conjNormal y
  let c : MulAut Q := MulAut.conjNormal x
  have ha : a ^ 2 = 1 := by dsimp [a]; rw [← map_pow, hz, map_one]
  have hb : b ^ 2 = 1 := by dsimp [b]; rw [← map_pow, hy, map_one]
  have hia : a.fixedSubgroup.index ≤ 2 := by rw [fixed_conjNormal]; exact hi
  have hib : b.fixedSubgroup.index ≤ 2 := by rw [fixed_conjNormal]; exact hiy
  have hc : ∀ q : Q, q⁻¹ * c q ∈ center Q := by
    intro q
    have he : c = a * b := by dsimp [a,b,c]; rw [← map_mul, hprod]
    rw [he, MulAut.mul_apply]
    have h1 := MulAut.right_displacement_central_of_fixed_index_le_two b hb hib q
    have h2 := MulAut.right_displacement_central_of_fixed_index_le_two a ha hia (b q)
    have hm := (center Q).mul_mem h1 h2
    simpa only [mul_assoc, mul_inv_cancel_left] using hm
  have hcard := MulAut.cyclic_commutator_card_eq_fixed_index_of_central c hc
  have hi4 := CubicCentralizerCount.centralizer_cubic_index_le_square Q hz hx hinv 1
    (by simpa using hi)
  have hfix : c.fixedSubgroup.index = (centralizer (zpowers x : Set G)).relIndex Q := by
    rw [fixed_conjNormal]
    congr 1
    rw [zpowers_eq_closure, centralizer_closure]
  have hbound : Nat.card (commutatorAction (zpowers c) Q) ≤ 4 := by
    rw [hcard, hfix]
    simpa using hi4
  have hnormal : zpowers x ≤ normalizer (Q : Set G) := le_normalizer_of_normal
  have htransfer := commutatorAction_subgroup_conj_map_eq_commutator Q (zpowers x) hnormal
  rw [← htransfer, card_map_of_injective Q.subtype_injective]
  have hsame : commutatorAction (zpowers x) Q = commutatorAction (zpowers c) Q := by
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    congr 1
    ext q
    constructor
    · rintro ⟨r,u,rfl⟩
      refine ⟨⟨MulAut.conjNormal (r : G), ?_⟩,u,rfl⟩
      obtain ⟨n,hn⟩ := r.property
      rw [← hn, map_zpow]
      exact zpow_mem (mem_zpowers c) n
    · rintro ⟨r,u,rfl⟩
      obtain ⟨n,hn⟩ := r.property
      refine ⟨⟨x ^ n, zpow_mem (mem_zpowers x) n⟩,u,?_⟩
      change u⁻¹ * (r : MulAut Q) u = u⁻¹ * (MulAut.conjNormal (x ^ n) u)
      rw [map_zpow]
      exact congrArg (fun f : MulAut Q => u⁻¹ * f u) hn.symm
  rw [hsame]
  exact hbound

public theorem exists_cubic_small_commutator
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) {z : G}
    (hz : orderOf z = 2) (hn : z ∉ pCore 2 G)
    (hi : (centralizer ({z} : Set G)).relIndex (pCore 2 G) ≤ 2) :
    ∃ x : G, orderOf x = 3 ∧ Nat.card (⁅pCore 2 G,zpowers x⁆ : Subgroup G) ≤ 4 := by
  obtain ⟨x,hx,hinv⟩ := CubicCentralizerCount.exists_inverted_cubic e hz hn
  refine ⟨x,hx,cubic_commutator_card_le_four (pCore 2 G) ?_ ?_ hinv hi⟩
  · rw [← hz]; exact pow_orderOf_eq_one z
  · rw [← hx]; exact pow_orderOf_eq_one x
end Theory.GroupTheory.SmallInvolutionResidual
