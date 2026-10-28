module

public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.Mathieu.M24.ChapterHStabilizers.PairInvolutions
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.PointStabilizer
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Representatives
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.CyclicFusion

/-!
# Seven-elements and fixed groups in the M₂₄ pair realization

Sylow conjugacy transports the literal order-seven representative table to
every seven-element of M₂₄. Its three fixed points prohibit a commuting
fixed-point-free involution. The faithful pair realization also identifies
an outer M₂₂ fixed group with the actual point stabilizer in its M₂₄
centralizer. Both facts keep the marked permutations and inclusions.

Source: the Mathieu involution centralizers in GLS3 Table 5.3g; the
PSL₃(2)-component exclusions used in Aschbacher–Smith 15.3.38, p.1137.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu
open M24ChapterHStabilizers M24InvolutionCentralizers

private noncomputable def markedSeven : M24 := M24OddCyclic.representative 1 ^ 3

private theorem markedSeven_order : orderOf markedSeven = 7 := by
  rw [markedSeven, orderOf_pow_of_dvd (by decide : 3 ≠ 0)
    (by rw [M24OddCyclic.representative_order]; decide), M24OddCyclic.representative_order]
  rfl

private theorem markedSeven_fixed_card : ∀ k : Fin 7, k ≠ 0 →
    (fixedPoints (markedSeven ^ k.val)).card = 3 := by
  have h : ∀ k : Fin 7, k ≠ 0 →
      (Finset.univ.filter (fun x : Fin 24 =>
        (((M24OddCyclic.representativePerm 1) ^ 3) ^ k.val) x = x)).card = 3 := by
    decide +kernel
  exact h

/-- Sylow conjugacy and the literal seven-cycle table retain the three fixed points. -/
theorem m24_seven_fixed_card (x : M24) (hx : orderOf x = 7) :
    (fixedPoints x).card = 3 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨n, hn⟩ := IsConj.of_order_eq_prime_power_generator markedSeven_order hx
    (by rw [m24_order]; decide)
  let k : Fin 7 := ⟨n % 7, Nat.mod_lt _ (by decide)⟩
  have hp : markedSeven ^ k.val = markedSeven ^ n := by
    simpa only [markedSeven_order] using pow_mod_orderOf markedSeven n
  have hk : k ≠ 0 := by
    intro he
    have ho : orderOf x = orderOf (markedSeven ^ n) := by
      obtain ⟨g, hg⟩ := isConj_iff.mp hn
      rw [← hg]
      exact ((MulAut.conj g).orderOf_eq x).symm
    rw [← hp, he, Fin.val_zero, pow_zero, orderOf_one, hx] at ho
    omega
  exact (fixedPoints_card_eq_of_isConj hn).trans (hp ▸ markedSeven_fixed_card k hk)

private theorem not_fixedPointFree_commuting_seven
    (t x : M24) (ht : t ^ 2 = 1) (hx : orderOf x = 7)
    (hcomm : Commute t x) (hfree : ∀ i : Fin 24, t.val i ≠ i) : False := by
  classical
  let X := Function.fixedPoints x.val
  let f : Function.End X := fun i => ⟨t.val i.val, by
    have hh := congrArg (fun z : M24 => z.val i.val) hcomm.eq
    change t.val (x.val i.val) = x.val (t.val i.val) at hh
    exact hh.symm.trans (congrArg t.val i.property)⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    funext i
    apply Subtype.ext
    exact congrArg (fun z : M24 => z.val i.val) ht
  let : IsEmpty (Function.fixedPoints f) := ⟨fun i =>
    hfree i.val.val (congrArg Subtype.val i.property)⟩
  have hc : Fintype.card X = 3 := by
    have he : Fintype.card X = (fixedPoints x).card :=
      Fintype.card_of_finset' (p := Function.fixedPoints x.val) _
        (fun i => mem_fixedPoints x i)
    exact he.trans (m24_seven_fixed_card x hx)
  have hm := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  rw [hc, Fintype.card_eq_zero] at hm
  norm_num [Nat.ModEq] at hm

/-- The marked fixed-point-free M₂₄ centralizer has no seven-element. -/
theorem m24_twoB_not_seven : ¬ 7 ∣ Nat.card centralizer2B := by
  intro hd
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := centralizer2B) 7 hd
  exact not_fixedPointFree_commuting_seven involution2B x.val
    (involution2B_order ▸ pow_orderOf_eq_one involution2B)
    ((Subgroup.orderOf_coe x).trans hx)
    (mem_centralizer_singleton_iff.mp x.property).symm
    (by decide +kernel)

/-- The pair realization identifies the literal M₂₂ fixed group with the
point stabilizer in the M₂₄ centralizer. -/
noncomputable def m22Pair_fixedEquiv (x : MathieuCode.m22PairStabilizer)
    (hout : x.val ∉ MathieuCode.m22PointwisePairStabilizer) :
    (MathieuCode.m22PairStabilizerEquivAut x).fixedSubgroup ≃*
      MulAction.stabilizer (centralizer ({x.val} : Set M24)) (0 : Fin 24) := by
  let f : (MathieuCode.m22PairStabilizerEquivAut x).fixedSubgroup →*
      MulAction.stabilizer (centralizer ({x.val} : Set M24)) (0 : Fin 24) := {
    toFun := fun g => ⟨⟨MathieuCode.m22Embedding g.val, by
      apply mem_centralizer_singleton_iff.mpr
      have he := MathieuCode.m22PairStabilizerEquivAut_apply x g.val
      rw [(MulAut.mem_fixedSubgroup _ _).mp g.property] at he
      exact eq_mul_inv_iff_mul_eq.mp he⟩,
      MathieuCode.m22Embedding_fixed_zero g.val⟩
    map_one' := Subtype.ext (Subtype.ext (map_one _))
    map_mul' _ _ := Subtype.ext (Subtype.ext (map_mul _ _ _)) }
  apply MulEquiv.ofBijective f
  constructor
  · intro g h he
    exact Subtype.ext (MathieuCode.m22Embedding_injective
      (congrArg (fun a => a.val.val) he))
  · intro g
    have hg0 : g.val.val • (0 : Fin 24) = 0 := g.property
    have hg9 : g.val.val • (9 : Fin 24) = 9 := by
      have hs := (outer_pair_iff_swaps x).mp hout
      have he := congrArg (fun a : M24 => a • (0 : Fin 24))
        (mem_centralizer_singleton_iff.mp g.val.property)
      simpa only [mul_smul, hg0, hs.1] using he
    obtain ⟨k, hk⟩ := (show g.val.val ∈ MathieuCode.m22Embedding.range by
      rw [MathieuCode.m22Embedding_range]
      exact ⟨hg0, hg9⟩)
    refine ⟨⟨k, ?_⟩, Subtype.ext (Subtype.ext hk)⟩
    rw [MulAut.mem_fixedSubgroup]
    apply MathieuCode.m22Embedding_injective
    rw [MathieuCode.m22PairStabilizerEquivAut_apply, hk]
    exact (mul_inv_eq_iff_eq_mul).mpr
      (mem_centralizer_singleton_iff.mp g.val.property).symm

end Sporadic.Mathieu
