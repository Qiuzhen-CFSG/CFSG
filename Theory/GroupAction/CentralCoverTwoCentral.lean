module

public import Theory.GroupAction.SylowFixedCentralQuotient
public import Theory.GroupTheory.DoubleCoverCentralizer.TwoCentralSylow
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Two-central inner actions through a marked central cover

An involutory inner automorphism of a perfect group induces conjugation by
an involution in any centerless central quotient. Central displacement
ensures the quotient action is nontrivial. If the original automorphism
fixes a Sylow two-subgroup, its image is Sylow and centralizes that
involution; maximality puts the involution in the Sylow subgroup's center.

The fixed-subgroup map also excludes an odd prime upstairs whenever the
kernel is a two-group and that prime is absent downstairs. This direction
needs no fixed-point lifting assumption.

Source: Aschbacher–Smith, 1.1.5(3), printed pp.502–503; these are the
marked-quotient transports used in the Mathieu cases of 14.7.68(2).
-/

public section
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
namespace MulAut
variable {G H : Type*} [Group G] [Group H] [Finite G] [Group.IsPerfect G]

/-- The actual cover transports the given action to a two-central model involution. -/
theorem exists_twoCentral_model_of_central_cover
    (f : G →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (hz : center H = ⊥) (a : MulAut G)
    (hi : a ∈ (MulAut.conj (G := G)).range) (ho : orderOf a = 2)
    (P : Sylow 2 G) (hP : ∀ x ∈ P, a x = x) :
    ∃ t : H, orderOf t = 2 ∧ TwoCentral t ∧
      ∀ x, f (a x) = (MulAut.conj t) (f x) := by
  obtain ⟨g, hg⟩ := hi
  let t := f g
  have heq (x : G) : f (a x) = (MulAut.conj t) (f x) := by
    rw [← hg]
    simp only [MulAut.conj_apply, map_mul, map_inv, t]
  have ha : a ^ 2 = 1 := (orderOf_eq_prime_iff.mp ho).1
  have hb : (MulAut.conj t) ^ 2 = 1 := by
    ext y
    obtain ⟨x, rfl⟩ := hf y
    change (MulAut.conj t) ((MulAut.conj t) (f x)) = f x
    rw [← heq, ← heq]
    exact congrArg f (show a (a x) = x from DFunLike.congr_fun ha x)
  have hbn : MulAut.conj t ≠ 1 := by
    intro h
    have ha1 : a = 1 := eq_one_of_central_displacement a (fun x => hc (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, heq, h, one_apply, inv_mul_cancel]))
    rw [ha1, orderOf_one] at ho
    omega
  have ht : orderOf t = 2 := by
    rw [← orderOf_injective MulAut.conj (conj_injective_of_center_eq_bot hz)]
    exact orderOf_eq_prime_iff.mpr ⟨hb, hbn⟩
  let Q := P.mapSurjective hf
  have hQc : (Q : Subgroup H) ≤ centralizer ({t} : Set H) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← fixedSubgroup_conj, mem_fixedSubgroup, ← heq, hP x hx]
  have htC : t ∈ centralizer (Q : Set H) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hQc hx)
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, ht, pow_one])
  have hn : zpowers t ≤ normalizer (Q : Set H) :=
    (zpowers_le.mpr htC).trans (Subgroup.centralizer_le_normalizer _)
  have hs : (Q : Subgroup H) ⊔ zpowers t = Q :=
    Q.is_maximal' (Q.isPGroup'.to_sup_of_normal_left' hp hn) le_sup_left
  have htQ : t ∈ Q := (sup_eq_left.mp hs) (mem_zpowers t)
  refine ⟨t, ht, ⟨Q, htQ, ?_⟩, heq⟩
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (hQc x.property))

omit [Group.IsPerfect G] in
/-- A two-group kernel cannot introduce an odd prime into a fixed subgroup. -/
theorem odd_prime_not_dvd_card_fixedSubgroup_of_cover
    (a : MulAut G) (b : MulAut H) (f : G →* H)
    (heq : ∀ x, f (a x) = b (f x)) (hp : IsPGroup 2 f.ker)
    {p : ℕ} (hprime : p.Prime) (hne : p ≠ 2)
    (hb : ¬ p ∣ Nat.card b.fixedSubgroup) : ¬ p ∣ Nat.card a.fixedSubgroup := by
  let k := fixedSubgroupMap a b f heq
  let j : k.ker →* f.ker := {
    toFun x := ⟨x.val.val, congrArg Subtype.val x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : G)) h
  have hk : IsPGroup 2 k.ker := hp.of_injective j hj
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hkn : ¬ p ∣ Nat.card k.ker := by
    rw [hn]
    intro hd
    exact hne ((Nat.dvd_prime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hd) |>.resolve_left
      (Nat.Prime.ne_one hprime))
  rw [← k.ker.card_mul_index, index_ker]
  intro hd
  rcases hprime.dvd_mul.mp hd with hd | hd
  · exact hkn hd
  · exact hb (hd.trans k.range.card_subgroup_dvd_card)

end MulAut
