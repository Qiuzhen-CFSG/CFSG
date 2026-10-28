module
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Prime-order generation above a simple quotient

Let Q be a normal q-subgroup of a finite q-perfect group. If G/Q is simple
and its order is divisible by a different prime p, the elements of order p
generate G. Their normal closure has nontrivial image in the simple quotient,
so it supplements Q; q-perfectness removes the remaining q-group quotient.

Source application: the PSL₂(16) factors in Aschbacher--Smith14.6.15,
printed p.1034. The conclusion concerns elements of exact prime order,
as required by the source's operation θ.
-/
public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Exact prime-order elements generate a prime-perfect simple extension. -/
theorem closure_prime_order_eq_top_of_simple_quotient {p q : ℕ} [Fact p.Prime]
    (Q : Subgroup G) [Q.Normal] [IsSimpleGroup (G ⧸ Q)]
    (hQ : IsPGroup q Q) (hp : IsPPerfect q G) (hcop : Nat.Coprime q p)
    (hd : p ∣ Nat.card (G ⧸ Q)) : closure {x : G | orderOf x = p} = ⊤ := by
  let C := closure {x : G | orderOf x = p}
  have hn : (⊤ : Subgroup G) ≤ normalizer (C : Set G) := by
    apply le_normalizer_closure_iff.mpr
    intro g _ x hx
    exact subset_closure ((MulAut.conj g).orderOf_eq x |>.trans hx)
  let : C.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  let f := QuotientGroup.mk' Q
  have hn' : (C.map f).Normal := Normal.map inferInstance f (QuotientGroup.mk'_surjective Q)
  have htop : C.map f = ⊤ := by
    apply hn'.eq_bot_or_eq_top.resolve_left
    intro hb
    have hCQ : C ≤ Q := by simpa only [f,QuotientGroup.ker_mk'] using (map_eq_bot_iff C).mp hb
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' p (hd.trans (card_quotient_dvd_card Q))
    have hxQ : x ∈ Q := hCQ (subset_closure hx)
    have hh := hQ.orderOf_coprime hcop (⟨x,hxQ⟩ : Q)
    have he : orderOf (⟨x,hxQ⟩ : Q) = p := (Subgroup.orderOf_coe _).symm.trans hx
    rw [he,Nat.coprime_self] at hh
    exact (Fact.out : p.Prime).ne_one hh
  have hs : C ⊔ Q = ⊤ := by
    have he := congrArg (fun A : Subgroup (G ⧸ Q) => A.comap f) htop
    simpa only [comap_map_eq,f,QuotientGroup.ker_mk',comap_top] using he
  exact hp C inferInstance (isPGroup_quotient_of_sup_eq_top C Q hQ hs)
end Subgroup
