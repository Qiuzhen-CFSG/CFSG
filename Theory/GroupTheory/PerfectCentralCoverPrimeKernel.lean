module

public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Comparing central covers with prime-order kernel

Let `U` be the universal perfect central cover of a finite perfect group `G`.
If a prime `p` occurs at most once in the order of its kernel, all perfect
central covers of `G` with kernel of order `p` are isomorphic. Lift `U` onto
each cover. The two lift kernels have order prime to `p`, so each maps
trivially into the other's order-`p` kernel. The lift kernels coincide, and
the first isomorphism theorem gives the comparison.

This is the prime-primary part of the covering comparison used for the
triple Mathieu cover in Aschbacher–Smith H.12, printed pp.393–394; the
universal-cover convention is I.1.1, printed p.407. The arithmetic bound on
the universal kernel remains an explicit input here.
-/

namespace PerfectCentralCovering

private theorem card_ker_mul_card_of_surjective
    {E B : Type*} [Group E] [Group B] (f : E →* B)
    (hf : Function.Surjective f) : Nat.card f.ker * Nat.card B = Nat.card E := by
  have h := f.ker.card_mul_index
  rwa [Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h

private theorem card_ker_factor
    {U L G : Type*} [Group U] [Group L] [Group G] [Finite G]
    (u : U →* G) (f : L →* G) (a : U →* L)
    (hu : Function.Surjective u) (hf : Function.Surjective f)
    (ha : Function.Surjective a) :
    Nat.card a.ker * Nat.card f.ker = Nat.card u.ker := by
  apply Nat.mul_right_cancel (Nat.card_pos (α := G))
  rw [mul_assoc, card_ker_mul_card_of_surjective f hf,
    card_ker_mul_card_of_surjective a ha, card_ker_mul_card_of_surjective u hu]

private theorem ker_le_of_prime_kernel
    {U L M G : Type*} [Group U] [Group L] [Group M] [Group G]
    [Finite U] [Finite G]
    (u : U →* G) (f : L →* G) (g : M →* G) (a : U →* L) (b : U →* M)
    (hu : Function.Surjective u) (hf : Function.Surjective f)
    (ha : Function.Surjective a) (hfa : f.comp a = u) (hgb : g.comp b = u)
    {p : ℕ} (hp : p.Prime) (hup : ¬ p ^ 2 ∣ Nat.card u.ker)
    (hfp : Nat.card f.ker = p) (hgp : Nat.card g.ker = p) : a.ker ≤ b.ker := by
  have hc : Nat.card a.ker * p = Nat.card u.ker := by
    rw [← hfp]
    exact card_ker_factor u f a hu hf ha
  have hcop : p.Coprime (Nat.card a.ker) := hp.coprime_iff_not_dvd.mpr (by
    intro h
    apply hup
    rw [← hc, pow_two]
    exact Nat.mul_dvd_mul h dvd_rfl)
  intro x hx
  have hbx : b x ∈ g.ker := by
    change g (b x) = 1
    calc
      g (b x) = u x := DFunLike.congr_fun hgb x
      _ = f (a x) := (DFunLike.congr_fun hfa x).symm
      _ = 1 := by rw [MonoidHom.mem_ker.mp hx, map_one]
  have hdvp : orderOf (b x) ∣ p := by
    rw [← hgp, Subgroup.orderOf_coe (⟨b x, hbx⟩ : g.ker)]
    exact orderOf_dvd_natCard _
  have hxpow : x ^ Nat.card a.ker = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : a.ker)))
  have hdva : orderOf (b x) ∣ Nat.card a.ker :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxpow, map_one])
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvp hdva)

/-- Prime-degree central covers are isomorphic if the prime occurs at most once
in the kernel of their universal cover. -/
public theorem Cover.nonempty_mulEquiv_of_prime_kernel
    {G L M : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    [Group L] [Group M]
    (f : Cover L G) (g : Cover M G)
    {p : ℕ} (hp : p.Prime)
    (hup : ¬ p ^ 2 ∣ Nat.card (universalProjection G).ker)
    (hfp : Nat.card f.toMonoidHom.ker = p)
    (hgp : Nat.card g.toMonoidHom.ker = p) : Nonempty (L ≃* M) := by
  let := f.isPerfect
  let := g.isPerfect
  obtain ⟨a, ha, _⟩ := universalProjection_existsUnique_lift
    f.toMonoidHom f.surjective f.ker_le_center
  obtain ⟨b, hb, _⟩ := universalProjection_existsUnique_lift
    g.toMonoidHom g.surjective g.ker_le_center
  have has : Function.Surjective a :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      f.toMonoidHom a (ha ▸ universalProjection_surjective G) f.ker_le_center
  have hbs : Function.Surjective b :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      g.toMonoidHom b (hb ▸ universalProjection_surjective G) g.ker_le_center
  have heq : a.ker = b.ker := le_antisymm
    (ker_le_of_prime_kernel (universalProjection G) f.toMonoidHom g.toMonoidHom a b
      (universalProjection_surjective G) f.surjective has ha hb hp hup hfp hgp)
    (ker_le_of_prime_kernel (universalProjection G) g.toMonoidHom f.toMonoidHom b a
      (universalProjection_surjective G) g.surjective hbs hb ha hp hup hgp hfp)
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective a has).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq heq).trans
      (QuotientGroup.quotientKerEquivOfSurjective b hbs))⟩

end PerfectCentralCovering
