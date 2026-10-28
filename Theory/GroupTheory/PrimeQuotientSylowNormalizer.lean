module

public import Theory.GroupTheory.CyclicNormalCentralizer
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow joins over a prime-order self-centralizing quotient subgroup

A normal self-centralizing subgroup F of prime order lies in every
nontrivial normal subgroup N. Indeed, if N meets F trivially, normality
makes N centralize F, forcing N into F and hence making N trivial.
The abelian automorphism group of the cyclic group F also forces the
derived group into F. Consequently every overgroup of N is normal.

Apply this in a quotient by a normal p-subgroup Q. A normal subgroup N
not contained in Q has nontrivial image, so the image of NS is normal
for every Sylow p-subgroup S. Since Q lies in S, normality lifts to NS.
The self-centralization input is explicit, allowing the generalized-Fitting
application to use the existing self-centralization theorem above Theory.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
E.4.2, printed p.241 (PDF p.252), prime-order local quotient branch.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A self-centralizing normal subgroup of prime order lies in every nontrivial normal subgroup. -/
theorem prime_order_selfCentralizing_le_normal
    (F : Subgroup G) [F.Normal] (hp : (Nat.card F).Prime)
    (hc : centralizer (F : Set G) ≤ F)
    (N : Subgroup G) [N.Normal] (hn : N ≠ ⊥) : F ≤ N := by
  let : Fact (Nat.card F).Prime := ⟨hp⟩
  rcases (N.subgroupOf F).eq_bot_or_eq_top_of_prime_card with hb | ht
  · have hi : N ⊓ F = ⊥ := by
      have he := congrArg (Subgroup.map F.subtype) hb
      simpa only [subgroupOf_map_subtype, Subgroup.map_bot] using he
    have hcomm : ⁅N, F⁆ = ⊥ :=
      le_bot_iff.mp ((commutator_le_inf N F).trans hi.le)
    have hNF : N ≤ F := (commutator_eq_bot_iff_le_centralizer.mp hcomm).trans hc
    exact (hn (by simpa only [inf_of_le_left hNF] using hi)).elim
  · have he := congrArg (Subgroup.map F.subtype) ht
    have hi : N ⊓ F = F := by
      simpa only [subgroupOf_map_subtype, ← MonoidHom.range_eq_map, F.range_subtype] using he
    exact hi ▸ (inf_le_left : N ⊓ F ≤ N)

/-- Every overgroup of a nontrivial normal subgroup is normal in the presence
of a self-centralizing normal subgroup of prime order. -/
theorem normal_of_nontrivial_normal_le_of_prime_order_selfCentralizing
    (F : Subgroup G) [F.Normal] (hp : (Nat.card F).Prime)
    (hc : centralizer (F : Set G) ≤ F)
    (N : Subgroup G) [N.Normal] (hn : N ≠ ⊥)
    (M : Subgroup G) (hNM : N ≤ M) : M.Normal := by
  let : Fact (Nat.card F).Prime := ⟨hp⟩
  let : IsCyclic F := isCyclic_of_prime_card (p := Nat.card F) rfl
  have hder : _root_.commutator G ≤ N :=
    (commutator_le_centralizer_of_isCyclic_normal F).trans
      (hc.trans (prime_order_selfCentralizing_le_normal F hp hc N hn))
  apply commutator_top_left_le_iff.mp
  exact (commutator_mono le_rfl le_top).trans (hder.trans hNM)

/-- A prime-order self-centralizing normal subgroup of G/Q makes NS normal
whenever Q is a normal p-subgroup, N is normal outside Q, and S is Sylow. -/
theorem normal_sup_sylow_of_prime_order_selfCentralizing_quotient
    {p : ℕ} (Q : Subgroup G) [Q.Normal] (hQ : IsPGroup p Q)
    (F : Subgroup (G ⧸ Q)) [F.Normal] (hp : (Nat.card F).Prime)
    (hc : centralizer (F : Set (G ⧸ Q)) ≤ F)
    (N : Subgroup G) [N.Normal] (hn : ¬ N ≤ Q) (S : Sylow p G) :
    (N ⊔ (S : Subgroup G)).Normal := by
  let q := QuotientGroup.mk' Q
  let Nb := N.map q
  have : Nb.Normal := (inferInstance : N.Normal).map q (QuotientGroup.mk'_surjective Q)
  have hNb : Nb ≠ ⊥ := by
    intro hb
    apply hn
    have hh := (map_eq_bot_iff N).mp hb
    simpa only [q, QuotientGroup.ker_mk'] using hh
  have hnM : ((N ⊔ (S : Subgroup G)).map q).Normal :=
    normal_of_nontrivial_normal_le_of_prime_order_selfCentralizing F hp hc Nb hNb
      _ (map_mono le_sup_left)
  have hback : (((N ⊔ (S : Subgroup G)).map q).comap q).Normal := inferInstance
  have hQS : Q ≤ (S : Subgroup G) := hQ.le_sylow_of_normal S
  simpa only [q, QuotientGroup.comap_map_mk', sup_of_le_right (hQS.trans le_sup_right)] using hback

end Theory.GroupTheory
