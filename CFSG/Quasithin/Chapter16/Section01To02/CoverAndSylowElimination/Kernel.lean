module
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.Basic
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.ElementaryAbelian.Quotient

/-!
# The two centralizer counting arguments

An elementary abelian group of order greater than eight cannot embed in
an automorphism group of two-rank at most three. For a centerless component,
a two-group acting by inner automorphisms has image of order at most that
of a Sylow two-subgroup. Both statements concern the genuine conjugation
homomorphism, so their kernels give ambient centralizer subgroups.

Source: Aschbacher–Smith, proofs of 16.2.11–16.2.12, printed p.1176.
-/

open Subgroup
@[expose] public section

namespace CFSG.Quasithin.Chapter16.CoverAndSylowElimination

variable {G : Type*} [Group G]

/-- The actual normalizer action restricted to the actor subgroup. -/
def actorHom (V L : Subgroup G) (hVN : V ≤ normalizer (L : Set G)) : V →* MulAut L :=
  L.normalizerMonoidHom.comp (inclusion hVN)

/-- The action kernel consists exactly of elements centralizing the component. -/
theorem actorHom_eq_one_iff (V L : Subgroup G) (hVN : V ≤ normalizer (L : Set G))
    (v : V) : actorHom V L hVN v = 1 ↔ (v : G) ∈ centralizer (L : Set G) := by
  change inclusion hVN v ∈ L.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

/-- Trivial ambient centralizer makes this action faithful. -/
theorem actorHom_injective (V L : Subgroup G) (hVN : V ≤ normalizer (L : Set G))
    (hC : V ⊓ centralizer (L : Set G) = ⊥) : Function.Injective (actorHom V L hVN) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro v hv
  apply mem_bot.mpr
  apply Subtype.ext
  have : (v : G) ∈ V ⊓ centralizer (L : Set G) :=
    ⟨v.property, (actorHom_eq_one_iff V L hVN v).mp hv⟩
  simpa only [hC, mem_bot, Subgroup.coe_one] using this

/-- The rank comparison in 16.2.11, with the actual automorphism group.
The Suzuki model computation supplying `hrank` is a separate obligation. -/
theorem elementary_centralizer_ne_bot [Finite G] (V L : Subgroup G) (hVN : V ≤ normalizer (L : Set G))
    (hV : IsElementaryAbelian 2 V) (hrank : primeRank 2 (MulAut L) ≤ 3)
    (hlarge : 8 < Nat.card V) : V ⊓ centralizer (L : Set G) ≠ ⊥ := by
  intro hC
  let f := actorHom V L hVN
  have hf : Function.Injective f := actorHom_injective V L hVN hC
  let : IsElementaryAbelian 2 V := hV
  have he : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hbound := (primeRank_le_iff_elementary_card_le (p := 2) (n := 3) (MulAut L)).mp hrank _ he
  have hcard : Nat.card V = Nat.card f.range := Nat.card_congr (MonoidHom.ofInjective hf).toEquiv
  omega

/-- The strict order comparison in 16.2.12 forces a nontrivial kernel.
The inner-action premise must come from 16.1.6, including its exceptions. -/
theorem inner_centralizer_ne_bot [Finite G] (V L : Subgroup G) (hVN : V ≤ normalizer (L : Set G))
    (hV : IsPGroup 2 V) (hcenter : center L = ⊥) (S : Sylow 2 L)
    (hinner : ∀ v : V, ∃ l : L, actorHom V L hVN v = MulAut.conj l)
    (hlarge : Nat.card S < Nat.card V) : V ⊓ centralizer (L : Set G) ≠ ⊥ := by
  intro hC
  let f := actorHom V L hVN
  have hf : Function.Injective f := actorHom_injective V L hVN hC
  let e : L ≃* (MulAut.conj : L →* MulAut L).range :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hcenter)
  let f' : V →* L := e.symm.toMonoidHom.comp
    (f.codRestrict (MulAut.conj : L →* MulAut L).range fun v => by
      obtain ⟨l, hl⟩ := hinner v
      exact ⟨l, hl.symm⟩)
  have hf' : Function.Injective f' := by
    intro a b hab
    apply hf
    have heq := congrArg e hab
    simpa [f', f] using congrArg Subtype.val heq
  obtain ⟨P, hP⟩ := (hV.of_surjective f'.rangeRestrict f'.rangeRestrict_surjective).exists_le_sylow
  have hb := Nat.card_le_card_of_injective (inclusion hP) (inclusion_injective hP)
  have heq : Nat.card f'.range = Nat.card V :=
    (Nat.card_congr (MonoidHom.ofInjective hf').toEquiv).symm
  have hSP : Nat.card P = Nat.card S := Nat.card_congr (P.equiv S).toEquiv
  omega

end CFSG.Quasithin.Chapter16.CoverAndSylowElimination
