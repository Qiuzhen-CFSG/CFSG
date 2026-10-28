module
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceNormality
public import Theory.SpecificGroups.Held.CentralCovers.OddCenter

/-!
# The full Held component in the covering configuration

The original C.2.8 configuration has trivial odd core. Hence an ordinary
quasisimple component has center equal to its two-core. For a Held quotient,
the native central-cover theorem makes this center odd, so it is trivial.
The resulting full-component equivalence agrees with the given Held marking
on the original central-quotient projection.

Source: Aschbacher--Smith C.3.3--5 and I.1.3, printed pp.149--150,407;
used in the covering argument for 4.4.6--7 and 10.2.3(2).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}

/-- The full Held cover in the actual C.2.8 configuration is centerless:
its center is both a two-group and odd. -/
theorem ordinary_held_center_eq_bot
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Held.He) : center K = ⊥ := by
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have ho : Odd (Nat.card (center K)) := Held.CentralCovers.odd_center ⟨e⟩
  have hp : IsPGroup 2 (center K) := hz.symm ▸ pCore_isPGroup
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hn0 : n = 0 := by
    by_contra hh
    exact ho.not_two_dvd_nat (hn ▸ dvd_pow_self 2 hh)
  exact eq_bot_of_card_eq _ (by simpa only [hn0,pow_zero] using hn)

/-- The Held marking lifts through the original central-quotient map;
no center is silently dropped. -/
theorem ordinary_held_equiv
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Held.He) :
    ∃ a : K ≃* Held.He, ∀ k : K, a k = e (QuotientGroup.mk' (center K) k) := by
  let q := QuotientGroup.mk' (center K)
  have hq : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rw [QuotientGroup.ker_mk']
    exact h.ordinary_held_center_eq_bot K hK e
  exact ⟨(MulEquiv.ofBijective q ⟨hq,QuotientGroup.mk'_surjective _⟩).trans e,fun _ => rfl⟩
end CFSG.Quasithin.ChapterC.HypothesisC28
