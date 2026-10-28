module

public import Theory.GroupTheory.PiCore
public import Theory.GroupTheory.PResidual.Defs

/-!
# Residuals for a set of primes

The π-residual is the intersection of the normal subgroups with π-group
quotient. In particular, the {2,3}-residual means this intersection, rather
than an iteration of the single-prime residuals. Pulling a quotient back
along a homomorphism proves functoriality and preservation of π-perfectness.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.1.26.
-/

@[expose] public section

/-- The residual for quotients whose prime divisors belong to π. -/
def piResidual (π : Set Nat.Primes) (G : Type*) [Group G] : Subgroup G :=
  sInf {N : Subgroup G | ∃ hN : N.Normal, @IsPiGroup π (G ⧸ N)
    (@QuotientGroup.Quotient.group G _ N hN)}

/-- A group with no nontrivial π-group quotient. -/
def IsPiPerfect (π : Set Nat.Primes) (G : Type*) [Group G] : Prop :=
  ∀ (N : Subgroup G) (hN : N.Normal), @IsPiGroup π (G ⧸ N)
    (@QuotientGroup.Quotient.group G _ N hN) → N = ⊤

theorem piResidual_eq_top_iff (π : Set Nat.Primes) (G : Type*) [Group G] :
    piResidual π G = ⊤ ↔ IsPiPerfect π G := by
  constructor
  · intro h N hN hp
    apply top_unique
    rw [← h]
    exact sInf_le ⟨hN, hp⟩
  · intro h
    apply top_unique
    apply le_sInf
    rintro N ⟨hN, hp⟩
    rw [h N hN hp]

theorem Subgroup.map_piResidual_le {G H : Type*} [Group G] [Finite G]
    [Group H] [Finite H] (π : Set Nat.Primes) (f : G →* H) :
    (piResidual π G).map f ≤ piResidual π H := by
  apply le_sInf
  rintro N ⟨hN, hp⟩
  let := hN
  let q := (QuotientGroup.mk' N).comp f
  have hk : IsPiGroup π (G ⧸ q.ker) :=
    IsPiGroup.of_injective hp (QuotientGroup.kerLift q) (QuotientGroup.kerLift_injective q)
  have hr : piResidual π G ≤ q.ker := sInf_le ⟨inferInstance, hk⟩
  rintro y ⟨x, hx, rfl⟩
  exact (QuotientGroup.eq_one_iff (f x)).mp (hr hx)

theorem IsPiPerfect.of_surjective {π : Set Nat.Primes} {G H : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    (h : IsPiPerfect π G) (f : G →* H) (hf : Function.Surjective f) :
    IsPiPerfect π H := by
  apply (piResidual_eq_top_iff π H).mp
  apply top_unique
  have hr := Subgroup.map_piResidual_le π f
  rw [(piResidual_eq_top_iff π G).mpr h, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr hf] at hr
  exact hr

/-- The primes allowed in the quotient in the superscript O^{2,3}. -/
def twoThreePrimes : Set Nat.Primes := {q | q.val = 2 ∨ q.val = 3}

end
