module

public import Theory.Representation.BinaryOffender.CubicFixedSpaceSaturation
public import Theory.Representation.Quotient

/-!
# Saturated actors and maximal involution centralizers

Suppose the moved dimension of every nonidentity element of an elementary
actor attains its whole rank bound. Their fixed spaces then coincide. Each
involution centralizer preserves this space. Irreducibility makes its
stabilizer proper, so maximality forces all these centralizers to coincide.
The whole actor lies in their double centralizer; if that has order at most
two, this contradicts the actor's saturated rank greater than one.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
Rudvalis paragraph on manuscript p.17. The numerical and local group
hypotheses are explicit; this lemma performs no model classification.
-/

public section
namespace Representation.BinaryOffender
open Subgroup Representation

/-- Maximal centralizers with small double centralizers forbid a saturated actor. -/
theorem not_small_actor_of_maximal_centralizers {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hi : ρ.IsIrreducible)
    {A : Subgroup G} (hA : IsElementaryTwo A)
    {n r : ℕ} (hn : 0 < n) (hr : 1 < r) (hrank : rank A ≤ r)
    (hdim : n * r < Module.finrank (ZMod 2) V)
    (hlarge : ∀ t ∈ A, t ≠ 1 → n * r ≤ fixedCodim ρ (zpowers t))
    (hlocal : ∀ t ∈ A, t ≠ 1 → fixedCodim ρ (zpowers t) ≤ n * r →
      IsCoatom (centralizer ({t} : Set G)) ∧
        Nat.card (centralizer (centralizer ({t} : Set G) : Set G)) ≤ 2) :
    ¬ fixedCodim ρ A ≤ n * rank A := by
  intro hsmall
  obtain ⟨t, ht, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hs (u : G) (hu : u ∈ A) (hu1 : u ≠ 1) :=
    fixedSpace_eq_of_saturated_actor ρ hu hrank hsmall (hlarge u hu hu1)
  have hcodim : fixedCodim ρ A = n * r := (hs t ht ht1).1
  have heq (u : G) (hu : u ∈ A) (hu1 : u ≠ 1) :
      fixedSpace ρ A = fixedSpace ρ (zpowers u) := (hs u hu hu1).2
  have hucodim (u : G) (hu : u ∈ A) (hu1 : u ≠ 1) :
      fixedCodim ρ (zpowers u) = n * r := by
    have h := congrArg (fun W : Submodule (ZMod 2) V => Module.finrank (ZMod 2) W)
      (heq u hu hu1)
    have h1 := fixedCodim_add_finrank ρ A
    have h2 := fixedCodim_add_finrank ρ (zpowers u)
    omega
  let H := subspaceStabilizer ρ (fixedSpace ρ A)
  have hH : H ≠ ⊤ := by
    intro htop
    let W : Subrepresentation ρ := ⟨fixedSpace ρ A, fun g _ hv =>
      (show g ∈ H from htop ▸ mem_top g) _ |>.2 hv⟩
    rcases hi.eq_bot_or_eq_top W with hb | ht
    · have he : fixedSpace ρ A = ⊥ := congrArg Subrepresentation.toSubmodule hb
      have h := fixedCodim_add_finrank ρ A
      rw [he, finrank_bot] at h
      omega
    · have he : fixedSpace ρ A = ⊤ := congrArg Subrepresentation.toSubmodule ht
      have h := fixedCodim_add_finrank ρ A
      rw [he, finrank_top] at h
      have hp : 0 < n * r := Nat.mul_pos hn (by omega)
      omega
  have hcentral (u : G) (hu : u ∈ A) (hu1 : u ≠ 1) :
      centralizer ({u} : Set G) = H := by
    have hle : centralizer ({u} : Set G) ≤ H := by
      apply le_subspaceStabilizer
      intro g hg v hv
      rw [heq u hu hu1] at hv ⊢
      rw [mem_fixedSpace_zpowers_iff] at hv ⊢
      have hg' := mem_centralizer_singleton_iff.mp hg
      rw [← Module.End.mul_apply, ← map_mul, ← hg', map_mul,
        Module.End.mul_apply, hv]
    exact ((hlocal u hu hu1 (hucodim u hu hu1).le).1.le_iff_eq hH).mp hle |>.symm
  have hle : A ≤ centralizer (centralizer ({t} : Set G) : Set G) := by
    intro u hu
    by_cases hu1 : u = 1
    · simpa only [hu1] using (centralizer (centralizer ({t} : Set G) : Set G)).one_mem
    apply mem_centralizer_iff.mpr
    intro g hg
    have hgu : g ∈ centralizer ({u} : Set G) := by
      rwa [hcentral u hu hu1, ← hcentral t ht ht1]
    exact mem_centralizer_singleton_iff.mp hgu
  have hc : Nat.card A ≤ 2 :=
    (Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)).trans (hlocal t ht ht1 (hucodim t ht ht1).le).2
  have hlog := Nat.log_mono_right (b := 2) hc
  have ha1 : rank A ≤ 1 := hlog.trans_eq (by decide)
  have hm : n * rank A ≤ n := by simpa using Nat.mul_le_mul_left n ha1
  have hnlt : n < n * r := by simpa using Nat.mul_lt_mul_of_pos_left hr hn
  omega

end Representation.BinaryOffender
