module

public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms

/-!
# Full normalizer actions in a subgroup with full quotient image

Let a finite group map to a quotient with kernel of order prime to `p`.
Suppose a subgroup `M` maps onto that quotient and contains a `p`-subgroup
`A` on which the quotient map is injective. Every automorphism of `A`
realized in the whole group is then realized in `M`.

The coprime normalizer lifting theorem supplies a normalizing lift in `M`;
injectivity on `A` identifies its action with the prescribed action.
This is the Frattini argument for coprime quotient normalizers, applied to
the restriction of the quotient map to `M`.
-/

open Subgroup

namespace Subgroup

/-- Full quotient image suffices to retain the full automizer of a coprime
subgroup on which the quotient map is injective. -/
public theorem normalizer_action_surjective_in_subgroup
    {G H : Type*} [Group G] [Finite G] [Group H]
    (p : ℕ) [Fact p.Prime] (A M : Subgroup G) [Fact (IsPGroup p A)]
    (hAM : A ≤ M) (f : G →* H)
    (hM : Function.Surjective (f.comp M.subtype))
    (hcop : Nat.Coprime p (Nat.card f.ker))
    (hi : Function.Injective (f.subgroupMap A))
    (hfull : Function.Surjective A.normalizerMonoidHom) :
    Function.Surjective (A.normalizerMonoidHom.comp
      (M.subgroupOf (normalizer (A : Set G))).subtype) := by
  let B := A.subgroupOf M
  let g := f.comp M.subtype
  have hBmap : B.map g = A.map f := by
    rw [show g = f.comp M.subtype from rfl, ← map_map,
      map_subgroupOf_eq_of_le hAM]
  let _ : Fact (IsPGroup p B) := ⟨(Fact.out : IsPGroup p A).comap_subtype⟩
  have hcopg : Nat.Coprime p (Nat.card g.ker) := by
    have hd : Nat.card g.ker ∣ Nat.card f.ker := by
      have hh := card_dvd_of_le (show g.ker.map M.subtype ≤ f.ker from by
        rintro _ ⟨x, hx, rfl⟩
        exact hx)
      rwa [card_map_of_injective M.subtype_injective] at hh
    exact Nat.Coprime.of_dvd_right hd hcop
  intro α
  obtain ⟨b, hb⟩ := hfull α
  have hbN : f (b : G) ∈ normalizer (B.map g : Set H) := by
    rw [hBmap]
    exact Subgroup.le_normalizer_map f (mem_map_of_mem f b.property)
  rw [normalizer_map_eq_of_coprime_kernel p B g hM hcopg] at hbN
  obtain ⟨n, hn, hnb⟩ := hbN
  have hnG : (n : G) ∈ normalizer (A : Set G) := by
    have hh := hn
    rw [← subgroupOf_normalizer_eq hAM] at hh
    exact hh
  refine ⟨⟨⟨n, hnG⟩, n.property⟩, ?_⟩
  apply MulEquiv.ext
  intro a
  apply hi
  apply Subtype.ext
  change f ((n : G) * (a : G) * (n : G)⁻¹) = f (α a)
  have hba : (b : G) * (a : G) * (b : G)⁻¹ = α a :=
    congrArg (fun β : MulAut A => (β a : G)) hb
  rw [← hba, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  change f (n : G) = f (b : G) at hnb
  rw [hnb]

end Subgroup
