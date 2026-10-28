module

public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# Prime-core-free preimages of prime-to-p subgroups

If the domain has trivial p-core, the preimage of a subgroup of order
prime to p also has trivial p-core. Its p-core maps trivially to the
prime-to-p subgroup. It is therefore a normal p-subgroup of the original
kernel, whose p-core is trivial by normal restriction.
-/

public section
namespace Subgroup
variable {A D : Type*} [Group A] [Group D]

/-- Restrict a core-free domain to the literal preimage of a prime-to-p subgroup. -/
theorem pCore_comap_eq_bot_of_coprime (p : ℕ) [Fact p.Prime]
    (f : A →* D) (R : Subgroup D) [Finite R]
    (hA : pCore p A = ⊥) (hR : Nat.Coprime p (Nat.card R)) :
    pCore p (R.comap f) = ⊥ := by
  let H := R.comap f
  let g : H →* R := (f.comp H.subtype).codRestrict R (fun x => x.property)
  let P := pCore p H
  have himage : P.map g = ⊥ := by
    have hd : Nat.card (P.map g) ∣ Nat.card R := (P.map g).card_subgroup_dvd_card
    have hp : IsPGroup p (P.map g) := pCore_isPGroup.map g
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    have hcop : Nat.Coprime (Nat.card (P.map g)) (Nat.card R) := hn ▸ hR.pow_left n
    exact card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hd)
  have hPk : P ≤ f.ker.subgroupOf H := by
    intro x hx
    have hh := himage ▸ mem_map_of_mem g hx
    exact congrArg Subtype.val (mem_bot.mp hh)
  have hkH : f.ker ≤ H := by
    intro x hx
    change f x ∈ R
    rw [show f x=1 from hx]
    exact R.one_mem
  let K := f.ker.subgroupOf H
  have hK : pCore p K=⊥ := by
    let e := subgroupOfEquivOfLe hkH
    have hk : pCore p f.ker=⊥ := by
      rw [pCore_eq_comap_of_normal,hA]
      exact f.ker.subtype.ker_eq_bot f.ker.subtype_injective
    apply (map_eq_bot_iff_of_injective (f:=e.toMonoidHom) _ e.injective).mp
    exact (pCore_map_iso p e).trans hk
  have hrestrict : P.subgroupOf K ≤ pCore p K :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
  apply bot_unique
  intro x hx
  have he : (⟨x,hPk hx⟩ : K)=1 := mem_bot.mp (hK ▸ hrestrict hx)
  exact congrArg Subtype.val he

end Subgroup
