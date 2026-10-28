module

public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Lifting arbitrary prime subgroups through coprime kernels

For a finite surjection with kernel order prime to p, take a Sylow p-subgroup
of the inverse image of the requested p-subgroup. Its image is the whole
p-subgroup, and coprimality makes the restriction injective. Thus the lift is
isomorphic to the literal subgroup in the codomain. No abelianness or centrality
is needed.

This extends the elementary-abelian lifting API in `CoprimeQuotientSubgroups`.
The extraspecial degree argument in Aschbacher–Smith G.7.1(2), used for K.4,
needs the nonabelian case.
-/

public section
namespace Subgroup
/-- Prime subgroups lift isomorphically through coprime kernels. -/
theorem exists_prime_subgroup_equiv_of_surjective_coprime
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hker : Nat.Coprime p (Nat.card f.ker))
    (D : Subgroup H) (hD : IsPGroup p D) :
    ∃ A : Subgroup G, A.map f = D ∧ Nonempty (A ≃* D) := by
  let K := D.comap f
  let q : K →* D := f.subgroupComap D
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective D hf
  let S : Sylow p K := Sylow.nonempty.some
  have hStop : (S.mapSurjective hq : Subgroup D) = ⊤ := by
    apply top_unique
    exact (hD.to_subgroup ⊤).le_sylow_of_normal _
  let A := (S : Subgroup K).map K.subtype
  have hA : IsPGroup p A := S.isPGroup'.map K.subtype
  have hmap : A.map f = D := by
    have hh := congrArg (Subgroup.map D.subtype) hStop
    change ((S : Subgroup K).map q).map D.subtype = (⊤ : Subgroup D).map D.subtype at hh
    rw [map_map, ← MonoidHom.range_eq_map, range_subtype] at hh
    change (S : Subgroup K).map (f.comp K.subtype) = D at hh
    simpa only [A, map_map] using hh
  let e : A ≃* D := (MulEquiv.ofBijective (f.subgroupMap A) ⟨by
    intro x y h
    exact injective_comp_subtype_of_coprime_ker f hker A hA
      (congrArg Subtype.val h), f.subgroupMap_surjective A⟩).trans
        (MulEquiv.subgroupCongr hmap)
  exact ⟨A, hmap, ⟨e⟩⟩
end Subgroup
