module

public import Theory.Representation.BinaryOffender.EndFieldTransport
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms

/-!
# The Schur field and the automorphisms of a central quotient

For a faithful action with irreducible restriction to a normal perfect subgroup
N, its centralizer injects into the actual endomorphism field E of that
restriction. Conjugation has kernel C_H(N), and perfectness makes descent
from Aut(N) to Aut(N/Z(N)) injective. Thus |H| ≤ |E| |Aut(N/Z(N))|.

When N is nontrivial, its faithful action over E has degree at least two:
a faithful action in degree at most one would make the perfect group abelian.
Consequently |E|² ≤ |V|. These estimates are the structural part of the
FF cardinality comparison used with Guralnick--Malle,
*Classification of 2F-modules, I*, Section 2 and Proposition 4.6.
The central quotient is literal, and no generalized-Fitting theorem is used.
-/

public section
open Representation Representation.BinaryOffender Subgroup
open scoped MonoidAlgebra
set_option backward.isDefEq.respectTransparency false

namespace Representation.BinaryOffender.QuasisimpleCardBound

private theorem two_le_finrank_of_faithful_perfect
    {F G V : Type*} [Field F] [Group G] [Group.IsPerfect G] [Nontrivial G]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F G V) (hf : Function.Injective ρ) :
    2 ≤ Module.finrank F V := by
  by_contra hd
  have hc : IsMulCommutative G := by
    refine ⟨⟨fun a b => hf ?_⟩⟩
    rw [map_mul, map_mul]
    rcases Nat.eq_zero_or_pos (Module.finrank F V) with hz | hp
    · let : Subsingleton V := Module.finrank_zero_iff.mp hz
      ext v
      exact Subsingleton.elim _ _
    · have he : Module.finrank F V = 1 := by omega
      obtain ⟨x, hx, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one he (ρ a)
      obtain ⟨y, hy, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one he (ρ b)
      rw [hx, hy]
      ext v
      simp [smul_smul, mul_comm]
  let := hc
  let : Subsingleton G := inferInstance
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  exact hab (Subsingleton.elim a b)

variable {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) H V)
  (N : Subgroup H) [IsIrreducible (ρ.comp N.subtype)]

omit [Finite H] [IsIrreducible (ρ.comp N.subtype)] in
private theorem centralizer_card_le_endField (hρ : Function.Injective ρ) :
    Nat.card (Subgroup.centralizer (N : Set H)) ≤
      Nat.card (Module.End (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))) := by
  let σ : Representation (ZMod 2) N V := ρ.comp N.subtype
  let f : Subgroup.centralizer (N : Set H) → IntertwiningMap σ σ := fun c =>
    { toLinearMap := ρ c
      isIntertwining' n := by
        change ρ (c : H) * ρ (n : H) = ρ (n : H) * ρ (c : H)
        rw [← map_mul, ← map_mul, (c.property n n.property)] }
  have hf : Function.Injective f := by
    intro c d h
    apply Subtype.ext
    apply hρ
    exact congrArg IntertwiningMap.toLinearMap h
  exact Nat.card_le_card_of_injective ((IntertwiningMap.equivAlgEnd σ) ∘ f)
    ((IntertwiningMap.equivAlgEnd σ).injective.comp hf)

omit [Finite H] in
/-- The field of endomorphisms of a faithful irreducible nontrivial perfect
action has square cardinality at most that of the module. -/
theorem endField_sq_le_card [Group.IsPerfect N] [Nontrivial N]
    (hρ : Function.Injective ρ) :
    Nat.card (Module.End (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))) ^ 2 ≤ Nat.card V := by
  let σ : Representation (ZMod 2) N V := ρ.comp N.subtype
  let E := Module.End (ZMod 2)[N] σ.asModule
  let : FiniteDimensional E σ.asModule := endFieldRep_finiteDimensional σ
  have hf : Function.Injective σ.endFieldRep :=
    endFieldRep_injective σ (fun _ _ h => Subtype.ext (hρ h))
  have hd := two_le_finrank_of_faithful_perfect σ.endFieldRep hf
  calc
    Nat.card E ^ 2 ≤ Nat.card E ^ Module.finrank E σ.asModule :=
      Nat.pow_le_pow_right (Nat.card_pos) hd
    _ = Nat.card σ.asModule := Module.natCard_eq_pow_finrank.symm
    _ = Nat.card V := Nat.card_congr σ.asModuleEquiv.toEquiv

omit [IsIrreducible (ρ.comp N.subtype)] in
/-- Faithfulness embeds the centralizer in the endomorphism ring. Conjugation embeds
the remaining quotient in the automorphisms of the literal central quotient. -/
theorem group_card_le_endField_mul_aut [N.Normal] [Group.IsPerfect N]
    (hρ : Function.Injective ρ) :
    Nat.card H ≤ Nat.card (Module.End (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))) *
      Nat.card (MulAut (N ⧸ Subgroup.center N)) := by
  let lift : H →* Subgroup.normalizer (N : Set H) :=
    { toFun := fun h => ⟨h, by rw [N.normalizer_eq_top]; exact Subgroup.mem_top h⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f := N.normalizerMonoidHom.comp lift
  have hker : f.ker = Subgroup.centralizer (N : Set H) := by
    ext h
    change lift h ∈ N.normalizerMonoidHom.ker ↔ h ∈ Subgroup.centralizer (N : Set H)
    rw [N.normalizerMonoidHom_ker]
    rfl
  let π : PerfectCentralCovering.Cover N (N ⧸ Subgroup.center N) :=
    { toMonoidHom := QuotientGroup.mk' (Subgroup.center N)
      surjective := QuotientGroup.mk'_surjective _
      isPerfect := inferInstance
      ker_le_center := by rw [QuotientGroup.ker_mk'] }
  have hπ : π.toMonoidHom.ker = Subgroup.center N := QuotientGroup.ker_mk' _
  have ha : Nat.card (MulAut N) ≤ Nat.card (MulAut (N ⧸ Subgroup.center N)) :=
    Nat.card_le_card_of_injective (π.autMap hπ) (π.autMap_injective hπ)
  calc
    Nat.card H = Nat.card f.ker * Nat.card f.range := by
      rw [← Subgroup.index_ker, Subgroup.card_mul_index]
    _ ≤ Nat.card (Module.End (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype))) *
        Nat.card (MulAut (N ⧸ Subgroup.center N)) := by
      apply Nat.mul_le_mul
      · rw [hker]
        exact centralizer_card_le_endField ρ N hρ
      · exact (Nat.card_le_card_of_injective _ Subtype.val_injective).trans ha

end Representation.BinaryOffender.QuasisimpleCardBound
