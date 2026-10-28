module

public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The residual of a Sylow overgroup of index three

If a Sylow two-subgroup has index three, the two-residual modulo its own
two-core has order three. The three-coset action has two-group kernel.
The residual image lies in A₃ and is nontrivial, since otherwise the residual
would lie in the Sylow subgroup, contradicting the residual/Sylow supplement.
A surjection with two-group kernel preserves the intrinsic core quotient.

This gives the index condition for the residual actors of the minimal
parabolics in Aschbacher--Smith, Lemma 14.4.12, printed pp.1011--1012.
It uses no Mathieu classification and does not require the Sylow subgroup
to be nonnormal.
-/

public section
namespace Subgroup
private theorem symmetricThree_residual :
    pResidual 2 (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 3)).index = 2 ^ 1
    simp
  · intro x hx
    have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have hp : x ^ 3 = 1 := congrArg Subtype.val
      (hc ▸ pow_card_eq_one' (x := (⟨x, hx⟩ : alternatingGroup (Fin 3))))
    exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hp))

/-- A Sylow two-subgroup of index three forces the residual core quotient
of the whole group to have order three. -/
theorem residual_core_quotient_card_of_sylow_index_three
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hi : (S : Subgroup G).index = 3) :
    Nat.card (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) = 3 := by
  classical
  let points := G ⧸ (S : Subgroup G)
  let e : points ≃ Fin 3 := (Finite.equivFin points).trans (finCongr hi)
  let a : G →* Equiv.Perm points := MulAction.toPermHom G points
  let f : G →* Equiv.Perm (Fin 3) := (Equiv.permCongrHom e).toMonoidHom.comp a
  have hker : f.ker = (S : Subgroup G).normalCore := by
    rw [MonoidHom.ker_comp_of_injective _ _ (Equiv.permCongrHom e).injective]
    exact (S : Subgroup G).normalCore_eq_ker.symm
  have hkS : f.ker ≤ (S : Subgroup G) := hker ▸ (S : Subgroup G).normalCore_le
  have hk : IsPGroup 2 f.ker := S.isPGroup'.to_le hkS
  let R := pResidual 2 G
  let A := R.map f
  have hA : A ≤ alternatingGroup (Fin 3) := by
    rw [← symmetricThree_residual]
    exact map_pResidual_le 2 f
  have hcard : Nat.card A = 3 := by
    have hAcard : Nat.card A ∣ 3 := by
      have hh := card_dvd_of_le hA
      have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
        rw [nat_card_alternatingGroup, Nat.card_fin]
        rfl
      simpa only [hc] using hh
    rcases (Nat.dvd_prime Nat.prime_three).mp hAcard with hc | hc
    · have hbot : A = ⊥ := card_eq_one.mp hc
      have hRS : R ≤ (S : Subgroup G) :=
        ((Subgroup.map_eq_bot_iff _).mp hbot).trans hkS
      have hsup : R ⊔ (S : Subgroup G) = ⊤ := pResidual_sup_sylow_eq_top S
      have he : (S : Subgroup G) = ⊤ := by simpa only [sup_eq_right.mpr hRS] using hsup
      have hh : (S : Subgroup G).index = 1 := index_eq_one.mpr he
      omega
    · exact hc
  have hcore : pCore 2 A = ⊥ := by
    have h3 : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hcard)
    have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) (pCore 2 A) ⊤
      pCore_isPGroup (h3.to_subgroup ⊤)
    simpa using hd.eq_bot
  let r := f.subgroupMap R
  have hkr : IsPGroup 2 r.ker := by
    change IsPGroup 2 (f.subgroupMap R).ker
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  have he := r.pCoreQuotientEquiv (f.subgroupMap_surjective R) hkr
  rw [Nat.card_congr he.toEquiv]
  change Nat.card (A ⧸ pCore 2 A) = 3
  rw [hcore, Nat.card_congr QuotientGroup.quotientBot.toEquiv, hcard]
end Subgroup
