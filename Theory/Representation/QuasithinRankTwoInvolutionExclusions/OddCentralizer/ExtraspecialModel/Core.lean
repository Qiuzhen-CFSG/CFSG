module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.MinimalDegree
public import Theory.ElementaryAbelian.ExtraspecialEquiv
/-!
# The cubic witness in an extraspecial-by-two group

The normal marked Heisenberg subgroup is the odd core because its quotient
is a two-group. Its explicit third-coordinate generator generates the
center of that core. The degree-six lemma supplies the fixed-space claim;
there is no assumed irreducibility or central-action field in a record.

Source: Aschbacher–Smith, G.11.2(3), printed p.364, and the cubic-center
exclusion in 6.2.19, printed p.691. A concrete extension and its source
identification are still required to instantiate this structural lemma.
-/

@[expose] public section

open Representation Subgroup
namespace Representation.RankTwo.ExtraspecialModel
variable {H V : Type*} [Group H] [Finite H]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A normal Heisenberg subgroup with two-group quotient is the odd core. -/
theorem oddCore_eq_of_heisenberg
    (P : Subgroup H) [P.Normal] (e : P ≃* HeisenbergPrime 3)
    (hquot : IsPGroup 2 (H ⧸ P)) : pPrimeCore 2 H = P := by
  apply le_antisymm (pPrimeCore_le_of_isPGroup_quotient 2 P hquot)
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  rw [Nat.card_congr e.toEquiv, HeisenbergPrime.card]
  decide

/-- The marked central cube root supplies the literal odd-core witness. -/
theorem exists_cubic_witness
    (P : Subgroup H) [P.Normal] (e : P ≃* HeisenbergPrime 3)
    (hquot : IsPGroup 2 (H ⧸ P))
    (ρ : Representation (ZMod 2) H V) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 6) :
    ∃ c : H, orderOf c = 3 ∧ (zpowers c).Normal ∧
      zpowers c = (center (pPrimeCore 2 H)).map (pPrimeCore 2 H).subtype ∧
      (∀ x, ρ c x = x → x = 0) := by
  let z : HeisenbergPrime 3 := ⟨0, 0, 1⟩
  have hz : orderOf z = 3 := by
    apply orderOf_eq_prime_iff.mpr
    refine ⟨HeisenbergPrime.pow_prime (by decide) z, ?_⟩
    intro he
    have hh := congrArg HeisenbergPrime.c he
    exact one_ne_zero hh
  have hzZ : z ∈ center (HeisenbergPrime 3) :=
    (HeisenbergPrime.mem_center_iff z).mpr ⟨rfl, rfl⟩
  let c : P := e.symm z
  have hc : orderOf c = 3 := (e.symm.orderOf_eq z).trans hz
  have hcZ : c ∈ center P := (centerCongr e.symm ⟨z, hzZ⟩).property
  let : IsExtraspecial 3 P := (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcyc : zpowers (c : H) = (center P).map P.subtype := by
    rw [← zpowers_eq_center c hc hcZ, MonoidHom.map_zpowers]
    rfl
  have hn : (zpowers (c : H)).Normal := by
    rw [hcyc]
    infer_instance
  have hcore := oddCore_eq_of_heisenberg P e hquot
  refine ⟨c, (orderOf_injective P.subtype P.subtype_injective c).trans hc, hn, ?_, ?_⟩
  · exact hcyc.trans (congrArg (fun Q : Subgroup H => (center Q).map Q.subtype) hcore.symm)
  · exact fixed_free_of_faithful_six (ρ.comp P.subtype) (hρ.comp P.subtype_injective)
      ((Nat.card_congr e.toEquiv).trans HeisenbergPrime.card) hdim c hc hcZ
end Representation.RankTwo.ExtraspecialModel
