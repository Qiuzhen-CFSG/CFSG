module
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.OddSubgroupBlockNormalizer
public import Theory.GroupTheory.Commutator.SimpleSubnormal

/-!
# Odd subgroups prevent exchange of C-components

If a nontrivial odd subgroup D of a C-component X normalizes a two-group Q,
then Q preserves X whenever X/O₂(X) is simple. Pass to the ambient two-core
quotient: distinct conjugates of the resulting simple perfect subgroup
commute. The odd-subgroup argument forces Q to normalize that image, and
uniqueness of C-component lifting returns the original normalizer.

Source application: Aschbacher--Smith, preliminary 15.2.23, printed p.1115.
This avoids assuming that the full Sylow subgroup fixes X.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem normalizes_cComponent_of_odd_subgroup
    (X Q D : Subgroup G) (hX : X.IsCComponent)
    [IsSimpleGroup (X ⧸ pCore 2 X)]
    (hQ : IsPGroup 2 Q) (hD : Odd (Nat.card D)) (hd : D ≠ ⊥)
    (hDX : D ≤ X) (hDQ : D ≤ normalizer (Q : Set G)) :
    Q ≤ normalizer (X : Set G) := by
  let N := pCore 2 G
  let := pCore_isNilpotent (p := 2) (G := G)
  let q := QuotientGroup.mk' N
  let A := X.map q
  have hA : A.IsCComponent := hX.map_quotient N
  let : IsSimpleGroup A := (cComponentTwoCoreQuotientEquiv hX).symm.isSimpleGroup
  let : Group.IsPerfect A := hA.perfect
  have hZA : center A = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center A) inferInstance with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp h)).elim
  have hodd : Odd (Nat.card (D.map q)) := Nat.not_even_iff_odd.mp (by
    rw [even_iff_two_dvd]
    exact fun h => hD.not_two_dvd_nat (h.trans (card_map_dvd D q)))
  have hne : D.map q ≠ ⊥ := by
    intro he
    have hDN : D ≤ N := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff D).mp he
    have hp := (pCore_isPGroup (p := 2) (G := G)).to_le hDN
    apply hd
    apply eq_bot_iff.mpr
    intro d hdD
    have he : (⟨d,hdD⟩ : D) = 1 := (hp.powEquiv hD.coprime_two_left).injective
      (by change (⟨d,hdD⟩ : D) ^ Nat.card D = 1 ^ Nat.card D; simp [pow_card_eq_one'])
    exact congrArg D.subtype he
  have hn : Q.map q ≤ normalizer (A : Set (G ⧸ N)) := by
    apply normalizes_of_odd_subgroup_and_commuting_conjugates A (Q.map q) (D.map q)
      (hQ.map q) hodd hne (map_mono hDX)
      ((map_mono hDQ).trans (le_normalizer_map q))
    · rw [hZA]
      exact IsPGroup.of_bot
    · intro a ha hne
      let B := A.map (MulAut.conj a).toMonoidHom
      let e : A ≃* B := A.equivMapOfInjective _ (MulAut.conj a).injective
      let : IsSimpleGroup B := e.symm.isSimpleGroup
      exact simple_subnormal_commute_of_ne A B hA.subnormal
        (hA.map_equiv (MulAut.conj a)).subnormal hne
  rw [← normalizer_cComponent_quotient hX N]
  exact map_le_iff_le_comap.mp hn
end Subgroup
