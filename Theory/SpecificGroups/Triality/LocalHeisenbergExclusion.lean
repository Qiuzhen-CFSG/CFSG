module
public import Theory.SpecificGroups.Triality.SolvableSylowControl
public import Theory.SpecificGroups.Triality.CubicComponentAction
public import Theory.SpecificGroups.HeisenbergPrime.SolvableSylowExclusion

/-!
# Triality excludes the local ternary Heisenberg action

The actual Borel is the positive subgroup times the root-defined torus.
The positive subgroup is normal in this Borel and the torus is abelian,
so the Borel's derived subgroup lies in the positive subgroup. Sylow
conjugacy transfers this inclusion to every Sylow two-normalizer.

For field order greater than two, solvable full-Sylow overgroups normalize
the given Sylow subgroup. The proved cubic-actor theorem makes every
ternary Heisenberg actor inner when the automorphism overgroup has
three-rank at most two. Pullback to the model puts the faithful Heisenberg
group in the Borel; its odd image in the abelian torus is then abelian,
a contradiction. Simplicity and perfectness are inherited hypotheses on
the genuine model, as supplied by the ordinary-component consumer.

Source: Aschbacher–Smith 14.7.26, printed p.1053, refs/quasithin.pdf;
A.2.6 and A.3.18 for cubic actors. The imported root Borel and solvable
Sylow-control proofs retain their GLS3 references.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace Triality.Standard.LocalHeisenbergExclusion
open Parabolics ConcreteBruhat

private theorem borel_derived (P : Parameters) (hp : P.prime = 2) :
    ⁅borel P,borel P⁆ ≤ unipotent P := by
  have hU : unipotent P ≤ borel P := by
    rw [←normalizer_unipotent_eq_borel P hp]
    exact (unipotent P).le_normalizer
  have hT : torus P ≤ borel P := by
    intro t ht
    change t ∈ (borel P : Set (Carrier P))
    rw [borel_eq_mul P hp]
    exact ⟨1,one_mem _,t,ht,one_mul t⟩
  let N := (unipotent P).subgroupOf (borel P)
  let H := (torus P).subgroupOf (borel P)
  let : N.Normal := unipotent_normal_in_borel P hp
  have he : unipotent P ⊔ torus P = borel P := by
    apply le_antisymm (sup_le hU hT)
    intro b hb
    obtain ⟨⟨u,t⟩,he,_⟩ := existsUnique_borel_factors P hp ⟨b,hb⟩
    change (u : Carrier P) * (t : Carrier P) = b at he
    rw [←he]
    exact mul_mem (mem_sup_left u.property) (mem_sup_right t.property)
  have hNH : N ⊔ H = ⊤ := by
    apply map_injective (borel P).subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hU,map_subgroupOf_eq_of_le hT,
      ←MonoidHom.range_eq_map,range_subtype,he]
  let e := (subgroupOfEquivOfLe hT).trans (TorusCoordinates.torusMulEquiv P hp).symm
  have hcomm : IsMulCommutative H := ⟨⟨fun a b => e.injective (by
    rw [map_mul,map_mul]
    exact mul_comm _ _)⟩⟩
  have hc := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hNH hcomm
  have hd := map_mono (f := (borel P).subtype) hc
  rwa [map_commutator_eq,range_subtype,map_subgroupOf_eq_of_le hU] at hd

/-- The full normalizer of every binary triality Sylow subgroup has abelian
quotient by that same Sylow subgroup. -/
theorem normalizer_derived (P : Parameters) (hp : P.prime = 2)
    (S : Sylow 2 (Carrier P)) :
    ⁅normalizer (S : Set (Carrier P)),normalizer (S : Set (Carrier P))⁆ ≤
      (S : Subgroup (Carrier P)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Carrier P) S (unipotentSylow P hp)
  let a := MulAut.conj g
  have hS : (S : Subgroup (Carrier P)).map a.toMonoidHom = unipotent P := by
    have hh := congrArg (fun V : Sylow 2 (Carrier P) => (V : Subgroup (Carrier P))) hg
    rw [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def,coe_unipotentSylow] at hh
    have he : MulDistribMulAction.toMonoidEnd (MulAut (Carrier P)) (Carrier P)
        (MulAut.conj g) = a.toMonoidHom := by ext x; rfl
    rwa [he] at hh
  have hN : (normalizer (S : Set (Carrier P))).map a.toMonoidHom ≤ borel P := by
    rw [←normalizer_unipotent_eq_borel P hp,←hS]
    exact fun _ hx => (S : Subgroup (Carrier P)).le_normalizer_map a.toMonoidHom hx
  apply (map_le_map_iff_of_injective (f := a.toMonoidHom) a.injective).mp
  rw [map_commutator,hS]
  exact (commutator_mono hN hN).trans (borel_derived P hp)

/-- Nonbinary triality cannot carry the original rank-two local Heisenberg
configuration in a solvable subgroup of odd index. -/
theorem no_action (n : ℕ) (hn : 1 < n)
    [IsSimpleGroup (BinaryCarrier n (lt_trans Nat.zero_lt_one hn))]
    [Group.IsPerfect (BinaryCarrier n (lt_trans Nat.zero_lt_one hn))]
    (A : Subgroup (MulAut (BinaryCarrier n (lt_trans Nat.zero_lt_one hn))))
    (hA : MulAut.innerSubgroup (BinaryCarrier n (lt_trans Nat.zero_lt_one hn)) ≤ A)
    (hr : primeRank 3 A ≤ 2) (J : Subgroup A) [Group.IsSolvable J] (ho : Odd J.index)
    (f : HeisenbergPrime 3 →* A) (hf : Function.Injective f) (hJ : ∀ y, f y ∈ J) : False := by
  have hz : center (BinaryCarrier n (lt_trans Nat.zero_lt_one hn)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (center (BinaryCarrier n (lt_trans Nat.zero_lt_one hn))) inferInstance with hh | hh
    · exact hh
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp hh)).elim
  apply HeisenbergPrime.no_inner_action_in_solvable_odd_index hz
    (SolvableSylowControl.binary_control n hn)
    (normalizer_derived (binaryParameters n (lt_trans Nat.zero_lt_one hn)) rfl) A hA J ho f hf hJ
  intro y
  apply CubicComponentAction.primePower_actor_inner n (lt_trans Nat.zero_lt_one hn) A hA hr
    (f y) (f y).property 1
  change (A.subtype.comp f) y ^ 3 = 1
  rw [←map_pow,HeisenbergPrime.pow_prime (by decide : 3 ≠ 2),map_one]

end Triality.Standard.LocalHeisenbergExclusion
