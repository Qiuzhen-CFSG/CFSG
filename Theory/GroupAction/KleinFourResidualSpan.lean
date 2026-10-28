module

public import Theory.GroupAction.FourGroupCoreAction
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# The two-residual spans every point of a full four-group action

If a finite subgroup induces all automorphisms of a four-group, its two-residual
moves every nonidentity point. Indeed, a cubic automorphism lies in the
image of the residual, and no cubic automorphism can fix such a point: the
point stabilizer has order at most two. A point and its moved image generate
the four-group. The conclusion keeps the original ambient conjugation maps.

This is the residual-span step in Aschbacher–Smith 14.7.70, printed p.1074,
following the application of A.1.14.
-/

public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The orbit-span of a nonidentity point under the actual embedded two-residual
is the entire four-group whenever the original conjugation action is full. -/
theorem conjugateSpanBy_point_twoResidual_eq_fourGroup
    (V H : Subgroup G) [IsKleinFour V]
    (hn : H ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (V.normalizerMonoidHom.comp (inclusion hn)))
    (v : G) (hv : v ∈ V) (hv1 : v ≠ 1) :
    conjugateSpanBy (zpowers v) ((pResidual 2 H).map H.subtype) = V := by
  classical
  let ρ : H →* MulAut V := V.normalizerMonoidHom.comp (inclusion hn)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := MulAut V) 3
    (by rw [IsKleinFour.card_mulAut]; decide)
  have har : a ∈ pResidual 2 (MulAut V) :=
    mem_pResidual_of_orderOf_coprime (by rw [ha]; decide)
  rw [← map_pResidual_of_surjective 2 ρ hfull] at har
  obtain ⟨r, hr, hra⟩ := har
  let x : V := ⟨v, hv⟩
  have hx : x ≠ 1 := fun hh => hv1 (congrArg Subtype.val hh)
  have hmove : a x ≠ x := by
    intro hfix
    have hcard : Nat.card (zpowers a) ≤ 2 :=
      card_mulAut_subgroup_le_two_of_fixed_point
        (IsKleinFour.card_four (G := V)) x hx (zpowers a) (by
          intro b hb
          exact (show zpowers a ≤ MulAction.stabilizer (MulAut V) x from
            zpowers_le.mpr hfix) hb)
    rw [Nat.card_zpowers, ha] at hcard
    omega
  let R := (pResidual 2 H).map H.subtype
  let S := conjugateSpanBy (zpowers v) R
  have hSV : S ≤ V := conjugateSpanBy_le (zpowers_le.mpr hv)
    ((map_subtype_le _).trans hn)
  have hxS : v ∈ S := le_conjugateSpanBy _ _ (mem_zpowers v)
  have hyS : (a x : G) ∈ S := by
    apply subset_closure
    refine ⟨r, mem_map_of_mem H.subtype hr, v, mem_zpowers v, ?_⟩
    change (ρ r x : G) = (a x : G)
    rw [hra]
  have hy : a x ≠ 1 := by simpa using hx
  apply le_antisymm hSV
  intro z hz
  let zV : V := ⟨z, hz⟩
  change (zV : G) ∈ S
  by_cases hz1 : zV = 1
  · exact hz1 ▸ S.one_mem
  by_cases hzx : zV = x
  · exact hzx ▸ hxS
  by_cases hzy : zV = a x
  · exact hzy ▸ hyS
  have heq := IsKleinFour.eq_mul_of_ne_all hx hy hmove.symm hz1 hzx hzy
  have hzval : z = v * (a x : G) := congrArg Subtype.val heq
  change z ∈ S
  rw [hzval]
  exact S.mul_mem hxS hyS

end Subgroup
