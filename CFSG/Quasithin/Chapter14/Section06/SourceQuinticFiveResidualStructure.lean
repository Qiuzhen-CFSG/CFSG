module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveResidualGeometry
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveExtraspecialInvolutions

/-!
# Exact intrinsic structure of the original five-residual

The residual is the actual commutator with the chosen order-five subgroup
inside the retained order-1024 core. Its original central and span markings
are used throughout. In particular, its nonabelianness forces its inherited
exponent-four bound to be exact. The actual nine-path involution constraint
and same-conjugator reciprocal span exclude the class-two possibility.
Thus the original residual has class three and its derived, Frattini and
second-center subgroups are the original quintic span, while its center
and third commutator are the original central line.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual five-residual in the large branch has exponent exactly four. -/
theorem source_quintic_large_five_residual_exponent
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let R := ⁅H.pCoreIn 2,A⁆
    Monoid.exponent R = 4 := by
  let Q := H.pCoreIn 2
  let R := ⁅Q,A⁆
  have hAQ : A ≤ normalizer (Q : Set G) := hAH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hRQ : R ≤ Q := le_normalizer_iff_commutator_le_left.mp hAQ
  let : Group.IsNilpotent R := ((isPGroup_pCoreIn 2 H).to_le hRQ).isNilpotent
  have hexp : Monoid.exponent R ∣ 4 := by
    have hh := Monoid.exponent_dvd_of_monoidHom (inclusion hRQ) (inclusion_injective hRQ)
    rw [(source_quintic_full_core_class_and_exponent
      hG T hempty hM hu hmany hcard e H hH hi).2] at hh
    exact hh
  have hclass : 2 ≤ Group.nilpotencyClass R := by
    rcases (source_quintic_large_five_residual_derived_alternative
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2.2.2 with h | h
    · exact h.1.ge
    · exact h.1.ge.trans' (by decide)
  have hn : ¬ Monoid.exponent R ∣ 2 := by
    intro hd
    have hab : IsMulCommutative R := ⟨⟨fun x y =>
      (Commute.of_orderOf_dvd_two (fun r => (Monoid.order_dvd_exponent r).trans hd) x y).eq⟩⟩
    have hh := Group.IsNilpotent.nilpotencyClass_le_one_iff.mpr hab
    omega
  obtain ⟨n, hnle, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show Monoid.exponent R ∣ 2 ^ 2 from hexp)
  interval_cases n
  · exact (hn (by rw [heq]; decide)).elim
  · exact (hn (by rw [heq]; decide)).elim
  · exact heq


/-- The original large branch has the actual order-512 class-three residual,
with all derived, Frattini, upper-center and central markings retained inside
its full order-1024 core. No residual class or model identification is assumed. -/
theorem source_quintic_large_five_residual_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    let R := ⁅Q,A⁆
    let Z := centralInvolutions T
    Nat.card C = 64 ∧ Nat.card Q = 1024 ∧ Nat.card R = 512 ∧
      Group.nilpotencyClass R = 3 ∧ Monoid.exponent R = 4 ∧
      ⁅R,R⁆ = U ∧ (frattini R).map R.subtype = U ∧
      (Subgroup.upperCentralSeries R 2).map R.subtype = U ∧
      (center R).map R.subtype = Z ∧ ⁅⁅R,R⁆,R⁆ = Z := by
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let R := ⁅Q,A⁆
  let Z := centralInvolutions T
  obtain ⟨hUR,_,_,halt⟩ := source_quintic_large_five_residual_derived_alternative
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  have hnot : ¬ ⁅R,R⁆ ≤ Z := by
    intro hlow
    have hinv := source_quintic_large_five_involutions_mem_residual_of_derived_central
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA hlow
    exact source_quintic_large_five_residual_derived_not_central_of_involutions
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA hinv hlow
  rcases halt with ⟨_,hlow⟩ | ⟨hclass,hderived,hPhi,hupper⟩
  · exact (hnot hlow.le).elim
  · obtain ⟨hCcard,hQcard,_,_,hRcard,_,_,_⟩ := source_quintic_large_five_residual
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
    have hexp := source_quintic_large_five_residual_exponent
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
    have hcenter := (source_quintic_large_five_residual_center
      hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA).2.2.2.1
    refine ⟨hCcard,hQcard,hRcard,hclass,hexp,hderived,hPhi,hupper,hcenter,?_⟩
    rw [hderived]
    exact hUR

end CFSG.Quasithin.Chapter14.Section06
