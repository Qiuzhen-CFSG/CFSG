module
public import Theory.SpecificGroups.Janko4.Model.SmallMathieuThompson

/-!
# The native Thompson normalizer excludes the nine-space

The normalizer of a full Sylow Thompson subgroup of order at most 2048
has order divisible by 23. Orbit counting shows that an automorphism of
order 23 fixes every group of order 512. Thus a nine-space cannot have
that two-group as its pointwise centralizer in the Thompson normalizer.
Source: Aschbacher--Smith 4.2.13 and 4.4.3, pp.611--612,623, used in
8.2.7, p.718. The imported native max1 certificates retain their attribution.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace MulAut
/-- Order 23 cannot occur in the automorphism group of a group of order 512.
The fixed subgroup order is a power of two with the same residue modulo 23. -/
theorem not_twentyThree_dvd_card_of_card_512 {V : Type*} [Group V] [Finite V]
    (hcard : Nat.card V = 512) : ¬ 23 ∣ Nat.card (MulAut V) := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  intro hdiv
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 23 hdiv
  let P := zpowers a
  have hP : Nat.card P = 23 := by rw [Nat.card_zpowers,ha]
  have hp : IsPGroup 23 P := IsPGroup.of_card (n := 1) (by simpa using hP)
  let F := FixedPoints.subgroup P V
  have hmod := hp.card_modEq_card_fixedPoints V
  change Nat.card V % 23 = Nat.card F % 23 at hmod
  have hFdiv : Nat.card F ∣ 2^9 := by
    simpa only [hcard,show 2^9 = 512 by norm_num] using F.card_subgroup_dvd_card
  obtain ⟨k,hk,hFcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hFdiv
  have heq : Nat.card F = Nat.card V := by
    rw [hcard,hFcard] at hmod ⊢
    interval_cases k <;> norm_num at *
  have htop := F.eq_top_of_card_eq heq
  have haone : a = 1 := by
    apply MulEquiv.ext
    intro x
    exact (show x ∈ F from htop ▸ mem_top x) ⟨a,mem_zpowers a⟩
  rw [haone,orderOf_one] at ha
  norm_num at ha
end MulAut

namespace Janko4
open Subgroup Stellmacher
attribute [local irreducible] modelGroup matrixA matrixB

/-- The native max1 prime 23 excludes a module of order 512 whose centralizer
is the elementary Thompson radical of a full Sylow subgroup. -/
theorem not_nineSpace_of_thompson_radical
    (P : Sylow 2 Model) (U E : Subgroup Model)
    (hth : elementaryAbelianMaxJ (P : Subgroup Model) = U)
    (hb : Nat.card U ≤ 2048) (hp : IsPGroup 2 U) (hE : Nat.card E = 512)
    (hn : normalizer (U : Set Model) ≤ normalizer (E : Set Model))
    (hc : normalizer (U : Set Model) ⊓ centralizer (E : Set Model) = U) : False := by
  let C := normalizer (U : Set Model)
  have hd : 23 ∣ Nat.card C := by
    change 23 ∣ Nat.card (normalizer (U : Set Model))
    rw [←hth]
    exact twentyThree_dvd_normalizer_thompson P (hth.symm ▸ hb)
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 23 hd
  let f : C →* MulAut E := E.normalizerMonoidHom.comp (inclusion hn)
  have hfa : f a = 1 := by
    apply orderOf_eq_one_iff.mp
    have hdiv : orderOf (f a) ∣ 23 := ha ▸ orderOf_map_dvd f a
    rcases (Nat.dvd_prime (by decide : Nat.Prime 23)).mp hdiv with he | he
    · exact he
    · exact (MulAut.not_twentyThree_dvd_card_of_card_512 hE
        (he ▸ orderOf_dvd_natCard (f a))).elim
  have hca : (a : Model) ∈ centralizer (E : Set Model) := by
    have hk : inclusion hn a ∈ E.normalizerMonoidHom.ker := hfa
    rwa [normalizerMonoidHom_ker] at hk
  have hau : (a : Model) ∈ U := hc.le ⟨a.property,hca⟩
  let u : U := ⟨a,hau⟩
  have hu : orderOf u = 23 := (orderOf_coe u).symm.trans ((orderOf_coe a).trans ha)
  have hdu : 23 ∣ Nat.card U := hu ▸ orderOf_dvd_natCard u
  obtain ⟨n,hcard⟩ := hp.exists_card_eq
  have htwo : 23 ∣ 2 := (show Nat.Prime 23 by decide).dvd_of_dvd_pow (hcard ▸ hdu)
  norm_num at htwo
end Janko4

