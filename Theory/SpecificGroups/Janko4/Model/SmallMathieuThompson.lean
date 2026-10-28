module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore.NormalElementary
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Mathlib.GroupTheory.PGroup

/-!
# The native J₄ Thompson normalizer excludes small faithful modules

A full Sylow Thompson subgroup of order at most 2048 is conjugate to the
literal max1 kernel. Its normalizer therefore has order divisible by 23.
An automorphism of order 23 fixes every group of order 1024, by counting
fixed points modulo 23. Thus such a module cannot have the Thompson radical
as its centralizer in the radical normalizer.

Source application: Aschbacher–Smith 4.2.13 and 4.4.14,
printed pp.611–612,624–625. The native max1 data retain their ATLAS attribution
through the imported local structure modules.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4
open LocalStructure Cardinality LocalStructure.SylowCore
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

/-- A Thompson subgroup of order at most 2048 is the native max1 kernel,
up to conjugacy. Its normalizer therefore has a factor of 23 in its order. -/
theorem twentyThree_dvd_normalizer_thompson (P : Sylow 2 Model)
    (hb : Nat.card (elementaryAbelianMaxJ (P : Subgroup Model)) ≤ 2048) :
    23 ∣ Nat.card (normalizer (elementaryAbelianMaxJ (P : Subgroup Model) : Set Model)) := by
  let S : Sylow 2 Local := Classical.choice inferInstance
  let Q : Sylow 2 Model := (S.isPGroup'.map Local.subtype).toSylow (by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul S.not_dvd_index
      OuterReduction.max1_odd_index_unconditional)
  let R := (localKernel matrixA_mul_self matrixB_pow_four).map Local.subtype
  let := localKernel_elementary matrixA_mul_self matrixB_pow_four
  have hR : IsElementaryAbelian 2 R := IsElementaryAbelian.map Local.subtype
  have hRc : Nat.card R = 2048 := by
    rw [card_map_of_injective Local.subtype_injective]
    exact localKernel_card matrixA_mul_self matrixB_pow_four
  have hRQ : R ≤ (Q : Subgroup Model) := map_mono (localKernel_le_sylow S)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model P Q
  let f := MulAut.conj g
  have hPQ : (P : Subgroup Model).map f.toMonoidHom = (Q : Subgroup Model) :=
    congrArg Sylow.toSubgroup hg
  have hJQ : (elementaryAbelianMaxJ (P : Subgroup Model)).map f.toMonoidHom =
      elementaryAbelianMaxJ (Q : Subgroup Model) := by
    rw [←elementaryAbelianMaxJ_map_equiv,hPQ]
  have hbQ : Nat.card (elementaryAbelianMaxJ (Q : Subgroup Model)) ≤ 2048 := by
    rw [←hJQ,card_map_of_injective f.injective]
    exact hb
  have hRmax : R ∈ elementaryAbelianMaxSubgroups (Q : Subgroup Model) := by
    obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty (Q : Subgroup Model)
    refine ⟨hRQ,hR,?_⟩
    intro B hBQ hB
    rw [hRc]
    exact (hA.2.2 B hBQ hB).trans ((card_le_of_le (le_sSup hA)).trans hbQ)
  have he : elementaryAbelianMaxJ (Q : Subgroup Model) = R :=
    (eq_of_le_of_card_ge (le_sSup hRmax) (by rwa [hRc])).symm
  have hLN : Local ≤ normalizer (R : Set Model) := by
    intro x hx
    exact (localKernel matrixA_mul_self matrixB_pow_four).le_normalizer_map Local.subtype
      (mem_map_of_mem Local.subtype
        (show (⟨x,hx⟩ : Local) ∈ normalizer (localKernel matrixA_mul_self matrixB_pow_four : Set Local)
          from le_normalizer_of_normal (mem_top _)))
  have hd : 23 ∣ Nat.card (normalizer (R : Set Model)) := by
    apply (show 23 ∣ Nat.card Local from ?_).trans (card_dvd_of_le hLN)
    rw [max1Subgroup_card matrixA_mul_self matrixB_pow_four]
    norm_num
  have hn := congrArg (fun X : Subgroup Model => Nat.card (normalizer (X : Set Model))) hJQ
  rw [←map_equiv_normalizer_eq,card_map_of_injective f.injective,he] at hn
  exact hn.symm ▸ hd
end Janko4

namespace MulAut
/-- Order 23 cannot occur in the automorphism group of a group of order 1024.
The fixed subgroup order is a power of two with the same residue modulo 23. -/
theorem not_twentyThree_dvd_card_of_card_1024 {V : Type*} [Group V] [Finite V]
    (hcard : Nat.card V = 1024) : ¬ 23 ∣ Nat.card (MulAut V) := by
  let : Fact (Nat.Prime 23) := ⟨by decide⟩
  intro hdiv
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 23 hdiv
  let P := zpowers a
  have hP : Nat.card P = 23 := by rw [Nat.card_zpowers,ha]
  have hp : IsPGroup 23 P := IsPGroup.of_card (n := 1) (by simpa using hP)
  let F := FixedPoints.subgroup P V
  have hmod := hp.card_modEq_card_fixedPoints V
  change Nat.card V % 23 = Nat.card F % 23 at hmod
  have hFdiv : Nat.card F ∣ 2^10 := by
    simpa only [hcard,show 2^10 = 1024 by norm_num] using F.card_subgroup_dvd_card
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

/-- The native max1 prime 23 excludes a module of order 1024 whose centralizer
is the elementary Thompson radical of a full Sylow subgroup. -/
theorem not_small_module_of_thompson_radical
    (P : Sylow 2 Model) (U E : Subgroup Model)
    (hth : elementaryAbelianMaxJ (P : Subgroup Model) = U)
    (hb : Nat.card U ≤ 2048) (hp : IsPGroup 2 U) (hE : Nat.card E = 1024)
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
    · exact (MulAut.not_twentyThree_dvd_card_of_card_1024 hE
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

