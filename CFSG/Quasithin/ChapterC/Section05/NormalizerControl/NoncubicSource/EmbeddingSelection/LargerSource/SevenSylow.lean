module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.EvenContaining
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.AlternatingSevenMaximal.Basic
public import Theory.Alternating.Aut
public import Theory.SpecificGroups.AlternatingSeven.TranspositionCore
/-!
# The intrinsic Sylow action on an alternating-seven local component

A faithful two-subgroup of Aut(A7)=S7 has order dividing sixteen. If the
full Sylow has order divisible by sixteen, its permutation image is Sylow
in S7 and contains a transposition. Lifting that transposition gives an
actual ambient involution whose centralizer contains an injected A5.
This retains the original subgroup inclusion and conjugation action.

Combined with even characteristic, the order bound excludes containing
carriers with two-part at least thirty-two. The involution-centralizer
conclusion treats the sharp order-sixteen odd ternary endpoint.
Source: Aschbacher–Smith A.3.12 and C.5.12, printed pp.47–48,163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02.LocalModels ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

theorem alternating_seven_normalizer_card_dvd (T : Sylow 2 G) (B : Subgroup G)
    (hB : IsAlternating B 7) (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (T : Subgroup G) ⊓ centralizer (B : Set G)=⊥) : Nat.card T ∣ 16 := by
  obtain ⟨e⟩ := hB
  let f := B.normalizerMonoidHom.comp (inclusion hTB)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hfaith]
    refine ⟨a.property,?_⟩
    change inclusion hTB a ∈ B.normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact ha
  let eA : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let j := eA.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp f)
  have hj : Function.Injective j := eA.symm.injective.comp ((MulAut.congr e).injective.comp hf)
  have hd : Nat.card T ∣ 16*315 := by
    have hd := card_dvd_of_injective j hj
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,show Nat.factorial 7 = 16*315 from rfl] using hd
  have hcop : Nat.Coprime (Nat.card T) 315 := by
    obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 315).pow_left n
  exact hcop.dvd_of_dvd_mul_right hd

theorem no_alternating_seven_local_of_even_large_twoPart
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T) {B : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hm : IsAlternating B 7) (hd : 32 ∣ Nat.card G) : False := by
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic T hE hB hTB
  have ht : 32 ∣ Nat.card T := T.pow_dvd_card_of_pow_dvd_card (n := 5) hd
  have hc := ht.trans (alternating_seven_normalizer_card_dvd T B hm hTB hf)
  norm_num at hc

/-- A faithful Sylow of order sixteen contains an actor centralizing an A5. -/
theorem alternating_seven_sylow_involution_centralizer
    (T : Sylow 2 G) (B : Subgroup G) (hB : IsAlternating B 7)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hfaith : (T : Subgroup G) ⊓ centralizer (B : Set G)=⊥)
    (hd : 16 ∣ Nat.card T) :
    ∃ t : G, orderOf t=2 ∧
      ∃ j : alternatingGroup (Fin 5) →* centralizer ({t} : Set G), Function.Injective j := by
  classical
  obtain ⟨e⟩ := hB
  let f := B.normalizerMonoidHom.comp (inclusion hTB)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hfaith]
    refine ⟨a.property,?_⟩
    change inclusion hTB a ∈ B.normalizerMonoidHom.ker at ha
    rw [normalizerMonoidHom_ker] at ha
    exact ha
  let eA : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 7)))
      (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))
  let q := eA.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp f)
  have hq : Function.Injective q := eA.symm.injective.comp ((MulAut.congr e).injective.comp hf)
  have hc : Nat.card T=16 := Nat.dvd_antisymm
    (alternating_seven_normalizer_card_dvd T B ⟨e⟩ hTB hfaith) hd
  have hqc : Nat.card q.range=16 := (Nat.card_congr (MonoidHom.ofInjective hq).toEquiv).symm.trans hc
  let P : Sylow 2 (Equiv.Perm (Fin 7)) := Sylow.ofCard q.range (by
    rw [hqc,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide +kernel)
  let z : Equiv.Perm (Fin 7) := Equiv.swap 5 6
  have hz2 : z^2=1 := by decide +kernel
  have hz : orderOf z=2 := orderOf_eq_prime hz2 (by decide)
  have hzp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hz,pow_one])
  obtain ⟨Q,hQ⟩ := hzp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Equiv.Perm (Fin 7)) P Q
  have hm : z ∈ q.range.map (MulAut.conj g).toMonoidHom := by
    change z ∈ ((g • P : Sylow 2 (Equiv.Perm (Fin 7))) : Subgroup (Equiv.Perm (Fin 7)))
    rw [hg]
    exact hQ (mem_zpowers z)
  obtain ⟨σ,⟨t,rfl⟩,ht⟩ := hm
  have hswap : (q t).IsSwap := by
    apply Equiv.Perm.isSwap_iff_cycleType.mpr
    have hh := Equiv.Perm.cycleType_conj (σ := q t) (τ := g)
    rw [show g * q t * g⁻¹ = z from ht] at hh
    exact hh.symm.trans (Equiv.Perm.isSwap_iff_cycleType.mp
      (Equiv.Perm.swap_isSwap_iff.mpr (by decide : (5 : Fin 7) ≠ 6)))
  have ht2 : orderOf (t : G)=2 := by
    rw [Subgroup.orderOf_coe,← orderOf_injective q hq]
    exact hswap.orderOf
  obtain ⟨c⟩ := AlternatingSeven.TranspositionCore.transposition_centralizer_equiv
    (MulEquiv.refl (Equiv.Perm (Fin 7))) (q t) hswap
  let A := alternatingGroup (Fin 5)
  let : Group.IsPerfect A := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let b : A →* Equiv.Perm (Fin 7) := (centralizer ({q t} : Set (Equiv.Perm (Fin 7)))).subtype.comp
    (c.symm.toMonoidHom.comp ((alternatingGroup (Fin 5)).subtype.prod (1 : A →* Equiv.Perm (Fin 2))))
  have hb : Function.Injective b := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg Prod.fst (c.symm.injective (Subtype.ext hxy))
  have heven : ∀ x, b x ∈ alternatingGroup (Fin 7) := by
    have hs : Equiv.Perm.sign.comp b=1 := by
      apply MonoidHom.ker_eq_top_iff.mp
      apply top_unique
      rw [← Group.IsPerfect.commutator_eq_top (G := A)]
      exact Abelianization.commutator_subset_ker _
    intro x
    exact Equiv.Perm.mem_alternatingGroup.mpr (DFunLike.congr_fun hs x)
  let a := b.codRestrict (alternatingGroup (Fin 7)) heven
  let k := e.symm.toMonoidHom.comp a
  have hk : Function.Injective k := e.symm.injective.comp (by
    intro x y heq
    exact hb (congrArg (fun x : alternatingGroup (Fin 7) => (x : Equiv.Perm (Fin 7))) heq))
  have hcomm (x : A) : (t : G) * (k x : G) = (k x : G) * (t : G) := by
    have hbcomm : b x ∈ centralizer ({q t} : Set (Equiv.Perm (Fin 7))) :=
      (c.symm ((x : Equiv.Perm (Fin 5)),1)).property
    have ha : MulAut.conjNormal (H := alternatingGroup (Fin 7)) (q t) (a x) = a x := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hbcomm).symm
    have hact : eA (q t) = MulAut.congr e (f t) := eA.apply_symm_apply _
    have heq : e (f t (k x)) = e (k x) := by
      have hv := congrArg (fun α : MulAut (alternatingGroup (Fin 7)) => α (a x)) hact
      rw [show eA (q t) (a x) = a x from ha] at hv
      change e (f t (e.symm (a x))) = e (e.symm (a x))
      simpa only [MulEquiv.apply_symm_apply,MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.symm_apply_apply,
        MonoidHom.coe_comp,Function.comp_apply,MulEquiv.coe_toMonoidHom] using hv.symm
    have hv := congrArg Subtype.val (e.injective heq)
    change (t : G) * (k x : G) * (t : G)⁻¹ = (k x : G) at hv
    exact mul_inv_eq_iff_eq_mul.mp hv
  let j : A →* centralizer ({(t : G)} : Set G) :=
    (B.subtype.comp k).codRestrict _ (fun x => mem_centralizer_singleton_iff.mpr (hcomm x).symm)
  refine ⟨t,ht2,j,?_⟩
  intro x y heq
  apply hk
  apply Subtype.ext
  exact congrArg (fun x : centralizer ({(t : G)} : Set G) => (x : G)) heq

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
