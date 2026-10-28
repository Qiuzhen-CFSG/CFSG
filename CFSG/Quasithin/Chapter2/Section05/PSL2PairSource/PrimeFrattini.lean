module

public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.PrimeModel
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Theory.Frattini.DihedralOmega
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# The marked Frattini element in the inner-involution model

For the original Fermat/Mersenne prime parameters, the reflected-torus
centralizer of a PSL₂ involution is an actual dihedral two-group of order
at least eight. Its central involution belongs to its Frattini subgroup.
The final theorem transports this fact to the literal ambient intersection
Q ∩ C_G(t), keeping the original subtype map into G.

Source: Aschbacher–Smith, proof of 2.5.21, printed p.567. This supplies the
Frattini membership after the inner action is aligned with the original t.
-/

public section

open Subgroup GorensteinWalter Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.PSL2PairSource

/-- The inner-involution centralizer is an actual dihedral two-group of
order at least eight, with the original Fermat/Mersenne restriction. -/
theorem prime_involution_centralizer_dihedral {p : ℕ} [Fact p.Prime]
    (hp : 7 ≤ p) (hparam : IsFermatOrMersennePrime p)
    (t : PSL(2, ZMod p)) (ht : orderOf t = 2) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (centralizer ({t} : Set PSL(2, ZMod p)) ≃*
      DihedralGroup (2 ^ m)) := by
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  have hfield : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, ho, by omega, by simp⟩
  have htI : IsInvolution t := ⟨by intro h; simp [h] at ht,
    by simpa only [ht] using pow_orderOf_eq_one t⟩
  obtain ⟨U, s, hUcyc, _, hs, hsU, hinv, hC, _, hUcard⟩ :=
    psl2_reflected_torus_card hfield htI
  have hU2 := (involution_centralizer_isTwoGroup hp hparam t ht).to_le
    (show U ≤ centralizer ({t} : Set PSL(2, ZMod p)) by rw [hC]; exact le_sup_left)
  obtain ⟨m, hm⟩ := hU2.exists_card_eq
  have hge : 3 ≤ Nat.card U := by
    have hcard : Nat.card U = (p - 1) / 2 ∨ Nat.card U = (p + 1) / 2 := by
      simpa using hUcard
    omega
  have hm2 : 2 ≤ m := by
    by_contra! hn
    have hpow : 3 ≤ 2 ^ m := hm ▸ hge
    interval_cases m <;> norm_num at hpow
  refine ⟨m, hm2, ?_⟩
  rw [hC, ← hm]
  exact nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted U s hUcyc hs.2 hsU hinv

/-- The marked involution lies in the Frattini subgroup of its actual
inner centralizer. This is a model theorem, not an added source premise. -/
theorem prime_involution_mem_frattini_centralizer {p : ℕ} [Fact p.Prime]
    (hp : 7 ≤ p) (hparam : IsFermatOrMersennePrime p)
    (t : PSL(2, ZMod p)) (ht : orderOf t = 2) :
    (⟨t, mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer ({t} : Set PSL(2, ZMod p))) ∈
      frattini (centralizer ({t} : Set PSL(2, ZMod p))) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := prime_involution_centralizer_dihedral hp hparam t ht
  have hphi := DihedralFrattini.omegaFrattini_top_of_equiv hm e
  rw [Subgroup.omegaFrattini_top] at hphi
  apply omegaOneAmbient_le _
  rw [hphi]
  apply mem_center_iff.mpr
  intro c
  exact Subtype.ext (mem_centralizer_singleton_iff.mp c.property)

/-- Transport the marked Frattini fact to the literal ambient intersection
Q ∩ C_G(t), preserving its subtype map back into G. -/
theorem model_mark_mem_frattini_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : 7 ≤ p) (hparam : IsFermatOrMersennePrime p)
    (Q : Subgroup G) (eQ : Q ≃* PSL(2, ZMod p))
    {t : G} (htQ : t ∈ Q) (ht : orderOf t = 2) :
    t ∈ (frattini (Q ⊓ centralizer ({t} : Set G) : Subgroup G)).map
      (Q ⊓ centralizer ({t} : Set G)).subtype := by
  let tQ : Q := ⟨t, htQ⟩
  let CQ := centralizer ({tQ} : Set Q)
  let C := Q ⊓ centralizer ({t} : Set G)
  let f : C ≃* CQ :=
    { toFun := fun c => ⟨⟨c.val, c.property.1⟩,
        mem_centralizer_singleton_iff.mpr (Subtype.ext
          (mem_centralizer_singleton_iff.mp c.property.2))⟩
      invFun := fun c => ⟨c.val.val, c.val.property,
        mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
          (mem_centralizer_singleton_iff.mp c.property))⟩
      left_inv := by intro c; rfl
      right_inv := by intro c; rfl
      map_mul' := by intros; rfl }
  have heq : CQ.map eQ.toMonoidHom = centralizer ({eQ tQ} : Set PSL(2, ZMod p)) := by
    rw [map_centralizer_equiv, Set.image_singleton]
  let eC := f.trans ((eQ.subgroupMap CQ).trans (MulEquiv.subgroupCongr heq))
  let tC : C := ⟨t, htQ, mem_centralizer_singleton_iff.mpr rfl⟩
  have htm : orderOf (eQ tQ) = 2 :=
    (eQ.orderOf_eq tQ).trans ((orderOf_coe tQ).symm.trans ht)
  have hphi : eC tC ∈ frattini (centralizer ({eQ tQ} : Set PSL(2, ZMod p))) :=
    prime_involution_mem_frattini_centralizer hp hparam (eQ tQ) htm
  rw [← frattini_map_equiv eC, mem_map_equiv] at hphi
  have hh : tC ∈ frattini C := by simpa only [eC.symm_apply_apply] using hphi
  exact mem_map.mpr ⟨tC, hh, rfl⟩

end CFSG.Quasithin.Chapter2.PSL2PairSource

end
