module

public import Theory.SpecificGroups.AlternatingSixNormalizer
public import Theory.SpecificGroups.SymmetricEight.ComponentMarking.PermutationFacts
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# A normal A5 seed cannot control a nontrivial two-subgroup in S8

The actual even seed normalizes the two-subgroup, and its normalizer contains
the latter's even centralizer. The binary four-space obstruction kills the
even intersection. The remaining two-subgroup has order two, and its factor
five centralizer forces a transposition. Perfectness puts the seed in the
alternating group on the six fixed letters; centralizer control makes it
normal there, contradicting its A5 two-core quotient.

Source: the A8 case of Aschbacher--Smith C.4.8 and 12.7.5, printed pp.153--154
and 840. No Sylow-containment or permutation-module recognition is assumed.
-/

public noncomputable section
open Subgroup Equiv Equiv.Perm Theory.GroupTheory
namespace Theory.SpecificGroups.SymmetricEight.NormalFiveSeed
local notation "S" => Perm (Fin 8)
local notation "A" => alternatingGroup (Fin 8)
local notation "E" => (A ⊓
  (MulAction.stabilizer S (0 : Fin 8) ⊓ MulAction.stabilizer S (1 : Fin 8)) : Subgroup S)

private theorem evenPair_simple : IsSimpleGroup E := by
  classical
  let s : Finset (Fin 8) := Finset.univ \ {0,1}
  let f : alternatingGroup s →* S := (A).subtype.comp (alternatingGroup.ofSubtype s)
  have hf : Function.Injective f :=
    (A).subtype_injective.comp alternatingGroup.ofSubtype_injective
  have hr : f.range ≤ E := by
    rintro _ ⟨g,rfl⟩
    refine ⟨(alternatingGroup.ofSubtype s g).property,?_,?_⟩
    · exact Perm.ofSubtype_apply_of_not_mem _ (by simp [s])
    · exact Perm.ofSubtype_apply_of_not_mem _ (by simp [s])
  have hs : Nat.card s = 6 := by rw [Nat.card_eq_fintype_card]; decide
  let : Nontrivial s := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have he : f.range = E := by
    apply eq_of_le_of_card_ge hr
    rw [ComponentMarking.card_evenPairFixer,
      ←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,nat_card_alternatingGroup,hs]
    norm_num [Nat.factorial]
  let : IsSimpleGroup (alternatingGroup s) := alternatingGroup.isSimpleGroup (by omega)
  exact ((MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr he)).symm.isSimpleGroup

private theorem no_normal_seed_in_evenPair (P : Subgroup S) [Group.IsPerfect P]
    (a : P ⧸ pCore 2 P ≃* alternatingGroup (Fin 5))
    (hPA : P ≤ A) (hPc : P ≤ centralizer ({swap (0 : Fin 8) 1} : Set S))
    (hEP : E ≤ normalizer (P : Set S)) : False := by
  have hPE : P ≤ E := le_inf hPA (ComponentMarking.perfect_le_pairFixer P hPc)
  let I := P.subgroupOf E
  let : I.Normal := (normal_subgroupOf_iff_le_normalizer hPE).mpr hEP
  let : IsSimpleGroup E := evenPair_simple
  have hp : P ≠ ⊥ := by
    intro hp
    have hd := card_quotient_dvd_card (pCore 2 P)
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,hp,card_bot] at hd
    norm_num [Nat.factorial] at hd
  have hI : I = ⊤ := (inferInstance : I.Normal).eq_bot_or_eq_top.resolve_left (by
    intro hb
    have hh := congrArg (map (E).subtype) hb
    rw [map_subgroupOf_eq_of_le hPE,Subgroup.map_bot] at hh
    exact hp hh)
  have he : P = E := le_antisymm hPE (subgroupOf_eq_top.mp hI)
  let : IsSimpleGroup P := (MulEquiv.subgroupCongr he).isSimpleGroup
  have hc : pCore 2 P = ⊥ := (inferInstance : (pCore 2 P).Normal).eq_bot_or_eq_top.resolve_right (by
    intro ht
    have hh := Nat.card_congr a.toEquiv
    rw [ht,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh)
  have hh := Nat.card_congr a.toEquiv
  rw [hc,Nat.card_congr (QuotientGroup.quotientBot (G := P)).toEquiv,he,
    ComponentMarking.card_evenPairFixer,nat_card_alternatingGroup] at hh
  norm_num [Nat.factorial] at hh

private theorem involution_swap (z : S) (hz : z ^ 2 = 1) (hne : z ≠ 1)
    (h5 : 5 ∣ Nat.card (centralizer ({z} : Set S))) : z.IsSwap := by
  have ht := cycleType_of_pow_prime_eq_one hz
  have hs := z.support.card_le_univ
  have hs' := z.sum_cycleType
  rw [ht,Multiset.sum_replicate] at hs'
  have hp : 0 < z.cycleType.card := by
    apply Nat.pos_of_ne_zero
    intro hh
    exact hne (cycleType_eq_zero.mp (Multiset.card_eq_zero.mp hh))
  have hb : z.cycleType.card ≤ 4 := by
    simp only [Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at hs hs'
    omega
  have h1 : z.cycleType.card = 1 := by
    rw [nat_card_centralizer,ht] at h5
    interval_cases hh : z.cycleType.card <;>
      first | rfl | norm_num [Nat.factorial] at h5
  apply isSwap_iff_cycleType.mpr
  rw [ht,h1]
  rfl

/-- The original normal A5 seed is incompatible with even-centralizer
control of any nontrivial permutation two-subgroup. -/
theorem no_normal_five_seed
    (Q P : Subgroup S) [Group.IsPerfect P]
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥) (hPA : P ≤ A)
    (a : P ⧸ pCore 2 P ≃* alternatingGroup (Fin 5))
    (hPQ : P ≤ normalizer (Q : Set S))
    (hcontrol : A ⊓ centralizer (Q : Set S) ≤ normalizer (P : Set S)) : False := by
  have h5 : 5 ∣ Nat.card P := by
    have hd := card_quotient_dvd_card (pCore 2 P)
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
    exact (by decide : 5 ∣ 60).trans hd
  have he : Q.subgroupOf A = ⊥ := by
    by_contra he
    apply AlternatingSixNormalizer.eight_five_not_dvd_normalizer _ hQ.comap_subtype he
    have hPN : P.subgroupOf A ≤ normalizer (Q.subgroupOf A : Set A) := by
      intro x hx
      apply mem_normalizer_iff.mpr
      intro y
      exact mem_normalizer_iff.mp (hPQ hx) y.val
    have hc : Nat.card (P.subgroupOf A) = Nat.card P :=
      Nat.card_congr (subgroupOfEquivOfLe hPA).toEquiv
    exact (hc.symm ▸ h5).trans (card_dvd_of_le hPN)
  have hcard : Nat.card Q = 2 := by
    let f := sign.comp Q.subtype
    have hf : Function.Injective f := by
      apply (MonoidHom.ker_eq_bot_iff f).mp
      apply bot_unique
      intro x hx
      apply Subtype.ext
      have hxA : (x : S) ∈ A := mem_alternatingGroup.mpr hx
      have hh : (⟨x,hxA⟩ : A) ∈ Q.subgroupOf A := x.property
      rw [he] at hh
      exact congrArg (fun y : A => y.val) (mem_bot.mp hh)
    have hl := Nat.card_le_card_of_injective f hf
    have hn : 1 < Nat.card Q := Finite.one_lt_card_iff_nontrivial.mpr
      ((nontrivial_iff_ne_bot Q).mpr hne)
    have hc : Nat.card (ℤˣ) = 2 := by simp [Nat.card_eq_fintype_card]
    rw [hc] at hl
    omega
  obtain ⟨z,hz,hall⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hcard
  have hz0 : (z : S) ≠ 1 := fun hh => hz (Subtype.ext hh)
  have hz2 : (z : S) ^ 2 = 1 := by
    have hh : z ^ Nat.card Q = 1 := pow_card_eq_one'
    rw [hcard] at hh
    exact congrArg Subtype.val hh
  have hNC : normalizer (Q : Set S) ≤ centralizer ({(z : S)} : Set S) :=
    (normalizer_le_centralizer_of_card_two Q hcard).trans
      (centralizer_le (Set.singleton_subset_iff.mpr z.property))
  have hswap := involution_swap z hz2 hz0 (h5.trans (card_dvd_of_le (hPQ.trans hNC)))
  have hconj : IsConj (z : S) (swap (0 : Fin 8) 1) := by
    apply isConj_iff_cycleType_eq.mpr
    exact (isSwap_iff_cycleType.mp hswap).trans
      (isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide))).symm
  obtain ⟨c,hc⟩ := isConj_iff.mp hconj
  let e := MulAut.conj c
  let P' := P.map e.toMonoidHom
  let : Group.IsPerfect P' := Group.IsPerfect.map _
  let d := e.subgroupMap P
  let a' := (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans a
  apply no_normal_seed_in_evenPair P' a'
  · have hh := map_mono (f := e.toMonoidHom) hPA
    rwa [show (A).map e.toMonoidHom = A from Normal.map_conj_eq A c] at hh
  · rintro _ ⟨x,hx,rfl⟩
    have hxz := mem_centralizer_singleton_iff.mp (hNC (hPQ hx))
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg e hxz
    simpa only [map_mul,MulEquiv.coe_toMonoidHom,show e z = swap (0 : Fin 8) 1 from hc] using hh
  · intro g hg
    have hm : e.symm g ∈ A ⊓ centralizer (Q : Set S) := by
      refine ⟨(inferInstance : (A).Normal).conj_mem g hg.1 c⁻¹,?_⟩
      apply mem_centralizer_iff.mpr
      intro q hq
      by_cases hq1 : q = 1
      · rw [hq1]; simp
      · have heq : q = z := congrArg Subtype.val
          (hall ⟨q,hq⟩ (fun hh => hq1 (congrArg Subtype.val hh)))
        rw [heq]
        apply e.injective
        rw [map_mul,map_mul,e.apply_symm_apply,show e z = swap (0 : Fin 8) 1 from hc]
        have hcomm : g * swap (0 : Fin 8) 1 = swap 0 1 * g := by
          rw [mul_swap_eq_swap_mul,show g 0 = 0 from hg.2.1,show g 1 = 1 from hg.2.2]
        exact hcomm.symm
    exact (P.le_normalizer_map e.toMonoidHom)
      ⟨e.symm g,hcontrol hm,e.apply_symm_apply g⟩

end Theory.SpecificGroups.SymmetricEight.NormalFiveSeed
