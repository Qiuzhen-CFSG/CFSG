module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSevenCentralizers
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Parameter
public import Theory.GroupAction.SolvablePrimitiveRegular
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimeDegree
public import Theory.GroupTheory.SolvableSylowControl.AbelianProduct

/-!
# The full symmetric-seven Cartan bound

An odd abelian Sylow permuter generates a solvable subgroup with that Sylow.
If seven divided its order, its prime-degree action would have a normal
regular subgroup of order seven, bounding the whole order by 42. The full
Sylow has order sixteen, contradicting divisibility by 112. The remaining
cyclic orders exclude every exponent above two in the literal E.3.37
parameter, including its Sylow permutation clause.

The chosen-orbit application is in NonFFSourceDoubledSevenGeneration.
Source: Aschbacher--Smith Table 7.2.1 and 7.3.4, printed pp.698--699;
E.3.37, printed p.239. The regular-action lemmas retain their original
ATLAS attribution in the imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterE.Section06.FixedPointBounds
local notation "S7" => Equiv.Perm (Fin 7)

private theorem solvable_seven_free (P : Sylow 2 S7) (H : Subgroup S7)
    (hPH : (P : Subgroup S7) ≤ H) (hs : Group.IsSolvable H) : ¬ 7 ∣ Nat.card H := by
  intro hd
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let := hs
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 7 hd
  let C : Subgroup H := zpowers x
  have hc : Nat.card C = 7 := by rw [Nat.card_zpowers,hx]
  let : MulAction.IsPretransitive C (Fin 7) :=
    Atlas.GroupTheory.prime_subgroup_pretransitive 7 (by simp) C hc
  let : MulAction.IsPretransitive H (Fin 7) := ⟨fun a b => by
    obtain ⟨c,hc⟩ := MulAction.exists_smul_eq C a b
    exact ⟨c.val,hc⟩⟩
  let : MulAction.IsPreprimitive H (Fin 7) :=
    MulAction.IsPreprimitive.of_prime_card (by norm_num)
  obtain ⟨A,hAc,hAb,hA,hr,_⟩ :=
    MulAction.exists_characteristic_abelian_regular (G := H) (0 : Fin 7)
  let := hAc
  let := hAb
  let f : A → Fin 7 := fun a => (a : H) • (0 : Fin 7)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      obtain ⟨c,_,hu⟩ := hr 0 (f a)
      exact (hu a rfl).trans (hu b hab.symm).symm
    · intro i
      obtain ⟨a,ha,_⟩ := hr 0 i
      exact ⟨a,ha⟩
  have hcard : Nat.card A = 7 := (Nat.card_congr (Equiv.ofBijective f hf)).trans (by simp)
  let : MulAction.IsPretransitive A (Fin 7) := ⟨fun a b => by
    obtain ⟨c,hc,_⟩ := hr a b
    exact ⟨c,hc⟩⟩
  have hbound := Atlas.GroupTheory.prime_normalizer_card_bound (G := H) A (0 : Fin 7)
    7 hcard (by simp)
  rw [A.normalizer_eq_top,card_top] at hbound
  have hP : Nat.card P = 16 := by
    rw [P.card_eq_multiplicity]
    rw [show Nat.card S7 = 5040 by
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]]
    rw [show 5040 = 2 ^ 4 * 315 by decide,
      Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow,
      Nat.prime_two.factorization]
    norm_num [Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 315)]
  have h16 : 16 ∣ Nat.card H := hP ▸ card_dvd_of_le hPH
  have h112 : 112 ∣ Nat.card H := (show Nat.Coprime 16 7 by decide).mul_dvd_of_dvd_of_dvd h16 hd
  have hlo := Nat.le_of_dvd (Nat.card_pos (α := H)) h112
  omega

/-- The literal Cartan parameter of the full seven-letter automizer is at most two. -/
theorem doubledSeven_nPrime_le_two : nPrime S7 ≤ 2 := by
  apply nPrime_le_iff.mpr
  intro c w
  let := w.abelian
  let := w.cyclic
  let H : Subgroup S7 := w.abelianGroup ⊔ (w.sylow : Subgroup S7)
  have hs : Group.IsSolvable H := solvable_of_odd_abelian_permuting_two_subgroup
    w.abelianGroup w.sylow w.odd w.sylow.isPGroup' w.permutes
  have h7 : ¬ 7 ∣ Nat.card w.cyclicGroup := fun hd =>
    solvable_seven_free w.sylow H le_sup_right hs
      (hd.trans (card_dvd_of_le (w.cyclic_le.trans le_sup_left)))
  obtain ⟨x,hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := w.cyclicGroup)
  have horder : orderOf (x : S7) = 2 ^ c - 1 := (Subgroup.orderOf_coe x).trans (hx.trans w.card)
  have hd : 2 ^ c - 1 ∣ 5040 := by
    have hd := w.cyclicGroup.card_subgroup_dvd_card
    rw [w.card] at hd
    norm_num only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,Nat.factorial] at hd
    exact hd
  have hpow : 2 ^ c - 1 ≤ 5040 := Nat.le_of_dvd (by decide) hd
  have hc : c ≤ 12 := by
    by_contra hn
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 13 ≤ c by omega)
    norm_num at hh
    omega
  have hcases : c ≤ 2 ∨ c = 3 ∨ c = 4 ∨ c = 6 :=
    (by decide : ∀ c : Fin 13, 2 ^ c.val - 1 ∣ 5040 →
      c.val ≤ 2 ∨ c.val = 3 ∨ c.val = 4 ∨ c.val = 6) ⟨c,by omega⟩ hd
  rcases hcases with hc | rfl | rfl | rfl
  · exact hc
  · exact (h7 (w.card ▸ (by decide))).elim
  · exact (doubledSeven_no_fifteen x horder).elim
  · exact (h7 (w.card ▸ (by decide))).elim

/-- Faithful transport of the complete Cartan witness to the original
whole-orbit automizer, with its actual Sylow subgroup retained. -/
theorem doubledSeven_faithful_cartan_bound
    {G : Type*} [Group G] [Finite G] (W M : Subgroup G)
    (hM : M = normalizer (W : Set G))
    (e : ChapterE.Automizer W ≃* S7) {c : ℕ} (w : NPrimeWitness M c)
    (hfaith : w.cyclicGroup.map M.subtype ⊓ centralizer (W : Set G) = ⊥) : c ≤ 2 := by
  subst M
  have hb : c ≤ nPrime (ChapterE.Automizer W) :=
    (w.map W.normalizerMonoidHom.rangeRestrict
      W.normalizerMonoidHom.rangeRestrict_surjective (by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        apply bot_unique
        intro x hx
        have he : W.normalizerMonoidHom (x : normalizer (W : Set G)) = 1 :=
          congrArg Subtype.val hx
        have hc : ((x : normalizer (W : Set G)) : G) ∈ centralizer (W : Set G) := by
          change (x : normalizer (W : Set G)) ∈ W.normalizerMonoidHom.ker at he
          rwa [normalizerMonoidHom_ker] at he
        have hone : ((x : normalizer (W : Set G)) : G) = 1 :=
          mem_bot.mp (hfaith ▸ ⟨mem_map_of_mem _ x.property,hc⟩)
        exact mem_bot.mpr (Subtype.ext (Subtype.ext hone)))).le_nPrime
  rw [nPrime_eq_of_mulEquiv e] at hb
  exact hb.trans doubledSeven_nPrime_le_two

end CFSG.Quasithin.Chapter7.NormalizedSource
