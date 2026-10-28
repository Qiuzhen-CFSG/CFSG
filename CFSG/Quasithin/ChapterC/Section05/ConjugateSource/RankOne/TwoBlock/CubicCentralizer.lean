module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.Factor
public import Theory.GroupTheory.CardFourAutomorphismStabilizer

/-!
# Full centralizers for the original A₃ block

Its actual U has order four. Every actor centralizing Uˣ fixes the nontrivial
intersection U∩Uˣ. The automorphism stabilizer of that point has order at most
two, while Uˣ already supplies a nontrivial action. Thus it supplies the entire
image, giving the same mutual-centralizer supplement as in the natural case.

Source: Aschbacher–Smith, C.5.6(7), printed pp.159–160.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

omit [Finite G] in
theorem Setup.cubic_module_card (_h : Setup R K F) (hA : IsAlternatingBlock K 3) : Nat.card (U K) = 4 := by
  have hz : blockFixed K = ⊥ := alternatingThreeCoverInput K hA
  have hq : Function.Bijective (QuotientGroup.mk' (blockFixed K)) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk',hz]),QuotientGroup.mk'_surjective _⟩
  have hc := hA.module_card_odd (by decide : Odd 3)
  rw [U,card_map_of_injective K.subtype_injective,
    Nat.card_congr (MulEquiv.ofBijective _ hq).toEquiv]
  simpa using hc

theorem Setup.cubic_full_centralizer_le
    (h : Setup R K F) (hA : IsAlternatingBlock K 3)
    {x : G} (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (hNK : R ⊓ centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤ normalizer (K : Set G)) :
    R ⊓ centralizer ((U K).map (MulAut.conj x⁻¹).toMonoidHom : Set G) ≤
      (U K).map (MulAut.conj x⁻¹).toMonoidHom ⊔ (R ⊓ centralizer (U K : Set G)) := by
  let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  let P := R ⊓ centralizer (V : Set G)
  let N := normalizer (U K : Set G)
  let a := (U K).normalizerMonoidHom
  have hVN : V ≤ N := (h.conjugate_le hx).trans h.coordinates.normalizes
  have hPN : P ≤ N := hNK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hJ : V ⊔ P ≤ N := sup_le hVN hPN
  have hne : U K ⊓ V ≠ ⊥ := by
    intro he
    have hc := (h.commutator_eq_fixed hx hnc).2.trans he
    exact hnc (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
  let : Nontrivial ↥(U K ⊓ V) := ((U K ⊓ V).nontrivial_iff_ne_bot).mpr hne
  obtain ⟨z,hz,hzne⟩ := (U K ⊓ V).exists_ne_one_of_nontrivial
  let z₀ : U K := ⟨z,hz.1⟩
  have hz₀ : z₀ ≠ 1 := fun he => hzne (congrArg Subtype.val he)
  let := h.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hfix : V ⊔ P ≤ centralizer ({z} : Set G) := by
    apply sup_le
    · intro v hv
      exact mem_centralizer_singleton_iff.mpr (le_centralizer V hv z hz.2).symm
    · rintro p ⟨_,hp⟩
      exact mem_centralizer_singleton_iff.mpr (hp z hz.2).symm
  let J := ((V ⊔ P).subgroupOf N).map a
  let B := (V.subgroupOf N).map a
  have hcard : Nat.card J ≤ 2 := card_mulAut_subgroup_le_two_of_fixed_point
    (h.cubic_module_card hA) z₀ hz₀ J (by
      rintro _ ⟨n,hn,rfl⟩
      apply Subtype.ext
      change (n : G) * z * (n : G)⁻¹ = z
      have he : (n : G) * z = z * (n : G) := mem_centralizer_singleton_iff.mp (hfix hn)
      rw [he,mul_inv_cancel_right])
  have hBne : B ≠ ⊥ := by
    intro he
    apply hnc
    intro v hv
    have ha : a ⟨v,hVN hv⟩ = 1 := by
      have hh : a ⟨v,hVN hv⟩ ∈ B := mem_map_of_mem a hv
      rw [he] at hh
      exact hh
    have hc : (⟨v,hVN hv⟩ : N) ∈ a.ker := ha
    rw [normalizerMonoidHom_ker] at hc
    exact hc
  have hBcard : 2 ≤ Nat.card B := by
    have hpos : 0 < Nat.card B := Nat.card_pos
    have hnot : Nat.card B ≠ 1 := fun he => hBne ((Subgroup.card_eq_one).mp he)
    omega
  have he : B = J := eq_of_le_of_card_ge (map_mono (subgroupOf_mono _ le_sup_left)) (hcard.trans hBcard)
  rintro p hp
  have hm : a ⟨p,hPN hp⟩ ∈ B := he.symm ▸ mem_map_of_mem a (mem_sup_right hp)
  obtain ⟨v,hv,he⟩ := hm
  have hk : v⁻¹ * (⟨p,hPN hp⟩ : N) ∈ a.ker := by
    change a _ = 1
    rw [map_mul,map_inv,he,inv_mul_cancel]
  rw [normalizerMonoidHom_ker] at hk
  have hc : (v : G)⁻¹ * p ∈ R ⊓ centralizer (U K : Set G) :=
    ⟨R.mul_mem (R.inv_mem ((h.conjugate_le hx).trans inf_le_left hv)) hp.1,hk⟩
  have hh : (v : G) * ((v : G)⁻¹ * p) ∈ V ⊔ (R ⊓ centralizer (U K : Set G)) :=
    mul_mem_sup hv hc
  simpa only [mul_inv_cancel_left] using hh
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
