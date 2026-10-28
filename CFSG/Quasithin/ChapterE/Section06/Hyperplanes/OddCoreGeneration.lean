module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Preliminaries
public import Theory.PPrimeCore
public import Theory.GroupAction.AbelianCoprimeFullFixedGeneration
public import Theory.GroupTheory.SelfCentralizingCore


/-!
# Odd-core restriction and generation

An odd core restricted to a subgroup is normal and odd there. Applied to
nested centralizers, this gives the containment used in E.6.19–21. The full
coprime fixed-point generation theorem then propagates vanishing from V and
its hyperplanes to every subspace A of V. The actor is the actual conjugation
action of V on O(C_G(A)); a cyclic actor quotient has order at most two.
Joining its kernel with A gives either a hyperplane or V.

The final conditional E.6.21 proof supplies vanishing at V from E.6.6(2)
and C_G(V) ≤ M. The E.6.20 conclusion remains an explicit input. E.6.6(2)
is expressed in the equivalent self-centralizing two-core convention.
No direct-sum assertion from the misprinted A.1.17 is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.19–21,
printed pp.252–253 (PDF pp.263–264); valid generation clause of A.1.17.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G}

/-- O(C_G(A)), embedded in G through its actual centralizer. -/
@[expose] def oddCentralizer (A : Subgroup G) : Subgroup G :=
  (pPrimeCore 2 (centralizer (A : Set G))).map (centralizer (A : Set G)).subtype

omit [Finite G] in
/-- Embedded odd-core vanishing is equivalent to intrinsic odd-core vanishing. -/
theorem oddCentralizer_eq_bot_iff (A : Subgroup G) :
    oddCentralizer A = ⊥ ↔ pPrimeCore 2 (centralizer (A : Set G)) = ⊥ := by
  constructor
  · intro h
    exact Subgroup.map_injective (centralizer (A : Set G)).subtype_injective
      (by simpa only [oddCentralizer, Subgroup.map_bot] using h)
  · intro h
    simp only [oddCentralizer, h, Subgroup.map_bot]

private theorem oddCore_inter_le {H K : Subgroup G} (hKH : K ≤ H) :
    (pPrimeCore 2 H).map H.subtype ⊓ K ≤ (pPrimeCore 2 K).map K.subtype := by
  let f : K →* H := inclusion hKH
  let N := (pPrimeCore 2 H).comap f
  have hN : N ≤ pPrimeCore 2 K := by
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    exact (pPrimeCore_coprime_card (p := 2) (G := H)).of_dvd_right
      (Subgroup.card_comap_dvd_of_injective (pPrimeCore 2 H) f (inclusion_injective hKH))
  rintro x ⟨⟨y, hy, rfl⟩, hx⟩
  exact ⟨⟨y, hx⟩, hN hy, rfl⟩

/-- Restriction to a smaller centralizer is normal only in that smaller centralizer. -/
theorem oddCentralizer_inter_le {A B : Subgroup G} (hAB : A ≤ B) :
    oddCentralizer A ⊓ centralizer (B : Set G) ≤ oddCentralizer B :=
  oddCore_inter_le (Subgroup.centralizer_le hAB)

omit [Finite G] in
/-- The embedded odd core lies in its defining centralizer. -/
theorem oddCentralizer_le (A : Subgroup G) :
    oddCentralizer A ≤ centralizer (A : Set G) :=
  Subgroup.map_subtype_le _

/-- Corank zero means the subspace contains V. -/
theorem corank_eq_zero_iff [IsElementaryAbelian 2 V] (A : Subgroup G) :
    subgroupCorank V A = 0 ↔ V ≤ A := by
  have hpow : A.relIndex V = 2 ^ subgroupCorank V A := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact Subgroup.relIndex_eq_two_pow_quotient_finrank V A
  constructor
  · intro h
    apply Subgroup.relIndex_eq_one.mp
    rw [hpow, h, pow_zero]
  · intro h
    simp [subgroupCorank, Subgroup.relIndex_eq_one.mpr h]

private theorem cyclic_quotient_corank_le_one [IsElementaryAbelian 2 V]
    (B : Subgroup V) (hB : IsCyclic (V ⧸ B)) :
    subgroupCorank V (B.map V.subtype) ≤ 1 := by
  let _ := hB
  have hd : Nat.card (V ⧸ B) ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 (V ⧸ B)
  have hrel : (B.map V.subtype).relIndex V = Nat.card (V ⧸ B) := by
    have hback : (B.map V.subtype).subgroupOf V = B := by
      ext v
      constructor
      · rintro ⟨w, hw, he⟩
        exact (Subtype.ext he : w = v) ▸ hw
      · intro hv
        exact ⟨v, hv, rfl⟩
    rw [Subgroup.relIndex, hback, Subgroup.index_eq_card]
  have hpow : (B.map V.subtype).relIndex V = 2 ^ subgroupCorank V (B.map V.subtype) := by
    rw [subgroupCorank_eq_quotient_finrank]
    exact Subgroup.relIndex_eq_two_pow_quotient_finrank V _
  have hle := Nat.le_of_dvd (by decide : 0 < 2) hd
  rw [← hrel, hpow] at hle
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by simpa using hle)

/-- Coprime fixed-point generation extends odd-core vanishing to every subspace of V. -/
theorem oddCentralizer_eq_bot_of_corank_one [IsElementaryAbelian 2 V]
    (hzero : ∀ W : Subgroup G, W ≤ V → subgroupCorank V W ≤ 1 → oddCentralizer W = ⊥)
    {A : Subgroup G} (hAV : A ≤ V) : oddCentralizer A = ⊥ := by
  let C := centralizer (A : Set G)
  let O := pPrimeCore 2 C
  have hVC : V ≤ C := V.le_centralizer.trans (Subgroup.centralizer_le hAV)
  let f : V →* C := inclusion hVC
  let act : V →* MulAut O := (MulAut.conjNormal : C →* MulAut O).comp f
  let _ : MulDistribMulAction V O := MulDistribMulAction.compHom O act
  let _ : Fact (IsPGroup 2 V) := ⟨IsElementaryAbelian.isPGroup 2 V⟩
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup_action
    (G := O) (A := V) 2 pPrimeCore_coprime_card
  have htop : (⊤ : Subgroup O) ≤ ⊥ := by
    rw [← hgen]
    refine iSup₂_le fun B hB => ?_
    intro y hy
    let W := B.map V.subtype
    have hWV : W ≤ V := Subgroup.map_subtype_le B
    have hcor : subgroupCorank V (A ⊔ W) ≤ 1 :=
      (subgroupCorank_antitone (show W ≤ A ⊔ W from le_sup_right)).trans
        (cyclic_quotient_corank_le_one B hB)
    have hz := hzero (A ⊔ W) (sup_le hAV hWV) hcor
    have hfix : ((y : C) : G) ∈ centralizer (W : Set G) := by
      rintro w ⟨b, hb, rfl⟩
      have he := (show ∀ a : B, a • y = y from hy) ⟨b, hb⟩
      have he' : (b : G) * ((y : C) : G) * (b : G)⁻¹ = ((y : C) : G) :=
        congrArg (fun x : O => ((x : C) : G)) he
      exact mul_inv_eq_iff_eq_mul.mp he'
    have hcentral : ((y : C) : G) ∈ centralizer (↑(A ⊔ W) : Set G) := by
      have hcy : A ⊔ W ≤ centralizer ({((y : C) : G)} : Set G) := by
        apply sup_le
        · intro a ha
          exact mem_centralizer_singleton_iff.mpr (y.val.property a ha)
        · intro w hw
          exact mem_centralizer_singleton_iff.mpr (hfix w hw)
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hcy hx)
    have hm : ((y : C) : G) ∈ oddCentralizer (A ⊔ W) :=
      oddCentralizer_inter_le le_sup_left ⟨⟨y, y.property, rfl⟩, hcentral⟩
    rw [hz, mem_bot] at hm
    exact (show y = 1 from Subtype.ext (Subtype.ext hm))
  apply le_bot_iff.mp
  rintro x ⟨y, hy, rfl⟩
  have hy1 := htop (mem_top (⟨y, hy⟩ : O))
  exact congrArg (fun x : O => ((x : C) : G)) hy1

/-- E.6.21 from E.6.20 and the earlier E.6.6(2); both inputs remain explicit. -/
theorem lemma_E_6_21 [IsElementaryAbelian 2 V]
    {K : CFSG.Quasithin.GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : HypothesisE61 K T M V)
    (h6 : ∀ A : Subgroup G, A ≠ ⊥ → A ≤ M → IsPGroup 2 A →
      HasCharacteristicTwo ↥(M ⊓ centralizer (A : Set G)))
    (h20 : ∀ W : Subgroup G, W ≤ V → subgroupCorank V W = 1 → oddCentralizer W = ⊥)
    {A : Subgroup G} (_hA : A ≠ ⊥) (hAV : A ≤ V) :
    pPrimeCore 2 (centralizer (A : Set G)) = ⊥ := by
  have hCV := h6 V h.nontrivial (h.le_sylow.trans h.sylow_le)
    (IsElementaryAbelian.isPGroup 2 V)
  rw [inf_eq_right.mpr h.centralizer_le] at hCV
  have hV0 : oddCentralizer V = ⊥ := (oddCentralizer_eq_bot_iff V).mpr
    (Theory.GroupTheory.pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hCV)
  apply (oddCentralizer_eq_bot_iff A).mp
  apply oddCentralizer_eq_bot_of_corank_one (V := V) _ hAV
  intro W hWV hWc
  by_cases hW0 : subgroupCorank V W = 0
  · have hWVeq : W = V := le_antisymm hWV ((corank_eq_zero_iff W).mp hW0)
    exact hWVeq ▸ hV0
  · exact h20 W hWV (by omega)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes
