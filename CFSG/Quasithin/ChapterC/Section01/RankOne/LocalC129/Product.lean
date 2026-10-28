module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.LocalC129.A7Control
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.Product

/-!
# The ordered χ₀ decomposition in the local C(G,T) theorem

Take all actual moved χ-blocks outside M. Sylow conjugation preserves this
family because T≤M; the two-conjugate bound makes its full join normal.
The earlier C.1.28 outside-block theorem makes that join supplement M.
The C.1.9 commutation theorem gives the literal ordered factorization, and
the odd three-rank bound gives at most two factors. The ordinary A₇ source
argument proves that every factor outside M is χ₀.

The sole independent earlier-source parameter is the universal C.1.28
outside-block implication. It is owned by ChiProduct and must be discharged
there in final assembly; no decomposition or model certificate is assumed.
Source: C.1.29, printed p.134.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.LocalC129
universe u
variable {G : Type u} [Group G] [Finite G] {C : GroupClass.{u}}

/-- C.1.29's ordered decomposition, assuming only the independently owned
universal C.1.28 outside-block implication. The factors are actual χ₀-blocks
outside M, and their original J(T)-movement is retained. -/
theorem ordered_chiZero_product_of_c128_outside
    (outside : ∀ {A : Type u} [Group A] [Finite A], IsSQTK C A →
      generalizedFitting A = pCore 2 A → ∀ (S : Sylow 2 A) (N : Subgroup A),
      (S : Subgroup A).characteristicNormalizerClosure ≤ N → N ≠ ⊤ →
      ∃ L : Subgroup A, ¬L ≤ N ∧ IsChiBlockIn L ∧
        L = ⁅L, elementaryAbelianMaxJ (S : Subgroup A)⁆)
    (hG : IsSQTK C G) (hf : generalizedFitting G = pCore 2 G)
    (T : Sylow 2 G) (M : Subgroup G)
    (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) :
    ∃ r : ℕ, r ≤ 2 ∧ ∃ L : Fin r → Subgroup G,
      (∀ i, IsChiZeroBlockIn (L i)) ∧ (∀ i, ¬L i ≤ M) ∧
      (∀ i, L i = ⁅L i, elementaryAbelianMaxJ (T : Subgroup G)⁆) ∧
      ∀ g : G, ∃ m : M, ∃ b : ∀ i, L i,
        g = (m : G) * (List.ofFn (fun i => (b i : G))).prod := by
  classical
  have hTM : (T : Subgroup G) ≤ M := by
    by_cases ht : (T : Subgroup G) = ⊥
    · rw [ht]; exact bot_le
    · exact (T : Subgroup G).le_normalizer.trans
        ((normalizer_le_characteristicNormalizerClosure_self _ ht).trans hcpu)
  have hr : primeRank 3 G ≤ 2 := hG.stronglyQuasithin 3 Nat.prime_three (by decide)
  let I := {L : Subgroup G // IsChiBlockIn L ∧
    L = ⁅L, elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧ ¬L ≤ M}
  let : Fintype I := Fintype.ofFinite I
  let r := Fintype.card I
  let e : I ≃ Fin r := Fintype.equivFin I
  let L : Fin r → Subgroup G := fun i => (e.symm i).val
  have hL (i) : IsChiBlockIn (L i) := (e.symm i).property.1
  have hm (i) : L i = ⁅L i, elementaryAbelianMaxJ (T : Subgroup G)⁆ :=
    (e.symm i).property.2.1
  have hout (i) : ¬L i ≤ M := (e.symm i).property.2.2
  have hi : Function.Injective L := fun i j hij => e.symm.injective (Subtype.ext hij)
  have hguard := RankOne.ChiProduct.blockCommutationHypothesis_of_fitting hf
  have hr' : r ≤ 2 := by
    have hh := (RankOne.ChiProduct.card_le_threeRank hguard L hi hL).trans hr
    simpa only [Fintype.card_fin] using hh
  let X := ⨆ i, L i
  have hmem {B : Subgroup G} (hB : IsChiBlockIn B)
      (hb : B = ⁅B, elementaryAbelianMaxJ (T : Subgroup G)⁆) (hn : ¬B ≤ M) : B ≤ X := by
    let b : I := ⟨B, hB, hb, hn⟩
    have he : L (e b) = B := by dsimp [L]; rw [e.symm_apply_apply]
    exact he ▸ le_iSup L (e b)
  let Y : Fin r → Subgroup G := fun i => conjugateSpanBy (L i) (T : Subgroup G)
  let (i : Fin r) : (Y i).Normal := conjugateSpanBy_sylow_normal (L i) T
    (RankOne.ChiProduct.normal_or_index_two hf hr (hL i))
  have hXY : X = ⨆ i, Y i := by
    apply le_antisymm
    · exact iSup_le fun i => (le_conjugateSpanBy (L i) _).trans (le_iSup Y i)
    · apply iSup_le
      intro i
      change conjugateSpanBy (L i) (T : Subgroup G) ≤ X
      rw [conjugateSpanBy_eq_iSup_conj]
      apply iSup_le
      intro t
      apply hmem (RankOne.ChiProduct.chi_map_equiv (MulAut.conj (t : G)) (hL i))
        (RankOne.ChiProduct.moved_conjugate _ (hm i) t)
      intro hle
      apply hout i
      intro x hx
      have hxM := hle (mem_map_of_mem (MulAut.conj (t : G)).toMonoidHom hx)
      have htM := hTM t.property
      have hh := M.mul_mem (M.mul_mem (M.inv_mem htM) hxM) htM
      change (t : G)⁻¹ * ((t : G) * x * (t : G)⁻¹) * (t : G) ∈ M at hh
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  let : X.Normal := by rw [hXY]; infer_instance
  have hgen : M ⊔ X = ⊤ := by
    by_contra hn
    obtain ⟨B, hb, hB, hmB⟩ := outside hG hf T (M ⊔ X) (hcpu.trans le_sup_left) hn
    exact hb ((hmem hB hmB (fun hh => hb (hh.trans le_sup_left))).trans le_sup_right)
  have hc : Pairwise fun i j => L i ≤ centralizer (L j : Set G) :=
    fun i j hij => commutator_eq_bot_iff_le_centralizer.mp
      (blocks_commute hguard (hL i).1 (hL j).1 (fun he => hij (hi he)))
  have hz (i) : IsChiZeroBlockIn (L i) := by
    rcases chi_zero_or_alternating_seven_in hG.stronglyQuasithin (hL i) with hh | hh
    · exact hh
    · exact False.elim (hout i ((alternating_seven_le_control_of_c128_outside outside
        hG hf T (hL i).1 hh.2).trans hcpu))
  refine ⟨r, hr', L, hz, hout, hm, fun g => ?_⟩
  obtain ⟨m, hmM, x, hx, he⟩ := mem_sup_of_normal_right.mp
    (show g ∈ M ⊔ X by rw [hgen]; exact mem_top g)
  obtain ⟨b, hb⟩ := RankOne.ChiProduct.ordered_product_of_mem_iSup L hc hx
  exact ⟨⟨m, hmM⟩, b, he.symm.trans (congrArg (fun x => m * x) hb)⟩
end CFSG.Quasithin.ChapterC.LocalC129
