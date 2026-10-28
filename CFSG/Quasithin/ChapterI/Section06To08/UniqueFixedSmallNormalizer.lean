module

public import CFSG.Quasithin.ChapterI.Section06To08.UniqueFixedSource
public import BenderSuzuki.SE.SmallBorel

/-!
# The order-48 unique-fixed-coset recognition

For a proper subgroup M of order 48 and a normal elementary four-group V,
the original I.8.5 unique-fixed-coset hypotheses identify the normal closure
of V with A5. I.8.5 gives a central odd cover of a simple Bender model.
The quotient Borel has order at most 48, hence the model is A5 and its Borel
has order 12. Its full preimage lies in M, so the odd center has order
dividing 4 and is trivial.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
I.8.5 (printed p.430) and its ordinary unitary application F.4.42.
This discharges the Bender-model and odd-cover recognition in that application.
-/

noncomputable section
open Subgroup

namespace CFSG.Quasithin.ChapterI.Section06To08
open Theory.GroupTheory BenderSuzuki

public theorem normalClosure_alternating_five_of_card_fortyEight
    {G : Type*} [Group G] [Finite G]
    (V M : Subgroup G) [IsElementaryAbelian 2 V] [(V.subgroupOf M).Normal]
    (hVM : V ≤ M) (hV : Nat.card V = 4) (hM : Nat.card M = 48)
    (hproper : M ≠ ⊤)
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q) :
    Nonempty (normalClosure (V : Set G) ≃* alternatingGroup (Fin 5)) := by
  have hVne : V ≠ ⊥ := by intro h; rw [h, card_bot] at hV; omega
  rcases lemma_I_8_5_oddCore_recognition V M hVM hVne hproper hfix with
    ⟨htwo, _⟩ | ⟨_hquasi, hmodel, _hcenter, hON, hB⟩
  · omega
  · let L := normalClosure (V : Set G)
    let O := pPrimeCore 2 L
    let N := M.comap L.subtype
    let q : L →* L ⧸ O := QuotientGroup.mk' O
    let f : N →* N.map q := q.subgroupMap N
    change BenderSuzuki.IsSimpleBenderGroup (L ⧸ O) at hmodel
    change O ≤ N at hON
    change IsBorelSubgroup (N.map q) at hB
    let j : N →* M := (L.subtype.comp N.subtype).codRestrict M (by
      intro x
      exact x.property)
    have hj : Function.Injective j := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : M => (x : G)) h
    have hNdiv : Nat.card N ∣ 48 := by
      rw [← hM]
      exact card_dvd_of_injective j hj
    have hBdiv : Nat.card (N.map q) ∣ 48 := (N.card_map_dvd q).trans hNdiv
    obtain ⟨⟨e⟩, hBcard⟩ := small_borel_alternating_five hmodel (N.map q) hB
      (Nat.le_of_dvd (by decide : 0 < 48) hBdiv)
    have hker : Nat.card f.ker = Nat.card O := by
      change Nat.card (q.subgroupMap N).ker = _
      rw [ker_subgroupMap, QuotientGroup.ker_mk']
      exact Nat.card_congr (subgroupOfEquivOfLe hON).toEquiv
    have hmult : Nat.card (N.map q) * Nat.card O = Nat.card N := by
      have he := f.ker.index_mul_card
      rw [index_ker, MonoidHom.range_eq_top.mpr
        (MonoidHom.subgroupMap_surjective q N), card_top, hker] at he
      exact he
    have hO4 : Nat.card O ∣ 4 := by
      have hd : 12 * Nat.card O ∣ 12 * 4 := by
        simpa only [← hmult, hBcard] using hNdiv
      exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 12)).mp hd
    have hOone : Nat.card O = 1 := by
      apply Nat.eq_one_of_dvd_coprimes
        ((pPrimeCore_coprime_card (G := L) (p := 2)).pow_left 2) hO4
      exact dvd_refl _
    have hObot : O = ⊥ := card_eq_one.mp hOone
    have hq : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp (by
      change (QuotientGroup.mk' O).ker = ⊥
      rw [QuotientGroup.ker_mk', hObot])
    exact ⟨(MulEquiv.ofBijective q ⟨hq, QuotientGroup.mk'_surjective O⟩).trans e⟩

end CFSG.Quasithin.ChapterI.Section06To08
