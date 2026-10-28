module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.TIAction
public import Theory.GroupAction.KleinFourFactorization
public import Theory.GroupTheory.CentralizerOddCore

/-!
# Odd cores in the diagonal-outer branch

A TI four-group centralizes every odd-order subgroup it normalizes.
For each nonidentity actor, its fixed subgroup has odd order and is
therefore two-perfect. Assertion (*) makes that fixed subgroup centralize
the whole four-group. Coprime three-fixed-subgroup factorization then
makes the entire odd group centralize it.

Applied to the odd core of the graph-field involution centralizer, this
puts that core inside `N_G(V₁) = I`. Normality is used only in the element
centralizer: the odd core is not assumed normal in the ambient group.
Source: Aschbacher--Smith 15.3.38, combined manuscript of 1 March 2004,
printed p.1137, the paragraph following assertion (*). The factorization
uses the valid generation assertion of A.1.17, not its invalid direct-sum
clause (see `docs/quasithin-proof-basis.md`).
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter

open Subgroup CFSG.Quasithin.ChapterI.Section06To08

variable {G : Type*} [Group G]

private theorem twoPerfect_of_odd_card {H : Type*} [Group H] [Finite H]
    (hH : Odd (Nat.card H)) : IsPPerfect 2 H := by
  intro N hN hp
  let : N.Normal := hN
  rcases hp.card_eq_or_dvd with he | hd
  · apply index_eq_one.mp
    rw [index_eq_card, he]
  · have hi : 2 ∣ Nat.card H := hd.trans (by
      rw [← index_eq_card]
      exact N.index_dvd_card)
    exact (hH.not_two_dvd_nat hi).elim

/-- A TI four-group has trivial action on any invariant odd-order subgroup. -/
theorem centralizes_odd_of_normalizes [Finite G]
    (V F : Subgroup G) [IsKleinFour V] (hV : IsTISubgroup V)
    (hF : Odd (Nat.card F)) (hnorm : V ≤ normalizer (F : Set G)) :
    V ≤ centralizer (F : Set G) := by
  classical
  let : IsMulCommutative V := IsKleinFour.isMulCommutative
  let : Fintype V := Fintype.ofFinite V
  have hthree : 3 ≤ ENat.card V := by
    rw [ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card, IsKleinFour.card_four]
    decide
  obtain ⟨a, ha, _⟩ := ENat.exists_ne_ne_of_three_le hthree (1 : V) 1
  obtain ⟨b, hb, hba⟩ := ENat.exists_ne_ne_of_three_le hthree (1 : V) a
  have hab : a * b ≠ 1 := by
    intro he
    apply hba
    have hh := congrArg (fun x : V => a * x) he
    simpa only [← mul_assoc, IsKleinFour.mul_self, one_mul, mul_one] using hh
  let ρ : V →* MulAut F := F.normalizerMonoidHom.comp (inclusion hnorm)
  have hinv (c : V) : Function.Involutive (ρ c) := by
    intro x
    have hc : c * c = 1 := IsKleinFour.mul_self c
    change (ρ c * ρ c) x = x
    rw [← map_mul, hc, map_one]
    rfl
  have hcomm : Commute (ρ a) (ρ b) := by
    have hab' : a * b = b * a := IsMulCommutative.is_comm.comm a b
    change ρ a * ρ b = ρ b * ρ a
    rw [← map_mul, ← map_mul, hab']
  have hfixed (c : V) (hc : c ≠ 1) (x : F) (hx : ρ c x = x) :
      (x : G) ∈ centralizer (V : Set G) := by
    let K := F ⊓ centralizer ({(c : G)} : Set G)
    have hK : Odd (Nat.card K) := hF.of_dvd_nat (card_dvd_of_le (inf_le_left : K ≤ F))
    have hcK : (c : G) ∈ centralizer (K : Set G) := by
      intro k hk
      exact mem_centralizer_singleton_iff.mp hk.2
    have hVK := centralizes_of_twoPerfect_fixed V K hV (twoPerfect_of_odd_card hK)
      c.property (fun he => hc (Subtype.ext he)) hcK
    apply le_centralizer_iff.mp hVK
    refine ⟨x.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have he : (c : G) * (x : G) * (c : G)⁻¹ = x := congrArg Subtype.val hx
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  apply le_centralizer_iff.mpr
  intro x hx
  obtain ⟨x₀, x₁, x₂, h₀, h₁, h₂, he⟩ :=
    MulAut.exists_fixed_mul_fixed_mul_fixed_of_odd_card hF (ρ a) (ρ b)
      (hinv a) (hinv b) hcomm (⟨x, hx⟩ : F)
  have h₂' : ρ (a * b) x₂ = x₂ := by simpa only [map_mul] using h₂
  have hm := (centralizer (V : Set G)).mul_mem
    ((centralizer (V : Set G)).mul_mem (hfixed a ha x₀ h₀) (hfixed b hb x₁ h₁))
    (hfixed (a * b) hab x₂ h₂')
  have hxEq : x = (x₀ : G) * (x₁ : G) * (x₂ : G) := congrArg Subtype.val he
  rwa [← hxEq] at hm


/-- The odd core of a centralizing element's centralizer lies in the normalizer
of the TI four-group. -/
theorem centralizer_oddCore_le [Finite G]
    (V I : Subgroup G) [IsKleinFour V] (hV : IsTISubgroup V)
    (hI : I = normalizer (V : Set G)) {w : G}
    (hw : w ∈ centralizer (V : Set G)) :
    (pPrimeCore 2 (centralizer ({w} : Set G))).map
      (centralizer ({w} : Set G)).subtype ≤ I := by
  let C := centralizer ({w} : Set G)
  let R := (pPrimeCore 2 C).map C.subtype
  have hodd : Odd (Nat.card R) := by
    have he := (pPrimeCore 2 C).equivMapOfInjective C.subtype C.subtype_injective
    rw [← Nat.card_congr he.toEquiv]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hn : V ≤ normalizer (R : Set G) := by
    apply le_trans _ (normalizer_le_normalizer_pPrimeCore_centralizer 2 w)
    apply le_trans _ (centralizer_le_normalizer (zpowers w : Set G))
    rw [zpowers_eq_closure, centralizer_closure]
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (hw a ha)
  have hc : R ≤ centralizer (V : Set G) :=
    le_centralizer_iff.mp (centralizes_odd_of_normalizes V R hV hodd hn)
  exact hc.trans (hI ▸ centralizer_le_normalizer (V : Set G))

/-- After containment in `I` is proved, normality inside `C_G(w)` puts its
odd core in the odd core of `C_I(w)`. No ambient normality is assumed. -/
theorem centralizer_oddCore_le_local_oddCore [Finite G] (V I : Subgroup G) [IsKleinFour V]
    (hV : IsTISubgroup V) (hI : I = normalizer (V : Set G)) {w : G}
    (hw : w ∈ centralizer (V : Set G)) :
    (pPrimeCore 2 (centralizer ({w} : Set G))).map
      (centralizer ({w} : Set G)).subtype ≤
    (pPrimeCore 2 ↥(I ⊓ centralizer ({w} : Set G))).map
      (I ⊓ centralizer ({w} : Set G)).subtype := by
  let C := centralizer ({w} : Set G)
  let D := I ⊓ C
  let R := (pPrimeCore 2 C).map C.subtype
  have hRI : R ≤ I := centralizer_oddCore_le V I hV hI hw
  have hRD : R ≤ D := le_inf hRI (map_subtype_le _)
  have hn : (R.subgroupOf D).Normal := by
    have he : R.subgroupOf D = (pPrimeCore 2 C).comap (inclusion inf_le_right) := by
      ext x
      change (x : G) ∈ R ↔ (⟨(x : G), x.property.2⟩ : C) ∈ pPrimeCore 2 C
      constructor
      · rintro ⟨a, ha, he⟩
        have ha' : a = (⟨(x : G), x.property.2⟩ : C) := Subtype.ext he
        exact ha' ▸ ha
      · intro hx
        exact mem_map.mpr ⟨⟨x, x.property.2⟩, hx, rfl⟩
    rw [he]
    infer_instance
  have hc : Nat.Coprime 2 (Nat.card (R.subgroupOf D)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hRD).toEquiv]
    rw [card_map_of_injective C.subtype_injective]
    exact pPrimeCore_coprime_card
  have hl : R.subgroupOf D ≤ pPrimeCore 2 D := le_sSup ⟨hn, hc⟩
  change R ≤ (pPrimeCore 2 D).map D.subtype
  rw [← map_subgroupOf_eq_of_le hRD]
  exact map_mono hl

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
