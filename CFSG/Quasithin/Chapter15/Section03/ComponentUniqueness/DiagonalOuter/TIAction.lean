module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Fusion
public import Theory.GroupTheory.SpecificGroups.KleinFourResidualAction

/-!
# TI four-groups and the graph-field nonfusion argument

These are the TI steps in Aschbacher--Smith 15.3.38, combined manuscript
of 1 March 2004, printed p.1137. Transitivity on the nonidentity elements
and control of one element centralizer imply the TI property. If a
nonidentity member of a TI four-group centralizes a two-perfect group,
the latter normalizes the four-group and fixes a point. Its action has
two-group image and is therefore trivial. This proves assertion (*),
including injectivity of the actual conjugation homomorphism.

For the graph-field involution, corrected I.6.2 makes a hypothetical fused
four-group commute with the original one. Assertion (*) makes it centralize
`F = O²(C_L(τf))`. Its action on `L` would then inject a four-group into a
centralizer image whose order is not divisible by four, which is impossible.

The normalizer/centralizer identities and the automorphism-centralizer
two-part bound are explicit inputs. They must be established for the genuine central
cover of L₃(4); these lemmas do not assert those model facts or 15.3.38.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter

open Subgroup CFSG.Quasithin.ChapterI.Section06To08

variable {G : Type*} [Group G]

/-- The TI criterion using transitivity and only one representative centralizer. -/
theorem ti_of_transitive_normalizer (V I : Subgroup G)
    (hI : I = normalizer (V : Set G)) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hCv : centralizer ({v} : Set G) ≤ I)
    (htrans : ∀ x y : G, x ∈ V → x ≠ 1 → y ∈ V → y ≠ 1 →
      ∃ m : I, (MulAut.conj (m : G)) x = y) : IsTISubgroup V := by
  apply lemma_I_6_1_1 V I hI
  · intro x hx hx1 c hc
    obtain ⟨m, hm⟩ := htrans v x hv hv1 hx hx1
    have hc' := mem_centralizer_singleton_iff.mp hc
    have hconj : (m : G)⁻¹ * c * (m : G) ∈ centralizer ({v} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have he : (m : G) * v * (m : G)⁻¹ = x := hm
      rw [← he] at hc'
      have hh := congrArg (fun a : G => (m : G)⁻¹ * a * (m : G)) hc'
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
    have hh := I.mul_mem (I.mul_mem m.property (hCv hconj)) (I.inv_mem m.property)
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hh
  · intro x y hx hy hxy
    by_cases hx1 : x = 1
    · subst x
      obtain ⟨g, hg⟩ := hxy
      have hy1 : y = 1 := by simpa using hg.symm
      exact ⟨1, by simp [hy1]⟩
    · have hy1 : y ≠ 1 := by
        obtain ⟨g, hg⟩ := hxy
        intro hy1
        have he : (MulAut.conj g) x = 1 := hg.trans hy1
        exact hx1 ((MulAut.conj g).map_eq_one_iff.mp he)
      exact htrans x y hx hx1 hy hy1

/-- Transport TI along an actual ambient group automorphism. -/
theorem ti_map (V : Subgroup G) (hV : IsTISubgroup V) (e : G ≃* G) :
    IsTISubgroup (V.map e.toMonoidHom) := by
  apply (isTISubgroup_iff _).mpr
  intro g hg x hx hconj
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
  have hgn : e.symm g ∉ normalizer (V : Set G) := by
    intro hn
    apply hg
    rw [← V.map_equiv_normalizer_eq e]
    exact mem_map.mpr ⟨e.symm g, hn, e.apply_symm_apply g⟩
  have hc : e.symm g * a * (e.symm g)⁻¹ ∈ V := by
    obtain ⟨b, hb, he⟩ := mem_map.mp hconj
    have hb' : b = e.symm g * a * (e.symm g)⁻¹ := by
      simpa using congrArg e.symm he
    exact hb' ▸ hb
  have ha1 := (isTISubgroup_iff V).mp hV (e.symm g) hgn a ha hc
  simp [ha1]

/-- A nonidentity fixed element forces a TI four-group to centralize a two-perfect group. -/
theorem centralizes_of_twoPerfect_fixed (V F : Subgroup G) [IsKleinFour V]
    (hV : IsTISubgroup V) (hF : IsPPerfect 2 F) {v : G}
    (hv : v ∈ V) (hv1 : v ≠ 1) (hvF : v ∈ centralizer (F : Set G)) :
    V ≤ centralizer (F : Set G) := by
  have hFN : F ≤ normalizer (V : Set G) := by
    intro x hx
    apply hV.centralizer_le_normalizer hv hv1
    exact mem_centralizer_singleton_iff.mpr (hvF x hx)
  let ρ : F →* MulAut V := V.normalizerMonoidHom.comp (inclusion hFN)
  have hfix : ∀ x : F, ρ x (⟨v, hv⟩ : V) = ⟨v, hv⟩ := by
    intro x
    apply Subtype.ext
    change (x : G) * v * (x : G)⁻¹ = v
    rw [hvF x x.property, mul_assoc, mul_inv_cancel, mul_one]
  have hρ := IsKleinFour.action_eq_one_of_twoPerfect_of_fixed_ne_one ρ hF
    (show (⟨v, hv⟩ : V) ≠ 1 from fun he => hv1 (congrArg Subtype.val he)) hfix
  intro a ha x hx
  have he := congrArg (fun φ : F →* MulAut V => φ ⟨x, hx⟩ ⟨a, ha⟩) hρ
  have hc : x * a * x⁻¹ = a := congrArg Subtype.val he
  exact (mul_inv_eq_iff_eq_mul).mp hc

/-- Assertion (*) in 15.3.38, expressed as triviality of the action kernel. -/
theorem faithful_of_twoPerfect_nontrivial (V F : Subgroup G) [IsKleinFour V]
    (hV : IsTISubgroup V) (hF : IsPPerfect 2 F)
    (hnontrivial : ¬ V ≤ centralizer (F : Set G)) :
    V ⊓ centralizer (F : Set G) = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  apply mem_bot.mpr
  by_contra hv1
  exact hnontrivial (centralizes_of_twoPerfect_fixed V F hV hF hv.1 hv1 hv.2)

/-- Assertion (*) for the actual conjugation action on an invariant subgroup. -/
theorem conjugation_injective_of_twoPerfect_nontrivial (V F : Subgroup G)
    [IsKleinFour V] (hV : IsTISubgroup V) (hF : IsPPerfect 2 F)
    (hVF : V ≤ normalizer (F : Set G))
    (hnontrivial : ¬ V ≤ centralizer (F : Set G)) :
    Function.Injective (F.normalizerMonoidHom.comp (inclusion hVF)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro v hv
  have hvC : (v : G) ∈ centralizer (F : Set G) := by
    have hh : inclusion hVF v ∈ F.normalizerMonoidHom.ker := hv
    rw [normalizerMonoidHom_ker] at hh
    exact hh
  have hh : (v : G) ∈ V ⊓ centralizer (F : Set G) := ⟨v.property, hvC⟩
  rw [faithful_of_twoPerfect_nontrivial V F hV hF hnontrivial] at hh
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp hh))

/-- The graph-field involution cannot fuse into the TI four-group when the
automorphism centralizer of its two-perfect fixed subgroup has order not
divisible by four. The image is the actual conjugation image on `L`.

The printed total-order bound `|C_Aut(L)(E₉)| = 2` cannot hold when the
inner action of `E₉` is faithful. Only the two-part is needed here. -/
theorem not_fused_of_centralizer_image_order [Finite G]
    (V L F : Subgroup G) [IsKleinFour V] (hV : IsTISubgroup V)
    (hF : IsPPerfect 2 F)
    (hnorm : centralizer (V : Set G) ≤ normalizer (L : Set G))
    (hkernel : centralizer (V : Set G) ⊓ centralizer (L : Set G) ≤ V)
    (hsmall : ¬ 4 ∣ Nat.card (((centralizer (F : Set G)).subgroupOf
      (normalizer (L : Set G))).map L.normalizerMonoidHom))
    {v w : G} (hv : v ∈ V) (hv1 : v ≠ 1)
    (hw : w ∉ V) (hwV : w ∈ centralizer (V : Set G))
    (hwF : w ∈ centralizer (F : Set G)) : ¬ IsConj v w := by
  rintro hfusion
  obtain ⟨g, hg⟩ := isConj_iff.mp hfusion
  let A := V.map (MulAut.conj g).toMonoidHom
  let e : V ≃* A := V.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective
  let : IsKleinFour A := {
    card_four := (Nat.card_congr e.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv e).symm.trans
      IsKleinFour.exponent_two }
  let : IsElementaryAbelian 2 V := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by simp }
  have hwA : w ∈ A := mem_map.mpr ⟨v, hv, hg⟩
  have hw1 : w ≠ 1 := by
    intro hw1
    exact hv1 ((MulAut.conj g).map_eq_one_iff.mp (hg.trans hw1))
  have hAV : A ≤ centralizer (V : Set G) := le_centralizer_iff.mp
    (ti_conjugate_centralizes_of_fusion_outside V hV hv hv1 hg hw hwV)
  have hAF : A ≤ centralizer (F : Set G) :=
    centralizes_of_twoPerfect_fixed A F (ti_map V hV (MulAut.conj g)) hF hwA hw1 hwF
  have hAN : A ≤ normalizer (L : Set G) := hAV.trans hnorm
  have hgn : g ∉ normalizer (V : Set G) := by
    intro hn
    exact hw ((mem_normalizer_iff.mp hn v).mp hv |> fun h => hg ▸ h)
  have hdisjoint : A ⊓ V = ⊥ := by
    apply eq_bot_iff.mpr
    rintro a ⟨haA, haV⟩
    obtain ⟨b, hb, rfl⟩ := mem_map.mp haA
    have hb1 := (isTISubgroup_iff V).mp hV g hgn b hb haV
    simp [hb1]
  let K := ((centralizer (F : Set G)).subgroupOf
    (normalizer (L : Set G))).map L.normalizerMonoidHom
  let φ : A →* K :=
    (L.normalizerMonoidHom.comp (inclusion hAN)).codRestrict K (fun a =>
      mem_map.mpr ⟨inclusion hAN a, hAF a.property, rfl⟩)
  have hinj : Function.Injective φ := by
    apply (MonoidHom.ker_eq_bot_iff φ).mp
    apply eq_bot_iff.mpr
    intro a ha
    have haφ : φ a = 1 := ha
    have haα : L.normalizerMonoidHom (inclusion hAN a) = 1 :=
      congrArg Subtype.val haφ
    have haC : (a : G) ∈ centralizer (L : Set G) := by
      have hh : inclusion hAN a ∈ L.normalizerMonoidHom.ker := haα
      rw [normalizerMonoidHom_ker] at hh
      exact hh
    have haV := hkernel ⟨hAV a.property, haC⟩
    have ha1 : (a : G) = 1 := mem_bot.mp (hdisjoint ▸ ⟨a.property, haV⟩)
    exact mem_bot.mpr (Subtype.ext ha1)
  have hcard := card_dvd_of_injective φ hinj
  have hfour : Nat.card A = 4 := IsKleinFour.card_four
  exact hsmall (hfour ▸ hcard)



/-- The inner action of an abelian subgroup embeds in its automorphism
centralizer when its intersection with the action kernel is trivial.
In particular, for the `E₉` on p.1137 this centralizer's total order is
divisible by nine; the source's printed total-order-two claim must not be
used as a model hypothesis. -/
theorem card_dvd_centralizer_action_image (L F : Subgroup G)
    (hFF : F ≤ centralizer (F : Set G))
    (hFN : F ≤ normalizer (L : Set G))
    (hker : F ⊓ centralizer (L : Set G) = ⊥) :
    Nat.card F ∣ Nat.card (((centralizer (F : Set G)).subgroupOf
      (normalizer (L : Set G))).map L.normalizerMonoidHom) := by
  let K := ((centralizer (F : Set G)).subgroupOf
    (normalizer (L : Set G))).map L.normalizerMonoidHom
  let φ : F →* K :=
    (L.normalizerMonoidHom.comp (inclusion hFN)).codRestrict K (fun a =>
      mem_map.mpr ⟨inclusion hFN a, hFF a.property, rfl⟩)
  apply card_dvd_of_injective φ
  apply (MonoidHom.ker_eq_bot_iff φ).mp
  apply eq_bot_iff.mpr
  intro a ha
  have he : L.normalizerMonoidHom (inclusion hFN a) = 1 :=
    congrArg Subtype.val (show φ a = 1 from ha)
  have haC : (a : G) ∈ centralizer (L : Set G) := by
    have hh : inclusion hFN a ∈ L.normalizerMonoidHom.ker := he
    rwa [normalizerMonoidHom_ker] at hh
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp (hker ▸ ⟨a.property, haC⟩)))

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter
