module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.LinearThree.Centers
public import Theory.SpecificGroups.PSL3.LinearThreeBorelOrder
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Complements in the PSL₃(4) Borel case

The action kernel in E.6.8 has index three when `n = 2`.  The quotient of a
marked central cover by its center embeds in the PSL₃(4) Borel, whose order is
`192`; the center and the kernel of the quotient map are two-groups.  Hence the
action kernel has order coprime to its index, and Schur–Zassenhaus supplies the
required cyclic complement.

Source: Aschbacher–Smith, E.6.8(1) and E.6.11, printed pp.247–250.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G} {n : ℕ}

private theorem card_dvd_two_pow_mul_three_of_quotient_image
    {H : Type*} [Group H] [Finite H] {Z B : Subgroup H} [Z.Normal]
    (hZ : IsPGroup 2 Z)
    (himg : Nat.card (B.map (QuotientGroup.mk' Z)) ∣ 192) :
    ∃ k, Nat.card B ∣ 2 ^ k * 3 := by
  let f := (QuotientGroup.mk' Z).comp B.subtype
  have hrange : f.range = B.map (QuotientGroup.mk' Z) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : IsPGroup 2 f.ker := by
    let i : f.ker →* H := B.subtype.comp f.ker.subtype
    intro x
    have hx0 : f (x : B) = 1 := x.property
    have hx : i x ∈ Z := by
      have hxker : i x ∈ (QuotientGroup.mk' Z).ker := by
        apply MonoidHom.mem_ker.mpr
        change QuotientGroup.mk' Z (i x) = 1
        change f (x : B) = 1 at hx0
        exact hx0
      simpa only [QuotientGroup.ker_mk'] using hxker
    obtain ⟨k, hk⟩ := hZ ⟨i x, hx⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((x : B) ^ 2 ^ k : H) = 1
    simpa [i] using congrArg Subtype.val hk
  obtain ⟨k, hk⟩ := hker.exists_card_eq
  have hmul : Nat.card f.ker * f.ker.index = Nat.card B := f.ker.card_mul_index
  have hidx : f.ker.index = Nat.card (B.map (QuotientGroup.mk' Z)) := by
    rw [Subgroup.index_ker, hrange]
  refine ⟨k + 6, ?_⟩
  rw [← hmul, hk, hidx]
  have hdvd : 2 ^ k * Nat.card (B.map (QuotientGroup.mk' Z)) ∣ 2 ^ k * 192 :=
    Nat.mul_dvd_mul_left _ himg
  have hpow : 2 ^ k * 192 = 2 ^ (k + 6) * 3 := by ring
  simpa [hpow] using hdvd

private theorem coprime_three_of_card_dvd_two_pow_mul_three
    {B K : Type*} [Group B] [Finite B] [Group K] [Finite K]
    (f : B →* K) (hi : f.ker.index = 3)
    (hcard : ∃ k, Nat.card B ∣ 2 ^ k * 3) :
    Nat.Coprime (Nat.card f.ker) f.ker.index := by
  obtain ⟨k, hk⟩ := hcard
  have hmul : Nat.card f.ker * f.ker.index = Nat.card B := f.ker.card_mul_index
  have hdvd : Nat.card f.ker * 3 ∣ 2 ^ k * 3 := by
    have hdvd' : Nat.card f.ker * f.ker.index ∣ 2 ^ k * 3 := hmul ▸ hk
    rw [hi] at hdvd'
    exact hdvd'
  have hpow : Nat.card f.ker ∣ 2 ^ k :=
    (Nat.mul_dvd_mul_iff_right (by decide : 0 < 3)).mp hdvd
  rw [hi]
  exact (Nat.Coprime.pow_left k (by decide : Nat.Coprime 2 3)).coprime_dvd_left hpow

theorem exists_complement_linear_three_cover
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (hn2 : n = 2) (hz : IsPGroup 2 (center L))
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) :
    ∃ X : Subgroup G, X ≤ L ⊓ M ∧ Nonempty (X ≃* Multiplicative (ZMod (2 ^ n - 1))) ∧
      (L ⊓ centralizer (V : Set G)) ⊔ X = L ⊓ M ∧
      (L ⊓ centralizer (V : Set G)) ⊓ X = ⊥ := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hp : 1 < 2 ^ n := one_lt_pow₀ (by decide) (Nat.ne_of_gt hn0)
  have hVL_use : V ≤ normalizer (L : Set G) := hVL
  let : NeZero (2 ^ n - 1) := ⟨by omega⟩
  let B := L ⊓ M
  have hBN := component_intersection_normalizes h hU hL.1
  let eL := (subgroupOfEquivOfLe hBN).symm
  let f : B →* inducedAutomizer V B :=
    (V.normalizerMonoidHom.rangeRestrict.subgroupMap
      (B.subgroupOf (normalizer (V : Set G)))).comp eL.toMonoidHom
  have hf : Function.Surjective f :=
    (MonoidHom.subgroupMap_surjective _ _).comp eL.surjective
  obtain ⟨a⟩ := b.action
  have hi : f.ker.index = 2 ^ n - 1 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top,
      Nat.card_congr a.toEquiv]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hker : f.ker.map B.subtype = L ⊓ centralizer (V : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property.1, ?_⟩
      change (y : G) ∈ Subgroup.centralizer (V : Set G)
      have heq : V.normalizerMonoidHom ⟨(y : G), hBN y.property⟩ = 1 :=
        congrArg (fun z => z.val.val) hy
      simpa only [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] using
        (show (⟨(y : G), hBN y.property⟩ : normalizer (V : Set G)) ∈
          V.normalizerMonoidHom.ker from heq)
    · intro hx
      let y : B := ⟨x, hx.1, h.centralizer_le hx.2⟩
      refine ⟨y, ?_, rfl⟩
      change f y = 1
      apply Subtype.ext
      apply Subtype.ext
      change V.normalizerMonoidHom ⟨x, hBN y.property⟩ = 1
      change (⟨x, hBN y.property⟩ : normalizer (V : Set G)) ∈ V.normalizerMonoidHom.ker
      rw [Subgroup.normalizerMonoidHom_ker]
      exact hx.2
  have hBnorm : B.subgroupOf L = normalizer (S : Set L) :=
    borel_eq_sylow_normalizer h b hQ S hS hz
  let q := QuotientGroup.mk' (center L)
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center L))
  have hmap : (B.subgroupOf L).map q ≤ normalizer (R : Set (L ⧸ center L)) := by
    rw [hBnorm]
    change (normalizer (S : Set L)).map q ≤ normalizer ((S : Subgroup L).map q)
    exact Subgroup.le_normalizer_map q
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  have hnormcard : Nat.card (normalizer (R : Set (L ⧸ center L))) = 192 := by
    let R' : Sylow 2 (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
      R.mapSurjective (f := e.toMonoidHom) e.surjective
    have hne : (normalizer (R : Set (L ⧸ center L))).map e.toMonoidHom =
        normalizer (R' : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) := by
      change (normalizer (R : Set (L ⧸ center L))).map e.toMonoidHom =
        normalizer ((R : Subgroup (L ⧸ center L)).map e.toMonoidHom)
      exact Subgroup.map_equiv_normalizer_eq R e
    let er : normalizer (R : Set (L ⧸ center L)) ≃*
        normalizer (R' : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)) :=
      (e.subgroupMap (normalizer (R : Set (L ⧸ center L)))).trans
        (MulEquiv.subgroupCongr hne)
    calc
      Nat.card (normalizer (R : Set (L ⧸ center L))) =
          Nat.card (normalizer (R' : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))) :=
        Nat.card_congr er.toEquiv
      _ = Nat.card (Matrix.PSL3.LinearThree.borel F) :=
        Nat.card_congr (Matrix.PSL3.CartanActions.BorelQuotient.sylowNormalizerEquiv
          F (n := 2) (by decide) hF R').toEquiv
      _ = 192 := Matrix.PSL3.CartanActions.BorelQuotient.card_borel_linear_three_four F hF
  have himg : Nat.card ((B.subgroupOf L).map q) ∣ 192 := by
    calc
      Nat.card ((B.subgroupOf L).map q) ∣ Nat.card (normalizer (R : Set (L ⧸ center L))) :=
        Subgroup.card_dvd_of_le hmap
      _ = 192 := hnormcard
  have hBcard : ∃ k, Nat.card B ∣ 2 ^ k * 3 := by
    have hsub := card_dvd_two_pow_mul_three_of_quotient_image hz himg
    obtain ⟨k, hk⟩ := hsub
    refine ⟨k, ?_⟩
    have heq : Nat.card B = Nat.card (B.subgroupOf L) :=
      Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : B ≤ L)).symm.toEquiv
    simpa only [heq] using hk
  have hcop : Nat.Coprime (Nat.card f.ker) f.ker.index := by
    apply coprime_three_of_card_dvd_two_pow_mul_three f
    simpa [hn2] using hi
    exact hBcard
  obtain ⟨X₀, hc⟩ := exists_right_complement'_of_coprime hcop
  let X := X₀.map B.subtype
  refine ⟨X, Subgroup.map_subtype_le X₀, ?_, ?_, ?_⟩
  · exact ⟨(X₀.equivMapOfInjective B.subtype B.subtype_injective).symm.trans
      (hc.symm.QuotientMulEquiv.symm.trans
        ((QuotientGroup.quotientKerEquivOfSurjective f hf).trans a))⟩
  · rw [← hker, ← Subgroup.map_sup, hc.sup_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · rw [← hker, ← Subgroup.map_inf _ _ _ B.subtype_injective,
      hc.disjoint.eq_bot, Subgroup.map_bot]

end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
