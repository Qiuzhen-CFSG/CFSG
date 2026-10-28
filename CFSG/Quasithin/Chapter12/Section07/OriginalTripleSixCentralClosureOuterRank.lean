module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureRank
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureAutomizerCases
import Theory.Representation.HexacodeAction.OddPointQuotient

/-!
# Rank two in the original outer central-closure branch

Both marked outer alternatives contain an actual odd involution. The
original closure W lies in the full action kernel N. Its displacements on
the original U therefore lie in the kernel of the unchanged chart followed
by U's quotient projection. That kernel also contains the literal scalar
point. The intrinsic odd-involution calculation bounds this quotient by
two binary dimensions; the original rank-two-or-four theorem makes its
order exactly four.

Source: Aschbacher--Smith, 12.7.17, printed p.845.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix DuadCalculation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem odd_original_image_card_le_four (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (z : U) (hz : z ≠ 1)
    (H W : Subgroup G) (hUH : U ≤ H) (hWH : W ≤ H)
    (N : Subgroup H) [N.Normal]
    (hVN : (tripleSixPoint D a z).subgroupOf H ≤ N) (hWN : W.subgroupOf H ≤ N)
    (f : Automizer U →* HexAutomorphisms)
    (hchart : ∀ (b : Automizer U) (u : U),
      (tripleSixPointCoordinates D a (b.val u)).toAdd =
        Hexacode.action (f b) (tripleSixPointCoordinates D a u).toAdd)
    (g : HexAutomorphisms) (hg : g ∈ (inducedAutomizer U W).map f)
    (hodd : hexSign g = -1) (h2 : g ^ 2 = 1)
    (hgz : Hexacode.action g (tripleSixPointCoordinates D a z).toAdd =
      (tripleSixPointCoordinates D a z).toAdd) :
    Nat.card ((U.subgroupOf H).map (QuotientGroup.mk' N)) ≤ 4 := by
  let q := QuotientGroup.mk' N
  let A := (U.subgroupOf H).map q
  let c := tripleSixPointCoordinates D a
  let v := (c z).toAdd
  let := D.elementary
  let : IsElementaryAbelian 2 (U.subgroupOf H) := IsElementaryAbelian.subgroupOf hUH
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map q
  let b : Multiplicative hexacode →* A :=
    (q.subgroupMap (U.subgroupOf H)).comp
      (((subgroupOfEquivOfLe hUH).symm.toMonoidHom).comp c.symm.toMonoidHom)
  let ℓ : hexacode →ₗ[ZMod 2] Additive A := b.toAdditiveRight.toZModLinearMap 2
  have hbc (u : U) : (b (c u)).val = q ⟨u, hUH u.property⟩ := by
    change q ((subgroupOfEquivOfLe hUH).symm (c.symm (c u))).val = _
    rw [c.symm_apply_apply]
    rfl
  have hℓ : Function.Surjective ℓ :=
    (q.subgroupMap_surjective (U.subgroupOf H)).comp
      ((subgroupOfEquivOfLe hUH).symm.surjective.comp c.symm.surjective)
  let E := ℓ.ker
  have hmem (w : hexacode) : w ∈ E ↔
      (⟨(c.symm (Multiplicative.ofAdd w) : G),
        hUH (c.symm (Multiplicative.ofAdd w)).property⟩ : H) ∈ N := by
    change b (Multiplicative.ofAdd w) = 1 ↔ _
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  have hPE : (Submodule.span Hexacode.F {v}).restrictScalars (ZMod 2) ≤ E := by
    intro w hw
    apply (hmem w).mpr
    apply hVN
    refine ⟨c.symm (Multiplicative.ofAdd w), ?_, rfl⟩
    change (c (c.symm (Multiplicative.ofAdd w))).toAdd ∈ Submodule.span Hexacode.F {v}
    rw [c.apply_symm_apply]
    change w ∈ Submodule.span Hexacode.F {v} at hw ⊢
    exact hw
  obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hg
  have hmove (x : hexacode) :
      Hexacode.action (f (U.normalizerMonoidHom.rangeRestrict w)) x - x ∈ E := by
    let u := c.symm (Multiplicative.ofAdd x)
    let wH : H := ⟨w, hWH hw⟩
    let uH : H := ⟨u, hUH u.property⟩
    have hwN : wH ∈ N := hWN hw
    have hqw : q wH = 1 := (QuotientGroup.eq_one_iff wH).mpr hwN
    have hu : c u = Multiplicative.ofAdd x := c.apply_symm_apply _
    have hcu : c ((U.normalizerMonoidHom.rangeRestrict w).val u) =
        Multiplicative.ofAdd (Hexacode.action (f (U.normalizerMonoidHom.rangeRestrict w)) x) := by
      apply Multiplicative.toAdd.injective
      have hh := hchart (U.normalizerMonoidHom.rangeRestrict w) u
      change (c ((U.normalizerMonoidHom.rangeRestrict w).val u)).toAdd =
        Hexacode.action (f (U.normalizerMonoidHom.rangeRestrict w)) (c u).toAdd at hh
      rw [hu] at hh
      exact hh
    change ℓ (_ - _) = 0
    rw [map_sub, sub_eq_zero]
    change b (Multiplicative.ofAdd _) = b (Multiplicative.ofAdd x)
    rw [← hcu, ← hu]
    apply Subtype.ext
    rw [hbc, hbc]
    change q (wH * uH * wH⁻¹) = q uH
    rw [map_mul, map_mul, map_inv, hqw, one_mul, inv_one, mul_one]
  have hv : v ≠ 0 := by
    intro he
    exact hz (c.injective (show c z = c 1 from he.trans c.map_one.symm))
  have hd := Hexacode.odd_involution_point_quotient_finrank_le_two
    (f (U.normalizerMonoidHom.rangeRestrict w)) hodd h2 v hv hgz E hPE hmove
  rw [(ℓ.quotKerEquivOfSurjective hℓ).finrank_eq] at hd
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  change Nat.card A = (Nat.card (ZMod 2)) ^ Module.finrank (ZMod 2) (Additive A) at hc
  rw [Nat.card_zmod] at hc
  exact hc.trans_le (Nat.pow_le_pow_right (by decide) hd)

/-- The unchanged full closure-action kernel has inner induced action or
an original U-image of order four. All prior quotient structure is retained. -/
theorem original_tripleSix_central_closure_outer_rank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2) :
    let C := centralizer ({(z : G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let V1 := tripleSixPoint D a z
    let W := conjugateSpanBy V1 R
    ∃ (N : Subgroup H) (hN : N.Normal),
      letI := hN
      (∀ x : H, x ∈ N ↔ ∀ w ∈ W, ⁅w, (x : G)⁆ ∈ zpowers (z : G)) ∧
      pCore 2 (H ⧸ N) = ⊥ ∧ V1.subgroupOf H ≤ N ∧
      let q := QuotientGroup.mk' N
      let A := (U.subgroupOf H).map q
      let Jstar := (J.subgroupOf H).map q
      A ≠ ⊥ ∧ IsElementaryAbelian 2 A ∧ (Nat.card A = 4 ∨ Nat.card A = 16) ∧
        A = ⁅A, Jstar⁆ ∧ Nat.card (Jstar ⧸ pCore 2 Jstar) = 3 ∧
        (inducedAutomizer U W ≤ inducedAutomizer U K ∨ Nat.card A = 4) := by
  let C := centralizer ({(z : G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  obtain ⟨N, hN, hmem, hcore, hVN, hne, helem, hcard, hgen, hcubic⟩ :=
    original_tripleSix_central_closure_rank h structural D a z hz hzT hnot
  let : N.Normal := hN
  let A := (U.subgroupOf H).map (QuotientGroup.mk' N)
  refine ⟨N, hN, hmem, hcore, hVN, hne, helem, hcard, hgen, hcubic, ?_⟩
  by_cases hinner : inducedAutomizer U W ≤ inducedAutomizer U K
  · exact Or.inl hinner
  right
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  change H ≤ C ∧ W = conjugateSpanBy V1 H ∧ W ≤ H.pCoreIn 2 ∧
    (frattini W).map W.subtype ≤ zpowers (z : G) ∧
    ⁅W, H.pCoreIn 2⁆ ≤ zpowers (z : G) ∧ ¬ U ≤ H.pCoreIn 2 ∧
    ¬ ⁅U, W⁆ ≤ zpowers (z : G) at hc
  have hWH : W ≤ H := hc.2.2.1.trans (pCoreIn_le 2 H)
  have hWN : W.subgroupOf H ≤ N := by
    intro w hw
    apply (hmem w).mpr
    intro u hu
    exact hc.2.2.2.2.1 (commutator_mem_commutator hu (hc.2.2.1 hw))
  obtain ⟨_, f, hf, _, hK, hchart, hfix, _, _, e, _, _, heven, hcases, _⟩ :=
    original_tripleSix_central_closure_automizer_cases h structural D a z hz hzT hnot
  let v := (tripleSixPointCoordinates D a z).toAdd
  let B := ((inducedAutomizer U W).map f).subgroupOf (Hexacode.fullVectorStabilizer v)
  have houter : B.map e.toMonoidHom = centralFactor ∨
      B.map e.toMonoidHom = productCore := by
    rcases hcases with hklein | hother
    · exfalso
      apply hinner
      intro b hb
      have hfb : f b ∈ (inducedAutomizer U W).map f := mem_map_of_mem _ hb
      let bS : Hexacode.fullVectorStabilizer v := ⟨f b, hfix hfb⟩
      have hmark : e bS ∈ (⊥ : Subgroup Two).prod core := by
        rw [← hklein]
        exact mem_map_of_mem _ hfb
      have he : hexSign (f b) = 1 := by
        apply (heven bS).mpr
        have hsign := ((core_mem_iff (e bS).2).mp hmark.2).1
        rw [mem_bot.mp hmark.1]
        change 1 = if (e bS).2.sign = 1 then 1 else Equiv.swap 0 1
        rw [if_pos hsign]
      have hbK : f b ∈ (inducedAutomizer U K).map f := hK.symm ▸ he
      obtain ⟨c, hc, hcb⟩ := hbK
      exact hf hcb ▸ hc
    · exact hother.2
  have hswap : (Equiv.swap 0 1, 1) ∈ B.map e.toMonoidHom := by
    rcases houter with he | he
    · rw [he]
      exact ⟨mem_top _, one_mem _⟩
    · rw [he]
      exact ⟨mem_top _, one_mem _⟩
  obtain ⟨g, hg, hgmark⟩ := hswap
  have hgodd : hexSign g.val = -1 := by
    rcases Int.units_eq_one_or (hexSign g.val) with he | he
    · have hh := (heven g).mp he
      rw [show e g = (Equiv.swap 0 1, 1) from hgmark] at hh
      exact ((by decide : (Equiv.swap 0 1 : Two) ≠ signPermTwo 1) hh).elim
    · exact he
  have hg2 : g.val ^ 2 = 1 := by
    have hgpow : g ^ 2 = 1 := by
      apply e.injective
      rw [map_pow, show e g = (Equiv.swap 0 1, 1) from hgmark, map_one]
      decide
    exact congrArg Subtype.val hgpow
  have hbound : Nat.card A ≤ 4 := odd_original_image_card_le_four D a z hz H W
    (D.le_sylow.trans le_sup_right) hWH N hVN hWN f hchart g.val hg hgodd hg2 g.property
  rcases hcard with he | he
  · exact he
  · change Nat.card A = 16 at he
    omega

end CFSG.Quasithin.Chapter12.Section07
