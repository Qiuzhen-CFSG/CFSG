module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.Divisibility
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.RankOneRoots
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Excluding binary PSL₂ from the contrary configuration

The inner involution centralizer is a two-group, including in a central
cover, so its two-residual is trivial. Containment makes the outer residual
trivial as well. The actual outer fixed subgroup is PSL₂ over the half field.
The matrix with rows (0,1) and (1,1) has order three over every binary field;
its odd divisor survives passage to O². This contradicts the trivial residual.
The argument includes the half-field order two endpoint, where O²(PSL₂(2))
is cyclic of order three rather than the full fixed subgroup.

Field isomorphisms give the statement for every `ClassicalGroup.IsPSL`
witness. The two component centers are never identified or discarded.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(1),(4), printed p.1171, and the comparison in 16.4.11(2), p.1193.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
open Subgroup Theory.GroupTheory BenderSuzuki.Converse BenderSuzuki.MatrixGroups
open BenderSuzuki.PFAppendixIII LiePreliminaries

private theorem three_dvd_psl2 (F : Type*) [Field F] [Finite F] [CharP F 2] :
    3 ∣ Nat.card (PSL2MatrixGroup F) := by
  let c : SL2 F := ⟨!![0, 1; 1, 1], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩
  have hpow : c ^ 3 = 1 := by
    apply Subtype.ext
    change ((!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) F) ^ 3) = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  have hne : c ≠ 1 := by
    intro h
    have he := congrArg (fun a : SL2 F => a.val 0 0) h
    simp [c] at he
  have horder : orderOf (pi F c) = 3 :=
    (orderOf_injective (pi F) pi_injective c).trans (orderOf_eq_prime hpow hne)
  exact horder ▸ orderOf_dvd_natCard (pi F c)

private noncomputable def binaryEquiv {H : Type*} [Group H] {n : ℕ} (hn : 0 < n)
    (h : ClassicalGroup.IsPSL H 2 (2 ^ n)) : H ≃* PSL2BinaryMatrixGroup n :=
  Classical.choice <| by
    obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
    let := Fintype.ofFinite F
    let := Fintype.ofFinite (BinaryGaloisField n)
    let f : F ≃+* BinaryGaloisField n := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        hcard, card_binaryGaloisField n (by omega)])
    exact ⟨e.trans (Atlas.fieldEquivPSL 2 f)⟩

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The binary model exclusion, including its smallest outer fixed subgroup. -/
theorem not_binary_psl_two_quotient (d : Contrary T z L g R r) {n : ℕ} (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* PSL2BinaryMatrixGroup n) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let hi := d.setup.sylow_normalizes (d.setup.le_sylow d.mem)
  let c := (centerQuotientEquivTwoCore (component_oddCore d)).trans e
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hb, _⟩ :=
    psl2_inner_involution_roots (component_oddCore d) hn e (action hi)
      d.inner_action_order d.inner_action
  have hX : residual L r = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : (⟨x, ((residual_le L r).trans inf_le_left) hx⟩ : L) ∈
        (residual L r).subgroupOf L := hx
    rw [residual_subgroupOf_eq hi, hb, mem_bot] at hh
    exact mem_bot.mpr (congrArg Subtype.val hh)
  have hY : residual (L.conjBy g) z = ⊥ :=
    le_bot_iff.mp (d.residual_normal.1.trans hX.le)
  let b := outerAction d c
  have hb2 : b ^ 2 = 1 := by
    have hbo : orderOf b = 2 := outerAction_order d c
    simpa only [hbo] using pow_orderOf_eq_one b
  obtain ⟨x, σ, he⟩ := BenderSuzuki.ZD.Linear.binary_semilinear_coverage hn b
  obtain ⟨m, _, _, ⟨efix⟩⟩ := BenderSuzuki.ZD.Linear.outer_fixed_model_of_semilinear
    hn b hb2 x σ he (outerAction_outer d c)
  have hfix : 3 ∣ Nat.card (outerAction d c).fixedSubgroup := by
    have hh := (Nat.card_congr efix.toEquiv).symm ▸ three_dvd_psl2 (BinaryGaloisField m)
    exact hh
  have hres := (OtherFamilies.odd_prime_dvd_residual_iff Nat.prime_three (by decide)).mpr hfix
  have himage : Nat.card (centralImage (L.conjBy g) (residual (L.conjBy g) z)) = 1 := by
    simp [hY, centralImage]
  rw [← Nat.card_congr (outerResidualEquiv d c).toEquiv, himage] at hres
  norm_num at hres

/-- The PSL₂ Bender alternative is impossible, with every field and cover
transport discharged and no table premise remaining. -/
theorem not_psl_two_quotient (d : Contrary T z L g R r) {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) : False :=
  not_binary_psl_two_quotient d hn (binaryEquiv (by omega) hmodel)

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
