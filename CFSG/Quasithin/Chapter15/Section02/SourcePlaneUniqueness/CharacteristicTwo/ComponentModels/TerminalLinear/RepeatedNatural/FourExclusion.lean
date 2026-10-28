module
public import Theory.SpecificGroups.BinaryLinear.FourPointRank
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.Exclusions
/-!
# Excluding the degree-four repeated-natural row

A nonzero coordinate of a generating seed is fixed by every actor fixing
the seed. In degree four its stabilizer has cubic rank at most one.
The original K has rank at least two, which is unchanged by the two-core
quotient of X. Thus repeated-natural must have degree five.

The original action and seed generation are constructed internally.
K-containment and the S₃-square quotient are earlier source clauses owned
by component preparation and the small-parabolic/final plane-uniqueness
assembly. No parabolic identification is assumed in this exclusion.
Source: Aschbacher--Smith, 15.2.23(a), printed p.1117.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource Section01
/-- A cubic-rank-two actor cannot fix a generating repeated-natural seed in degree four. -/
theorem repeatedNatural_four_not_le_seedCentralizer
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (r : ℕ) (hr : 0 < r)
    (e : ActionEquiv ρ (repeated (linearNatural BinaryField.two 4) r))
    (Z : Submodule (ZMod 2) W) (hgen : (⨆ g : D, Z.map (ρ g)) = ⊤)
    (A : Subgroup D) (hA : 2 ≤ primeRank 3 A) :
    ¬ A ≤ subspaceKernel ρ Z ⊤ := by
  let : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  let : Nontrivial W := e.linearEquiv.symm.injective.nontrivial
  have hZne : Z ≠ ⊥ := by
    intro he
    have hb : (⊥ : Submodule (ZMod 2) W) = ⊤ := by
      simpa only [he, Submodule.map_bot, iSup_bot] using hgen
    exact bot_ne_top hb
  obtain ⟨z,hz,hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZne
  have hez : e.linearEquiv z ≠ 0 := by
    intro he
    exact hz0 (e.linearEquiv.map_eq_zero_iff.mp he)
  obtain ⟨i,hi⟩ : ∃ i, e.linearEquiv z i ≠ 0 := Function.ne_iff.mp hez
  let v : Fin 4 → ZMod 2 := e.linearEquiv z i
  intro hfix
  have hle : A.map e.groupEquiv.toMonoidHom ≤
      MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
        v := by
    rintro _ ⟨g,hg,rfl⟩
    have he := congrFun (e.intertwines g z) i
    rw [(hfix hg).2 z hz] at he
    exact he.symm
  have hbound := (primeRank_mono 3 hle).trans
    (BinaryLinear.PointStabilizerRank.natural_four_threeRank_le_one _ hi)
  rw [primeRank_equiv 3 (A.equivMapOfInjective
    e.groupEquiv.toMonoidHom e.groupEquiv.injective).symm] at hbound
  omega


/-- The original U-action cannot be a positive sum of natural four-spaces. -/
theorem not_repeatedNatural_four_canonical
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
    {hsource : ChosenSmallSource T M Mc V}
    (d : PlaneUniquenessPreceding hsource H ZS)
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (r : ℕ) (hr : 0 < r) :
    letI := U_elementary d hI hfit hXI
    ¬ Nonempty (ActionEquiv (U_representation d hI hfit hXI hn)
      (repeated (linearNatural BinaryField.two 4) r)) := by
  let := U_elementary d hI hfit hXI
  rintro ⟨e⟩
  let σ := U_representation d hI hfit hXI hn
  let q := QuotientGroup.mk' (pCore 2 X)
  let Z := AddSubgroup.toZModSubmodule 2 (ZS.subgroupOf (U X ZS)).toAddSubgroup
  let A := (((pResidual 2 H).map H.subtype).subgroupOf X).map q
  have hA : 2 ≤ primeRank 3 A := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide) q
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup),
      primeRank_equiv 3 (subgroupOfEquivOfLe hKX)]
    exact K_threeRank_ge_two d hpair
  apply repeatedNatural_four_not_le_seedCentralizer σ r hr e Z
    (U_seed_module_generates d hI hfit hXI hn σ
      (U_representation_apply d hI hfit hXI hn)) A hA
  rintro _ ⟨x,hx,rfl⟩
  refine ⟨mem_top _, ?_⟩
  intro u hu
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [U_representation_apply]
  have hh : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) :=
    d.residual_centralizes hx _ hu
  rw [← hh, mul_inv_cancel_right]

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
