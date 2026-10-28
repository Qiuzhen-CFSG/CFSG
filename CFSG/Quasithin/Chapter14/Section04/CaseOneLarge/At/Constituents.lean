module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.At.Orthogonal
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.MarkedMultiplicity
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.HigherMultiplicity
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineConstituent
import all CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineModels

/-!
# Marked constituent multiplicity at G,T

The original fixed line controls the actor centralizer and multiplicity.
Passing through the literal action quotient constructs the faithful
constituent and its normal component. The retained original actor and
point stabilizer then give the complete fixed-line constituent reduction.

The earlier inputs are restricted to the original group and Sylow subgroup.
The universal APIs remain unchanged. The `import all` edges intentionally
reuse the private calculations of the corresponding source implementation;
only deductions depending on the earlier inputs are specialized here.
Source: Aschbacher--Smith, G.11.6--8, 14.4.2; printed pp.365--369,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section

/- Specialization of CaseOneLarge/MarkedMultiplicity.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction.Components

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
  (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
  (classification : EarlierFaithfulClassification G (T : Subgroup G))
  (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
  (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
  (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
  {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
  (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
  {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I) (hv : v ∈ I)

include d earlier hq chosen structural alternatives hne hZ hlarge hgP hgH hyp hC hm hI hv

private theorem marked_homogeneous_data_at :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    Homogeneous.homogeneousPart R ⊤ = ⊤ ∧ Function.Injective R.toRepresentation ∧
      (∀ J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype),
        IsIrreducible J.toRepresentation → Homogeneous.SameModule R J) := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow_at d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hn := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  have ha := hyp.constituent_homogeneous_faithful_selfDual_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv
  exact ⟨ha.1,ha.2.1,hyp.constituent_sameModule_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv⟩

theorem source_large_marked_centralizer_displacement_at
    (c : F.terminalDot (F.X g))
    (hc : (c : F.TerminalHdot) ∈ centralizer (componentOrbit C ⊤ : Set F.TerminalHdot))
    (hc1 : c ≠ 1) :
    LinearMap.range (F.terminalRepresentation c - LinearMap.id) = I ∧
      LinearMap.ker (F.terminalRepresentation c - LinearMap.id) = B.orthogonal I := by
  let H := componentOrbit C ⊤
  let := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  have hn := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hn
  have ha := marked_homogeneous_data_at d earlier hq chosen structural alternatives F hne hZ
    hlarge g hgP hgH hyp hC hm hI hv
  exact hyp.centralizer_displacement_range_and_ker hi H hC.componentOrbit_top_ne_bot
    (invariantSubspace F.terminalRepresentation H I hI.choose)
    (hI.irreducible_of_normal_restriction _ hi H) ha.1 hv
    (by change 3 ≤ finrank (ZMod 2) I
        have hh := hI.finrank_gt_two F.terminalRepresentation H
        omega) c hc hc1

theorem source_large_marked_actor_schur_bound_at :
    let H := componentOrbit C ⊤
    let R := invariantSubspace F.terminalRepresentation H I hI.choose
    finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) +
        primeRank 2 (MulAut H) := by
  let := componentOrbit_top_normal C
  exact finrank_le_schur_add_automorphism_rank F.terminalRepresentation hyp.faithful
    (componentOrbit C ⊤) (F.terminalDot (F.X g))
    (invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose)
    (B.orthogonal I)
    (source_large_marked_centralizer_displacement_at d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv)

include classification

theorem source_large_marked_double_kernel_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 2 * finrank (ZMod 2) I)
    (hk : (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf
      (F.terminalDot (F.X g)) ≠ ⊥) :
    let Y := (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf
      (F.terminalDot (F.X g))
    Nat.card Y = 2 ∧
      finrank (ZMod 2) I = finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸ Y)) + 2 := by
  classical
  let X := F.terminalDot (F.X g)
  let Y := (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf X
  have hiso := source_large_point_constituent_isotropic_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv
  have ho : B.orthogonal I = I := by
    apply Eq.symm
    apply Submodule.eq_of_le_of_finrank_eq
    · intro w hw u hu
      exact hiso u hu w hw
    · rw [LinearMap.BilinForm.finrank_orthogonal hyp.nondegenerate]
      omega
  have hker (y : X) (hy : y ≠ 1)
      (hyC : (y : F.TerminalHdot) ∈ centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)) :
      LinearMap.ker (F.terminalRepresentation y - LinearMap.id) = I := by
    rw [← ho]
    exact (source_large_marked_centralizer_displacement_at d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv y hyC hy).2
  obtain ⟨_,hE,hX,hfaith⟩ := source_terminal_ranks_of_no_lowRank_at d earlier hq chosen
    structural alternatives F hne hZ g hgP hgH v hline hn
  have hEI : ¬ hatSpace F (F.E g) ≤ I := by
    intro hle
    obtain ⟨c,hc⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hk
    have hcX : (c : X) ≠ 1 := fun he => hc (Subtype.ext he)
    apply hcX
    apply hfaith
    intro w
    rw [Subgroup.coe_one,map_one,Module.End.one_apply]
    apply sub_eq_zero.mp
    change w.val ∈ LinearMap.ker (F.terminalRepresentation (c : X) - LinearMap.id)
    rw [hker (c : X) hcX c.property]
    exact hle w.property
  obtain ⟨w,hw,hwI⟩ := SetLike.not_le_iff_exists.mp hEI
  have hfree (y : Y) (hy : F.terminalRepresentation (y : X) w = w) : y = 1 := by
    by_contra hy1
    apply hwI
    rw [← hker (y : X) (fun he => hy1 (Subtype.ext he)) y.property]
    exact sub_eq_zero.mpr hy
  have hinj : Function.Injective (fun y : Y => F.terminalRepresentation (y : X) w) := by
    intro a b hab
    dsimp only at hab
    have he : a⁻¹ * b = 1 := by
      apply hfree
      change F.terminalRepresentation ((a : F.TerminalHdot)⁻¹ * b) w = w
      rw [map_mul,Module.End.mul_apply,← hab,← Module.End.mul_apply,← map_mul,
        inv_mul_cancel,map_one,Module.End.one_apply]
    exact inv_mul_eq_one.mp he
  let c (y : Y) : ZMod 2 := (hyp.transvections (y : X)).choose ⟨w,hw⟩
  have hc (y : Y) : F.terminalRepresentation (y : X) w = w + c y • v :=
    (hyp.transvections (y : X)).choose_spec.2 ⟨w,hw⟩
  have hci : Function.Injective c := by
    intro a b he
    apply hinj
    change F.terminalRepresentation (a : X) w = F.terminalRepresentation (b : X) w
    rw [hc a,hc b,he]
  have hb : Nat.card Y ≤ 2 := by
    simpa only [Nat.card_zmod] using Nat.card_le_card_of_injective c hci
  have hl : 1 < Nat.card Y := (Subgroup.one_lt_card_iff_ne_bot Y).mpr hk
  have hcard : Nat.card Y = 2 := by omega
  refine ⟨hcard,?_⟩
  have hcX : Nat.card X = 2 ^ finrank (ZMod 2) (Additive X) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X)
  have hcQ : Nat.card (X ⧸ Y) = 2 ^ finrank (ZMod 2) (Additive (X ⧸ Y)) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (X ⧸ Y))
  have he := Y.index_mul_card
  rw [Subgroup.index_eq_card,hcard,hcX,hcQ,← pow_succ] at he
  have hr := (Nat.pow_right_injective (by decide : 2 ≤ 2)) he
  rw [marked_binary_rank] at hX
  change finrank (ZMod 2) (Additive X) + 1 = finrank (ZMod 2) (hatSpace F (F.E g)) at hX
  change finrank (ZMod 2) I = finrank (ZMod 2) (Additive (X ⧸ Y)) + 2
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/HigherMultiplicity.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative MonoidAlgebra

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction.Components

open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.MarkedHigherOrthogonal

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
  (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
  (classification : EarlierFaithfulClassification G (T : Subgroup G))
  (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
  (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
  (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
  {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
  (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
  {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I) (hv : v ∈ I)

include d earlier hq chosen structural alternatives hne hZ hlarge hgP hgH hyp hC hm hI hv

private theorem higher_homogeneous_data_at :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    Homogeneous.homogeneousPart R ⊤ = ⊤ ∧ Function.Injective R.toRepresentation ∧
      (∀ J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype),
        IsIrreducible J.toRepresentation → Homogeneous.SameModule R J) := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow_at d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hn := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  have ha := hyp.constituent_homogeneous_faithful_selfDual_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv
  exact ⟨ha.1,ha.2.1,hyp.constituent_sameModule_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv⟩

include classification

private theorem higher_stable_orthogonal_at
    (hd : 2 * finrank (ZMod 2) I < finrank (ZMod 2) (Additive F.Uhat))
    (x : F.terminalDot (F.X g)) :
    ∃ J : Submodule (ZMod 2) (Additive F.Uhat),
      IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) J ∧
      v ∉ J ∧ J ≤ B.orthogonal I ∧
      (x : F.TerminalHdot) ∈ subspaceStabilizer F.terminalRepresentation J := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  let : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hC.componentOrbit_top_ne_bot
  have hn := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hn
  let R := invariantSubspace F.terminalRepresentation H I hI.choose
  let : IsIrreducible R.toRepresentation := hI.irreducible_of_normal_restriction _ hi H
  let : IsSemisimpleModule (ZMod 2)[H]
      (Representation.asModule (F.terminalRepresentation.comp H.subtype)) :=
    NormalConstituentDisplacement.restriction_semisimple F.terminalRepresentation hi H
  obtain ⟨hh,hfaith,hsame⟩ := higher_homogeneous_data_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv
  have hxx : (x : F.TerminalHdot) * x = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : F.TerminalHdot) x.property
  obtain ⟨J,hJ,hdis,hperp,hxJ⟩ := exists_stable_orthogonal_simple
    F.terminalRepresentation H R hsame B hyp.preserves hyp.alternating hyp.nondegenerate
    (source_large_point_constituent_isotropic_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv) x hxx
    (hyp.stabilizes_constituent_of_point_mem hi H hI hv x.property) hd
  have hJs : H ≤ subspaceStabilizer F.terminalRepresentation J.toSubmodule := by
    apply le_subspaceStabilizer
    exact fun h hh w hw => J.apply_mem_toSubmodule ⟨h,hh⟩ hw
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible F.terminalRepresentation
    hyp.faithful hi H hC.componentOrbit_top_ne_bot
  have hnfix : ¬ J.toSubmodule ≤ fixedSpace F.terminalRepresentation H := by
    intro he
    apply ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot
    apply Subrepresentation.toSubmodule_injective
    exact le_bot_iff.mp (he.trans_eq hfix)
  obtain ⟨K,hKJ,hK⟩ := exists_isIrrPlus_le_of_not_fixed F.terminalRepresentation H
    J.toSubmodule hJs hnfix
  let S : Subrepresentation (F.terminalRepresentation.comp H.subtype) :=
    ⟨K,fun h w hw => (hK.choose h.property w).mpr hw⟩
  have hSJ : S = J := ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).le_iff_eq
    (fun hb => hK.ne_bot F.terminalRepresentation (congrArg Subrepresentation.toSubmodule hb)) |>.mp hKJ
  have hJI : IsIrrPlus F.terminalRepresentation H J.toSubmodule :=
    (congrArg Subrepresentation.toSubmodule hSJ) ▸ hK
  have hvJ : v ∉ J.toSubmodule := fun hvJ => hyp.point_ne_zero
    ((Submodule.disjoint_def.mp hdis) v hv hvJ)
  exact ⟨J.toSubmodule,hJI,hvJ,hperp,hxJ⟩

private theorem source_large_marked_higher_natural_model_at
    (hd : 2 * finrank (ZMod 2) I < finrank (ZMod 2) (Additive F.Uhat)) :
    ∃ n, 5 ≤ n ∧ n ≤ 8 ∧
      ChapterG.Section09.Quasiequivalent
        (invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose).toRepresentation
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  let : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hC.componentOrbit_top_ne_bot
  have hn := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hn
  obtain ⟨_,hfaith,hsame⟩ := higher_homogeneous_data_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv
  have hnon : ¬ F.terminalDot (F.X g) ≤ centralizer (H : Set F.TerminalHdot) := by
    intro he
    apply hm
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
    exact (centralizer_le (le_componentOrbit C ⊤)).trans' he
  obtain ⟨x,hx,hxc⟩ := SetLike.not_le_iff_exists.mp hnon
  let a : F.terminalDot (F.X g) := ⟨x,hx⟩
  obtain ⟨J,hJ,hvJ,hperp,hxJ⟩ := higher_stable_orthogonal_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hd a
  let Q := invariantSubspace F.terminalRepresentation H J hJ.choose
  have hiQ : IsIrreducible Q.toRepresentation := hJ.irreducible_of_normal_restriction _ hi H
  obtain ⟨f,hf⟩ := hsame Q hiQ
  have hfQ : Function.Injective Q.toRepresentation := by
    intro b c he
    apply hfaith
    apply LinearMap.ext
    intro w
    apply f.injective
    exact (hf b w).trans ((LinearMap.congr_fun he (f w)).trans (hf c w).symm)
  have hr := orthogonal_rank_one hyp hi H hJ hv hvJ hperp hfQ a hxJ hxc
  have hdual := constituent_selfDual_of_sameModule F.terminalRepresentation H hi B hyp.preserves
    hyp.nondegenerate hJ (fun K hK => (hsame Q hiQ).symm.trans (hsame K hK))
  obtain ⟨n,hn5,hn8,_,e,c,hc⟩ := ChapterG.Section11.normal_constituent_natural_model
    F.terminalRepresentation H (zpowers x) J hJ.choose (zpowers_le.mpr hxJ)
    hiQ hfQ (by have he := hJ.finrank_gt_two F.terminalRepresentation H; omega)
    hdual (source_terminal_cover F d chosen) ⟨x,mem_zpowers _⟩
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx) hr
  exact ⟨n,hn5,hn8,e,f.trans c,fun b w => by change c (f (_)) = _; rw [hf,hc]; rfl⟩

theorem source_large_marked_double_at :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    finrank (ZMod 2) (Additive F.Uhat) = 2 * finrank (ZMod 2) I ∧
      Nonempty (Representation.Equiv (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype)
        (R.toRepresentation.prod R.toRepresentation)) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let R := invariantSubspace F.terminalRepresentation H I hI.choose
  have hn := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hn
  have hiR := hI.irreducible_of_normal_restriction _ hi H
  have hh := (higher_homogeneous_data_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).1
  have hiso := source_large_point_constituent_isotropic_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv
  have hl := B.twice_finrank_le_of_isotropic hyp.nondegenerate I hiso
  have hp : I ≠ ⊤ := by
    intro he
    exact hyp.point_ne_zero (hyp.nondegenerate.1 v
      (fun w => hiso v hv w (he.symm ▸ Submodule.mem_top)))
  have hu : finrank (ZMod 2) (Additive F.Uhat) ≤ 2 * finrank (ZMod 2) I := by
    by_contra hu
    obtain ⟨n,hn5,hn8,hmodel⟩ := source_large_marked_higher_natural_model_at d earlier hq chosen
      structural alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv (by omega)
    have hg := natural_schur_rank_gap R.toRepresentation n hn5 hn8 hmodel
    have hr := source_large_marked_actor_schur_bound_at d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv
    have hq := (Group.rank_le_of_surjective
      (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
      (QuotientGroup.mk'_surjective _)).trans
        (IsElementaryAbelian.rank_le_finrank (p := 2) (F.terminalDot (F.X g)))
    have hd := hyp.dimension_bound.1
    have hlt : finrank (ZMod 2) (Additive F.Uhat) < 3 * finrank (ZMod 2) I := by
      change 2 * (finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) +
        primeRank 2 (MulAut H) + 1) < 3 * finrank (ZMod 2) I at hg
      change finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
        finrank (ZMod 2) (IntertwiningMap R.toRepresentation R.toRepresentation) +
        primeRank 2 (MulAut H) at hr
      omega
    exact hu (Homogeneous.degree_le_double_of_lt_triple R hiR hh hp hlt)
  exact ⟨by omega,Homogeneous.double_coordinates_of_degree_le R hiR hh hp hu⟩

theorem source_large_marked_nontrivial_kernel_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    (hk : (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf
      (F.terminalDot (F.X g)) ≠ ⊥) :
    let Y := (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf
      (F.terminalDot (F.X g))
    Nat.card Y = 2 ∧
      finrank (ZMod 2) I = finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸ Y)) + 2 := by
  exact source_large_marked_double_kernel_at d earlier hq chosen structural alternatives classification
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn
    (source_large_marked_double_at d earlier hq chosen structural alternatives classification
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv).1 hk

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/FixedLineConstituent.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

open ChapterG.Section09

universe u v




open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry LargerDimension

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension.LocalAction.Components

open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
  (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
  (classification : EarlierFaithfulClassification G (T : Subgroup G))
  (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
  (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
  (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
  {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
  (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
  {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I) (hv : v ∈ I)

include d earlier hq chosen structural alternatives hne hZ hlarge hgP hgH hyp hC hm hI hv

private theorem fixed_constituent_data_at :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    Homogeneous.homogeneousPart R ⊤ = ⊤ ∧ Function.Injective R.toRepresentation ∧
      (∀ J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype),
        IsIrreducible J.toRepresentation → Homogeneous.SameModule R J) := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow_at d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hn := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  have ha := hyp.constituent_homogeneous_faithful_selfDual_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv
  exact ⟨ha.1,ha.2.1,hyp.constituent_sameModule_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv⟩

variable (hXI : F.terminalDot (F.X g) ≤ subspaceStabilizer F.terminalRepresentation I)

private noncomputable def fixed_constituent_actor_equiv_at :
    ((F.terminalDot (F.X g)) ⧸
      (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf
        (F.terminalDot (F.X g))) ≃*
      MarkedAction.image F.terminalRepresentation (componentOrbit C ⊤)
        (F.terminalDot (F.X g)) I hI.choose hXI (F.terminalDot (F.X g)) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let X := F.terminalDot (F.X g)
  let P := H ⊔ X
  let σ := MarkedAction.action F.terminalRepresentation H X I hI.choose hXI
  let q := QuotientGroup.mk' σ.ker
  let eX : X.subgroupOf P ≃* X := subgroupOfEquivOfLe (show X ≤ P from le_sup_right)
  let f := (q.subgroupMap (X.subgroupOf P)).comp eX.symm.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp eX.symm.surjective
  have hn := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hI.irreducible_of_normal_restriction _ (hyp.irreducible_of_not_solvable hn) H
  have hfaith := (fixed_constituent_data_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2.1
  have hker : f.ker = (centralizer (H : Set F.TerminalHdot)).subgroupOf X := by
    ext a
    change f a = 1 ↔ (a : F.TerminalHdot) ∈ centralizer (H : Set F.TerminalHdot)
    rw [Subtype.ext_iff]
    change (QuotientGroup.mk ⟨a,(show X ≤ P from le_sup_right) a.property⟩ : P ⧸ σ.ker) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    change σ ⟨a,(show X ≤ P from le_sup_right) a.property⟩ = 1 ↔ _
    rw [← MarkedAction.fixes_iff_centralizes F.terminalRepresentation H X I hI.choose hXI
      hfaith hi ⟨v,hv⟩ (fun he => hyp.point_ne_zero (congrArg Subtype.val he))
      a (hyp.fixes_point a.property)]
    constructor
    · intro he w
      exact congrArg Subtype.val (LinearMap.congr_fun he w)
    · intro he
      ext w
      exact he w
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)

include classification

theorem source_large_fixed_line_constituent_degree_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    finrank (ZMod 2) I ≤
      finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸
        (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf
          (F.terminalDot (F.X g)))) + 2 := by
  let X := F.terminalDot (F.X g)
  let Y := (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf X
  by_cases hk : Y = ⊥
  · let e : X ⧸ Y ≃* X :=
      (QuotientGroup.quotientMulEquivOfEq hk).trans QuotientGroup.quotientBot
    have hc : Nat.card (X ⧸ Y) = Nat.card X := Nat.card_congr e.toEquiv
    change Nat.card (Additive (X ⧸ Y)) = Nat.card (Additive X) at hc
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (X ⧸ Y)),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive X),Nat.card_zmod] at hc
    have hr := (Nat.pow_right_injective (by decide : 2 ≤ 2)) hc
    have hs := source_large_point_constituent_isotropic_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv
    have hb := hyp.isotropic_degree_le_actor_rank_add_one hs
    change finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive X) + 1 at hb
    change finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive (X ⧸ Y)) + 2
    omega
  · exact (source_large_marked_nontrivial_kernel_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn hk).2.le

theorem source_large_fixed_line_constituent_input_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    let H := componentOrbit C ⊤
    let X := F.terminalDot (F.X g)
    let Y := (centralizer (H : Set F.TerminalHdot)).subgroupOf X
    let σ := MarkedAction.action F.terminalRepresentation H X I hI.choose hXI
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple (kerRepresentation σ)
      (MarkedAction.image F.terminalRepresentation H X I hI.choose hXI X)
      (MarkedAction.image F.terminalRepresentation H X I hI.choose hXI C)
      (MarkedAction.image F.terminalRepresentation H X I hI.choose hXI H)
      (finrank (ZMod 2) (Additive (X ⧸ Y))) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let X := F.terminalDot (F.X g)
  let Y := (centralizer (H : Set F.TerminalHdot)).subgroupOf X
  have hns := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hI.irreducible_of_normal_restriction _ (hyp.irreducible_of_not_solvable hns) H
  obtain ⟨hh,hfaith,hsame⟩ := fixed_constituent_data_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv
  have hd := source_large_fixed_line_constituent_degree_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn
  change finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive (X ⧸ Y)) + 2 at hd
  refine componentHypothesis_constituent_image F.terminalRepresentation (source_terminal_cover F d chosen)
    X C H I hI.choose hXI hfaith hi (finrank (ZMod 2) (Additive (X ⧸ Y)))
    ?_ (by omega) hC hm (le_componentOrbit C ⊤) ?_
  · change Nat.card (MarkedAction.image F.terminalRepresentation H X I hI.choose hXI X) = _
    rw [← Nat.card_congr (fixed_constituent_actor_equiv_at d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI).toEquiv]
    change Nat.card (Additive (X ⧸ Y)) = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  · let := chosen.elementary
    have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
    rcases orbit_pair C hind with he | ⟨a,he⟩
    · exact Or.inl he
    have h₂H : C.map (MulAut.conj a).toMonoidHom ≤ H := by
      rw [show H = C ⊔ C.map (MulAut.conj a).toMonoidHom from he]
      exact le_sup_right
    exact Or.inr ⟨_,h₂H,hC.map_equiv (MulAut.conj a),he,
      ChapterG.Section09.constituent_quasiequivalent_conjugate F.terminalRepresentation H I
        hI.choose hi hsame C (le_componentOrbit C ⊤) a _ _⟩

theorem source_large_fixed_line_component_normal_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    componentOrbit C ⊤ = C ∧ C.Normal := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  have hns := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hXI := hyp.stabilizes_constituent_of_point_mem (hyp.irreducible_of_not_solvable hns) H hI hv
  have hc := source_large_fixed_line_constituent_input_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI hline hn
  have hd := source_large_fixed_line_constituent_degree_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn
  have he := ChapterG.Section09.TwoComponents.single_component_of_sharp_degree hc hd
  have hf := (fixed_constituent_data_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2.1
  have hHC := (MarkedAction.image_eq_iff F.terminalRepresentation H
    (F.terminalDot (F.X g)) I hI.choose hXI hf C (le_componentOrbit C ⊤)).mp he
  exact ⟨hHC,hHC ▸ (inferInstance : H.Normal)⟩

omit classification in
private theorem fixed_constituent_selfDual_image_at :
    let H := componentOrbit C ⊤
    let X := F.terminalDot (F.X g)
    let σ := MarkedAction.action F.terminalRepresentation H X I hI.choose hXI
    let Hbar := MarkedAction.image F.terminalRepresentation H X I hI.choose hXI H
    Nonempty (Representation.Equiv ((kerRepresentation σ).comp Hbar.subtype)
      (Representation.dual ((kerRepresentation σ).comp Hbar.subtype))) := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  have hns := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hns
  have hsame := (fixed_constituent_data_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2.2
  exact MarkedAction.selfDual_image F.terminalRepresentation H (F.terminalDot (F.X g)) I hI.choose hXI
    (constituent_selfDual_of_sameModule F.terminalRepresentation H hi B hyp.preserves
      hyp.nondegenerate hI hsame)

theorem source_large_fixed_line_single_input_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    let H := componentOrbit C ⊤
    let X := F.terminalDot (F.X g)
    let Y := (centralizer (H : Set F.TerminalHdot)).subgroupOf X
    let σ := MarkedAction.action F.terminalRepresentation H X I hI.choose hXI
    let Cbar := MarkedAction.image F.terminalRepresentation H X I hI.choose hXI C
    let Abar := MarkedAction.image F.terminalRepresentation H X I hI.choose hXI X
    ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple (kerRepresentation σ)
      Abar Cbar Cbar (finrank (ZMod 2) (Additive (X ⧸ Y))) ∧
      finrank (ZMod 2) I ≤ finrank (ZMod 2) (Additive (X ⧸ Y)) + 2 ∧
      Nonempty (Representation.Equiv ((kerRepresentation σ).comp Cbar.subtype)
        (Representation.dual ((kerRepresentation σ).comp Cbar.subtype))) ∧
      fixedSpace (kerRepresentation σ) Abar = Submodule.span (ZMod 2) {(⟨v,hv⟩ : I)} := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let X := F.terminalDot (F.X g)
  refine single_input_of_image_eq
    (source_large_fixed_line_constituent_input_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI hline hn)
    (congrArg (MarkedAction.image F.terminalRepresentation H X I hI.choose hXI)
      (source_large_fixed_line_component_normal_at d earlier hq chosen structural alternatives
        classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn).1)
    (source_large_fixed_line_constituent_degree_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn)
    (fixed_constituent_selfDual_image_at d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI) ?_
  have hf := (source_terminal_ranks_of_no_lowRank_at d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH v hline hn).1
  rw [← hline] at hf
  exact MarkedAction.fixedSpace_image_eq_line F.terminalRepresentation H X I hI.choose hXI ⟨v,hv⟩ hf

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end

/- Specialization of CaseOneLarge/FixedLineModels.lean at the original G,T. -/
section
open CFSG.Quasithin.Chapter14.Section04.CaseOneHS

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory

open scoped IsMulCommutative MatrixGroups

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge


open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag

open Chapter12.Section08.InvariantFlag.Symplectic

open Chapter14.Section03.CaseOneSource CaseOneGeometry

open Chapter14.Section03.NonabelianSource.Recognition

open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension

open LargerDimension LargerDimension.LocalAction.Components

open Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable

universe u

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
  (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
  (classification : EarlierFaithfulClassification G (T : Subgroup G))
  (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
  (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
  (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
  [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
    (hatSpace F (F.E g)) (F.terminalDot (F.X g))
    ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
  {C : Subgroup F.TerminalHdot} (hC : IsComponent F.TerminalHdot C)
  (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
  {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (hI : IsIrrPlus F.terminalRepresentation (componentOrbit C ⊤) I) (hv : v ∈ I)

include d earlier hq chosen structural alternatives hne hZ hlarge hgP hgH hyp hC hm hI hv

private theorem models_homogeneous_data_at :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    Homogeneous.homogeneousPart R ⊤ = ⊤ ∧ Function.Injective R.toRepresentation ∧
      (∀ J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype),
        IsIrreducible J.toRepresentation → Homogeneous.SameModule R J) := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow_at d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hn := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  have ha := hyp.constituent_homogeneous_faithful_selfDual_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv
  exact ⟨ha.1,ha.2.1,hyp.constituent_sameModule_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv⟩

include classification

private theorem fixed_line_original_carrier_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    FixedLineModels.SmallCarrier C := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let X := F.terminalDot (F.X g)
  have hns := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hXI := hyp.stabilizes_constituent_of_point_mem (hyp.irreducible_of_not_solvable hns) H hI hv
  have hinput := source_large_fixed_line_single_input_at d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI hline hn
  have hf := (models_homogeneous_data_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2.1
  let eC := MarkedAction.subgroupEquiv F.terminalRepresentation H X I hI.choose hXI hf
    C (le_componentOrbit C ⊤)
  have hc := FixedLineModels.smallCarrier_of_selfDual_sharp_fixed_line
    hinput.1 hinput.2.1 hinput.2.2.1 ⟨v,hv⟩
    (fun he => hyp.point_ne_zero (congrArg Subtype.val he)) hinput.2.2.2
  exact FixedLineModels.SmallCarrier.of_equiv eC hc

private theorem fixed_line_no_eight_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    (e : C ≃* alternatingGroup (Fin 8)) : False := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let X := F.terminalDot (F.X g)
  have hns := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hXI := hyp.stabilizes_constituent_of_point_mem (hyp.irreducible_of_not_solvable hns) H hI hv
  have hinput := source_large_fixed_line_single_input_at d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI hline hn
  have hHC := (source_large_fixed_line_component_normal_at d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn).1
  have hf := (models_homogeneous_data_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2.1
  let eC := MarkedAction.subgroupEquiv F.terminalRepresentation H X I hI.choose hXI hf
    C (le_componentOrbit C ⊤)
  have hm8 := ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.four_alternating_natural_of_selfDual
    hinput.1 hinput.2.2.1 ((eC.symm.trans e).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two)
  have hmH := model_of_subgroup_eq
    (congrArg (MarkedAction.image F.terminalRepresentation H X I hI.choose hXI) hHC) hm8
  have hmR := MarkedAction.quasiequivalent_of_image F.terminalRepresentation H X I hI.choose hXI hf
    (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) hmH
  let f := Classical.choice (source_large_marked_double_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2
  exact ChapterG.Section11.not_doubled_natural_eight hyp (source_terminal_cover F d chosen) H
    (fixed_doubled_model _ _ _ f hmR)

theorem source_large_fixed_line_component_models_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    C.Normal ∧ (Nonempty (C ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (C ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (C ≃* alternatingGroup (Fin 7))) := by
  refine ⟨(source_large_fixed_line_component_normal_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn).2,?_⟩
  rcases fixed_line_original_carrier_at d earlier hq chosen structural alternatives classification
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn with h5 | h6 | h7 | h8
  · exact Or.inl h5
  · exact Or.inr (Or.inl h6)
  · exact Or.inr (Or.inr h7)
  · obtain ⟨e8⟩ := h8
    exact (fixed_line_no_eight_at d earlier hq chosen structural alternatives classification
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn e8).elim

theorem source_large_fixed_line_marked_degree_at
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
      Nat.card (F.terminalDot (F.X g)) = 8 := by
  let H := componentOrbit C ⊤
  let : H.Normal := componentOrbit_top_normal C
  let X := F.terminalDot (F.X g)
  have hns := source_large_terminal_not_solvable_at d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hXI := hyp.stabilizes_constituent_of_point_mem (hyp.irreducible_of_not_solvable hns) H hI hv
  have hinput := source_large_fixed_line_single_input_at d earlier hq chosen structural
    alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hXI hline hn
  have hf := (models_homogeneous_data_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH hyp hC hm hI hv).2.1
  let eC := MarkedAction.subgroupEquiv F.terminalRepresentation H X I hI.choose hXI hf
    C (le_componentOrbit C ⊤)
  have hdI := FixedLineModels.small_alternating_degree hinput.1 hinput.2.1 eC
    (source_large_fixed_line_component_models_at d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn).2
  have hd := (source_large_marked_double_at d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv).1
  have he : finrank (ZMod 2) (Additive F.Uhat) = 8 := by omega
  exact ⟨hdI,he,(source_fixed_line_module_at d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH B v hyp hline hn).2.2 he |>.1⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge

end
