module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ComponentOrbitExclusion
public import CFSG.Quasithin.ChapterG.Section10.Components.CentralizerDisplacement
public import Theory.Representation.BinaryOffender.Homogeneous.SchurDisplacementRank

/-!
# Multiplicity of the original marked component constituent

The normal component orbit is homogeneous and faithful on the constituent
through the marked point. Every nonidentity centralizing actor has that
constituent as its displacement space and its perpendicular as fixed space.
This bounds the actor rank by the constituent's Schur degree and the two-rank
of the component-orbit automorphism group.

A nonzero displacement of rank at most two forces exactly two copies, with
literal intertwining coordinates. In the fixed-line branch, when there are
two copies, the nontrivial centralizing actor kernel has order two: its action
on a vector in E outside the constituent is free and has at most two values.
The quotient consequently loses exactly one binary dimension. These results
retain the original flag and both G.11 clauses; catalogue recognition remains
an assembly obligation.

In degree eight homogeneity itself forces exactly two four-dimensional
copies, under either fixed-point clause. The fixed-line application then
leaves precisely kernel orders one and two, with quotient ranks three and
two respectively, without an assumed multiplicity or kernel size.

The kernel count adapts ComponentCatalogueMarkedKernelTwoCopies for the
original rank-three flag, using its proved fixed-line rank equalities.
Source: Aschbacher--Smith G.10.12--16, G.11.7--9 and 14.4.2,
printed pp.360--369,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter14.Section03.NonabelianSource.Recognition
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction.Components
private theorem marked_double_of_lt_three
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {ρ : Representation (ZMod 2) D W}
    (R : Subrepresentation ρ) (hi : IsIrreducible R.toRepresentation)
    (hh : Homogeneous.homogeneousPart R ⊤ = ⊤) (hp : R.toSubmodule ≠ ⊤)
    (hd : finrank (ZMod 2) W < 3 * finrank (ZMod 2) R.toSubmodule) :
    Nonempty (ρ.Equiv (R.toRepresentation.prod R.toRepresentation)) := by
  have hex (N : Subrepresentation ρ) (hN : N.toSubmodule ≠ ⊤) :
      ∃ J : Subrepresentation ρ, Homogeneous.SameModule R J ∧ ¬ J ≤ N := by
    by_contra! hn
    apply hN
    apply top_unique
    rw [← hh]
    exact iSup_le fun J => iSup_le fun hj => hn J hj.2
  obtain ⟨J,hJ,hJR⟩ := hex R hp
  have hiJ := hJ.irreducible hi
  have hdis : Disjoint R.toSubmodule J.toSubmodule := by
    rw [disjoint_iff]
    exact congrArg Subrepresentation.toSubmodule
      (((Subrepresentation.irreducible_iff_isAtom J).mp hiJ).not_le_iff_disjoint.mp hJR).symm.eq_bot
  have heJ : finrank (ZMod 2) J.toSubmodule = finrank (ZMod 2) R.toSubmodule :=
    hJ.choose.finrank_eq.symm
  have heRJ : finrank (ZMod 2) (R ⊔ J).toSubmodule = 2 * finrank (ZMod 2) R.toSubmodule := by
    have hs := Submodule.finrank_sup_add_finrank_inf_eq R.toSubmodule J.toSubmodule
    rw [hdis.eq_bot,finrank_bot,add_zero,heJ] at hs
    change finrank (ZMod 2) (R.toSubmodule ⊔ J.toSubmodule : Submodule (ZMod 2) W) = _
    omega
  have htop : (R ⊔ J).toSubmodule = ⊤ := by
    by_contra hn
    obtain ⟨K,hK,hKRJ⟩ := hex (R ⊔ J) hn
    have hiK := hK.irreducible hi
    have heK := hK.choose.finrank_eq
    have hdK : Disjoint K.toSubmodule (R ⊔ J).toSubmodule := by
      rw [disjoint_iff]
      exact congrArg Subrepresentation.toSubmodule
        (((Subrepresentation.irreducible_iff_isAtom K).mp hiK).not_le_iff_disjoint.mp hKRJ).eq_bot
    have hs := Submodule.finrank_sup_add_finrank_inf_eq K.toSubmodule (R ⊔ J).toSubmodule
    rw [hdK.eq_bot,finrank_bot,add_zero,heRJ] at hs
    have hb := (K.toSubmodule ⊔ (R ⊔ J).toSubmodule).finrank_le
    omega
  rw [htop,finrank_top] at heRJ
  exact Homogeneous.double_coordinates_of_degree_le R hi hh hp heRJ.le

private theorem marked_binary_rank (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Group.rank A = finrank (ZMod 2) (Additive A) := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  apply le_antisymm (IsElementaryAbelian.rank_le_finrank (p := 2) A)
  have hc : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [← hc]
  exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' A
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)))

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
  (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
  (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
  (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
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

private theorem marked_homogeneous_data :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    Homogeneous.homogeneousPart R ⊤ = ⊤ ∧ Function.Injective R.toRepresentation ∧
      (∀ J : Subrepresentation (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype),
        IsIrreducible J.toRepresentation → Homogeneous.SameModule R J) := by
  let := chosen.elementary
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  obtain ⟨hXP,hN⟩ := source_terminal_actor_normal_in_sylow d earlier hq chosen
    structural alternatives F hne g hgP hgH
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hind := terminal_component_normalizer_index_le_two d.qtke F (by decide) C hC
  have ha := hyp.constituent_homogeneous_faithful_selfDual_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv
  exact ⟨ha.1,ha.2.1,hyp.constituent_sameModule_of_point_mem hn hC hm P
    ((normal_subgroupOf_iff_le_normalizer hXP).mp hN) hind hI hv⟩

/-- The displacement of every nonidentity actor centralizing the original
component orbit is exactly the marked constituent. Its fixed space is the
perpendicular of that same constituent. Both G.11 fixed-point clauses apply. -/
theorem source_large_marked_centralizer_displacement
    (c : F.terminalDot (F.X g))
    (hc : (c : F.TerminalHdot) ∈ centralizer (componentOrbit C ⊤ : Set F.TerminalHdot))
    (hc1 : c ≠ 1) :
    LinearMap.range (F.terminalRepresentation c - LinearMap.id) = I ∧
      LinearMap.ker (F.terminalRepresentation c - LinearMap.id) = B.orthogonal I := by
  let H := componentOrbit C ⊤
  let := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hn
  have ha := marked_homogeneous_data d earlier hq chosen structural alternatives F hne hZ
    hlarge g hgP hgH hyp hC hm hI hv
  exact hyp.centralizer_displacement_range_and_ker hi H hC.componentOrbit_top_ne_bot
    (invariantSubspace F.terminalRepresentation H I hI.choose)
    (hI.irreducible_of_normal_restriction _ hi H) ha.1 hv
    (by change 3 ≤ finrank (ZMod 2) I
        have hh := hI.finrank_gt_two F.terminalRepresentation H
        omega) c hc hc1

/-- The original actor rank is bounded by the actual constituent endomorphism
space and the automorphism two-rank of its normal component orbit. -/
theorem source_large_marked_actor_schur_bound :
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
    (source_large_marked_centralizer_displacement d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv)

include classification

/-- Any nonidentity element of the original terminal group with displacement
at most two forces multiplicity exactly two and rank one on the constituent.
The element need not belong to the marked elementary actor. -/
theorem source_large_marked_double_of_small_displacement
    (a : F.TerminalHdot) (ha : a ≠ 1)
    (hr : finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - LinearMap.id)) ≤ 2) :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    finrank (ZMod 2) (Additive F.Uhat) = 2 * finrank (ZMod 2) I ∧
      Nonempty (Representation.Equiv (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype)
        (R.toRepresentation.prod R.toRepresentation)) ∧
      I.map (F.terminalRepresentation a) = I ∧
      finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - LinearMap.id)) = 2 ∧
      finrank (ZMod 2) (I.map (F.terminalRepresentation a - LinearMap.id)) = 1 := by
  let H := componentOrbit C ⊤
  let := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hn
  have hd := hI.finrank_gt_two F.terminalRepresentation H
  have ha' := marked_homogeneous_data d earlier hq chosen structural alternatives F hne hZ
    hlarge g hgP hgH hyp hC hm hI hv
  have hiso := source_large_point_constituent_isotropic d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv
  have hp : I ≠ ⊤ := by
    intro he
    apply hyp.point_ne_zero
    exact hyp.nondegenerate.1 v (fun w => hiso v hv w (he.symm ▸ Submodule.mem_top))
  have hpos : 0 < finrank (ZMod 2) (LinearMap.range
      (F.terminalRepresentation a - LinearMap.id)) := by
    apply Nat.pos_of_ne_zero
    intro hz
    apply ha
    apply hyp.faithful
    rw [map_one]
    apply LinearMap.ext
    intro w
    change F.terminalRepresentation a w = w
    have hh : F.terminalRepresentation a w - w ∈
        LinearMap.range (F.terminalRepresentation a - LinearMap.id) := ⟨w,rfl⟩
    rw [Submodule.finrank_eq_zero.mp hz] at hh
    exact sub_eq_zero.mp hh
  exact Homogeneous.double_and_rank_one_of_small_displacement F.terminalRepresentation H
    (invariantSubspace F.terminalRepresentation H I hI.choose)
    (hI.irreducible_of_normal_restriction _ hi H) ha'.1 ha'.2.1 ha'.2.2
    (by change 3 ≤ finrank (ZMod 2) I; omega) a hpos hr hp

/-- Higher marked multiplicity excludes every nonidentity displacement of
rank at most two in the whole terminal group, and forces the original fixed
line, half-dimension equalities, and cyclic actor module. -/
theorem source_large_marked_higher_fixed_line
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hd : 2 * finrank (ZMod 2) I < finrank (ZMod 2) (Additive F.Uhat)) :
    (∀ a : F.TerminalHdot, a ≠ 1 →
      2 < finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - LinearMap.id))) ∧
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
    2 * finrank (ZMod 2) (hatSpace F (F.E g)) = finrank (ZMod 2) (Additive F.Uhat) ∧
    Group.rank (F.terminalDot (F.X g)) + 1 = finrank (ZMod 2) (hatSpace F (F.E g)) ∧
    FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) := by
  have hall (a : F.TerminalHdot) (ha : a ≠ 1) :
      2 < finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - LinearMap.id)) := by
    by_contra hr
    have he := (source_large_marked_double_of_small_displacement d earlier hq chosen structural
      alternatives classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv a ha (by omega)).1
    omega
  have hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) := by
    rintro ⟨a,ha,hr,hav⟩
    have ha1 : a ≠ 1 := by
      intro he
      apply hyp.point_ne_zero
      simpa [RankTwo.movedSpace,he] using hav
    exact (not_le_of_gt (hall a ha1)) hr
  obtain ⟨hf,hE,hX,_⟩ := source_terminal_ranks_of_no_lowRank d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH v hline hn
  exact ⟨hall,hf,hE,hX,source_fixed_line_module d earlier hq chosen structural alternatives
    F hne hZ hlarge g hgP hgH B v hyp hline hn⟩


/-- In degree eight, every original marked component constituent has
binary degree four and occurs exactly twice, under either fixed-point clause.
No assumption on the constituent's actor kernel or multiplicity is needed. -/
theorem source_large_marked_degree_eight
    (h8 : finrank (ZMod 2) (Additive F.Uhat) = 8) :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    finrank (ZMod 2) I = 4 ∧
      Nonempty (Representation.Equiv (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype)
        (R.toRepresentation.prod R.toRepresentation)) := by
  let H := componentOrbit C ⊤
  let := componentOrbit_top_normal C
  let : Group.IsPerfect H := hC.orbit_isPerfect ⊤
  have hn := source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge
  have hi := hyp.irreducible_of_not_solvable hn
  have ha := marked_homogeneous_data d earlier hq chosen structural alternatives F hne hZ
    hlarge g hgP hgH hyp hC hm hI hv
  have hiso := source_large_point_constituent_isotropic d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv
  have hp : I ≠ ⊤ := by
    intro he
    exact hyp.point_ne_zero (hyp.nondegenerate.1 v
      (fun w => hiso v hv w (he.symm ▸ Submodule.mem_top)))
  have hdegree := hI.finrank_gt_two F.terminalRepresentation H
  obtain ⟨e⟩ := marked_double_of_lt_three
    (invariantSubspace F.terminalRepresentation H I hI.choose)
    (hI.irreducible_of_normal_restriction _ hi H) ha.1 hp
    (by change finrank (ZMod 2) (Additive F.Uhat) < 3 * finrank (ZMod 2) I; omega)
  have he := e.toLinearEquiv.finrank_eq
  rw [Module.finrank_prod] at he
  change finrank (ZMod 2) (Additive F.Uhat) = finrank (ZMod 2) I + finrank (ZMod 2) I at he
  exact ⟨by omega,⟨e⟩⟩

/-- In the fixed-line two-copy branch a nontrivial component centralizer
inside the original actor has order two. The quotient is the literal
X/C_X(H), whose binary degree is the constituent degree minus two. -/
theorem source_large_marked_double_kernel
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
  have hiso := source_large_point_constituent_isotropic d earlier hq chosen structural alternatives
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
    exact (source_large_marked_centralizer_displacement d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH hyp hC hm hI hv y hyC hy).2
  obtain ⟨_,hE,hX,hfaith⟩ := source_terminal_ranks_of_no_lowRank d earlier hq chosen
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

/-- The degree-eight fixed-line branch determines both the multiplicity
and every possible rank of the literal constituent actor quotient. The
centralizer kernel has order one or two, and the quotient rank is respectively
three or two. No kernel-size or multiplicity premise is retained. -/
theorem source_large_marked_degree_eight_quotient
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)))
    (h8 : finrank (ZMod 2) (Additive F.Uhat) = 8) :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit C ⊤) I hI.choose
    let Y := (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf
      (F.terminalDot (F.X g))
    finrank (ZMod 2) I = 4 ∧
      Nonempty (Representation.Equiv (F.terminalRepresentation.comp (componentOrbit C ⊤).subtype)
        (R.toRepresentation.prod R.toRepresentation)) ∧
      ((Nat.card Y = 1 ∧ finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸ Y)) = 3) ∨
       (Nat.card Y = 2 ∧ finrank (ZMod 2) (Additive ((F.terminalDot (F.X g)) ⧸ Y)) = 2)) := by
  obtain ⟨h4,he⟩ := source_large_marked_degree_eight d earlier hq chosen structural alternatives
    classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv h8
  refine ⟨h4,he,?_⟩
  let X := F.terminalDot (F.X g)
  let Y := (centralizer (componentOrbit C ⊤ : Set F.TerminalHdot)).subgroupOf X
  by_cases hk : Y = ⊥
  · left
    have hc : Nat.card Y = 1 := by rw [hk]; exact Subgroup.card_bot
    refine ⟨hc,?_⟩
    obtain ⟨_,hE,hX,_⟩ := source_terminal_ranks_of_no_lowRank d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH v hline hn
    rw [marked_binary_rank] at hX
    have hx : finrank (ZMod 2) (Additive X) = 3 := by
      change finrank (ZMod 2) (Additive X) + 1 = finrank (ZMod 2) (hatSpace F (F.E g)) at hX
      omega
    have hcX : Nat.card X = 8 := by
      rw [Nat.card_congr Additive.ofMul,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hx]
      norm_num
    have hq := Y.index_mul_card
    rw [Subgroup.index_eq_card,hc,mul_one,hcX] at hq
    rw [Nat.card_congr Additive.ofMul,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hq
    exact Nat.pow_right_injective (by decide : 2 ≤ 2) hq
  · obtain ⟨hc,hr⟩ := source_large_marked_double_kernel d earlier hq chosen structural alternatives
      classification F hne hZ hlarge g hgP hgH hyp hC hm hI hv hline hn (by omega) hk
    exact Or.inr ⟨hc,by omega⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
