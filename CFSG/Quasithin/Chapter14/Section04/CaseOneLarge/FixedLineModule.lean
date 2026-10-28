module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CatalogueReduction
public import Theory.Representation.PGroupRegularCoordinates
public import Theory.Representation.TwistedRegularActor
public import Theory.Representation.BinaryOffender.PermutedSupports
public import Mathlib.GroupTheory.Schreier

/-!
# Cyclic and regular modules in the original fixed-line branch

A nonzero subspace stable under the elementary actor contains a fixed vector,
hence the marked point. The orthogonal complement argument therefore shows
that every vector pairing nontrivially with that point generates the module
under the actor. Its dimension is at most the actor's order.

Together with the original half-dimension rank equalities, this excludes degree
six. In degree eight the actor has order eight, so the p-group coefficient map
gives regular coordinates on the literal actor. The regular shifts then give
displacement rank four for every nonidentity actor. The final source reduction
retains these coordinates, the original flag and both G.11 branches.

These results do not identify the whole terminal group. The fixed-line and
remaining low-rank group/module recognitions, and hence the exhaustion of the
marked 14.4.2 catalogue, remain open.

Source: Aschbacher--Smith, G.11.1(3i), G.11.6--9 and 14.4.1--2,
printed pp.364--369,1006--1007; the p-group fixed-vector and regular-module
arguments are supplied by the imported representation lemmas.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLine
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {B : LinearMap.BilinForm (ZMod 2) W}
  {v : W} {E : Submodule (ZMod 2) W} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

private theorem point_mem_of_stable
    (_h : ChapterG.Section10.Hypothesis ρ B v E X X₀)
    (hf : fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (Q : Submodule (ZMod 2) W) (hQ : Q ≠ ⊥)
    (hs : X ≤ subspaceStabilizer ρ Q) : v ∈ Q := by
  obtain ⟨u,hu,hu0,huf⟩ := PermutedSupports.exists_nonzero_fixed ρ X
    (IsElementaryAbelian.isPGroup 2 X) Q hQ hs
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hf ▸ huf)
  have hc0 : c ≠ 0 := by
    intro hz
    exact hu0 (by simpa [hz] using hc.symm)
  exact (Q.smul_mem_iff hc0).mp (hc.symm ▸ hu)

private theorem span_eq_top_of_pairing_ne_zero
    (h : ChapterG.Section10.Hypothesis ρ B v E X X₀)
    (hf : fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (w : W) (hw : B w v ≠ 0) :
    Submodule.span (ZMod 2) (Set.range (fun x : X => ρ x w)) = ⊤ := by
  let Q := Submodule.span (ZMod 2) (Set.range (fun x : X => ρ x w))
  have hs : X ≤ subspaceStabilizer ρ Q := by
    apply le_subspaceStabilizer
    intro x hx u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨y,rfl⟩ := hu
      apply Submodule.subset_span
      refine ⟨(⟨x,hx⟩ : X)*y,?_⟩
      exact LinearMap.congr_fun (map_mul ρ x y) w
    | zero => simp
    | add a b ha hb iha ihb => simpa only [map_add] using Q.add_mem iha ihb
    | smul c a ha ih => simpa only [map_smul] using Q.smul_mem c ih
  have ho : B.orthogonal Q = ⊥ := by
    by_contra hne
    have hv := point_mem_of_stable h hf (B.orthogonal Q) hne
      (orthogonal_invariant ρ B h.preserves hs)
    apply hw
    exact hv w (Submodule.subset_span ⟨1,by simp⟩)
  have hh := B.orthogonal_orthogonal h.nondegenerate h.alternating.isRefl Q
  rw [ho,LinearMap.BilinForm.orthogonal_bot] at hh
  exact hh.symm

private theorem cyclic_and_bound
    (h : ChapterG.Section10.Hypothesis ρ B v E X X₀)
    (hf : fixedSpace ρ X = Submodule.span (ZMod 2) {v}) :
    (∃ w : W, B w v ≠ 0 ∧
      Submodule.span (ZMod 2) (Set.range (fun x : X => ρ x w)) = ⊤) ∧
      finrank (ZMod 2) W ≤ Nat.card X := by
  have hex : ∃ w : W, B w v ≠ 0 := by
    by_contra! hh
    exact h.point_ne_zero (h.nondegenerate.2 v hh)
  obtain ⟨w,hw⟩ := hex
  have hspan := span_eq_top_of_pairing_ne_zero h hf w hw
  refine ⟨⟨w,hw,hspan⟩,?_⟩
  let : Fintype X := Fintype.ofFinite X
  simpa only [Nat.card_eq_fintype_card] using finrank_le_of_span_eq_top hspan

private theorem elementary_card_eq_rank (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Nat.card A = 2 ^ Group.rank A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hc : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
  apply le_antisymm
  · exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' A
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)))
  · rw [hc]
    exact Nat.pow_le_pow_right (by decide) (IsElementaryAbelian.rank_le_finrank A)

private theorem regular_of_degree_eight
    (h : ChapterG.Section10.Hypothesis ρ B v E X X₀)
    (hf : fixedSpace ρ X = Submodule.span (ZMod 2) {v})
    (hE : 2 * finrank (ZMod 2) E = finrank (ZMod 2) W)
    (hX : Group.rank X + 1 = finrank (ZMod 2) E)
    (hd : finrank (ZMod 2) W = 8) :
    Nat.card X = 8 ∧ ∃ e : W ≃ₗ[ZMod 2] (X → ZMod 2),
      ∀ (a : X) w x, e (ρ a w) x = e w (a⁻¹ * x) := by
  have hc : Nat.card X = 8 := by
    rw [elementary_card_eq_rank X,show Group.rank X = 3 by omega]
    norm_num
  refine ⟨hc,?_⟩
  let : Fintype X := Fintype.ofFinite X
  apply Representation.TwistedRegular.exists_regular_coordinates (ρ.comp X.subtype)
    (by rw [ringChar.eq (ZMod 2) 2]; decide)
    (by rw [ringChar.eq (ZMod 2) 2]; exact IsElementaryAbelian.isPGroup 2 X) v h.point_ne_zero
  · intro u hu
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hf ▸ (show u ∈ fixedSpace ρ X from hu))
    exact ⟨c,hc.symm⟩
  · simpa only [← Nat.card_eq_fintype_card,hc] using hd
private theorem movedRank_of_regular
    (e : W ≃ₗ[ZMod 2] (X → ZMod 2))
    (he : ∀ (a : X) w x, e (ρ a w) x = e w (a⁻¹ * x))
    (hc : Nat.card X = 8) (hd : finrank (ZMod 2) W = 8)
    (a : X) (ha : a ≠ 1) : finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 4 := by
  let : Fintype X := Fintype.ofFinite X
  have ha2 : a * a = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 X) a
  let S : Module.End (ZMod 2) (X → ZMod 2) :=
    e.toLinearMap.comp ((ρ a).comp e.symm.toLinearMap)
  have heq (w : W) : e (ρ a w) = S (e w) := by simp [S]
  have hl := Representation.TwistedRegular.finrank_le_twice_displacement
    (Equiv.mulLeft a⁻¹) (u := fun _ => LinearMap.id) (T := S)
    (by intro x; change a⁻¹ * (a⁻¹ * x) = x
        rw [← mul_assoc,← mul_inv_rev,ha2,inv_one,one_mul])
    (by intro x hx; exact ha (inv_eq_one.mp (mul_right_cancel
          (show a⁻¹*x = 1*x by simpa using hx))))
    (by intro f x; change e (ρ a (e.symm f)) x = _
        rw [he,e.apply_symm_apply]; rfl)
  have ht := NaturalTensor.operatorFixedCodim_eq_of_equiv (ρ a) S e heq
  rw [← ht] at hl
  have hc' : Fintype.card X = 8 := by simpa only [Nat.card_eq_fintype_card] using hc
  simp only [hc',Module.finrank_self,mul_one] at hl
  change 8 ≤ 2 * finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) at hl
  have hk : LinearMap.range (ρ a - LinearMap.id) ≤ LinearMap.ker (ρ a - LinearMap.id) := by
    rintro _ ⟨w,rfl⟩
    change ρ a (ρ a w - w) - (ρ a w - w) = 0
    rw [map_sub,← Module.End.mul_apply,← map_mul,
      show (a:D)*a=1 from congrArg Subtype.val ha2,map_one,Module.End.one_apply]
    have hneg (w : W) : -w = w := by
      apply neg_eq_iff_add_eq_zero.mpr
      have hh := @two_smul (ZMod 2) W _ _ _ w
      rw [show (2 : ZMod 2)=0 by decide,zero_smul] at hh
      exact hh.symm
    simp only [sub_eq_add_neg,hneg]
    exact add_eq_zero_iff_eq_neg.mpr (by rw [hneg]; exact add_comm _ _)
  have hr := Submodule.finrank_mono hk
  have hn := (ρ a - LinearMap.id).finrank_range_add_finrank_ker
  omega
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLine

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Module information derived in the fixed-line branch. Regular coordinates
identify the restriction to the original elementary actor, with its literal
translation action; they do not identify the whole terminal group. -/
@[expose] def FixedLineModuleData {D W : Type*} [Group D] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (B : LinearMap.BilinForm (ZMod 2) W)
    (v : W) (X : Subgroup D) : Prop :=
  (∃ w : W, B w v ≠ 0 ∧
    Submodule.span (ZMod 2) (Set.range (fun a : X => ρ a w)) = ⊤) ∧
  8 ≤ finrank (ZMod 2) W ∧
  (finrank (ZMod 2) W = 8 → Nat.card X = 8 ∧
    ∃ e : W ≃ₗ[ZMod 2] (X → ZMod 2),
      (∀ (a : X) w x, e (ρ a w) x = e w (a⁻¹ * x)) ∧
      ∀ a : X, a ≠ 1 → finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 4)

/-- The original large fixed-line branch is cyclic on its actual actor and has
degree at least eight. At degree eight it is the regular actor module, and
every nonidentity actor has displacement rank four. -/
theorem source_fixed_line_module (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (hn : ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) := by
  obtain ⟨hf,hE,hX,_⟩ := source_terminal_ranks_of_no_lowRank d earlier hq chosen structural
    alternatives F hne hZ g hgP hgH v hline hn
  rw [← hline] at hf
  obtain ⟨hgen,hbound⟩ := FixedLine.cyclic_and_bound hyp hf
  refine ⟨hgen,?_,?_⟩
  · have hd : 4 < finrank (ZMod 2) (Additive F.Uhat) := by
      have hcenter := (source_extraspecial_order d earlier hq chosen structural alternatives
        F hne hZ).1.center_order_p
      have hc : Nat.card F.U = 2 ^ (finrank (ZMod 2) (Additive F.Uhat) + 1) := by
        rw [card_eq_card_quotient_mul_card_subgroup (center F.U),hcenter]
        change Nat.card (Additive F.Uhat) * 2 = _
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,pow_succ]
      by_contra hh
      have hb := Nat.pow_le_pow_right (n := 2) (by decide)
        (by omega : finrank (ZMod 2) (Additive F.Uhat) + 1 ≤ 5)
      rw [← hc] at hb
      norm_num at hb
      omega
    have h6 : finrank (ZMod 2) (Additive F.Uhat) ≠ 6 := by
      intro h6
      have hr : Group.rank (F.terminalDot (F.X g)) = 2 := by omega
      rw [FixedLine.elementary_card_eq_rank _,hr,h6] at hbound
      norm_num at hbound
    omega
  · intro h8
    obtain ⟨hc,e,he⟩ := FixedLine.regular_of_degree_eight hyp hf hE hX h8
    exact ⟨hc,e,he,FixedLine.movedRank_of_regular e he hc h8⟩

/-- The original catalogue reduction, now excluding degree six in the fixed-line
branch and supplying actual regular actor coordinates when its degree is eight.
The low-rank component recognition and whole-group catalogue remain open. -/
theorem source_large_catalogue_reduction_with_fixed_module (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ((¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
          fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
          2 * finrank (ZMod 2) (hatSpace F (F.E g)) = finrank (ZMod 2) (Additive F.Uhat) ∧
          Group.rank (F.terminalDot (F.X g)) + 1 = finrank (ZMod 2) (hatSpace F (F.E g)) ∧
          (∀ a b : F.terminalDot (F.X g),
            (∀ w : hatSpace F (F.E g),
              F.terminalRepresentation a w = F.terminalRepresentation b w) → a = b) ∧
          FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g))) ∨
        ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ChapterG.Section11.ExchangedRecognition.RemainingComponentModels
            F.terminalRepresentation B v (hatSpace F (F.E g)) (F.terminalDot (F.X g)))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hcases⟩ := source_large_catalogue_reduction d earlier hq
    chosen structural alternatives F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,?_⟩
  rcases hcases with ⟨hn,hf,hE,hX,hinj⟩ | hc
  · exact Or.inl ⟨hn,hf,hE,hX,hinj,source_fixed_line_module d earlier hq chosen structural
      alternatives F hne hZ hlarge g hgP hgH B v hyp hline hn⟩
  · exact Or.inr hc
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
