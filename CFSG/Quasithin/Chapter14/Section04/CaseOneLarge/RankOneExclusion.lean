module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.RankOneReduction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.FullLinearExclusion
public import Theory.Representation.SL2.BinarySmallInvolution.TripleFixedSpaces
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration

/-!
# Excluding the rank-one remainder using the original seed

A proper nonzero seed subspace stable under a component Sylow has a stabilizer
that normalizes that Sylow. Indeed its intersection with the irreducible SL₂
component is proper, so the rank-one Borel theorem places it in the Sylow
normalizer. Normality of the component makes the same statement hold for the
whole seed stabilizer.

For the SL₂(8) triple tensor the component Sylow fixes exactly a binary line.
The original Sylow fixes the marked point and stabilizes the original
V/V₁ seed plane. Hence every seed stabilizer fixes that point, contradicting
the actual L₁ movement supplied by the original flag. Applying the checked
rank-one reduction excludes every normal irreducible Bender component in
both clauses of G.11.1(3), with no low-rank witness assumed.

This closes the rank-one component branch. The other component and multiplicity
branches, and exhaustion of the marked whole-group catalogue, remain required
for the large-case source assembly.

Source: Aschbacher--Smith, G.11.2(11), 12.8.5 and 14.4.2, printed
pp.364,850,1006--1007; `refs/quasithin.pdf`. The Sylow fixed-space calculation
is the imported triple-tensor regular-module theorem.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups TensorProduct
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.RankOne
variable {D W k : Type*} [Group D] [Finite D] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  [Field k] [Finite k] [CharP k 2]

omit [FiniteDimensional (ZMod 2) W] in
private theorem seed_normalizes_component_sylow
    (ρ : Representation (ZMod 2) D W) (C : Subgroup D) [C.Normal]
    [IsIrreducible (ρ.comp C.subtype)] (e : C ≃* SL(2,k))
    (P : Sylow 2 C) (U : Submodule (ZMod 2) W)
    (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤)
    (hPU : (P : Subgroup C) ≤ subspaceStabilizer (ρ.comp C.subtype) U) :
    subspaceStabilizer ρ U ≤ normalizer (((P : Subgroup C).map C.subtype) : Set D) := by
  let M := subspaceStabilizer (ρ.comp C.subtype) U
  have hM : M ≠ ⊤ := by
    intro hm
    let S : Subrepresentation (ρ.comp C.subtype) := {
      toSubmodule := U
      apply_mem_toSubmodule c w hw := (show c ∈ M from hm ▸ mem_top c) w |>.2 hw }
    have hs0 : S ≠ ⊥ := fun hh => hU0 (congrArg Subrepresentation.toSubmodule hh)
    have hs := ((inferInstance : IsIrreducible (ρ.comp C.subtype)).eq_bot_or_eq_top S).resolve_left hs0
    exact hU1 (congrArg Subrepresentation.toSubmodule hs)
  let R : Sylow 2 SL(2,k) := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRM : (R : Subgroup SL(2,k)) ≤ M.map e.toMonoidHom := map_mono hPU
  have hM' : M.map e.toMonoidHom ≠ ⊤ := by
    intro hm
    apply hM
    apply top_unique
    intro c _
    obtain ⟨b,hb,he⟩ := (show e c ∈ M.map e.toMonoidHom from hm ▸ mem_top _)
    exact e.injective he ▸ hb
  have hMN : M ≤ normalizer (P : Set C) := by
    have hn := Matrix.SpecialLinearGroup.overgroup_le_sylowNormalizer R hRM hM'
    intro c hc
    have hh := hn (mem_map_of_mem e.toMonoidHom hc)
    change e c ∈ normalizer (((P : Subgroup C).map e.toMonoidHom) : Set SL(2,k)) at hh
    rw [← map_normalizer_eq_of_bijective _ e.bijective] at hh
    obtain ⟨b,hb,he⟩ := hh
    exact e.injective he ▸ hb
  apply le_normalizer_iff.mpr
  intro a ha y hy
  obtain ⟨x,hx,rfl⟩ := hy
  let α : MulAut C := MulAut.conjNormal a
  let Q : Sylow 2 C := P.mapSurjective (f := α.toMonoidHom) α.surjective
  have hQM : (Q : Subgroup C) ≤ M := by
    apply le_subspaceStabilizer
    rintro _ ⟨b,hb,rfl⟩ w hw
    change ρ (a * (b : D) * a⁻¹) w ∈ U
    rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply]
    exact (ha _).2 ((hPU hb _).2 (((subspaceStabilizer ρ U).inv_mem ha _).2 hw))
  have hh := Q.isPGroup'.inf_normalizer_sylow P
  rw [inf_eq_left.mpr (hQM.trans hMN)] at hh
  have hQP : (Q : Subgroup C) ≤ (P : Subgroup C) := inf_eq_left.mp hh.symm
  exact ⟨α x,hQP (mem_map_of_mem α.toMonoidHom hx),rfl⟩

local instance : Algebra (ZMod 2) k := SL2.BinarySmall.binaryAlgebra

private theorem triple_seed_point_fixed
    (ρ : Representation (ZMod 2) D W) (C : Subgroup D) [C.Normal]
    [IsIrreducible (ρ.comp C.subtype)] (e : C ≃* SL(2,k))
    (hk : Nat.card k = 8)
    (ht : SL2.BinarySmall.IsTriple ((ρ.comp C.subtype).comp e.symm.toMonoidHom))
    (S : Sylow 2 D) (U : Submodule (ZMod 2) W)
    (hd : finrank (ZMod 2) U = 2)
    (hSU : (S : Subgroup D) ≤ subspaceStabilizer ρ U)
    (v : W) (hv : v ≠ 0) (hSv : v ∈ fixedSpace ρ S)
    (a : D) (ha : a ∈ subspaceStabilizer ρ U) : ρ a v = v := by
  obtain ⟨P,hP⟩ := S.exists_sylow_map_eq_inf_of_normal C
  let σ := (ρ.comp C.subtype).comp e.symm.toMonoidHom
  let R : Sylow 2 SL(2,k) := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hR : Nat.card R = 8 := by
    rw [← Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 R).toEquiv]
    exact hk
  have hdim := SL2.BinarySmall.TripleFixedSpaces.binary_fixed_mul_card hk σ ht
    (R : Subgroup SL(2,k)) R.isPGroup'
  rw [hR] at hdim
  let A := (P : Subgroup C).map C.subtype
  have hAS : A ≤ (S : Subgroup D) := by
    change (P : Subgroup C).map C.subtype ≤ (S : Subgroup D)
    rw [hP]
    exact inf_le_left
  have hfixed : fixedSpace σ R = fixedSpace ρ A := by
    ext w
    constructor
    · intro hw b
      obtain ⟨c,hc,he⟩ := b.property
      have hh := hw ⟨e c,mem_map_of_mem e.toMonoidHom hc⟩
      change ρ ((e.symm (e c) : C) : D) w = w at hh
      rw [e.symm_apply_apply] at hh
      change ρ (b : D) w = w
      change (c : D) = (b : D) at he
      rw [he] at hh
      exact hh
    · intro hw b
      obtain ⟨c,hc,he⟩ := b.property
      have hh := hw ⟨(c : D),mem_map_of_mem C.subtype hc⟩
      change ρ ((e.symm b : C) : D) w = w
      rw [← he]
      change ρ ((e.symm (e c) : C) : D) w = w
      rw [e.symm_apply_apply]
      exact hh
  have hf1 : finrank (ZMod 2) (fixedSpace ρ A) = 1 := by rw [← hfixed]; omega
  have hvA : v ∈ fixedSpace ρ A := fun b => hSv ⟨b,hAS b.property⟩
  have hU0 : U ≠ ⊥ := by
    intro h
    have hz : finrank (ZMod 2) U = 0 := by rw [h]; exact finrank_bot (ZMod 2) W
    omega
  have hU1 : U ≠ ⊤ := by
    intro h
    have h8 := SL2.BinarySmall.TripleFixedSpaces.binary_finrank σ ht
    rw [h,finrank_top,h8] at hd
    omega
  have hn := seed_normalizes_component_sylow ρ C e P U hU0 hU1
    (by intro c hc w; exact hSU (hAS (mem_map_of_mem C.subtype hc)) w)
  have hfix : ρ a v ∈ fixedSpace ρ A := by
    intro b
    have hb : a⁻¹ * (b : D) * a ∈ A := by
      simpa only [inv_inv] using (mem_normalizer_iff.mp
        ((normalizer (A : Set D)).inv_mem (hn ha)) (b : D)).mp b.property
    have hh := congrArg (ρ a) (hvA ⟨_,hb⟩)
    change ρ a (ρ (a⁻¹ * (b : D) * a) v) = ρ a v at hh
    change ρ (b : D) (ρ a v) = ρ a v
    simpa only [map_mul,Module.End.mul_apply,ρ.self_inv_apply] using hh
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hf1 hvA hv
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ hfix)
  have hc0 : c ≠ 0 := by
    intro hz
    have hh := congrArg (ρ a⁻¹) hc
    rw [hz,zero_smul,map_zero,ρ.inv_self_apply] at hh
    exact hv hh.symm
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa only [hc1,one_smul] using hc.symm
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.RankOne

namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem rankOne_seed_stable (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 F.Uhat]
    (a : F.H) (ha : (a:G) ∈ normalizer (V : Set G)) (w : Additive F.Uhat)
    (hw : w ∈ hatSpace F V) :
    F.terminalRepresentation (QuotientGroup.mk' F.terminalHatAction.ker a) w ∈ hatSpace F V := by
  obtain ⟨b,hb,he⟩ := (show w.toMul ∈ hatImage F V from hw)
  refine ⟨F.uAction a b,(mem_normalizer_iff.mp ha (b:G)).mp hb,?_⟩
  change QuotientGroup.mk' (center F.U) (F.uAction a b) = F.uhatAction a w.toMul
  rw [← F.uhatAction_apply_mk,he]

/-- The original seed excludes an irreducible normal SL₂(8) triple-tensor
component, including the fixed-line branch of G.11.1(3). -/
theorem source_no_triple_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
    (C : Subgroup F.TerminalHdot) [C.Normal]
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (e : C ≃* SL(2,k)) (hk : Nat.card k = 8)
    (ht : letI : Algebra (ZMod 2) k := SL2.BinarySmall.binaryAlgebra
      SL2.BinarySmall.IsTriple ((F.terminalRepresentation.comp C.subtype).comp e.symm.toMonoidHom)) :
    False := by
  let := chosen.elementary
  let := hirr
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_,_,B,v,hyp,hline,hfix⟩ := source_terminal_marked_hypothesis F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let P : Sylow 2 F.TerminalHdot := (T.subtype (F.invariant 1)).mapSurjective
    (QuotientGroup.mk'_surjective F.terminalHatAction.ker)
  have hP : (P : Subgroup F.TerminalHdot) = F.terminalDot (T : Subgroup G) := rfl
  have hs : (P : Subgroup F.TerminalHdot) ≤ subspaceStabilizer F.terminalRepresentation (hatSpace F V) := by
    apply le_subspaceStabilizer
    intro a ha w hw
    obtain ⟨b,hb,rfl⟩ := (show a ∈ F.terminalDot (T : Subgroup G) from hP ▸ ha)
    apply rankOne_seed_stable F b _ w hw
    have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := by
      simpa only [F.last] using F.invariant 3
    exact hTV hb
  obtain ⟨a,ha,hm⟩ := CaseOneHS.source_seed_point_moved d earlier hq chosen F hne v hline
  apply hm
  apply RankOne.triple_seed_point_fixed F.terminalRepresentation C e hk ht P (hatSpace F V)
    (seed_hat_dimension F (source_closure d earlier hq chosen structural alternatives F hne).2.2)
    hs v hyp.point_ne_zero (fun b => hfix b (hP ▸ b.property)) a
  have hstable : F.terminalDot (F.Li L 1) ≤ subspaceStabilizer F.terminalRepresentation (hatSpace F V) := by
    apply le_subspaceStabilizer
    intro b hb w hw
    obtain ⟨c,hc,rfl⟩ := hb
    exact rankOne_seed_stable F c (chosen.normalizes (F.Li_le L 1 hc).1) w hw
  exact hstable ha

/-- Both G.11 fixed-point clauses exclude every normal irreducible Bender
component on the original large extraspecial action. -/
theorem source_large_no_bender_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (C : Subgroup F.TerminalHdot) [C.Normal] (hC : IsComponent F.TerminalHdot C)
    (hm : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥)
    (hirr : IsIrreducible (F.terminalRepresentation.comp C.subtype))
    (model : ClassificationModels.IsBenderModel C) : False := by
  obtain ⟨_,_,k,_,_,_,e,hk,ht⟩ := source_large_bender_component_triple d earlier hq chosen
    structural alternatives F hne hZ hlarge g hgP hgH C hC hm hirr model
  exact source_no_triple_component d earlier hq chosen structural alternatives F hne C hirr e hk ht

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
