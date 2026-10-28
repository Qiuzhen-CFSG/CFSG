module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.G2
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.CatalogueExclusions
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeModels
public import CFSG.Quasithin.ChapterG.Section11.LargeWholePair
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeSeven
public import CFSG.Quasithin.ChapterG.Section11.LargeWholeBinaryG2
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.SelfDual
public import Theory.Representation.BinaryPermutation.EightCentralizer
public import Theory.SpecificGroups.Alternating.EightComponent

/-!
# Excluding the natural A₈ branch before centerlessness

A quasisimple residual acting irreducibly on the original hatted module
lifts to a normal C-component of H. If its order exceeds 168, a nonzero
central LT seed would put that component in the genuine faithful local
family. The earlier A₅/PSL₃(2) classification contradicts the order of
its actual quotient image, so the central seed is trivial.

For a natural normal A₈, its trivial linear centralizer and outer two-group
identify it with the solvable residual. The preceding seed exclusion
therefore permits the shifted-involution argument when Z(I₂) is nontrivial.
When Z(I₂) is trivial, the original conjugate-center argument applies.
In both cases A₈ lies in the dotted image of C_H(Z(U)), whose marked point
stabilizer has three-rank at most one. The literal natural A₈ stabilizer
has three-rank at least two. This excludes both the split-six catalogue
row and the remaining whole A₈ component, without assuming centerlessness.

The original local application is in Centerless.Exhaustion. The earlier
structural and faithful-family inputs retain their original source producers.
Source: Aschbacher--Smith 14.3.23--25,28--31, printed pp.999--1003;
12.8.13(8), p.856; G.11.2 and G.9.3 with the corrected whole-action reduction.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

/-- A large irreducible quotient residual excludes the original central LT seed. -/
theorem source_seed_exclusion_of_large_residual
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hR : IsQuasisimple (solvableResidual F.TerminalHdot))
    (hirr : IsIrreducible (F.terminalRepresentation.comp (solvableResidual F.TerminalHdot).subtype))
    (hlarge : 168 < Nat.card (solvableResidual F.TerminalHdot)) : centralLTSeed F L = ⊥ := by
  by_contra hz
  let := chosen.elementary
  obtain ⟨K,hn,hK,hm⟩ := source_lift_dotted_residual d chosen F hR
  let := hn
  let q := QuotientGroup.mk' F.uhatAction.ker
  let R := solvableResidual F.TerminalHdot
  change K.map q = R at hm
  let π : K →* R := (q.comp K.subtype).codRestrict R
    (fun k => show q k ∈ R from hm ▸ mem_map_of_mem q k.property)
  have hπ : Function.Surjective π := by
    intro r
    obtain ⟨k,hk,he⟩ := (show (r : F.TerminalHdot) ∈ K.map q from hm.symm ▸ r.property)
    exact ⟨⟨k,hk⟩,Subtype.ext he⟩
  have hi := (irreducible_comp_surjective_iff π hπ
    (F.terminalRepresentation.comp R.subtype)).mpr hirr
  have hρ : ((F.terminalRepresentation.comp R.subtype).comp π) =
      (elementaryRepresentation (p := 2) F.uhatAction).comp K.subtype := by
    ext k x
    rfl
  rw [hρ] at hi
  have hout := source_irreducible_actor_escapes d earlier hq chosen structural alternatives F hne K hi
  have unique : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S A hA
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hA
  have hcoreH := F.pCore_le_uhatAction_ker_of_tilde_kernel (by decide)
    (source_action_kernel d earlier hq chosen ⟨structural,unique,alternatives⟩ F)
  have hcore : pCore 2 K ≤ π.ker := by
    have hp : (pCore 2 K).map K.subtype ≤ pCore 2 F.H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
    intro k hk
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr (hcoreH (hp (mem_map_of_mem K.subtype hk)))
  let β := QuotientGroup.lift (pCore 2 K) π hcore
  have hsur : Function.Surjective β := by
    intro z
    obtain ⟨k,rfl⟩ := hπ z
    exact ⟨QuotientGroup.mk' (pCore 2 K) k,rfl⟩
  have hbound := Nat.card_le_card_of_surjective β hsur
  let i := K.equivMapOfInjective F.H.subtype F.H.subtype_injective
  let iq := QuotientGroup.congr (pCore 2 K) (pCore 2 (K.map F.H.subtype)) i (pCore_map_iso 2 i)
  obtain ⟨hc,_,_⟩ := source_faithful_component_classification d earlier hq chosen structural
    alternatives classification F hz hK hout
  rcases hc with hA | hP
  · obtain ⟨e⟩ := hA
    have hc : Nat.card (K ⧸ pCore 2 K) = 60 := by
      rw [Nat.card_congr (iq.trans e).toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    change Nat.card R ≤ Nat.card (K ⧸ pCore 2 K) at hbound
    change 168 < Nat.card R at hlarge
    omega
  · obtain ⟨e⟩ := hP
    have hc : Nat.card (K ⧸ pCore 2 K) = 168 :=
      (Nat.card_congr (iq.trans e).toEquiv).trans Matrix.PSL3Two.card_PSL
    change Nat.card R ≤ Nat.card (K ⧸ pCore 2 K) at hbound
    change 168 < Nat.card R at hlarge
    omega

/-- The actual natural A₈ component supplies every premise of the seed exclusion. -/
theorem source_seed_exclusion_of_alternatingEight
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (J : Subgroup F.TerminalHdot) [J.Normal]
    (e : J ≃* alternatingGroup (Fin 8))
    (c : Additive F.Uhat ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hc : ∀ (j : J) w, c (F.terminalRepresentation j w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e j) (c w)) :
    centralLTSeed F L = ⊥ := by
  have hJc := BinaryPermutation.EightCommutant.centralizer_eq_bot_of_coordinates
    F.terminalRepresentation F.terminalRepresentation_injective J e c hc
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 8)) := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent (MulAut.Outer J) :=
    (alternatingGroup.EightComponent.outer_two.of_equiv (MulAut.outerCongr e).symm).isNilpotent
  let : Group.IsSolvable (F.TerminalHdot ⧸ J) := quotient_isSolvable_of_centralizer_eq_bot J hJc
  have hr : solvableResidual F.TerminalHdot = J :=
    le_antisymm (solvableResidual_le_of_solvable_quotient J) (le_solvableResidual_of_isPerfect J)
  let : IsQuasisimple (alternatingGroup (Fin 8)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hi : IsIrreducible (F.terminalRepresentation.comp J.subtype) := by
    let σ := (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)).comp e.toMonoidHom
    let E : RepEquiv (F.terminalRepresentation.comp J.subtype) σ := {
      toLinearEquiv := c
      isIntertwining' j := by apply LinearMap.ext; intro w; exact hc j w }
    exact E.irreducible_of_euqiv
      ((irreducible_comp_surjective_iff e.toMonoidHom e.surjective _).mpr
        (BinaryPermutation.alternatingNatural_isIrreducible (by simp)))
  apply source_seed_exclusion_of_large_residual d earlier hq chosen structural alternatives F hne classification
  · rw [hr]
    exact IsQuasisimple.of_mulEquiv e.symm
  · rwa [hr]
  · rw [hr,Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]

/-- Natural A₈ is impossible on the original flag, independently of centerlessness. -/
theorem source_no_alternatingEight_natural
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat) (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (J : Subgroup F.TerminalHdot) [J.Normal]
    (e : J ≃* alternatingGroup (Fin 8))
    (c : Additive F.Uhat ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hc : ∀ (j : J) w, c (F.terminalRepresentation j w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e j) (c w)) : False := by
  have hJc := BinaryPermutation.EightCommutant.centralizer_eq_bot_of_coordinates
    F.terminalRepresentation F.terminalRepresentation_injective J e c hc
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup J := e.isSimpleGroup
  have hJa : ¬ IsMulCommutative J := by
    intro hab
    let := hab
    have hp : (Nat.card J).Prime := IsSimpleGroup.prime_card
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hp
    norm_num [Nat.factorial] at hp
  have hJC : J ≤ F.terminalDot (centralizer (F.ZU : Set G)) := by
    by_cases hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥
    · exact source_simple_normal_le_center_centralizer d earlier hq chosen structural alternatives
        F hne hZ hI g hgP hgH J hJa hJc
    · exact source_contrary_simple_normal_le_center_centralizer d earlier hq chosen structural alternatives
        F hne (source_seed_exclusion_of_alternatingEight d earlier hq chosen structural alternatives
          F hne classification J e c hc) hI J hJa hJc
  let C := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hr : 2 ≤ primeRank 3 (C.subgroupOf J) := by
    let a := BinaryNaturalDual.Transport.stabilizerEquiv (F.terminalRepresentation.comp J.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) e c hc v
    have hb := BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer
      (by simp : 8 ≤ Fintype.card (Fin 8)) (c v)
    exact hb.trans (primeRank_equiv 3 a).ge
  let f : C.subgroupOf J →* C.subgroupOf D := {
    toFun := fun a => ⟨⟨a.val.val,hJC a.val.property⟩,a.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C.subgroupOf D => z.val.val) he))
  have hl := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
  have hu := source_center_centralizing_point_image_three_rank_le_one d earlier hq chosen
    structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (C.subgroupOf D) ≤ 1 at hu
  omega

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
