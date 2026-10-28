module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.Actor
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.Constituents

/-!
# Common tensor data from the original flag

The original binary parabolic provides the conjugate actor in T and
[W,Wᵍ] ≤ E. Its order and relative normality come from the actual tensor
action. These facts construct the unique Sylow-invariant constituent,
its complement and X₁ ∈ Y. No two-core equality or constituent selection
is imposed on the caller; the quotient coordinates and source conjugator
remain unchanged.

Source: Aschbacher--Smith 14.4.10(1--2), printed pp.1010--1011;
12.8.9--12, printed pp.852--855.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The original conjugate actor preserves the index-two hyperplane, and its
commutators lie in the literal intersection. -/
theorem source_tensor_conjugate_geometry (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    F.X g ≤ (T : Subgroup G) ∧ ⁅F.W, F.X g⁆ ≤ F.E g ∧ F.W.relIndex F.U = 2 := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm,hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  have hspan := (source_seed_geometry d earlier hq chosen F).2.1
  obtain ⟨ι,_,hgen,_,hIG,hIN,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare hspan hne g hgP hgH
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm ι hcore hindex
  have hXT := F.X_le_T_of_parabolic_core L g hIG
    ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN) hsplit
  have hqn := F.binary_source_E_normal_in_core L chosen.normalizes g hgP hgen.symm hcomm
  let := hqn
  have hqe := F.binary_source_quotient_elementary L chosen.normalizes g hgP hgen.symm hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
  have hpair : ∃ hn : ((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal, letI := hn
      IsElementaryAbelian 2 ((F.W ⊔ F.X g : Subgroup G) ⧸ (F.E g).subgroupOf (F.W ⊔ F.X g)) := by
    have hh : ∃ hn : ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)).Normal, letI := hn
        IsElementaryAbelian 2 (((F.I₂ L).pCoreIn 2 : Subgroup G) ⧸
          (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) := ⟨hqn,hqe⟩
    rwa [hsplit] at hh
  obtain ⟨hn,helem⟩ := hpair
  let := hn
  let := helem
  exact ⟨hXT, F.commutator_W_X_le_E g, hindex⟩

/-- The original flag constructs all common tensor constituent data and
membership of X₁ in Y, retaining the original conjugator. -/
theorem source_tensor_common (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    XFamily F.H (T : Subgroup G) = {first F.H, second F.H (T : Subgroup G)} ∧
      first F.H ≠ second F.H (T : Subgroup G) ∧
      first F.H ∈ YFamily F.H T (F.Vi 2) (F.E g) ∧
      Nonempty (c.SelectedConstituent T (F.Vi 2) g) := by
  let := chosen.elementary
  let : IsExtraspecial 2 F.U :=
    (source_extraspecial_order d earlier hq chosen structural alternatives F hne hZ).1
  obtain ⟨hex, _⟩ := source_extraspecial_data d earlier hq chosen structural alternatives
    F hne hZ g hg hgP hgH
  have hT : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hSylow : ((T.subtype hT : Sylow 2 F.H) : Subgroup F.H).map F.H.subtype = T :=
    map_subgroupOf_eq_of_le hT
  obtain ⟨S, hS⟩ := exists_star_sylow (T.subtype hT) hSylow
  let S' : Sylow 2 (Three × D) := S.mapSurjective (f := c.actor.toMonoidHom) c.actor.surjective
  have hS' : (S' : Subgroup (Three × D)) = c.actorImage (T : Subgroup G) := by
    change (S : Subgroup (coreQuotient F.H)).map c.actor.toMonoidHom = _
    rw [hS]
  have hpT : IsPGroup 2 (c.actorImage (T : Subgroup G)) := hS' ▸ S'.isPGroup'
  obtain ⟨he, hc⟩ := source_tensor_actor_card d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH c
  let := he
  have he' : IsElementaryAbelian 2 (c.actorImage (F.X g)) :=
    IsElementaryAbelian.map c.actor.toMonoidHom
  let := he'
  let : IsElementaryAbelian 2 (c.actorImage (conjugateLayer F.U (F.Vi 2) g)) := he'
  have hc' : Nat.card (c.actorImage (F.X g)) = 8 := by
    change Nat.card ((star F.H (F.X g)).map c.actor.toMonoidHom) = _
    rw [card_map_of_injective c.actor.injective, hc]
  have hr := source_tensor_point_rank d earlier hq chosen F hne c
  have hfix := c.point_fixed_of_normalizes hT (F.invariant 2) hr
  obtain ⟨s⟩ := TensorGeometry.selectedConstituent c hpT hex.Wg_le_T hc' hfix
  have hn := (source_tensor_actor_normal d earlier hq chosen structural alternatives
    F hne hZ g hgP hgH c).2
  have hZP : center F.U ≤ (F.Vi 2).subgroupOf F.U := by
    intro z hz
    exact F.monotone (by omega : 1 ≤ 2) (hZ ▸ (show (z:G) ∈ F.ZU from ⟨z,hz,rfl⟩))
  have hPE : F.Vi 2 ≤ F.E g :=
    (F.le_seed 2).trans (F.seed_le_E_of_normalizes g (chosen.normalizes hg))
  have hbound : ⁅F.X g, F.W⁆ ≤ F.E g := by
    rw [commutator_comm]
    exact (source_tensor_conjugate_geometry d earlier hq chosen structural alternatives
      F hne g hgP hgH).2.1
  have hfirst := TensorGeometry.first_mem_Y c S' hS' s hT hex.U_le_T
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) hZP hr
    hex.Wg_le_T hPE he' hc' hn hbound
  obtain ⟨hpair, hneq⟩ := family_eq_pair_of_model (T.subtype hT) hSylow c.actor_models
  exact ⟨hpair, hneq, hfirst, ⟨s⟩⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
