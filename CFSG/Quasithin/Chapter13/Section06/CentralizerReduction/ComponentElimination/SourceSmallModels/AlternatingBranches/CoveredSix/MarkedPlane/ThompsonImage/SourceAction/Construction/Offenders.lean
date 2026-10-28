module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.MarkedPlane.ThompsonImage.SourceAction.Construction.BlockLayer
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.ComponentExtraction.StarSelection.MaximalImages

/-!
# Actual maximum-elementary images are best offenders

Restrict the ambient block to the original plus actor. The full model's
faithfulness identifies the plus kernel with its exact relative centralizer.
The source Sylow witness puts the block in Tᵥ. Maximum elementary subgroups
and their orders transfer through the literal inclusion into the actor;
the established maximal-elementary theorem therefore applies. An explicit
linear equivalence transports every fixed-space dimension back to the
original Additive U(K), with the same literal plus images.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.2.5–7
(printed p.76), applied to the covered-six paragraph of 13.6.22 (p.932).
No offender assertion or four-group classification is an input.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage.Construction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction ComponentSelection
variable {G : Type*} [Group G] [Finite G] {K L T : Subgroup G} {z v : G}
variable {hL : Tv T v ≤ normalizer (Lv L v : Set G)}
    {hz : Tv T v ≤ centralizer ({z} : Set G)}
    {h : IsExceptionalAhat6Block K} [IsElementaryAbelian 2 (blockU K)] {m : HexacodeModel h}
    {f : (K ⧸ pCore 2 K) →* Gplus K L T z v hL hz}

/-- Every nontrivial literal image of a maximum elementary subgroup is a best offender on the original block. -/
theorem plusBlockModel_maxElementary_isBestOffender
    (d : PlusBlockModel K L T z v h hL hz m f)
    (hK : K ∈ Yz L T z v) (hn : Tv T v ≤ normalizer (K : Set G))
    (hLK : Lv L v ≤ K) (A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups (Tv T v))
    (hne : plusImage K L T z v hL hz A ≠ ⊥) :
    IsBestOffender d.action (plusImage K L T z v hL hz A) := by
  let H := plusActor K L T v
  let U0 := (blockU K).map K.subtype
  have hUT : U0 ≤ Tv T v := blockU_le_Tv K L T z v hK hn
  have hUH : U0 ≤ H := hUT.trans le_sup_right
  let U := U0.subgroupOf H
  have : U.Normal := normal_subgroupOf_of_le_normalizer (plusActor_normalizes_block hn hLK)
  have : IsElementaryAbelian 2 U0 := IsElementaryAbelian.map K.subtype
  have : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  let e : blockU K ≃* U :=
    ((blockU K).equivMapOfInjective K.subtype K.subtype_injective).trans
      (subgroupOfEquivOfLe hUH).symm
  let E : Additive U ≃ₗ[ZMod 2] Additive (blockU K) :=
    LinearEquiv.ofBijective (e.symm.toMonoidHom.toAdditive.toZModLinearMap 2) e.symm.bijective
  have he (u : Additive U) : (((E u).toMul : K) : G) = ((u.toMul : H) : G) :=
    congrArg (fun w : U => ((w : H) : G)) (e.apply_symm_apply u.toMul)
  let q := plusMk K L T z v hL hz
  have hq := plusMk_surjective K L T z v hL hz
  have hker : q.ker = centralizer (U : Set H) := by
    ext g
    change q g = 1 ↔ g ∈ centralizer (U : Set H)
    constructor
    · intro hg u hu
      apply Subtype.ext
      have hfix : d.action (q g) (E (Additive.ofMul ⟨u, hu⟩)) =
          E (Additive.ofMul ⟨u, hu⟩) := by rw [hg, map_one]; rfl
      have heq := congrArg (fun w : Additive (blockU K) => ((w.toMul : K) : G)) hfix
      rw [d.action_conjugation, he] at heq
      exact (mul_inv_eq_iff_eq_mul.mp heq).symm
    · intro hg
      apply d.action_injective
      rw [map_one]
      apply LinearMap.ext
      intro u
      have hc : ((u.toMul : K) : G) * (g : G) = (g : G) * ((u.toMul : K) : G) :=
        congrArg H.subtype (hg (e u.toMul) (e u.toMul).property)
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      rw [d.action_conjugation, ← hc, mul_inv_cancel_right]
      rfl
  let ρ := NormalElementaryQuotient.representation U q hq hker
  have hE (a : Gplus K L T z v hL hz) (u : Additive U) :
      E (ρ a u) = d.action a (E u) := by
    obtain ⟨g, rfl⟩ := hq a
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    rw [he, d.action_conjugation, he]
    exact congrArg H.subtype (NormalElementaryQuotient.representation_apply U q hq hker g u)
  have hAH : A ≤ H := hA.1.trans le_sup_right
  have hAm : A.subgroupOf H ∈ elementaryAbelianMaxSubgroups ((Tv T v).subgroupOf H) := by
    have : IsElementaryAbelian 2 A := hA.2.1
    refine ⟨comap_mono hA.1, IsElementaryAbelian.subgroupOf hAH, ?_⟩
    intro B hBS hB
    have : IsElementaryAbelian 2 B := hB
    calc
      Nat.card B = Nat.card (B.map H.subtype) := (card_map_of_injective H.subtype_injective).symm
      _ ≤ Nat.card A := hA.2.2 _
        ((map_mono hBS).trans_eq (map_subgroupOf_eq_of_le le_sup_right))
        (IsElementaryAbelian.map H.subtype)
      _ = Nat.card (A.subgroupOf H) := (Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).symm
  have hbest := CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
    U q hq hker ((Tv T v).subgroupOf H) (A.subgroupOf H) (comap_mono hUT) hAm hne
  have hdim (B : Subgroup (Gplus K L T z v hL hz)) :
      Module.finrank (ZMod 2) (fixedSpace ρ B) = Module.finrank (ZMod 2) (fixedSpace d.action B) := by
    have hh := fixedSpace_map_equivariant ρ d.action (MonoidHom.id _) E hE B
    rw [Subgroup.map_id] at hh
    rw [← hh]
    exact (Submodule.equivMapOfInjective E.toLinearMap E.injective _).finrank_eq
  refine ⟨hbest.1, ?_⟩
  intro B hBA
  have hb : weight ρ B ≤ weight ρ (plusImage K L T z v hL hz A) := hbest.2 B hBA
  simpa only [weight, hdim] using hb
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.ThompsonImage.Construction
