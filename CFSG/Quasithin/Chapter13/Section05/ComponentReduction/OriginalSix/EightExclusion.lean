module
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.EightPointRank
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix.PlaneRank
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.CComponent.ThreeCore
public import Theory.GroupTheory.Commutator.CoprimeQuadratic
public import Theory.GroupAction.MaximalCosetOrbit
public import Theory.Representation.BinaryConjugationSection.FixedSplitting

/-!
# Excluding the original A₈ branch by the plane centralizer

Choose a generator of the original line V₂/V₁. Its K* point stabilizer
contains an elementary nine-group, which lifts through O₂(H) with the
same order. The lifted group centralizes V₂/V₁ and V₁, so its coprime
quadratic action on V₂ is trivial. Thus C_G(V₂) has three-rank at least
two, contrary to the original13.5.4(3) bound of one.

The proof retains the prescribed H/O₂(H) action, central quotient and
natural A₈ coordinates. It does not require a splitting of U_H/V₁.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),13.5.23,
printed p.925, and13.5.4(3), printed p.916.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open BinaryNaturalDual.VectorStabilizers
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
open Section08.SourceCompletion Section08.Source Recognition Recognition.Configuration
open Recognition.MarkedModule Recognition.MarkedModule.AlternatingParabolics
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]
include d h

private theorem lifted_nine_centralizes_plane
    (v : G) (hv : v ∈ V₂) (hgen : D.V₁ ⊔ zpowers v = V₂)
    (A : Subgroup D.H) [IsElementaryAbelian 3 A]
    (hfix : ∀ a : A, Action.starRepresentation D h
      (QuotientGroup.mk' (pCore 2 D.H) a.val)
      (Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
        ⟨v,(d.plane_le_seed.trans (le_conjugateSpanBy D.Vplus D.H)) hv⟩)) =
      Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
        ⟨v,(d.plane_le_seed.trans (le_conjugateSpanBy D.Vplus D.H)) hv⟩)) :
    A.map D.H.subtype ≤ centralizer (V₂ : Set G) := by
  let B := A.map D.H.subtype
  have hBH : B ≤ D.H := map_subtype_le _
  have hBZ : B ≤ centralizer (D.V₁ : Set G) := hBH.trans h.H_centralizes
  have hUZ : D.UH ≤ normalizer (D.V₁ : Set G) :=
    (h.UH_le_H.trans h.H_centralizes).trans (Subgroup.centralizer_le_normalizer _)
  have hvU : v ∈ D.UH := (d.plane_le_seed.trans (le_conjugateSpanBy D.Vplus D.H)) hv
  have hvC : v ∈ commutatorPreimage D.UH B D.V₁ := by
    apply (mem_commutatorPreimage_iff _ _ _ hUZ v).mpr
    refine ⟨hvU, ?_⟩
    rintro a ⟨a,ha,rfl⟩
    have he := hfix ⟨a,ha⟩
    rw [Action.starRepresentation_apply] at he
    have hm := QuotientGroup.eq_iff_div_mem.mp (Additive.ofMul.injective he)
    have hm' : ⁅(a : G),v⁆ ∈ D.V₁ := by
      simpa only [mem_subgroupOf, coe_div, coe_mul, coe_inv, div_eq_mul_inv,
        commutatorElement_def] using hm
    change ⁅v,(a : G)⁆ ∈ D.V₁
    simpa only [commutatorElement_inv] using D.V₁.inv_mem hm'
  have hZC : D.V₁ ≤ commutatorPreimage D.UH B D.V₁ := by
    apply le_commutatorPreimage
    · exact d.line_le_plane.trans (d.plane_le_seed.trans (le_conjugateSpanBy D.Vplus D.H))
    · rw [commutator_comm, commutator_eq_bot_iff_le_centralizer.mpr hBZ]
      exact bot_le
  have hEC : V₂ ≤ commutatorPreimage D.UH B D.V₁ := by
    rw [← hgen]
    exact sup_le hZC (zpowers_le.mpr hvC)
  have hcomm : ⁅V₂,B⁆ ≤ D.V₁ := (commutator_mono hEC le_rfl).trans
    (commutator_commutatorPreimage_le D.UH B D.V₁ hUZ)
  have hn : B ≤ normalizer (V₂ : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hcomm.trans d.line_le_plane)
  have hquad : ⁅⁅V₂,B⁆,B⁆ = ⊥ := by
    apply bot_unique
    calc
      ⁅⁅V₂,B⁆,B⁆ ≤ ⁅D.V₁,B⁆ := commutator_mono hcomm le_rfl
      _ = ⊥ := by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr hBZ
  have hpE : IsPGroup 2 V₂ := IsPGroup.of_card (n := 2) d.plane_card
  let : Group.IsNilpotent V₂ := hpE.isNilpotent
  have hpB : IsPGroup 3 B := (IsElementaryAbelian.isPGroup 3 A).map D.H.subtype
  obtain ⟨n,hnB⟩ := hpB.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card V₂) := by
    rw [hnB,d.plane_card]
    exact (by decide : Nat.Coprime 3 4).pow_left n
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [commutator_comm]
  exact commutator_eq_bot_of_coprime_quadratic V₂ B hn inferInstance hcop hquad

/-- The natural A₈ case contradicts the original ordinary-A₆ plane-centralizer bound. -/
theorem alternating_eight_source_false
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hU : ¬IsMulCommutative D.UH)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T D.L)
    (hc : centralizer (D.Vplus : Set G) ≤ M ⊓ normalizer (D.V : Set G))
    (K : Subgroup G) (s : Selected D K) [(componentCentralizer s h).Normal]
    (c : SourceConfiguration s h D.L₁ le_rfl)
    (f : Catalogue.actor D K ≃* alternatingGroup (Fin 8))
    (fV : CentralQuotient.Space D h K ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hfV : ∀ b : Catalogue.actor D K, ∀ u,
      centralProjection D h fV (Action.starRepresentation D h b.val u) =
        BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (f b)
          (centralProjection D h fV u)) : False := by
  have hnot : ¬ V₂ ≤ D.V₁ := by
    intro hle
    have hc' := card_le_of_le hle
    rw [d.plane_card,d.line_card] at hc'
    omega
  obtain ⟨v,hv,hvZ⟩ := Set.not_subset.mp hnot
  have hi : D.V₁.relIndex V₂ = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) D.V₁ V₂ bot_le d.line_le_plane
    rw [relIndex_bot_left, relIndex_bot_left, d.line_card, d.plane_card] at hh
    omega
  have hgen := sup_zpowers_eq_of_relIndex_prime d.line_le_plane Nat.prime_two hi hv hvZ
  let u : Action.Space D := Additive.ofMul (QuotientGroup.mk' (D.V₁.subgroupOf D.UH)
    ⟨v,(d.plane_le_seed.trans (le_conjugateSpanBy D.Vplus D.H)) hv⟩)
  let S := representationStabilizer (Action.starRepresentation D h) u
  let j : S.subgroupOf (starImage D.H K) →* S := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S => (z : Hstar D.H)) he
  have hr : 2 ≤ primeRank 3 S :=
    (alternating_eight_source_point_rank d h e hU h1221 hc K s c f fV hfV u).trans
      (Theory.GroupTheory.primeRank_le_of_injective 3 j hj)
  obtain ⟨E,hEe,hEc⟩ := exists_elementary_nine_of_three_rank hr
  let := hEe
  let Ebar := E.map S.subtype
  let : IsElementaryAbelian 3 Ebar := IsElementaryAbelian.map_subtype
  let π := QuotientGroup.mk' (pCore 2 D.H)
  have hker : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := D.H)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  obtain ⟨A,hAe,hAmap,hAc⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    π (QuotientGroup.mk'_surjective _) hker Ebar
  let := hAe
  have hcentral : A.map D.H.subtype ≤ centralizer (V₂ : Set G) := by
    apply lifted_nine_centralizes_plane d h v hv hgen A
    intro a
    have hm : π a.val ∈ Ebar := hAmap ▸ mem_map_of_mem π a.property
    exact (map_subtype_le E) hm
  let B := A.map D.H.subtype
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.map_subtype
  have hBc : Nat.card B = 3 ^ 2 := by
    rw [card_map_of_injective D.H.subtype_injective,hAc,
      card_map_of_injective S.subtype_injective,hEc]
  let : IsElementaryAbelian 3 (B.subgroupOf (centralizer (V₂ : Set G))) :=
    IsElementaryAbelian.subgroupOf hcentral
  have hCr : 2 ≤ primeRank 3 (centralizer (V₂ : Set G)) := by
    apply IsElementaryAbelian.primeRank_ge_of_card (B.subgroupOf (centralizer (V₂ : Set G)))
    exact (Nat.card_congr (subgroupOfEquivOfLe hcentral).toEquiv).trans hBc
  have hbound := source_plane_centralizer_rank d h e hU
  omega
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.OriginalSix
