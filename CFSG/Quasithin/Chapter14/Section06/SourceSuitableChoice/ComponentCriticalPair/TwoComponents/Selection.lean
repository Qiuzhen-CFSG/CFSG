module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.AlternatingSix.Selection
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.CriticalActions

/-!
# Selected quadratic endpoints on the literal terminal quotient

The critical-path selection is transported to the normalized F.9 endpoint
without changing its representative. Its positive denominator and comparison
refer to U intersect O₂(Mc)^g and the actual image in Mc/O₂(Mc).
The common-center estimate is also proved for every normalized endpoint,
so it applies after reversing the endpoint in the equal-rank branch.

The no-involution-transvection premise remains explicit. The component-module
argument must discharge it; this module does not assert component normalization
or placement of the critical point in either component support.
Source: Aschbacher--Smith 14.6.24(a,b), printed p.1039, and F.9.16--17.
-/

@[expose] public section
open scoped commutatorElement
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]

/-- The selected path gives the normalized F.9 endpoint with exactly the
same group representative, hence the same conjugates of every source label. -/
theorem exists_endpoint_of_criticalPair
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (c : CriticalPair D.L (D.T : Subgroup G) D.H D.V) (hb : 3 ≤ c.path.length) :
    ∃ i : h.CriticalEndpoint, i.representative = (c.gb : G) := by
  have hf : cosetFamily D.L (D.T : Subgroup G) D.H =
      ChapterF.Section07.Geometry.family D.LT D.H := by
    funext b
    cases b <;> rfl
  have hd := c.distance_eq.trans (c.length_eq.trans (f9_criticalDistance_eq D h))
  have hs := SimpleGraph.length_eq_dist_of_subwalk c.distance_eq.symm (c.path.isSubwalk_drop 1)
  rw [SimpleGraph.Walk.drop_length,c.first] at hs
  have hd₁ : (graph D.L (D.T : Subgroup G) D.H).dist
      (base _ _ _ true) c.gamma + 1 = h.b := by
    have he := c.length_eq.trans (f9_criticalDistance_eq D h)
    omega
  have hc : ¬ D.V.subgroupOf (D.LT ⊔ D.H) ≤
      Subgroup.CosetGeometry.RankTwo.ballKernel (cosetFamily D.L (D.T : Subgroup G) D.H)
        c.gamma 1 := by
    intro hh
    exact c.critical ((le_firstKernel_iff _ _ _ _
      (h.V_le_LT.trans le_sup_left) c.gamma).mpr hh)
  rw [← c.gb_one] at hd hd₁ hc
  change (Subgroup.CosetGeometry.RankTwo.graph (cosetFamily D.L (D.T : Subgroup G) D.H)).dist
    (Subgroup.CosetGeometry.base _ false) (c.gb • Subgroup.CosetGeometry.base _ true) = _ at hd
  change (Subgroup.CosetGeometry.RankTwo.graph (cosetFamily D.L (D.T : Subgroup G) D.H)).dist
    (Subgroup.CosetGeometry.base _ true) (c.gb • Subgroup.CosetGeometry.base _ true) + 1 = _ at hd₁
  let g : (D.LT ⊔ D.H : Subgroup G) := ⟨c.gb.val,c.gb.property⟩
  have hdEq (b : Bool) := congrArg (fun F : Bool → Subgroup (D.LT ⊔ D.H : Subgroup G) =>
    (Subgroup.CosetGeometry.RankTwo.graph F).dist
      (Subgroup.CosetGeometry.base F b) (g • Subgroup.CosetGeometry.base F true)) hf
  have hcEq := congrArg (fun F : Bool → Subgroup (D.LT ⊔ D.H : Subgroup G) =>
    Subgroup.CosetGeometry.RankTwo.ballKernel F (g • Subgroup.CosetGeometry.base F true) 1) hf
  refine ⟨⟨g,?_,?_,?_⟩,rfl⟩
  · rw [← hdEq false]
    exact hd
  · rw [← hdEq true]
    exact hd₁
  · rw [h.f7Seed_eq, ← hcEq]
    exact hc
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Representation Representation.BinaryOffender
open Chapter13.Section08
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]

/-- Match the reusable marked binary section to the original star-quotient
section used by the critical-path selection theorem. -/
def criticalSection {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    {ρ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) E}
    (s : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H)))) :
    ConjugationSection D.H D.UH D.V₁ ρ where
  le := s.section_le
  normalizes := s.normalized
  centralizes := h.H_centralizes
  line_le := s.kernel_le
  quotient := s.coordinates
  surjective := s.onto
  kernel := s.kernel_eq
  conjugates := fun a u => (s.equivariant a u).symm
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- F.9's common-center estimate for every normalized endpoint, including
an endpoint obtained by reversal in the equality case. -/
theorem endpoint_fixedCodim_le_rank_add_denominator
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (i : h.CriticalEndpoint) (hb : 3 ≤ h.b) [IsElementaryAbelian 2 D.UH]
    {ρ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) E}
    (c : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H)))) :
    fixedCodim ρ (((i.conjugate D.UH).subgroupOf D.H).map
      (QuotientGroup.mk' (pCore 2 D.H))) ≤
      rank (((i.conjugate D.UH).subgroupOf D.H).map
        (QuotientGroup.mk' (pCore 2 D.H))) +
      Nat.log 2 ((D.UH ⊓ i.conjugate D.QH).relIndex D.UH) := by
  let s := criticalSection h c
  let Ug := i.conjugate D.UH
  let Zg := i.conjugate D.V₁
  let Dh := commutatorPreimage D.UH Ug Zg
  let B := Source.starImage D.H Ug
  have huv : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hUgH : Ug ≤ D.H := (map_mono huv).trans (i.large_le hb)
  have hUZg : D.UH ≤ normalizer (Zg : Set G) := by
    have hn := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
    rw [map_equiv_normalizer_eq] at hn
    exact huv.trans ((i.reverse_le hb).trans hn)
  have hUgZg : Ug ≤ centralizer (Zg : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    change ⁅D.UH.map _,D.V₁.map _⁆ = ⊥
    rw [← map_commutator,commutator_eq_bot_iff_le_centralizer.mpr
      (h.UH_le_H.trans h.H_centralizes),Subgroup.map_bot]
  have hn : Ug ≤ normalizer (Dh : Set G) :=
    commutatorPreimage_normalized _ _ _ _ hUZg (hUgH.trans s.normalizes)
      Ug.le_normalizer (hUgZg.trans (Subgroup.centralizer_le_normalizer _))
  let : IsElementaryAbelian 2 Ug := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 B := starImage_isElementaryAbelian D.H Ug hUgH
  let τ := ρ.comp B.subtype
  let W : Subrepresentation τ := {
    toSubmodule := s.image Dh
    apply_mem_toSubmodule := by
      rintro ⟨b,hb⟩ v hv
      obtain ⟨a,ha,rfl⟩ := hb
      obtain ⟨u,hu,rfl⟩ := (s.mem_image Dh v).mp hv
      change ρ (QuotientGroup.mk' (pCore 2 D.H) a) (s.quotient u).toAdd ∈ s.image Dh
      rw [s.conjugates]
      exact ⟨_,(mem_normalizer_iff.mp (hn ha) u).mp hu,rfl⟩ }
  have hcard : Nat.card Zg = 2 :=
    (card_map_of_injective (MulAut.conj i.representative).injective).trans h.point_card
  obtain ⟨hdim,hdisp⟩ := s.critical_line_displacement Ug Zg hUZg hcard
  have hfixed : ∀ b : B, ∀ z ∈ s.image Zg, τ b z = z := by
    rintro ⟨b,hb⟩ z hz
    obtain ⟨a,ha,rfl⟩ := hb
    obtain ⟨u,hu,rfl⟩ := (s.mem_image Zg z).mp hz
    apply sub_eq_zero.mp
    change ρ (QuotientGroup.mk' (pCore 2 D.H) a) (s.quotient u).toAdd -
      (s.quotient u).toAdd = 0
    rw [s.displacement]
    apply (s.quotient_eq_zero_iff _).mpr
    have hc : ⁅(a : G),(u : G)⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr ((hUgZg ha) u hu).symm
    change ⁅(a : G),(u : G)⁆ ∈ D.V₁
    rw [hc]
    exact D.V₁.one_mem
  have hbound := CommonCenter.fixedCodim_top_le_rank_add_codim τ W (s.image Zg) hdim
    (fun b v hv => hdisp b b.property v hv) hfixed
  have hcodim : fixedCodim τ ⊤ = fixedCodim ρ B := by
    change Module.finrank (ZMod 2) (E ⧸ fixedSpace (ρ.comp B.subtype) ⊤) = _
    rw [fixedSpace_comp_map, ← MonoidHom.range_eq_map,B.range_subtype]
    rfl
  rw [hcodim] at hbound
  have hdenom : Module.finrank (ZMod 2) (E ⧸ W.toSubmodule) =
      Nat.log 2 (Dh.relIndex D.UH) :=
    s.quotient_finrank Dh (s.line_le_DH Ug Zg hUgH)
  rw [hdenom] at hbound
  change fixedCodim ρ B ≤ rank B +
    Nat.log 2 ((commutatorPreimage D.UH (i.conjugate D.UH)
      (i.conjugate D.V₁)).relIndex D.UH) at hbound
  rwa [(i.denominators h hb).1] at hbound
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]

/-- The selected actor, before the component normalization and point-placement
arguments. Its denominator is the literal opposite two-core intersection. -/
structure QuadraticEndpoint {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (ρ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) E) where
  endpoint : h.CriticalEndpoint
  positive : 0 < Nat.log 2 ((D.UH ⊓ endpoint.conjugate D.QH).relIndex D.UH)
  comparison : Nat.log 2 ((D.UH ⊓ endpoint.conjugate D.QH).relIndex D.UH) ≤
    rank (((endpoint.conjugate D.UH).subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)))
  member : Reorientation.QuadraticMember ρ
    (((endpoint.conjugate D.UH).subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H)))

/-- The proved critical-path selection has the exact normalized endpoint type
used by the two-component endgame. Only the preceding module-theoretic
exclusion of involution transvections is explicit. -/
theorem exists_quadraticEndpoint_of_no_transvections
    [FiniteDimensional (ZMod 2) E]
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (hplus : D.Vplus = D.V) [IsElementaryAbelian 2 D.UH]
    (hcomm : ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    {ρ : Representation (ZMod 2) (D.H ⧸ pCore 2 D.H) E}
    (s : BinaryConjugationSection D.H D.UH D.V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 D.H))))
    (hno : ∀ a : D.H ⧸ pCore 2 D.H, orderOf a = 2 → 2 ≤ fixedCodim ρ (zpowers a)) :
    Nonempty (QuadraticEndpoint h ρ) := by
  obtain ⟨c,hbc,_,_,_,hcmp,hq⟩ :=
    AlternatingSix.exists_critical_quadratic_selection D h hplus hcomm (criticalSection h s) hno
  obtain ⟨i,hi⟩ := exists_endpoint_of_criticalPair h c hbc
  have hb : 3 ≤ h.b := by
    rwa [c.length_eq, SourceCompletion.f9_criticalDistance_eq D h] at hbc
  have hU : c.Ugamma D.Vplus = i.conjugate D.UH := by
    change D.UH.map (MulAut.conj (c.gb : G)).toMonoidHom =
      D.UH.map (MulAut.conj i.representative).toMonoidHom
    rw [hi]
  have hZ : c.Aone D.V₁ = i.conjugate D.V₁ := by
    change D.V₁.map (MulAut.conj (c.gb : G)).toMonoidHom =
      D.V₁.map (MulAut.conj i.representative).toMonoidHom
    rw [hi]
  refine ⟨⟨i,i.denominator_positive h hb hplus,?_,?_⟩⟩
  · change Nat.log 2 ((commutatorPreimage D.UH (c.Ugamma D.Vplus)
      (c.Aone D.V₁)).relIndex D.UH) ≤ _ at hcmp
    rw [hU,hZ,(i.denominators h hb).1] at hcmp
    exact hcmp
  · rwa [hU] at hq

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Original H=Mc application of the selection. No endpoint, denominator,
rank comparison, or quadratic actor is assumed. The no-transvection premise
is precisely the still-required consequence of the actual component modules
in 14.6.24(a), printed p.1039. -/
theorem source_quadraticEndpoint_of_no_transvections
    [FiniteDimensional (ZMod 2) E]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Mc ⧸ pCore 2 Mc) E}
    (s : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) (ρ.comp (QuotientGroup.mk' (pCore 2 Mc))))
    (hno : ∀ a : Mc ⧸ pCore 2 Mc, orderOf a = 2 → 2 ≤ fixedCodim ρ (zpowers a)) :
    Nonempty (QuadraticEndpoint
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) ρ) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  let h : D.Hypothesis := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  exact exists_quadraticEndpoint_of_no_transvections h rfl
    (source_rankTwo_intersecting_conjugates_commute hG T hempty hM hunique hmany hcard e hab) s hno
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
