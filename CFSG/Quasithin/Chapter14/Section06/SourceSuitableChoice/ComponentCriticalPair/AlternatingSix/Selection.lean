module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.AlternatingSix.Sections
public import CFSG.Quasithin.Chapter14.Section06.SourceQuadraticBound

/-!
# Critical-pair selection in the terminal alternating-six branch

In the full-span case `Vplus = V`, the F.9 commutator obstruction makes the
first critical denominator proper. If the second were full, conjugating back
would produce an elementary actor with displacement in one line. An involution
movement bound kills that actor, contradicting the same commutator obstruction.
The genuine reversal theorem then selects the required quadratic actor and
compares its rank with the literal denominator index.

This supplies the geometric selection used in Aschbacher--Smith,
*The Classification of Quasithin Groups*, 14.6.24(2), printed p. 1041.
The final theorem specializes to the original rank-two setup with `H = Mc`.
-/

public section
open Subgroup Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.AlternatingSix
open Chapter13.Section08 Chapter13.Section08.CriticalGeometry
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Chapter13.Section08.SourceCompletion

variable {G E : Type*} [Group G] [Finite G] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

private theorem common_line_le_kernel {H U Z A C : Subgroup G}
    [IsElementaryAbelian 2 A]
    {ρ : Representation (ZMod 2) (Source.Hstar H) E}
    (s : ConjugationSection H U Z ρ) (hA : A ≤ H)
    (hC : Nat.card C = 2) (hc : ⁅U,A⁆ ≤ C)
    (hno : ∀ a : Source.Hstar H, orderOf a = 2 → 2 ≤ fixedCodim ρ (zpowers a)) :
    ⁅U,A⁆ ≤ Z := by
  let B := Source.starImage H A
  let : IsElementaryAbelian 2 B := starImage_isElementaryAbelian H A hA
  have hv (v : E) : v ∈ s.image U := by
    obtain ⟨u,hu⟩ := s.surjective (Multiplicative.ofAdd v)
    exact ⟨u,u.property,congrArg Multiplicative.toAdd hu⟩
  have hd : ∀ b ∈ B, ∀ v, ρ b v-v ∈ s.image C := by
    intro b hb v
    exact s.displacement_mem U A C (by rwa [commutator_comm]) b hb v (hv v)
  have hdim : Module.finrank (ZMod 2) (s.image C) ≤ 1 := by
    simpa only [hC,show Nat.log 2 2=1 from by decide] using s.image_finrank_le C
  have hone (b : Source.Hstar H) (hb : b ∈ B) : b = 1 := by
    by_contra hn
    have ho : orderOf b = 2 :=
      orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian b hb) hn
    have hlo := hno b ho
    have hhi := fixedCodim_zpowers_le_of_displacement_mem ρ b (s.image C) (hd b hb)
    omega
  rw [commutator_comm]
  apply commutator_le.mpr
  intro b hb u hu
  apply (s.quotient_eq_zero_iff ⟨⁅b,u⁆,s.commutator_mem ⟨b,hA hb⟩ ⟨u,hu⟩⟩).mp
  rw [←s.displacement ⟨b,hA hb⟩ ⟨u,hu⟩]
  have hh : QuotientGroup.mk' (pCore 2 H) ⟨b,hA hb⟩=1 :=
    hone _ (mem_map_of_mem _ hb)
  rw [hh,map_one,Module.End.one_apply,sub_self]

/-- In the full-span source case Vplus=V, absence of involution
transvections forces the two literal critical denominators to be proper. -/
theorem critical_strict_denominators
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hplus : D.Vplus = D.V) [IsElementaryAbelian 2 D.UH]
    (c : CriticalPair D.L (D.T : Subgroup G) D.H D.V) (hb : 3 ≤ c.path.length)
    (h62 : ∀ g:G, D.V⊓D.V.map (MulAut.conj g).toMonoidHom≠⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (s : ConjugationSection D.H D.UH D.V₁ ρ)
    (hno : ∀ a : Source.Hstar D.H, orderOf a = 2 → 2 ≤ fixedCodim ρ (zpowers a)) :
    Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁) < D.UH ∧
    Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁ < c.Ugamma D.Vplus := by
  have geo := f9_earlierGeometry D h c hb h62
  have huv : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hVU : D.V ≤ D.UH := by
    change D.V ≤ conjugateSpanBy D.Vplus D.H
    rw [hplus]
    exact le_conjugateSpanBy _ _
  have hγH : c.Ugamma D.Vplus ≤ D.H := (map_mono huv).trans geo.Vgamma_H
  have hUA : D.UH ≤ normalizer (c.Aone D.V₁ : Set G) := by
    apply le_trans (huv.trans geo.VH_endpoint)
    rw [c.vertexGroup_gamma,CriticalPair.Aone,←map_equiv_normalizer_eq]
    exact map_mono (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hbad := f9_commutator_not_le_Aone D h c hb
  have hDH : Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁) < D.UH := by
    apply lt_of_le_of_ne (commutatorPreimage_le _ _ _)
    intro he
    have hc : ⁅D.UH,c.Ugamma D.Vplus⁆ ≤ c.Aone D.V₁ := by
      conv_lhs => lhs; rw [←he]
      exact commutator_commutatorPreimage_le _ _ _ hUA
    apply hbad
    rw [commutator_comm]
    exact (commutator_mono hVU le_rfl).trans hc
  refine ⟨hDH,?_⟩
  apply lt_of_le_of_ne (commutatorPreimage_le _ _ _)
  intro he
  have hc : ⁅D.UH,c.Ugamma D.Vplus⁆ ≤ D.V₁ := by
    rw [commutator_comm]
    conv_lhs => lhs; rw [←he]
    exact commutator_commutatorPreimage_le _ _ _
      (hγH.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
  let k : G := (c.gb:G)⁻¹
  let A := D.UH.map (MulAut.conj k).toMonoidHom
  let C := D.V₁.map (MulAut.conj k).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAH : A ≤ D.H := AsymmetricPair.return_conjugate_le_H c D.UH
    (huv.trans geo.VH_endpoint)
  have hUC : ⁅D.UH,A⁆ ≤ C := by
    have hm := map_mono (f := (MulAut.conj k).toMonoidHom) hc
    rw [map_commutator] at hm
    have hcancel : (c.Ugamma D.Vplus).map (MulAut.conj k).toMonoidHom = D.UH :=
      PairConsequences.conjugate_inverse_cancel (c.gb:G) D.UH
    rw [hcancel,commutator_comm] at hm
    exact hm
  have hCZ : C⊓D.V₁ = ⊥ := by
    have hm := congrArg (fun X:Subgroup G => X.map (MulAut.conj k).toMonoidHom) geo.lines_disjoint
    rw [map_inf _ _ _ (MulAut.conj k).injective,Subgroup.map_bot] at hm
    have hh : (c.Aone D.V₁).map (MulAut.conj k).toMonoidHom = D.V₁ :=
      PairConsequences.conjugate_inverse_cancel (c.gb:G) D.V₁
    rwa [hh] at hm
  have hCC : Nat.card C = 2 := by
    rw [card_map_of_injective (MulAut.conj k).injective,h.point_card]
  have hz := common_line_le_kernel s hAH hCC hUC hno
  have hzero : ⁅D.UH,A⁆ = ⊥ := le_bot_iff.mp ((le_inf hUC hz).trans hCZ.le)
  have hback := congrArg (fun X:Subgroup G => X.map (MulAut.conj (c.gb:G)).toMonoidHom) hzero
  rw [map_commutator,Subgroup.map_bot] at hback
  have hcancel : A.map (MulAut.conj (c.gb:G)).toMonoidHom = D.UH := by
    simpa only [inv_inv] using PairConsequences.conjugate_inverse_cancel (c.gb:G)⁻¹ D.UH
  rw [hcancel] at hback
  apply hbad
  exact (commutator_mono le_rfl hVU).trans (hback.le.trans bot_le)

/-- Select an actual critical pair, retaining both proper denominators and
their numerical comparison. The involution bound is the only model input. -/
theorem exists_critical_quadratic_selection
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hplus : D.Vplus = D.V) [IsElementaryAbelian 2 D.UH]
    (h62 : ∀ g:G, D.V⊓D.V.map (MulAut.conj g).toMonoidHom≠⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥)
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (s : ConjugationSection D.H D.UH D.V₁ ρ)
    (hno : ∀ a : Source.Hstar D.H, orderOf a = 2 → 2 ≤ fixedCodim ρ (zpowers a)) :
    ∃ c : CriticalPair D.L (D.T : Subgroup G) D.H D.V,
      3 ≤ c.path.length ∧
      Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁) < D.UH ∧
      Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁ < c.Ugamma D.Vplus ∧
      0 < rank (Source.starImage D.H (c.Ugamma D.Vplus)) ∧
      Reorientation.denominatorRank D.Vplus D.V₁ c ≤
        rank (Source.starImage D.H (c.Ugamma D.Vplus)) ∧
      Reorientation.QuadraticMember ρ (Source.starImage D.H (c.Ugamma D.Vplus)) := by
  have hcore : D.V ≤ D.QH := by
    have hVU : D.V ≤ D.UH := by
      change D.V ≤ conjugateSpanBy D.Vplus D.H
      rw [hplus]
      exact le_conjugateSpanBy _ _
    exact hVU.trans h.UH_le_QH
  have hb := h.b_bounds_of_intersecting_conjugates_commute hcore h62
  have hdist : 3≤criticalDistance D.L (D.T:Subgroup G) D.H D.V ∧
      Odd (criticalDistance D.L (D.T:Subgroup G) D.H D.V) := by
    simpa only [f9_criticalDistance_eq D h] using hb
  obtain ⟨c,hbc,_⟩ := f9_criticalPair_bounds D h hdist
  have hlength (c' : CriticalPair D.L (D.T:Subgroup G) D.H D.V) :
      3≤c'.path.length := by rw [c'.length_eq]; exact hdist.1
  have geo (c' : CriticalPair D.L (D.T:Subgroup G) D.H D.V) :=
    f9_earlierGeometry D h c' (hlength c') h62
  have huv : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  obtain ⟨hDH,hDγ⟩ := critical_strict_denominators D h hplus c hbc h62 s hno
  let : IsElementaryAbelian 2 (Source.UH D.H D.Vplus) := ‹IsElementaryAbelian 2 D.UH›
  let : IsElementaryAbelian 2 (Source.VH D.H D.V) := by
    change IsElementaryAbelian 2 (conjugateSpanBy D.V D.H)
    rw [←hplus]
    exact ‹IsElementaryAbelian 2 D.UH›
  obtain ⟨d,hd,hdγ,hp,hcomp,hq⟩ := Reorientation.exists_quadratic_selection D.Vplus D.V₁ c s
    (f9_section_faithful D h s) hbc h.plus_le (fun c' => (geo c').Vgamma_H)
    (huv.trans (geo c).VH_endpoint) (geo c).first_kernel hDH hDγ
    (fun c' => (c'.quadratic_star_on_Utilde D.Vplus D.V₁ s h.plus_le (geo c').VH_endpoint).2)
    (fun c' _ hc => f9_fixedCodim_le_twice_rank D h c' (hlength c') s hc)
  exact ⟨d,hlength d,hd,hdγ,hp,hcomp,hq⟩

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- Original H=Mc application: all geometric inputs to critical selection are
proved from the full rank-two source setup. -/
theorem terminal_critical_quadratic_selection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    {ρ : Representation (ZMod 2) (Source.Hstar Mc) E}
    (s : ConjugationSection Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T) ρ)
    (hno : ∀ a : Source.Hstar Mc, orderOf a = 2 → 2 ≤ fixedCodim ρ (zpowers a)) :
    ∃ c : CriticalPair (sourceResidual M Mc) (T : Subgroup G) Mc (localModule T M),
      3 ≤ c.path.length ∧
      Source.DH (conjugateSpanBy (localModule T M) Mc)
        (c.Ugamma (localModule T M)) (c.Aone (centralInvolutions T)) <
          conjugateSpanBy (localModule T M) Mc ∧
      Source.Dgamma (c.Ugamma (localModule T M))
        (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T) < c.Ugamma (localModule T M) ∧
      0 < rank (Source.starImage Mc (c.Ugamma (localModule T M))) ∧
      Reorientation.denominatorRank (localModule T M) (centralInvolutions T) c ≤
        rank (Source.starImage Mc (c.Ugamma (localModule T M))) ∧
      Reorientation.QuadraticMember ρ (Source.starImage Mc (c.Ugamma (localModule T M))) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  have h : D.Hypothesis :=
    ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  exact exists_critical_quadratic_selection D h rfl
    (source_rankTwo_intersecting_conjugates_commute hG T hempty hM hunique hmany hcard e hab) s hno

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.AlternatingSix
