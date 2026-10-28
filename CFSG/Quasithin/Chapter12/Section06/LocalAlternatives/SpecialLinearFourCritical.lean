module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.ModuleBound.OriginalF916
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.RankBound

/-!
# The F.9 obstruction to a full SL₃(4) natural-plus-dual section

Use F.9 on the actual local group. Commutativity of intersecting conjugates
and the seed-centralizer condition give an odd critical pair. When both
critical denominators are proper, reversal selects a quadratic actor whose
rank bounds the codimension of the literal image of D_H. Its displacements
lie in the image of the same conjugate A₁ of the original central line.
The natural-plus-dual quadratic-actor classification contradicts this
common-line geometry.

If a denominator fills its numerator, the common-line commutator acts on
the entire module. In the opposite orientation, conjugating back gives
such an actor in the original H; the disjoint original central lines ensure
nontriviality. The same matrix obstruction excludes both asymmetric cases.
No equality of H with the full point centralizer, selected critical pair,
rank comparison, or actor marking is assumed.

Source: Aschbacher–Smith F.9.13–16, printed pp.322–324; applied to the
12.6.32 SL₃(4) branch, p.837, using the natural-plus-dual matrix obstruction
also used in 13.8.20, p.955. The original application supplies every F.9
premise and the actual equivariant coordinates.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section06.LocalAlternatives
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open Chapter13.Section08.CriticalGeometry Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open PairConsequences.ReversedSourceData
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.ModuleBound
open Chapter15.Section03.AbelianAmalgam.ModuleBound.OriginalF916
open Representation.SL3FourNaturalDual
variable {G E : Type*} [Group G] [Finite G]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]

private theorem no_common_line {H U Z A C : Subgroup G}
    [IsElementaryAbelian 2 A]
    {ρ : Representation (ZMod 2) (Source.Hstar H) E}
    (s : ConjugationSection H U Z ρ)
    (hshape : ∀ B, QuadraticMember ρ B → CriticalShapes ρ B)
    (hA : A ≤ H) (hC : Nat.card C = 2) (hc : ⁅U,A⁆ ≤ C)
    (hfix : A ≤ centralizer (C : Set G)) (hne : ¬ ⁅U,A⁆ ≤ Z) : False := by
  have hq := quadratic_member_of_common_line s hA hC hc hfix hne
  have hdim : Module.finrank (ZMod 2) (s.image C) ≤ 1 := by
    simpa only [hC,show Nat.log 2 2 = 1 from by decide] using s.image_finrank_le C
  obtain ⟨z,hz⟩ := (finrank_le_one_iff (K := ZMod 2)).mp hdim
  apply critical_obstruction ρ (Source.starImage H A) (hshape _ hq) ⊤ z.val
  · have ht := Submodule.finrank_quotient_add_finrank (⊤ : Submodule (ZMod 2) E)
    rw [finrank_top] at ht
    omega
  · intro a ha d _
    have hd : d ∈ s.image U := by
      obtain ⟨u,hu⟩ := s.surjective (Multiplicative.ofAdd d)
      exact ⟨u,u.property,congrArg Multiplicative.toAdd hu⟩
    have hm := s.displacement_mem U A C (by rwa [commutator_comm]) a ha d hd
    obtain ⟨b,hb⟩ := hz ⟨ρ a d-d,hm⟩
    exact Submodule.mem_span_singleton.mpr ⟨b,congrArg Subtype.val hb⟩

/-- The F.9 critical geometry excludes a faithful natural-plus-dual SL₃(4)
section for the actual local group, without requiring the full point centralizer. -/
theorem specialLinearFour_impossible_of_f9
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH] [IsElementaryAbelian 2 D.VH]
    {ρ : Representation (ZMod 2) (Source.Hstar D.H) E}
    (s : ConjugationSection D.H D.UH D.V₁ ρ)
    (B : Subgroup (Source.Hstar D.H)) [B.Normal]
    (e : B ≃* SL) (q : E ≃ₗ[ZMod 2] Representation.SL3FourNaturalDual.V)
    (hq : ∀ (k : B) v, q (ρ k v) = representation (e k) (q v))
    (h62 : ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (h47 : ∀ x ∈ centralizer (D.Vplus : Set G),
      ⁅D.V,zpowers x⁆ = ⊥ ∨ NormalizingConjugatesCentralize D.V x) : False := by
  have hf := f9_section_faithful D h s
  have shape (A : Subgroup (Source.Hstar D.H)) (ha : QuadraticMember ρ A) :
      CriticalShapes ρ A :=
    QuadraticActors.criticalShapes_of_equivariant_unbounded ρ hf B e q hq
      A ha.1 ha.2.1 ha.2.2
  have hcore : D.V ≤ D.QH := (le_conjugateSpanBy D.V D.H).trans
    (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 D.VH)
      h.VH_le_H (le_normalizer_conjugateSpanBy D.V D.H))
  have hb := h.b_bounds_of_intersecting_conjugates_commute hcore h62
  have hdist : 3 ≤ criticalDistance D.L (D.T : Subgroup G) D.H D.V ∧
      Odd (criticalDistance D.L (D.T : Subgroup G) D.H D.V) := by
    simpa only [f9_criticalDistance_eq D h] using hb
  obtain ⟨c,hbc,_⟩ := f9_criticalPair_bounds D h hdist
  have hlength (d : CriticalPair D.L (D.T : Subgroup G) D.H D.V) :
      3 ≤ d.path.length := by rw [d.length_eq]; exact hdist.1
  have geo (d : CriticalPair D.L (D.T : Subgroup G) D.H D.V) :=
    f9_earlierGeometry D h d (hlength d) h62
  have huv : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hγH : c.Ugamma D.Vplus ≤ D.H := (map_mono huv).trans (geo c).Vgamma_H
  have hUA : D.UH ≤ normalizer (c.Aone D.V₁ : Set G) := by
    apply le_trans (huv.trans (geo c).VH_endpoint)
    rw [c.vertexGroup_gamma,CriticalPair.Aone,←map_equiv_normalizer_eq]
    exact map_mono (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hUgA : c.Ugamma D.Vplus ≤ centralizer (c.Aone D.V₁ : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [CriticalPair.Ugamma,CriticalPair.Aone,←map_commutator]
    exact (congrArg (fun A : Subgroup G => A.map (MulAut.conj (c.gb : G)).toMonoidHom)
      (commutator_eq_bot_iff_le_centralizer.mpr (h.UH_le_H.trans h.H_centralizes))).trans (map_bot _)
  have hcardA : Nat.card (c.Aone D.V₁) = 2 := by
    rw [CriticalPair.Aone,card_map_of_injective (MulAut.conj _).injective,h.point_card]
  let : IsElementaryAbelian 2 (Source.UH D.H D.Vplus) := ‹IsElementaryAbelian 2 D.UH›
  let : IsElementaryAbelian 2 (Source.VH D.H D.V) := ‹IsElementaryAbelian 2 D.VH›
  let : IsMulCommutative (conjugateSpanBy D.V D.H) :=
    ‹IsElementaryAbelian 2 D.VH›.toIsMulCommutative
  let : IsElementaryAbelian 2 (c.Ugamma D.Vplus) := IsElementaryAbelian.map _
  have hbad := f9_commutator_not_le_Aone D h c hbc
  by_cases hDγ : Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁ < c.Ugamma D.Vplus
  · by_cases hDH : Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁) < D.UH
    · obtain ⟨d,_,_,_,hd,hquad⟩ := Reorientation.exists_quadratic_selection D.Vplus D.V₁ c s hf
        hbc h.plus_le (fun d => (geo d).Vgamma_H)
        (huv.trans (geo c).VH_endpoint) (geo c).first_kernel hDH hDγ
        (fun d => (d.quadratic_star_on_Utilde D.Vplus D.V₁ s h.plus_le (geo d).VH_endpoint).2)
        (fun d _ hc => f9_fixedCodim_le_twice_rank D h d (hlength d) s hc)
      have hUgH : d.Ugamma D.Vplus ≤ D.H := (map_mono huv).trans (geo d).Vgamma_H
      have hreverse : D.UH ≤ D.H.map (MulAut.conj (d.gb : G)).toMonoidHom := by
        rw [←d.vertexGroup_gamma]
        exact huv.trans (geo d).VH_endpoint
      have hline := s.critical_line_displacement_of_conjugate (d.Ugamma D.Vplus)
        (d.gb : G) hreverse h.point_card
      obtain ⟨z,hz⟩ := (finrank_le_one_iff (K := ZMod 2)).mp hline.1
      apply critical_obstruction ρ (Source.starImage D.H (d.Ugamma D.Vplus)) (shape _ hquad)
        (s.image (Source.DH D.UH (d.Ugamma D.Vplus) (d.Aone D.V₁))) z.val
      · rw [s.quotient_finrank _ (s.line_le_DH _ _ hUgH)]
        exact hd
      · intro a ha v hv
        have hm := hline.2 a ha v hv
        obtain ⟨b,hb⟩ := hz ⟨ρ a v-v,hm⟩
        exact Submodule.mem_span_singleton.mpr ⟨b,congrArg Subtype.val hb⟩
    · have he := eq_of_le_of_not_lt (commutatorPreimage_le D.UH
        (c.Ugamma D.Vplus) (c.Aone D.V₁)) hDH
      have hc : ⁅D.UH,c.Ugamma D.Vplus⁆ ≤ c.Aone D.V₁ := by
        conv_lhs => lhs; rw [←he]
        exact commutator_commutatorPreimage_le _ _ _ hUA
      have hn : ¬ ⁅D.UH,c.Ugamma D.Vplus⁆ ≤ D.V₁ := by
        intro hh
        apply hDγ.not_ge
        exact le_commutatorPreimage le_rfl (by rwa [commutator_comm])
      exact no_common_line s shape hγH hcardA hc hUgA hn
  · have hfull := eq_of_le_of_not_lt
      (commutatorPreimage_le (c.Ugamma D.Vplus) D.UH D.V₁) hDγ
    have hn : ⁅D.UH,c.Ugamma D.Vplus⁆ ≠ ⊥ :=
      small_spans_not_commute (c.gb : G) h.plus_le
        (le_normalizer_iff_commutator_le_right.mp
          ((geo c).VH_endpoint.trans (c.normalizes_Ugamma D.V))) h47 hbad
    have hc : ⁅D.UH,c.Ugamma D.Vplus⁆ ≤ D.V₁ := by
      rw [commutator_comm]
      conv_lhs => lhs; rw [←hfull]
      exact commutator_commutatorPreimage_le _ _ _
        (hγH.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
    have he : ⁅D.UH,c.Ugamma D.Vplus⁆ = D.V₁ := by
      have hd : Nat.card (⁅D.UH,c.Ugamma D.Vplus⁆ : Subgroup G) ∣ 2 := by
        have hd' := card_dvd_of_le hc
        rw [h.point_card] at hd'
        exact hd'
      have hcard := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
        (fun hz => hn (card_eq_one.mp hz))
      exact eq_of_le_of_card_ge hc (by rw [hcard,h.point_card])
    let k : G := (c.gb : G)⁻¹
    let A := D.UH.map (MulAut.conj k).toMonoidHom
    let C := D.V₁.map (MulAut.conj k).toMonoidHom
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
    have hAH : A ≤ D.H := AsymmetricPair.return_conjugate_le_H c D.UH
      (huv.trans (geo c).VH_endpoint)
    have hUC : ⁅D.UH,A⁆ = C := by
      have hm := congrArg (fun X : Subgroup G => X.map (MulAut.conj k).toMonoidHom) he
      rw [map_commutator] at hm
      have hcancel : (c.Ugamma D.Vplus).map (MulAut.conj k).toMonoidHom = D.UH :=
        PairConsequences.conjugate_inverse_cancel (c.gb : G) D.UH
      rw [hcancel,commutator_comm] at hm
      exact hm
    have hCA : A ≤ centralizer (C : Set G) := by
      apply commutator_eq_bot_iff_le_centralizer.mp
      change ⁅D.UH.map _,D.V₁.map _⁆ = ⊥
      rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr
        (h.UH_le_H.trans h.H_centralizes),Subgroup.map_bot]
    have hCZ : C ⊓ D.V₁ = ⊥ := by
      have hm := congrArg (fun X : Subgroup G => X.map (MulAut.conj k).toMonoidHom) (geo c).lines_disjoint
      rw [map_inf _ _ _ (MulAut.conj k).injective,Subgroup.map_bot] at hm
      have hh : (c.Aone D.V₁).map (MulAut.conj k).toMonoidHom = D.V₁ :=
        PairConsequences.conjugate_inverse_cancel (c.gb : G) D.V₁
      rwa [hh] at hm
    have hCC : Nat.card C = 2 := by
      rw [card_map_of_injective (MulAut.conj k).injective,h.point_card]
    have hnZ : ¬ ⁅D.UH,A⁆ ≤ D.V₁ := by
      rw [hUC]
      intro hz
      have heC : C = ⊥ := by simpa only [inf_eq_left.mpr hz] using hCZ
      rw [heC,card_bot] at hCC
      omega
    exact no_common_line s shape hAH hCC hUC.le hCA hnZ

end CFSG.Quasithin.Chapter12.Section06.LocalAlternatives
