module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.SelectedEndpoint
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Transport

/-!
# The full-denominator endpoint in 14.6.13

When Vplus = V, criticality forces the left denominator to be proper. A full
right denominator therefore makes the commutator equal the base central line.
Conjugating by the inverse of the same terminal-edge representative gives the
literal returned module, its two containments, and its transported commutator
line. The intersecting-conjugates condition separates that line from the base
line. The endpoint bridge preserves the original critical pair's representative.

This is the endpoint geometry in the first paragraph of the proof of 14.6.13;
the orthogonal-action recognition and factor normalization belong to its
separate assembly. The original-source application discharges the
intersecting-conjugates condition in `FullDenominatorSource`.

Source: Aschbacher--Smith, 14.6.13, printed p.1031, and F.9.13--16,
printed pp.322--324. All maps use left conjugation.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open Chapter13.Section08 Chapter13.Section08.SourceCompletion
open Chapter13.Section08.CriticalGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The inverse of a full-denominator endpoint gives a common noncentral
commutator line on the original module. -/
structure ReturnedLineAction (H U Z : Subgroup G) where
  g : G
  in_H : U.map (MulAut.conj g).toMonoidHom ≤ H
  reverse : U ≤ H.map (MulAut.conj g).toMonoidHom
  commutator : ⁅U,U.map (MulAut.conj g).toMonoidHom⁆ = Z.map (MulAut.conj g).toMonoidHom
  disjoint : Z ⊓ Z.map (MulAut.conj g).toMonoidHom = ⊥

/-- When the two source seeds coincide, criticality already excludes a full
left denominator. No rank or recognition theorem is used. -/
theorem left_denominator_strict (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hplus : D.Vplus = D.V)
    (c : CriticalPair D.L (D.T : Subgroup G) D.H D.V) (hb : 3 ≤ c.path.length) :
    Source.DH D.UH (c.Ugamma D.Vplus) (c.Aone D.V₁) < D.UH := by
  have hUA : D.UH ≤ normalizer (c.Aone D.V₁ : Set G) := by
    apply le_trans ((conjugateSpanBy_mono h.plus_le le_rfl).trans
      (f9_endpoint_spans D h c hb).1)
    rw [c.vertexGroup_gamma,CriticalPair.Aone,←map_equiv_normalizer_eq]
    exact map_mono (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  apply lt_of_le_of_ne (commutatorPreimage_le _ _ _)
  intro he
  have hc : ⁅D.UH,c.Ugamma D.Vplus⁆ ≤ c.Aone D.V₁ := by
    conv_lhs => lhs; rw [←he]
    exact commutator_commutatorPreimage_le _ _ _ hUA
  apply f9_commutator_not_le_Aone D h c hb
  rw [commutator_comm]
  apply (commutator_mono ?_ le_rfl).trans hc
  change D.V ≤ conjugateSpanBy D.Vplus D.H
  rw [hplus]
  exact le_conjugateSpanBy _ _

/-- A full right denominator supplies an actual inverse conjugator, with
the entire commutator equal to its transported central point. -/
theorem returned_line_of_full (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hplus : D.Vplus = D.V)
    (c : CriticalPair D.L (D.T : Subgroup G) D.H D.V) (hb : 3 ≤ c.path.length)
    (hcomm : ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hfull : Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁ = c.Ugamma D.Vplus) :
    ∃ t : ReturnedLineAction D.H D.UH D.V₁, t.g = (c.gb : G)⁻¹ := by
  have hends := f9_endpoint_spans D h c hb
  have huv : D.UH ≤ D.VH := conjugateSpanBy_mono h.plus_le le_rfl
  have hγH : c.Ugamma D.Vplus ≤ D.H := (map_mono huv).trans hends.2
  have hc := AsymmetricPair.commutator_eq_line_of_asymmetry D.UH (c.Ugamma D.Vplus)
    D.V₁ (c.Aone D.V₁) h.point_card
    (hγH.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
    (left_denominator_strict D h hplus c hb) hfull
  let g : G := (c.gb : G)⁻¹
  have hcancel (A : Subgroup G) :
      (A.map (MulAut.conj (c.gb : G)).toMonoidHom).map (MulAut.conj g).toMonoidHom = A :=
    conjBy_inv A (c.gb : G)
  have hback : D.UH.map (MulAut.conj g).toMonoidHom ≤ D.H := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) (huv.trans hends.1)
    rw [c.vertexGroup_gamma,hcancel] at hh
    exact hh
  have hrev : D.UH ≤ D.H.map (MulAut.conj g).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hγH
    change (D.UH.map (MulAut.conj (c.gb : G)).toMonoidHom).map _ ≤ _ at hh
    rwa [hcancel] at hh
  have hc' := congrArg (fun A : Subgroup G => A.map (MulAut.conj g).toMonoidHom) hc
  rw [map_commutator,CriticalPair.Ugamma,hcancel,commutator_comm] at hc'
  have hd := congrArg (fun A : Subgroup G => A.map (MulAut.conj g).toMonoidHom)
    (f9_lines_disjoint D h c hb hcomm)
  rw [map_inf _ _ _ (MulAut.conj g).injective,CriticalPair.Aone,hcancel,Subgroup.map_bot,inf_comm] at hd
  exact ⟨⟨g,hback,hrev,hc',hd⟩,rfl⟩

/-- The returned conjugator is the inverse of the same normalized F.9 endpoint. -/
theorem full_endpoint (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hplus : D.Vplus = D.V)
    (c : CriticalPair D.L (D.T : Subgroup G) D.H D.V) (hb : 3 ≤ c.path.length)
    (hcomm : ∀ g : G, D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆ = ⊥)
    (hfull : Source.Dgamma (c.Ugamma D.Vplus) D.UH D.V₁ = c.Ugamma D.Vplus) :
    ∃ i : h.CriticalEndpoint, i.representative = (c.gb : G) ∧
      ∃ t : ReturnedLineAction D.H D.UH D.V₁, t.g = i.representative⁻¹ := by
  obtain ⟨i,hi⟩ := f9_criticalPair_endpoint D h c (by omega)
  obtain ⟨t,ht⟩ := returned_line_of_full D h hplus c hb hcomm hfull
  exact ⟨i,hi,t,ht.trans (congrArg Inv.inv hi).symm⟩

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
