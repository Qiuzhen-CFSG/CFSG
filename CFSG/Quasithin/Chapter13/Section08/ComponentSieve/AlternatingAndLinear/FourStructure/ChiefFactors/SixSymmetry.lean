module

public import Theory.ElementaryAbelian.AbelianNormalClosure
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceSix
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Heads
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Equivalence
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Selection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.PreliminaryGeometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.SectionActions
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.LineContainments.Symmetry

/-!
# Symmetry in the six-dimensional chief-factor branch

For a fixed noncentral exterior-square chief section below a maximal W,
the marked actor calculation is a uniform implication on eligible critical
pairs. `Eligible` contains only earlier selection, quadratic-action and edge
placement conditions. It includes neither actor rank two nor absence of
offenders, line containment or strict inclusion of the star images.

The forward sieve gives A₁ ≤ W, Uγ*=Vγ* of order four, and denominator
codimension two. F.9.17 constructs a reversed geodesic with both stabilizer
adjustments. The actual adjusted conjugator exchanges actor rank and
codimension, making both equal to two at the reversal. We check its strict
denominators, quadratic actions, Q-family bound, noncyclic Vγ* and actual
H-conjugate placement in the edge two-core. The same marked implication
and forward sieve now give the reversed A₁ ≤ W. Transport of this genuine
subgroup containment proves V₁ ≤ Uγ.

The final theorem constructs the original pair's eligibility from the
selected numerical choice and the earlier 13.8.18(4) rank bound. It invokes
the proved component generation in 13.8.18(2), derives the terminal-edge
commutator bound from the index-two flag, and applies 13.8.11(1) to obtain
Uγ* < Vγ*. The explicit component inputs use relative normality, the actual
two-residual and the actual endpoint quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.25,
printed p.961 (PDF p.978), Remark F.9.17, printed p.324, and 13.8.11(1),
13.8.18(2), printed pp.949–950 and 953. The F.9 geometry and estimate,
common natural heads and marked-actor implication remain explicit earlier
inputs. This conditional symmetry step uses no p.962 nonsplitting results;
the parent owns the marked-actor discharge and final chief-factor exclusion.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SixSymmetry
open CriticalTransfer CriticalGeometry CriticalGeometry.Reorientation
open CriticalTransfer.PairConsequences.ReversedSourceData
variable {G U : Type*} [Group G] [Finite G] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] {L T H V : Subgroup G}
  {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- The earlier hypotheses required at one critical pair. The placement
witness is an actual element of H carrying the adjacent edge to the base edge. -/
structure Eligible (L₁ V₃ V₁ : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) U)
    (c : CriticalPair L T H V) : Prop where
  proper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃
  endpoint_proper : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃
  comparison : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃))
  member : QuadraticMember ρ (Source.starImage H (c.Ugamma V₃))
  noncyclic : 1 < rank (Source.starImage H c.Vgamma)
  quadratic : IsQuadratic ρ (Source.starImage H c.Vgamma)
  placement : ∃ h : H, inG0 (L := L) (T := T) h • c.second = base L T H false ∧
    c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2

omit [Finite G] [FiniteDimensional (ZMod 2) U] in
private theorem faithful_of_heads
    (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
    (hheads : AllNaturalHeads ρ eH) (W : Subrepresentation ρ) (hW : IsCoatom W) :
    Function.Injective ρ := by
  have hf := IsNatural.faithful W.quotientRepresentation eH (hheads W hW)
  intro a b hab
  apply hf
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with | _ v =>
  exact congrArg W.toSubmodule.mkQ (LinearMap.congr_fun hab v)

variable (V₃ V₁ : Subgroup G)
  [IsElementaryAbelian 2 (Source.UH H V₃)]
  [IsElementaryAbelian 2 (Source.VH H V)]

omit [Finite G] [IsElementaryAbelian 2 (Source.VH H V)] in
private theorem elementary_star_of_rank (d : CriticalPair L T H V)
    (hV₃ : V₃ ≤ V) (hVH : d.Vgamma ≤ H)
    (hp : 0 < rank (Source.starImage H (d.Ugamma V₃))) :
    IsElementaryTwo (Source.starImage H (d.Ugamma V₃)) := by
  let _ : IsElementaryAbelian 2 (d.Ugamma V₃) := IsElementaryAbelian.map _
  refine ⟨?_, starImage_isElementaryAbelian H _
    ((map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans hVH)⟩
  intro hbot
  rw [hbot, Representation.BinaryOffender.rank_bot] at hp
  omega

omit [FiniteDimensional (ZMod 2) U] in
/-- Check all actor eligibility conditions from the selected numerical
choice, 13.8.18(4)'s noncyclicity, and the earlier F.9 conclusions. The
endpoint denominator is strict because the faithful star action has positive
rank. The quadratic action and the edge adjustment are constructed. -/
theorem eligible_of_choice
    (L₁ : Subgroup G) (d : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ) (hfaith : Function.Injective ρ)
    (hV₃ : V₃ ≤ V) (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hgeo : EarlierGeometry d V₃ V₁)
    (hcore : d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2)
    (hF916 : 0 < rank (Source.starImage H (d.Ugamma V₃)) →
      denominatorRank V₃ V₁ d ≤ rank (Source.starImage H (d.Ugamma V₃)) →
      fixedCodim ρ (Source.starImage H (d.Ugamma V₃)) ≤
        2 * rank (Source.starImage H (d.Ugamma V₃)))
    (hD : Source.DH (Source.UH H V₃) (d.Ugamma V₃) (d.Aone V₁) < Source.UH H V₃)
    (hp : 0 < rank (Source.starImage H (d.Ugamma V₃)))
    (hc : denominatorRank V₃ V₁ d ≤ rank (Source.starImage H (d.Ugamma V₃)))
    (hv : 1 < rank (Source.starImage H d.Vgamma)) : Eligible L₁ V₃ V₁ ρ d := by
  have hγH : d.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans hgeo.Vgamma_H
  have hdγ : Source.Dgamma (d.Ugamma V₃) (Source.UH H V₃) V₁ < d.Ugamma V₃ := by
    refine lt_of_le_of_ne (commutatorPreimage_le _ _ _) ?_
    intro heq
    have hi := s.Dgamma_relIndex (d.Ugamma V₃) hγH hfaith
    rw [heq, relIndex_self] at hi
    have hz : rank (Source.starImage H (d.Ugamma V₃)) = 0 := by
      rw [rank, ← hi]
      decide
    omega
  obtain ⟨h, hh, hplace, _⟩ := exists_second_to_base d L₁ ((L₁ ⊔ T).pCoreIn 2)
    (by have := hgeo.length; omega) he hcore le_rfl
  have hq := d.quadratic_star_on_Utilde V₃ V₁ s hV₃ hgeo.VH_endpoint
  exact ⟨hD, hdγ, hc,
    ⟨elementary_star_of_rank V₃ d hV₃ hgeo.Vgamma_H hp, hq.2, hF916 hp hc⟩,
    hv, hq.1, h, hh, hplace⟩

/-- The p.961 symmetry with an actual reversed geodesic. Both conjugator
adjustments are retained by `Reversal`; its eligibility is a conclusion.
The fixed section X ⋖ Y ≤ W is reused with the same actor identification.
The original forward equality and codimensions are retained for the parent
chief-factor exclusion, but no final contradiction is taken here. -/
theorem six_factor_reversal
    (L₁ : Subgroup G) (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hV₃ : V₃ ≤ V) (hline : Nat.card V₁ = 2)
    (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hgeo : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ V₁)
    (hcore : ∀ d : CriticalPair L T H V,
      d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2)
    (hF916 : ∀ d : CriticalPair L T H V,
      0 < rank (Source.starImage H (d.Ugamma V₃)) →
      denominatorRank V₃ V₁ d ≤ rank (Source.starImage H (d.Ugamma V₃)) →
      fixedCodim ρ (Source.starImage H (d.Ugamma V₃)) ≤
        2 * rank (Source.starImage H (d.Ugamma V₃)))
    (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
    (hheads : AllNaturalHeads ρ eH) (W : Subrepresentation ρ) (hW : IsCoatom W)
    (X Y : Subrepresentation ρ) (hXY : X ⋖ Y) (hYW : Y ≤ W)
    (hn : ¬ IsCentralSection ρ X Y)
    (hsix : Alignment.IsExteriorSquare (sectionRepresentation ρ X Y) eH)
    (hactor : ∀ d : CriticalPair L T H V, Eligible L₁ V₃ V₁ ρ d →
      X ⋖ Y → Y ≤ W → ¬ IsCentralSection ρ X Y →
      Alignment.IsExteriorSquare (sectionRepresentation ρ X Y) eH →
      SixActorFacts ρ X Y (Source.starImage H (d.Ugamma V₃)) (Source.starImage H d.Vgamma))
    (hc : Eligible L₁ V₃ V₁ ρ c) :
    ∃ r : Reversal c,
      Eligible L₁ V₃ V₁ ρ r.pair ∧
      rank (Source.starImage H (r.pair.Ugamma V₃)) = 2 ∧
      denominatorRank V₃ V₁ r.pair = 2 ∧
      c.Aone V₁ ≤ liftedSubmodule s W.toSubmodule ∧
      r.pair.Aone V₁ ≤ liftedSubmodule s W.toSubmodule ∧
      V₁ ≤ c.Ugamma V₃ ∧
      Source.starImage H (c.Ugamma V₃) = Source.starImage H c.Vgamma ∧
      rank (Source.starImage H (c.Ugamma V₃)) = 2 ∧
      Nat.card (Source.starImage H (c.Ugamma V₃)) = 4 ∧
      Module.finrank (ZMod 2) ((U ⧸ W.toSubmodule) ⧸
        (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))).map
          W.toSubmodule.mkQ) = 1 ∧
      denominatorRank V₃ V₁ c = 2 := by
  have hf := faithful_of_heads eH hheads W hW
  have hUV (d : CriticalPair L T H V) : d.Ugamma V₃ ≤ d.Vgamma :=
    map_mono (conjugateSpanBy_mono hV₃ le_rfl)
  have hγH (d : CriticalPair L T H V) : d.Ugamma V₃ ≤ H :=
    (hUV d).trans (hgeo d).Vgamma_H
  have hback (d : CriticalPair L T H V) :
      Source.UH H V₃ ≤ H.map (MulAut.conj (d.gb : G)).toMonoidHom := by
    rw [← d.vertexGroup_gamma]
    exact (conjugateSpanBy_mono hV₃ le_rfl).trans (hgeo d).VH_endpoint
  have forward (d : CriticalPair L T H V) (hd : Eligible L₁ V₃ V₁ ρ d) := by
    have ha := hactor d hd hXY hYW hn hsix
    let _ : IsElementaryAbelian 2 d.Vgamma := IsElementaryAbelian.map _
    have hv : IsElementaryTwo (Source.starImage H d.Vgamma) := by
      refine ⟨?_, starImage_isElementaryAbelian H _ (hgeo d).Vgamma_H⟩
      intro hz
      have hh := hd.noncyclic
      rw [hz, Representation.BinaryOffender.rank_bot] at hh
      omega
    have hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (d.Ugamma V₃)
        (d.Aone V₁)).relIndex (Source.UH H V₃)) ≤
        Nat.log 2 ((Source.Dgamma (d.Ugamma V₃) (Source.UH H V₃) V₁).relIndex
          (d.Ugamma V₃)) := by
      rw [s.Dgamma_relIndex _ (hγH d) hf]
      exact hd.comparison
    exact source_six_factor_codimensions s (d.gb : G) d.Vgamma hline (hback d)
      (hUV d) (hgeo d).Vgamma_H hd.member.1 hv ha.1 hcritical eH hheads
      W hW X Y hXY.le hYW ha.2
  obtain ⟨hAW, _, _, hUVeq, hr, hcard, hhead, hdim, _⟩ := forward c hc
  change rank (Source.starImage H (c.Ugamma V₃)) = 2 at hr
  change Module.finrank (ZMod 2) (U ⧸ s.image
    (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))) = 2 at hdim
  obtain ⟨r⟩ := exists_reversal_of_rank V₃ V₁ c s hf (hgeo c).length
    (hUV c) (hgeo c).Vgamma_H (hgeo c).first_kernel (by rw [hr]; decide)
  obtain ⟨hrank, hcodim⟩ := adjusted_rank_and_codimension s (c.gb : G)
    r.adjustment r.terminalAdjustment (hγH c) (hback c) hf
  rw [← r.conjugator_val] at hrank hcodim
  change Module.finrank (ZMod 2) (U ⧸ s.image
    (Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃) (r.pair.Aone V₁))) = _ at hcodim
  have hrank' : rank (Source.starImage H (r.pair.Ugamma V₃)) = 2 := hrank.trans hdim
  have hcodim' : denominatorRank V₃ V₁ r.pair = 2 := by
    rw [s.quotient_finrank _ (s.line_le_DH _ _ (hγH r.pair))] at hcodim
    exact hcodim.trans hr
  have hc' : denominatorRank V₃ V₁ c = 2 := by
    rw [s.quotient_finrank _ (s.line_le_DH _ _ (hγH c))] at hdim
    exact hdim
  have hproper : Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃)
      (r.pair.Aone V₁) < Source.UH H V₃ := by
    refine lt_of_le_of_ne (commutatorPreimage_le _ _ _) ?_
    intro heq
    simp only [denominatorRank, heq, relIndex_self, Nat.log_one_right] at hcodim'
    contradiction
  have hnoncyclic : 1 < rank (Source.starImage H r.pair.Vgamma) := by
    have hle : Source.starImage H (r.pair.Ugamma V₃) ≤ Source.starImage H r.pair.Vgamma :=
      map_mono (subgroupOf_mono H (hUV r.pair))
    have hm := Nat.log_monotone (b := 2) (card_le_of_le hle)
    change rank (Source.starImage H (r.pair.Ugamma V₃)) ≤
      rank (Source.starImage H r.pair.Vgamma) at hm
    omega
  have heligible := eligible_of_choice V₃ V₁ L₁ r.pair s hf hV₃ he (hgeo r.pair)
    (hcore r.pair) (hF916 r.pair) hproper (by rw [hrank']; decide)
    (by rw [hcodim', hrank']) hnoncyclic
  have hrevAW := (forward r.pair heligible).1
  have hZ := s.centralizes.trans (centralizer_le_normalizer _)
  have hlineU : V₁ ≤ c.Ugamma V₃ :=
    (A6Endgame.LineContainments.reversal_lines c r V₃ V₁ hZ).1.mp
      (hrevAW.trans (liftedSubmodule_le s W.toSubmodule))
  exact ⟨r, heligible, hrank', hcodim', hAW, hrevAW, hlineU, hUVeq, hr, hcard, hhead, hc'⟩

/-- The line containment and strict star inclusion in the six-factor
branch of 13.8.25. The initial numerical choice and noncyclicity are the
explicit earlier 13.8.8(2)/13.8.18(4) conclusions. Eligibility at the reversal,
the line containment, and 13.8.18(2)'s generation are all proved here. The
parent discharges `hactor` from the common marked heads and B.3.2(6). -/
theorem source_six_factor_strict
    (L₁ K : Subgroup G) (c : CriticalPair L T H V)
    (s : ConjugationSection H (Source.UH H V₃) V₁ ρ)
    (hV₃ : V₃ ≤ V) (hVH : V ≤ H) (hline : Nat.card V₁ = 2)
    (hH : H = K ⊔ (L₁ ⊔ T)) (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hK : ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)).Normal)
    (hres : pResidual 2 ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)) = ⊤)
    (hqs : IsQuasisimple (Source.starImage (vertexGroup L T H c.gamma)
      (K.map (MulAut.conj (c.gb : G)).toMonoidHom)))
    (hU : Source.UH H V₃ ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2)
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hindex : V₃.relIndex V = 2) (hnorm : (L ⊔ T) ⊓ H ≤ normalizer (V : Set G))
    (hgeo : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ V₁)
    (hcore : ∀ d : CriticalPair L T H V,
      d.Vgamma ≤ (edgeGroup L T H (base L T H true) d.second).pCoreIn 2)
    (hF916 : ∀ d : CriticalPair L T H V,
      0 < rank (Source.starImage H (d.Ugamma V₃)) →
      denominatorRank V₃ V₁ d ≤ rank (Source.starImage H (d.Ugamma V₃)) →
      fixedCodim ρ (Source.starImage H (d.Ugamma V₃)) ≤
        2 * rank (Source.starImage H (d.Ugamma V₃)))
    (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
    (hheads : AllNaturalHeads ρ eH) (W : Subrepresentation ρ) (hW : IsCoatom W)
    (X Y : Subrepresentation ρ) (hXY : X ⋖ Y) (hYW : Y ≤ W)
    (hn : ¬ IsCentralSection ρ X Y)
    (hsix : Alignment.IsExteriorSquare (sectionRepresentation ρ X Y) eH)
    (hactor : ∀ d : CriticalPair L T H V, Eligible L₁ V₃ V₁ ρ d →
      X ⋖ Y → Y ≤ W → ¬ IsCentralSection ρ X Y →
      Alignment.IsExteriorSquare (sectionRepresentation ρ X Y) eH →
      SixActorFacts ρ X Y (Source.starImage H (d.Ugamma V₃)) (Source.starImage H d.Vgamma))
    (hD : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hp : 0 < rank (Source.starImage H (c.Ugamma V₃)))
    (hcomp : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hrV : 1 < rank (Source.starImage H c.Vgamma)) :
    V₁ ≤ c.Ugamma V₃ ∧
      Source.starImage H (c.Ugamma V₃) < Source.starImage H c.Vgamma := by
  have hf := faithful_of_heads eH hheads W hW
  have hc := eligible_of_choice V₃ V₁ L₁ c s hf hV₃ he (hgeo c)
    (hcore c) (hF916 c) hD hp hcomp hrV
  obtain ⟨_, _, _, _, _, _, hlineU, _⟩ := six_factor_reversal V₃ V₁ L₁ c s
    hV₃ hline he hgeo hcore hF916 eH hheads W hW X Y hXY hYW hn hsix hactor hc
  obtain ⟨hstar, hgen⟩ := c.generation_hypotheses L₁ K V₃ V₁ hH he hK hres hqs hU
    (hgeo c).DH_kernel hV₃ (hgeo c).Vgamma_H (hgeo c).Dgamma_kernel
    hc.proper hc.endpoint_proper
  let _ : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  let _ : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le
    (show V ≤ Source.VH H V from le_conjugateSpanBy V H)
  have hstrict := SectionActions.CriticalPair.strict_star_of_line_or_no_v_transvection c
    V₃ V₁ hV₃ hVH (hgeo c).Vgamma_H
    ((conjugateSpanBy_mono hV₃ le_rfl).trans (hgeo c).VH_endpoint) s.line_le
    (s.centralizes.trans (centralizer_le_normalizer _)) hQ hline hgen
    (c.edge_commutator_le_of_flag V₃ hV₃ hindex hnoncentral hnorm) hnoncentral hstar
    (Or.inl hlineU)
  exact ⟨hlineU, hstrict.1⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SixSymmetry
