module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.SourceHeads
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.MarkedSix.Eligible

/-!
# Source assembly of the L₄ head and chief-factor argument

The literal action on U_H/V₁ first supplies its elementary quadratic actor.
The covered natural flag and B.4.2/B.4.5 then identify every maximal quotient
as natural for one common identification H/O₂(H) ≃ GL₄(2). The actual
conjugate span supplies the generating seed, so the natural Sylow fixed line
forces a unique maximal submodule.

For a noncentral exterior-square chief section below that maximal submodule,
the marked radical calculation gives rank two and absence of offenders.
The forward sieve derives A₁ containment, a strong offender on the natural
head, Uγ*=Vγ*≅E₄, and quotient codimension one. The codimension equality
constructs an eligible reversed pair. Applying the same proved actor
calculation there gives V₁≤Uγ; component generation and 13.8.11(1) force
Uγ*<Vγ*, a contradiction. Thus B.4 leaves only natural or dual chief factors.
The proved I.1.6(6) cohomology calculation, with dual transport, removes
central factors. Failure of the whole-module natural conclusion also supplies
a nonzero maximal submodule and an irreducible submodule inside it.

Inputs are the genuine covered flag and source quotient action, the earlier
component/Sylow and normalizer statements, and the selected strict critical
pair of 13.8.8 with the earlier geometry and 13.8.18(4) rank inequality.
The endpoint component uses relative normality, the two-residual, and its
actual quotient image. Centralization of V₁ is the consequence of H=G₁
used by this argument. The only unproved model input is the explicitly
permitted universal B.4 classification, with faithfulness, irreducibility
and the quadratic-ratio bound retained. No natural-head, uniqueness,
rank-two-actor, strict-inclusion, chief-factor or splitting conclusion is
assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), 13.8.25, printed pp.960–961, PDF pp.977–978;
B.3.2(6), B.4.2/B.4.5, Remark F.9.17 and I.1.6(6).
-/

public section

open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open Alignment CriticalTransfer CriticalGeometry CriticalGeometry.Reorientation
open Chapter2.ComponentRefinement.LieType.Binary
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LinearReduction.Parabolics

universe v
variable {G : Type v} [Group G] [Finite G]

/-- The head and chief-factor conclusions of the L₄ branch of 13.8.25,
assembled from the source action and earlier selected critical-pair inputs.
The same actor equivalence identifies all heads and all natural-or-dual
chief sections; every chief section is noncentral. The final implication
retains the nonzero maximal kernel and an atom needed by the p.961–962
continuation. -/
theorem source_chief_factors
    (H K M L T V V₁ V₃ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (hKH : K ≤ H) (hLK : one L T V₁ ≤ K)
    (hLM : one L T V₁ ≤ M) (hTM : T ≤ M)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (hT : Chapter1.IsSylowIn 2 T H) (hKT : K ⊔ T = H)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hrel : ((one L T V₁).subgroupOf (H ⊓ M)).Normal)
    (hNM : normalizer (zero L : Set G) ≤ M)
    (eK : (K ⧸ pCore 2 K) ≃* PSL 4)
    (hseedIndex : V₁.relIndex V₃ = 4)
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      one L T V₁ ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃)
    (hVH : V ≤ H) (hz : H ≤ centralizer (V₁ : Set G)) (hline : Nat.card V₁ = 2)
    (he : (L ⊔ T) ⊓ H = one L T V₁ ⊔ T)
    (hKγ : ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)).Normal)
    (hresγ : pResidual 2 ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)) = ⊤)
    (hqsγ : IsQuasisimple (Source.starImage (vertexGroup L T H c.gamma)
      (K.map (MulAut.conj (c.gb : G)).toMonoidHom)))
    (hU : Source.UH H V₃ ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2)
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hindex : V₃.relIndex V = 2) (hnorm : (L ⊔ T) ⊓ H ≤ normalizer (V : Set G))
    (hgeo : ∀ b : CriticalPair L T H V, EarlierGeometry b V₃ V₁)
    (hcore : ∀ b : CriticalPair L T H V,
      b.Vgamma ≤ (edgeGroup L T H (base L T H true) b.second).pCoreIn 2)
    (hF916 : ∀ b : CriticalPair L T H V,
      0 < rank (Source.starImage H (b.Ugamma V₃)) →
      denominatorRank V₃ V₁ b ≤ rank (Source.starImage H (b.Ugamma V₃)) →
      fixedCodim ρ (Source.starImage H (b.Ugamma V₃)) ≤
        2 * rank (Source.starImage H (b.Ugamma V₃)))
    (hD : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hp : 0 < rank (Source.starImage H (c.Ugamma V₃)))
    (hcomp : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hrV : 1 < rank (Source.starImage H c.Vgamma))
    (hB4 : ∀ e : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace, LinearB4.{v} e) :
    ∃ (e : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
      (P : Submodule (ZMod 2) NaturalSpace) (W : Subrepresentation ρ),
      Module.finrank (ZMod 2) P = 2 ∧
      (Source.starImage H (one L T V₁ ⊔ T)).map e.toMonoidHom = BinaryLinear.parabolic P ∧
      AllNaturalHeads ρ e ∧ IsCoatom W ∧
      (∀ X : Subrepresentation ρ, IsCoatom X → X = W) ∧
      ChiefFactorsNaturalOrDual ρ e ∧
      (¬ IsNatural ρ e → W ≠ ⊥ ∧
        ∃ I : Subrepresentation ρ, IsAtom I ∧ I ≤ W) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) :=
    IsElementaryAbelian.of_le
      (show Source.UH H V₃ ≤ Source.VH H V from conjugateSpanBy_mono d.seed_le le_rfl)
  let s := sourceConjugationSection H V₃ V₁ ρ hρ
    (conjugateSpanBy_le_self (d.seed_le.trans hVH)) hz
    (d.line_le_seed.trans (le_conjugateSpanBy V₃ H))
  have hUV : c.Ugamma V₃ ≤ c.Vgamma :=
    map_mono (conjugateSpanBy_mono d.seed_le le_rfl)
  have hγH : c.Ugamma V₃ ≤ H := hUV.trans (hgeo c).Vgamma_H
  let : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have hA : IsElementaryTwo (Source.starImage H (c.Ugamma V₃)) := by
    refine ⟨?_, starImage_isElementaryAbelian H _ hγH⟩
    intro hbot
    rw [hbot, Representation.BinaryOffender.rank_bot] at hp
    omega
  have hquad := (c.quadratic_star_on_Utilde V₃ V₁ s d.seed_le (hgeo c).VH_endpoint).2
  have hbound := hF916 c hp hcomp
  obtain ⟨e, P, W, hP, hmark, hheads, hW, hu, hatom⟩ :=
    source_heads_unique_maximal H K M L T V V₁ V₃ (c.Ugamma V₃) d ρ hρ
      hKH hLK hLM hTM hK hKn hT hKT hcover hfactor hrel hNM eK hseedIndex hirr
      hA hquad hbound hB4
  have hTH := (Chapter1.isSylowIn_iff.mp hT).2.1
  have ht := (Chapter1.isSylowIn_iff.mp hT).1
  have hPH : one L T V₁ ⊔ T ≤ H := sup_le (hLK.trans hKH) hTH
  have hN : one L T V₁ ⊔ T ≤ normalizer (V₃ : Set G) := by
    apply sup_le _ d.seed_stable
    rw [hfactor]
    exact sup_le d.plus_normalizes_seed
      ((d.zero_centralizes.trans (centralizer_le d.seed_le)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hseedLine : V₁ < V₃ := lt_of_le_of_ne d.line_le_seed (by
    intro heq
    rw [heq, relIndex_self] at hseedIndex
    contradiction)
  let seed := sourceSeedOfEarlier H V₃ V₁ ρ hρ (one L T V₁ ⊔ T) T hPH le_sup_right ht hN
    hseedLine (fun X hx hy hn => hirr X hx hy (le_sup_left.trans hn)) hseedIndex
  have hstable : ∀ a : Source.starImage H (one L T V₁ ⊔ T), ∀ v ∈ s.image V₃,
      ρ a v ∈ s.image V₃ := by
    intro a v hv
    exact seed.space.apply_mem_toSubmodule a hv
  have hseedIrr : IsAtom (⟨s.image V₃, hstable⟩ :
      Subrepresentation (ρ.comp (Source.starImage H (one L T V₁ ⊔ T)).subtype)) :=
    seed.irreducible
  have hseedDim : Module.finrank (ZMod 2) (s.image V₃) = 2 := seed.dim_two
  have hzero : zero L ≤ one L T V₁ := by rw [hfactor]; exact le_sup_right
  have hH : H = K ⊔ (one L T V₁ ⊔ T) := by
    rw [← sup_assoc, sup_eq_left.mpr hLK, hKT]
  have hf : Function.Injective ρ := by
    have hfaith := IsNatural.faithful W.quotientRepresentation e (hheads W hW)
    intro a b hab
    apply hfaith
    apply LinearMap.ext
    intro v
    induction v using Submodule.Quotient.induction_on with | _ v =>
    exact congrArg W.toSubmodule.mkQ (LinearMap.congr_fun hab v)
  have hc := SixSymmetry.eligible_of_choice V₃ V₁ (one L T V₁) c s hf d.seed_le he
    (hgeo c) (hcore c) (hF916 c) hD hp hcomp hrV
  have hno : ∀ X Y : Subrepresentation ρ, X ⋖ Y → Y ≤ W →
      ¬ IsCentralSection ρ X Y → ¬ IsExteriorSquare (sectionRepresentation ρ X Y) e := by
    intro X Y hXY hYW hn hsix
    have hactor := MarkedSix.source_eligible_sixActorFacts s d.seed_le (zero L)
      (one L T V₁) hzero hPH d.zero_core_card d.zero_seed_commutator ht
      hstable hseedIrr hseedDim hgeo e hheads W hW X Y
    have ha := hactor c hc hXY hYW hn hsix
    let : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
    have hv : IsElementaryTwo (Source.starImage H c.Vgamma) := by
      refine ⟨?_, starImage_isElementaryAbelian H _ (hgeo c).Vgamma_H⟩
      intro hbot
      rw [hbot, Representation.BinaryOffender.rank_bot] at hrV
      omega
    have hback : Source.UH H V₃ ≤ H.map (MulAut.conj (c.gb : G)).toMonoidHom := by
      rw [← c.vertexGroup_gamma]
      exact (conjugateSpanBy_mono d.seed_le le_rfl).trans (hgeo c).VH_endpoint
    have hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃)
        (c.Aone V₁)).relIndex (Source.UH H V₃)) ≤
        Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex
          (c.Ugamma V₃)) := by
      rw [s.Dgamma_relIndex _ hγH hf]
      exact hcomp
    obtain ⟨_, _, _, heq, _⟩ := source_six_factor_codimensions s (c.gb : G) c.Vgamma
      hline hback hUV (hgeo c).Vgamma_H hA hv ha.1 hcritical e hheads W hW
      X Y hXY.le hYW ha.2
    have hstrict := (SixSymmetry.source_six_factor_strict V₃ V₁ (one L T V₁) K c s
      d.seed_le hVH hline hH he hKγ hresγ hqsγ hU hQ hnoncentral hindex hnorm
      hgeo hcore hF916 e hheads W hW X Y hXY hYW hn hsix hactor hD hp hcomp hrV).2
    exact hstrict.ne heq
  have hfactors := chief_factors_of_exterior_exclusion ρ e hheads W hW hu (hB4 e)
    (Source.starImage H (c.Ugamma V₃)) hA hquad hbound hno
  exact ⟨e, P, W, hP, hmark, hheads, hW, hu, hfactors, hatom⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
