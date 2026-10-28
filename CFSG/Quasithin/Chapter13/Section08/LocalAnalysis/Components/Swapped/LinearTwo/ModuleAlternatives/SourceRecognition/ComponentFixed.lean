module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition.Quotients
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.ConjugatePairInternalLift

/-!
# Fixed spaces in the original irreducible quotient

The two component fixed spaces have an invariant sum, because the original
component normalizer has index two. Irreducibility makes this sum zero or
the entire quotient. In the latter case each component moves only vectors
fixed by the other, producing the cross-factor quotient excluded by the
literal diagonal seed argument. Hence both fixed spaces vanish.

This removes trivial component constituents without any B.4/B.5
classification premise. It does not identify the remaining module.

Source: Aschbacher–Smith, 13.8.16(1), printed pp.952–953.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition

private theorem fixed_conjugate_image
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (A : Subgroup D) (g : D) :
    (fixedSpace ρ A).map (ρ g) ≤ fixedSpace ρ (A.conjBy g) := by
  rintro _ ⟨v,hv,rfl⟩ b
  obtain ⟨a,ha,he⟩ := b.property
  have hb : (b : D) = g * a * g⁻¹ := he.symm
  change ρ (b : D) (ρ g v) = ρ g v
  rw [hb]
  simp only [map_mul, Module.End.mul_apply, inv_self_apply]
  exact congrArg (ρ g) (hv ⟨a,ha⟩)

/-- For an irreducible representation with two conjugate components, either
both component fixed spaces vanish, or each component's moved space is
fixed by the other. This uses the literal conjugation orbit, not a module
classification. -/
private theorem cross_fixed_or_component_fixed_eq_bot
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) [ρ.IsIrreducible]
    (A B : Subgroup D)
    (hA : ∀ g : D, A.conjBy g = A ∨ A.conjBy g = B)
    (hB : ∀ g : D, B.conjBy g = A ∨ B.conjBy g = B)
    (hc : A ≤ centralizer (B : Set D)) :
    (subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B ∧
      subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A) ∨
    (fixedSpace ρ A = ⊥ ∧ fixedSpace ρ B = ⊥) := by
  let C : Subrepresentation ρ := {
    toSubmodule := fixedSpace ρ A ⊔ fixedSpace ρ B
    apply_mem_toSubmodule := by
      intro g v hv
      obtain ⟨a,ha,b,hb,rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add]
      apply Submodule.add_mem
      · have hh := fixed_conjugate_image ρ A g (Submodule.mem_map_of_mem (f := ρ g) ha)
        rcases hA g with he | he
        · exact Submodule.mem_sup_left (he ▸ hh)
        · exact Submodule.mem_sup_right (he ▸ hh)
      · have hh := fixed_conjugate_image ρ B g (Submodule.mem_map_of_mem (f := ρ g) hb)
        rcases hB g with he | he
        · exact Submodule.mem_sup_left (he ▸ hh)
        · exact Submodule.mem_sup_right (he ▸ hh) }
  rcases IsSimpleOrder.eq_bot_or_eq_top C with h | h
  · right
    have hh : fixedSpace ρ A ⊔ fixedSpace ρ B = ⊥ :=
      congrArg Subrepresentation.toSubmodule h
    exact ⟨bot_unique (le_sup_left.trans hh.le),bot_unique (le_sup_right.trans hh.le)⟩
  · left
    have hh : fixedSpace ρ A ⊔ fixedSpace ρ B = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    have hf (X Y : Subgroup D) (hXY : X ≤ centralizer (Y : Set D))
        (hs : fixedSpace ρ X ⊔ fixedSpace ρ Y = ⊤) :
        subspaceCommutator ρ ⊤ X ≤ fixedSpace ρ Y := by
      apply Submodule.span_le.mpr
      rintro _ ⟨x,hx,v,_,rfl⟩
      obtain ⟨u,hu,w,hw,he⟩ := Submodule.mem_sup.mp (hs.symm ▸ (Submodule.mem_top (x := v)))
      have hxu : ρ x u = u := hu ⟨x,hx⟩
      rw [← he,map_add,hxu]
      have heq : u + ρ x w - (u+w) = ρ x w - w := by abel
      rw [heq]
      apply (fixedSpace ρ Y).sub_mem _ hw
      intro y
      change ρ y (ρ x w) = ρ x w
      rw [← Module.End.mul_apply, ← map_mul, (hXY hx y y.property),map_mul,
        Module.End.mul_apply]
      exact congrArg (ρ x) (hw y)
    exact ⟨hf A B hc hh,hf B A (le_centralizer_iff.mp hc) (by rwa [sup_comm])⟩


open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hmoving

private theorem source_pair_conjugates {t : G} (ht : t ∈ T)
    (htn : t ∉ normalizer (K : Set G)) :
    (∀ g : Source.Hstar H,
      (Source.starImage H K).conjBy g = Source.starImage H K ∨
      (Source.starImage H K).conjBy g = Source.starImage H (K.conjBy t)) ∧
    (∀ g : Source.Hstar H,
      (Source.starImage H (K.conjBy t)).conjBy g = Source.starImage H K ∨
      (Source.starImage H (K.conjBy t)).conjBy g = Source.starImage H (K.conjBy t)) := by
  have hi := Original.moving_index d h hF9all hcentral hcomm hsource hH hKH hK hmoving
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  let tH : H := ⟨t,hTH ht⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  have hm : (K.subgroupOf H).conjBy tH ≠ K.subgroupOf H := by
    intro he
    have he' := congrArg (Subgroup.map H.subtype) he
    rw [map_conjBy_hom,map_subgroupOf_eq_of_le hKH] at he'
    exact htn (mem_normalizer_iff_map_conj_eq.mpr he')
  have htstar : (Source.starImage H K).conjBy (q tH) =
      Source.starImage H (K.conjBy t) :=
    starImage_conjBy H K hKH (hTH ht)
  have hfirst (g : Source.Hstar H) :
      (Source.starImage H K).conjBy g = Source.starImage H K ∨
      (Source.starImage H K).conjBy g = Source.starImage H (K.conjBy t) := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
    rcases NormPair.conjugate_eq_or_eq_of_normalizer_index_two hi hm x with he | he
    · left
      exact (map_conjBy_hom q (K.subgroupOf H) x).symm.trans
        (congrArg (Subgroup.map q) he)
    · right
      exact ((map_conjBy_hom q (K.subgroupOf H) x).symm.trans
        (congrArg (Subgroup.map q) he)).trans
        ((map_conjBy_hom q (K.subgroupOf H) tH).trans htstar)
  refine ⟨hfirst,fun g => ?_⟩
  have he : (Source.starImage H (K.conjBy t)).conjBy g =
      (Source.starImage H K).conjBy (g * q tH) := by
    rw [conjBy_mul,htstar]
  rw [he]
  exact hfirst _

include hgen in
/-- Every irreducible proper source quotient has zero fixed space for both
literal components. A nonzero fixed space would supply the cross-factor
quotient already excluded by the source diagonal argument. -/
theorem source_irreducible_quotient_component_fixed_eq_bot {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G))
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    [W.quotientRepresentation.IsIrreducible] :
    fixedSpace W.quotientRepresentation (Source.starImage H K) = ⊥ ∧
      fixedSpace W.quotientRepresentation (Source.starImage H (K.conjBy t)) = ⊥ := by
  obtain ⟨hA,hB⟩ := source_pair_conjugates d h hF9all hcentral hcomm hsource
    hH hKH hK hmoving ht htn
  obtain ⟨F,hF,hfin,hchar,a,ha,hb,_,_⟩ := exists_source_exchangedActor
    d h hF9all hcentral hcomm hsource hH hKH hK hgen hmoving hn hmodel ht htn
  have hc : Source.starImage H K ≤ centralizer (Source.starImage H (K.conjBy t) : Set (Source.Hstar H)) := by
    rw [← ha,← hb]
    exact commutator_eq_bot_iff_le_centralizer.mp
      (a.component_isComponent.commutator_eq_bot_of_ne a.second_isComponent a.distinct.symm)
  rcases cross_fixed_or_component_fixed_eq_bot W.quotientRepresentation _ _ hA hB hc with hx | hz
  · exact (Original.false_of_cross_factor_quotient d h hF9all hcentral hcomm hsource
      hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn ⟨W,hW,hx⟩).elim
  · exact hz

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.SourceRecognition
