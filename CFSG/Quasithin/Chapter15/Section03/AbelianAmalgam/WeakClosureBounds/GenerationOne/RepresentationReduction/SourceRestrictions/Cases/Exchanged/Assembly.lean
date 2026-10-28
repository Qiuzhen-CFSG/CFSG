module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.Filtering
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.MarkingTransport

/-!
# Conditional exchanged-case deduction with compatible Borel markings

The complete F.9.18(5) output is filtered against E.2.2, then the actual
overlaps are aligned with the natural-module identification by Sylow
conjugacy. The same adjusted map is used on both constituent coordinates.
The orthogonal case identifies the literal T-orbit with the actual
OmegaPlus natural action, without taking another central quotient.

The extra source premises are explicit: the finite faithful action, the
K₀-homogeneous Irr⁺ section, relative normalization of K in K₀, the two
commuting disjoint factors and return condition for each exchanger, the
product of their overlaps, normalization of that overlap by T, the actual
E.2.2 component/overlap comparison, and the complete earlier F.9.18 output.
No fixation, FF exclusion, or filtered module list is an input.

Source: Aschbacher--Smith, E.2.2, pp.215--216, F.9.18(5), pp.325--326,
and 15.3.65(i),(iii), printed p.1152.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
open RemainingModels PairCoordinates BorelReduction BorelReduction.SourceCases
variable {D E V X : Type*} [Group D] [Group E]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup X] [Module (ZMod 2) X]

/-- Group geometry only. These are explicit source-assembly obligations;
no statement about the representation is hidden in this structure. -/
structure ExchangedGeometry (K K₀ T B C : Subgroup D) : Prop where
  component_le : K ≤ K₀
  component_normal : K₀ ≤ normalizer (K : Set D)
  overlap_le : C ≤ K
  borel_normalized : T ≤ normalizer (B : Set D)
  moved : ∃ t ∈ T, t ∉ normalizer (K : Set D)
  pair : ∀ t ∈ T, t ∉ normalizer (K : Set D) →
    K ⊔ K.conjBy t⁻¹ = K₀ ∧ Disjoint K (K.conjBy t⁻¹) ∧
    K ≤ centralizer (K.conjBy t⁻¹ : Set D) ∧ K.conjBy t = K.conjBy t⁻¹ ∧
    B = C ⊔ C.conjBy t⁻¹

variable (ρ : Representation (ZMod 2) D V) {K K₀ T B C : Subgroup D}
  {I : Submodule (ZMod 2) V} (hi : IsIrrPlusWith ρ K₀ T I)

include hi in
/-- The supplied disjoint/commuting group geometry constructs the coordinates'
marked product for every actual source exchanger. -/
theorem ExchangedGeometry.marking (geo : ExchangedGeometry K K₀ T B C)
    {t : D} (ht : t ∈ T) (hout : t ∉ normalizer (K : Set D)) :
    Nonempty (ProductMarking K K₀ t) := by
  obtain ⟨hs, hd, hc, hr, _⟩ := geo.pair t ht hout
  exact productMarking_of_disjoint (hi.normalizes ht) hs hd hc hr

/-- An already established central-quotient identification can be aligned
with a source Sylow normalizer using the same group and module adjustment. -/
theorem alignCentralIdentification [Finite D] [Finite E]
    {hJ : K ≤ subspaceStabilizer ρ I} {σ : Representation (ZMod 2) E X}
    (d : CentralQuotientIdentification ρ K I hJ σ)
    (A : Subgroup K) (A' : Subgroup E)
    (hA : ∃ P : Sylow 2 K, normalizer (P : Set K) = A)
    (hA' : ∃ P : Sylow 2 E, normalizer (P : Set E) = A') :
    ∃ d' : CentralQuotientIdentification ρ K I hJ σ,
      A.map d'.groupEquiv.toMonoidHom = A' := by
  obtain ⟨g, hg, he⟩ := exists_innerIntertwiner_sylowNormalizer A A' hA hA'
    (centralQuotientRepresentation ρ K I hJ) σ d.groupEquiv d.linearEquiv d.equivariant
  exact ⟨⟨d.groupEquiv.trans (MulAut.conj g),
    d.linearEquiv.trans (innerIntertwiner σ g), he⟩, hg⟩

/-- The marked natural case retains its original and conjugate constituent
and the one actor map from which the pair action and both Borel images are computed. -/
structure MarkedPair (K K₀ T B : Subgroup D) (I : Submodule (ZMod 2) V)
    (hI : K₀ ≤ subspaceStabilizer ρ I) (σ : Representation (ZMod 2) E X)
    (B' : Subgroup E) where
  element : D
  mem_T : element ∈ T
  outside : element ∉ normalizer (K : Set D)
  product : ProductMarking K K₀ element
  orbit : orbitSpan ρ T I = I ⊔ rightConjugate ρ I element
  cross : subspaceCommutator ρ I (K.conjBy element⁻¹) = ⊥
  normalizes_borel : element ∈ normalizer (B : Set D)
  first : CentralQuotientIdentification ρ K I (product.le.trans hI) σ
  borel : (B.subgroupOf K₀).map (product.modelMap ρ first) = B'

namespace MarkedPair
variable {ρ} {hI : K₀ ≤ subspaceStabilizer ρ I} {σ : Representation (ZMod 2) E X}
    {B' : Subgroup E} (d : MarkedPair ρ K K₀ T B I hI σ B')

/-- Coordinates on the central quotient of the literal pair. -/
def coordinates := d.product.pairEquiv ρ d.cross d.first

/-- The pair representation uses conjugation by the actual element t⁻¹. -/
theorem coordinates_equivariant (g : K₀)
    (v : centralQuotient ρ K₀ (I ⊔ rightConjugate ρ I d.element)) :
    d.coordinates (centralQuotientRepresentation ρ K₀ _
      (d.product.pair_invariant ρ d.cross hI) g v) =
    exchangedAction σ K₀ d.product.exchanger (d.product.modelMap ρ d.first) g
      (d.coordinates v) := d.product.pairEquiv_equivariant ρ d.cross d.first hI g v

/-- The coordinate formula retains the aligned first constituent on both lifts. -/
theorem coordinates_lift (i j : I) :
    d.coordinates (Submodule.Quotient.mk (ProductMarking.pairLift ρ i j)) =
      (ProductMarking.constituentMap ρ d.first i, ProductMarking.constituentMap ρ d.first j) :=
  d.product.pairEquiv_lift ρ d.cross d.first i j

/-- The literal conjugate constituent uses the same group identification. -/
def second : CentralQuotientIdentification ρ (K.conjBy d.element⁻¹)
    (rightConjugate ρ I d.element)
    (ProductMarking.conjugate_invariant ρ (d.product.le.trans hI)) σ :=
  ProductMarking.conjugateIdentification ρ d.first

/-- The second Borel image uses exactly the second map of the exchanged action. -/
theorem second_borel : (B.subgroupOf K₀).map ((d.product.modelMap ρ d.first).comp
    (K₀.normalizerMonoidHom d.product.exchanger).symm.toMonoidHom) = B' :=
  d.product.second_borel_image ρ d.first B d.normalizes_borel B' d.borel

/-- These are exactly the kernel and return clauses used by the existing
cross-centralization calculation on the pair's two coordinate axes. -/
theorem kernels :
    (K.subgroupOf K₀).map (K₀.normalizerMonoidHom d.product.exchanger).symm.toMonoidHom =
      (K.subgroupOf K₀).map (K₀.normalizerMonoidHom d.product.exchanger).toMonoidHom ∧
    (K.subgroupOf K₀).map (K₀.normalizerMonoidHom d.product.exchanger).toMonoidHom =
      (d.product.modelMap ρ d.first).ker :=
  ⟨d.product.model_return, d.product.model_cross_kernel ρ d.first⟩

end MarkedPair

variable [Finite D]

/-- Construct the full pair output from one hatted natural constituent and
the source overlap. Neither pair coordinates nor either model Borel image is assumed. -/
theorem markedPair_of_hat [Finite E] (geo : ExchangedGeometry K K₀ T B C)
    (hC : ∃ P : Sylow 2 K, normalizer (P : Set K) = C.subgroupOf K)
    {t : D} (ht : t ∈ T) (hout : t ∉ normalizer (K : Set D))
    (horbit : orbitSpan ρ T I = I ⊔ rightConjugate ρ I t)
    (hcross : subspaceCommutator ρ I (K.conjBy t⁻¹) = ⊥)
    {σ : Representation (ZMod 2) E X} (B' : Subgroup E)
    (hB' : ∃ P : Sylow 2 E, normalizer (P : Set E) = B')
    (d : HatIdentification ρ K K₀ geo.component_le I hi.invariant σ) :
    Nonempty (MarkedPair ρ K K₀ T B I hi.invariant σ B') := by
  obtain ⟨p⟩ := geo.marking ρ hi ht hout
  obtain ⟨d', hd'⟩ := alignCentralIdentification ρ (p.centralIdentification ρ hcross d)
    (C.subgroupOf K) B' hC hB'
  refine ⟨⟨t, ht, hout, p, horbit, hcross, geo.borel_normalized ht, d', ?_⟩⟩
  change (B.subgroupOf K₀).map (d'.groupEquiv.toMonoidHom.comp p.firstProjection) = B'
  rw [← Subgroup.map_map, p.firstProjection_borel geo.overlap_le (geo.pair t ht hout).2.2.2.2]
  exact hd'

/-- The orthogonal identification is of the T-orbit itself, with its named
flag Borel under the same actor map. -/
structure MarkedOrthogonal {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (K₀ T B : Subgroup D) (I : Submodule (ZMod 2) V)
    (hIT : K₀ ≤ subspaceStabilizer ρ (orbitSpan ρ T I)) where
  identification : LiteralIdentification ρ K₀ (orbitSpan ρ T I) hIT (omegaNatural (F := F))
  borel : (B.subgroupOf K₀).map identification.groupEquiv.toMonoidHom = omegaBorel

/-- Transport a literal module identification across an equality of subspaces;
its group map is unchanged. -/
def LiteralIdentification.changeSpace {J : Submodule (ZMod 2) V}
    {hI : K₀ ≤ subspaceStabilizer ρ I} {σ : Representation (ZMod 2) E X}
    (d : LiteralIdentification ρ K₀ I hI σ) (h : I = J)
    (hJ : K₀ ≤ subspaceStabilizer ρ J) : LiteralIdentification ρ K₀ J hJ σ where
  groupEquiv := d.groupEquiv
  linearEquiv := (LinearEquiv.ofEq _ _ h.symm).trans d.linearEquiv
  equivariant := by subst J; exact d.equivariant

/-- H-invariance gives I_T=I; align the literal orthogonal module by Sylow conjugacy. -/
theorem markedOrthogonal_of_literal {F : Type*} [Field F] [Finite F] [CharP F 2]
    [Algebra (ZMod 2) F] (geo : ExchangedGeometry K K₀ T B C)
    (hC : ∃ P : Sylow 2 K, normalizer (P : Set K) = C.subgroupOf K)
    (hinv : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ I)
    (d : LiteralIdentification ρ K₀ I hi.invariant (omegaNatural (F := F))) :
    Nonempty (MarkedOrthogonal ρ (F := F) K₀ T B I
      (orbitSpan_component_invariant ρ hi.normalizes hi.isIrrPlus)) := by
  obtain ⟨t, ht, hout⟩ := geo.moved
  obtain ⟨p⟩ := geo.marking ρ hi ht hout
  have hB := p.borel_normalizer geo.overlap_le (geo.pair t ht hout).2.2.2.2 hC
  obtain ⟨g, hg, he⟩ := exists_innerIntertwiner_sylowNormalizer _ _ hB
    (BorelMarkings.omega_borel_normalizer (F := F))
    (invariantSubspace ρ K₀ I hi.invariant).toRepresentation omegaNatural
    d.groupEquiv d.linearEquiv d.equivariant
  have horbit := orbitSpan_eq_self ρ ((le_top : T ≤ ⊤).trans hinv)
  let d' : LiteralIdentification ρ K₀ I hi.invariant (omegaNatural (F := F)) :=
    ⟨d.groupEquiv.trans (MulAut.conj g),
      d.linearEquiv.trans (innerIntertwiner omegaNatural g), he⟩
  exact ⟨⟨d'.changeSpace ρ horbit.symm _, hg⟩⟩

/-- The p.1152 exchanged alternatives, now with actual marked module identities. -/
inductive MarkedConclusion (f : ℕ) : Prop
  | linear (F : Type) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
      (card : Nat.card F = 2 ^ f)
      (pair : MarkedPair ρ K K₀ T B I hi.invariant
        (restrictScalars (specialLinearNatural (k := F) 2)) (SpecialLinearGroup.rankOneBorel F))
  | suzuki (m : ℕ) (positive : 0 < m) (exponent : f = 2 * m + 1)
      (pair : MarkedPair ρ K K₀ T B I hi.invariant (suzukiNatural m)
        (BenderSuzuki.MatrixGroups.SuzukiBorelSubgroup m))
  | orthogonal (F : Type) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
      (card : Nat.card F = 2 ^ f)
      (module_id : MarkedOrthogonal ρ (F := F) K₀ T B I
        (orbitSpan_component_invariant ρ hi.normalizes hi.isIrrPlus))

/-- The conditional deduction from the complete F.9.18(5) list. The source
comparison identifies the actual component and overlap together. Finiteness,
faithfulness and K₀-homogeneity are retained for the upstream application. -/
theorem exchanged_cases_of_full_five [Finite V] (_faithful : Function.Injective ρ)
    {G : Type*} [Group G] {H M L : Subgroup G} {f : ℕ}
    (source : ExchangedModel H M L f) (hf : 1 < f) (ho : Odd f)
    (geo : ExchangedGeometry K K₀ T B C)
    (comparison : K ≃* sourceImage H M L)
    (overlap : (C.subgroupOf K).map comparison.toMonoidHom = componentOverlap H M L)
    (full : FullFiveConclusion ρ K K₀ T geo.component_le I hi.invariant) :
    MarkedConclusion ρ hi (K := K) (B := B) f := by
  let : Finite (sourceImage H M L) := Finite.of_equiv K comparison.toEquiv
  have hC := exists_sylow_normalizer_of_equiv comparison _ _ overlap
    (BorelMarkings.source_overlap_normalizer source)
  have h := full.filter ρ source comparison hf ho hi geo.component_normal
  cases h with
  | orthogonal F hF hinv d =>
    obtain ⟨d'⟩ := markedOrthogonal_of_literal ρ hi geo hC hinv d
    exact .orthogonal F hF d'
  | natural t ht hout horbit hcross natural =>
    cases natural with
    | linear F hF d =>
      obtain ⟨d'⟩ := markedPair_of_hat ρ hi geo hC ht hout horbit hcross _
        (BorelMarkings.slTwo_borel_normalizer (F := F)) d
      exact .linear F hF d'
    | suzuki m hm he d =>
      obtain ⟨d'⟩ := markedPair_of_hat ρ hi geo hC ht hout horbit hcross _
        (BorelMarkings.suzuki_borel_normalizer m hm) d
      exact .suzuki m hm he d'

omit [Finite D] in
/-- A literal marked orthogonal module has no Borel-fixed vectors. The
statement concerns I_T itself, so no central-extension splitting is required. -/
theorem MarkedOrthogonal.fixed_eq_bot {F : Type*} [Field F] [Finite F]
    [Algebra (ZMod 2) F] (hF : 2 < Nat.card F)
    {hIT : K₀ ≤ subspaceStabilizer ρ (orbitSpan ρ T I)}
    (d : MarkedOrthogonal ρ (F := F) K₀ T B I hIT) :
    orbitSpan ρ T I ⊓ fixedSpace ρ B = ⊥ := by
  have hz := fixedSpace_eq_bot_of_equivariant
    (invariantSubspace ρ K₀ (orbitSpan ρ T I) hIT).toRepresentation
    (omegaNatural (F := F)) d.identification.groupEquiv.toMonoidHom
    d.identification.linearEquiv d.identification.equivariant
    (B.subgroupOf K₀) omegaBorel d.borel (omega_borel_fixedSpace_eq_bot hF)
  apply le_bot_iff.mp
  intro v hv
  have hw : (⟨v, hv.1⟩ : orbitSpan ρ T I) ∈
      fixedSpace (invariantSubspace ρ K₀ (orbitSpan ρ T I) hIT).toRepresentation
        (B.subgroupOf K₀) := by
    intro g
    apply Subtype.ext
    exact hv.2 ⟨g.val, g.property⟩
  rw [hz] at hw
  exact congrArg Subtype.val hw

omit [Finite D] in
/-- The constructed module identities feed the existing fixed-space calculations.
No fixed-space conclusion is part of the classification input. -/
theorem MarkedConclusion.fixedSpace_le {f : ℕ} (hf : 1 < f)
    (h : MarkedConclusion ρ hi (K := K) (B := B) f) :
    orbitSpan ρ T I ⊓ fixedSpace ρ B ≤ fixedSpace ρ K₀ := by
  cases h with
  | linear F hF d =>
    rw [d.orbit]
    exact slTwo_exchanged_centralQuotient_fixed (field_card_gt_two hF hf)
      ρ K₀ B _ (d.product.pair_invariant ρ d.cross hi.invariant)
      d.product.exchanger (d.product.modelMap ρ d.first) d.coordinates
      d.coordinates_equivariant d.borel d.second_borel
  | suzuki m hm _ d =>
    rw [d.orbit]
    exact suzuki_exchanged_centralQuotient_fixed m hm ρ K₀ B _
      (d.product.pair_invariant ρ d.cross hi.invariant)
      d.product.exchanger (d.product.modelMap ρ d.first) d.coordinates
      d.coordinates_equivariant d.borel d.second_borel
  | orthogonal F hF d =>
    rw [d.fixed_eq_bot ρ (field_card_gt_two hF hf)]
    exact bot_le

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
