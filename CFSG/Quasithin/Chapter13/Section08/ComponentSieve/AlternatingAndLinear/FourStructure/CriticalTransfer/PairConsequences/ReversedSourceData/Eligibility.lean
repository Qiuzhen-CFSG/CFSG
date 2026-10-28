module

public import Theory.ElementaryAbelian.AbelianNormalClosure
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData.Modules
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Equivalence
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.PreliminaryGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.ExclusionBounds
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.MarkedGeometry

/-!
# Eligibility of the normalized reversed L₄ critical pair

Normalization returns the first edge to the fixed source edge. Thus the
actual section U_H/V₁, its nonzero unique maximal submodule W, its natural
head and the chosen natural-or-dual irreducible I can be reused at that
base. `Reversal.endpoint_modules` identifies their pre-normalization
transports at the original endpoint through the actual quotient isomorphism,
retaining the adjustment in the normalizing transporter.

The swapped actor is different. Its elementary and quadratic actions are
proved from the actual V_H-conjugate span and F.9.13's endpoint containment.
The finite-length splitting argument then proves both nonsplitting exclusions
for this actor. The required edge adjustment is constructed from incidence;
the source radical-placement theorem uses that same adjustment and the same
head. The actual line-normalizer theorem gives A₁ ≰ I. The centralizer bound
is conjugated from 13.7.3(7), and the flag proves 13.8.9(1)'s noncentrality.
Consequently `Eligible.forward` discharges every input of the proved forward
marked argument.

`SourceData` contains only intrinsic earlier data: the actual central section,
H=G₁=N_G(V₁), the source flag and marked L₀/L₁ facts, and the preceding
chief-factor conclusions of 13.8.25. The splitting premise is the precise
B.4.9(1) implication for a faithful two-factor module with natural kernel,
natural-or-dual head and a quadratic four-group having a common axis; its
whole-module consequences are proved by `SplittingCyclic.nonsplitting_bounds`.
The pair-specific inputs to the constructor are explicit F.9.11/13/15
conclusions and the complete 13.8.18(1) generation implication. The umbrella
specializes their explicitly uniform forms to the constructed reversal.
Neither a reversed witness, reversed nonsplitting, nor either final line
noncontainment is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.25,
printed pp.961–962 (PDF pp.978–979), using Remark F.9.17 and F.9.12–16,
printed pp.322–324. The final equality-case fixation and contradiction are
owned by the parent critical-pair argument.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
open CriticalGeometry CriticalGeometry.Reorientation ChiefFactors MarkedGeometry
universe u v
variable {G : Type u} {U : Type v} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  {L T H V V₃ V₁ : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) U}

/-- Intrinsic, pair-independent data from the standing source setup and the
preceding chief-factor argument of 13.8.25. All module identifications use the
same actual H/O₂(H). The only splitting input is two-factor B.4.9(1). -/
structure SourceData (L T H V V₃ V₁ : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) U) where
  sectionModel : ConjugationSection H (Source.UH H V₃) V₁ ρ
  normalizer_line : H = normalizer (V₁ : Set G)
  line_card : Nat.card V₁ = 2
  seed_le : V₃ ≤ V
  V_le : V ≤ H
  flag_index : V₃.relIndex V = 2
  edge_normalizes : (L ⊔ T) ⊓ H ≤ normalizer (V : Set G)
  noncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃
  centralizer_bound : ⁅Source.HC H V₃, Source.VH H V⁆ ≤ V₁
  L₀ : Subgroup G
  L₁ : Subgroup G
  edge_eq : (L ⊔ T) ⊓ H = L₁ ⊔ T
  L₀_le : L₀ ≤ L₁
  cubic : Nat.card (L₀ ⧸ pCore 2 L₀) = 3
  fixes_seed : ⁅L₀, V₃⁆ ≤ V₁
  two_group : IsPGroup 2 T
  seed_stable : ∀ a : Source.starImage H (L₁ ⊔ T), ∀ v ∈ sectionModel.image V₃,
    ρ a v ∈ sectionModel.image V₃
  seed_irreducible : IsAtom (⟨sectionModel.image V₃, seed_stable⟩ :
    Subrepresentation (ρ.comp (Source.starImage H (L₁ ⊔ T)).subtype))
  seed_dim : Module.finrank (ZMod 2) (sectionModel.image V₃) = 2
  eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace
  W : Subrepresentation ρ
  maximal : IsCoatom W
  nonzero : W ≠ ⊥
  unique_maximal : ∀ X : Subrepresentation ρ, IsCoatom X → X = W
  head : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] NaturalSpace
  head_equivariant : ∀ a w, head (W.quotientRepresentation a w) = eH a (head w)
  chief_factors : ChiefFactorsNaturalOrDual ρ eH
  splitting : SplittingCyclic.AxisExclusions.TwoFactorSplitting.{u, v} (Source.Hstar H)
  N : Subrepresentation ρ
  irreducible : IsAtom N
  submodule_le : N ≤ W
  I : Subgroup G
  line_le_I : V₁ ≤ I
  I_le : I ≤ Source.UH H V₃
  image_I : sectionModel.image I = N.toSubmodule

namespace SourceData
variable (S : SourceData L T H V V₃ V₁ ρ)

/-- The marked plane comes from the actual V₃-image in the chosen head. -/
noncomputable def plane : Submodule (ZMod 2) NaturalSpace :=
  headPlane ρ (sourceGeneratingSeed S.sectionModel S.L₁ T S.two_group
    S.seed_stable S.seed_irreducible S.seed_dim) S.W S.head

theorem plane_dim : Module.finrank (ZMod 2) S.plane = 2 :=
  headPlane_finrank ρ _ S.W S.maximal.ne_top S.head

theorem parabolic_le :
    (Source.starImage H (S.L₁ ⊔ T)).map S.eH.toMonoidHom ≤ BinaryLinear.parabolic S.plane :=
  headPlane_stable ρ (sourceGeneratingSeed S.sectionModel S.L₁ T S.two_group
    S.seed_stable S.seed_irreducible S.seed_dim) S.W S.eH S.head S.head_equivariant

theorem natural_irreducible : IsNaturalOrDual S.N.toRepresentation S.eH :=
  SplittingCyclic.AxisExclusions.naturalOrDual_atom ρ S.eH S.chief_factors S.N S.irreducible

include S in
theorem faithful : Function.Injective ρ :=
  SplittingCyclic.AxisExclusions.faithful_of_equivariant_surjection
    ρ S.W.quotientRepresentation S.W.toSubmodule.mkQ S.W.toSubmodule.mkQ_surjective
    (fun _ _ => rfl)
    (SplittingCyclic.AxisExclusions.natural_faithful _ S.eH ⟨S.head, S.head_equivariant⟩)

include S in
/-- Conjugation of 13.7.3(7), for the actual endpoint and centralizer.
No pair-specific centralizer hypothesis is promoted to a uniform one. -/
theorem endpoint_centralizer (c : CriticalPair L T H V) :
    ⁅vertexGroup L T H c.gamma ⊓ centralizer (c.Ugamma V₃ : Set G), c.Vgamma⁆ ≤
      c.Aone V₁ := by
  let e := MulAut.conj (c.gb : G)
  have hC : vertexGroup L T H c.gamma ⊓ centralizer (c.Ugamma V₃ : Set G) ≤
      (Source.HC H V₃).map e.toMonoidHom := by
    intro x hx
    rw [mem_map_equiv]
    refine ⟨?_, mem_centralizer_iff.mpr ?_⟩
    · have hh : x ∈ vertexGroup L T H c.gamma := hx.1
      rw [c.vertexGroup_gamma, mem_map_equiv] at hh
      exact hh
    · intro y hy
      apply e.injective
      have hh := mem_centralizer_iff.mp hx.2 (e y)
        (mem_map_of_mem e.toMonoidHom hy)
      simpa only [map_mul, e.apply_symm_apply] using hh
  have hc := map_mono (f := e.toMonoidHom) S.centralizer_bound
  rw [map_commutator] at hc
  exact (commutator_mono hC le_rfl).trans hc

end SourceData

/-- The pre-normalization base really is the original endpoint. The actual
normalizing transporter gives its central section, maximal kernel, natural
head and irreducible, with identical vector coordinates. Its inverse is the
normalization used by `r.walk_eq`; the final edge also has `terminalAdjustment`.
This connects the intrinsic module transport to this specific graph reversal. -/
theorem Reversal.endpoint_modules
    (S : SourceData L T H V V₃ V₁ ρ) {c : CriticalPair L T H V} (r : Reversal c) :
    let k : G0 L T H := c.gb * inG0 r.adjustment
    let e := MulAut.conj (k : G)
    let Wγ := endpointLattice e ρ S.W
    let Nγ := endpointLattice e ρ S.N
    H.map e.toMonoidHom = vertexGroup L T H c.gamma ∧
    (Source.UH H V₃).map e.toMonoidHom = c.Ugamma V₃ ∧
    V₁.map e.toMonoidHom = c.Aone V₁ ∧
    IsCoatom Wγ ∧ Wγ ≠ ⊥ ∧
    (∀ X : Subrepresentation (ρ.comp (starEquiv e H).symm.toMonoidHom),
      IsCoatom X → X = Wγ) ∧
    IsNatural Wγ.quotientRepresentation ((starEquiv e H).symm.trans S.eH) ∧
    IsAtom Nγ ∧ Nγ ≤ Wγ ∧
    IsNaturalOrDual Nγ.toRepresentation ((starEquiv e H).symm.trans S.eH) ∧
    (conjugateSection S.sectionModel e).image (S.I.map e.toMonoidHom) = Nγ.toSubmodule := by
  dsimp only
  let k : G0 L T H := c.gb * inG0 r.adjustment
  let e := MulAut.conj (k : G)
  have hk : k • base L T H true = c.gamma := by
    simp only [k, mul_smul, inG0_one, c.gb_one]
  have hH : H.map e.toMonoidHom = vertexGroup L T H c.gamma := by
    rw [← hk, vertexGroup_smul, vertexGroup_base]
    rfl
  have hmap (Q : Subgroup G) (hn : H ≤ normalizer (Q : Set G)) :
      Q.map e.toMonoidHom = Q.map (MulAut.conj (c.gb : G)).toMonoidHom := by
    change Q.map (MulAut.conj ((c.gb : G) * (r.adjustment : G))).toMonoidHom = _
    rw [conjugate_mul]
    have hfixed : Q.map (MulAut.conj (r.adjustment : G)).toMonoidHom = Q :=
      mem_normalizer_iff_map_conj_eq.mp (hn r.adjustment.property)
    rw [hfixed]
  exact ⟨hH, hmap _ S.sectionModel.normalizes,
    hmap _ (S.sectionModel.centralizes.trans (centralizer_le_normalizer _)),
    (endpointLattice_isCoatom e S.W).mpr S.maximal,
    endpointLattice_ne_bot e S.W S.nonzero,
    endpointLattice_unique_maximal e S.W S.unique_maximal,
    endpointLattice_natural_head e S.W S.eH ⟨S.head, S.head_equivariant⟩,
    (endpointLattice_isAtom e S.N).mpr S.irreducible,
    endpointLattice_le e S.N S.W S.submodule_le,
    endpointLattice_natural_or_dual e S.N S.eH S.natural_irreducible,
    endpointLattice_image S.sectionModel e S.I S.N S.image_I⟩

/-- Full eligibility for the forward marked argument, constructed below.
The intrinsic module data remain in `S`; these fields all concern this actor.
In particular the nonsplitting exclusions are for Vγ* of this pair. -/
structure Eligible (S : SourceData L T H V V₃ V₁ ρ) (c : CriticalPair L T H V) : Prop where
  Ugamma_le : c.Ugamma V₃ ≤ c.Vgamma
  Vgamma_le : c.Vgamma ≤ H
  endpoint_le : Source.UH H V₃ ≤ vertexGroup L T H c.gamma
  proper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃
  endpoint_proper : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃
  noncyclic : 1 < rank (Source.starImage H (c.Ugamma V₃))
  equality : Module.finrank (ZMod 2) (U ⧸ S.sectionModel.image
    (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))) =
      rank (Source.starImage H (c.Ugamma V₃))
  elementary : IsElementaryTwo (Source.starImage H c.Vgamma)
  quadratic : IsQuadratic ρ (Source.starImage H c.Vgamma)
  axes : ∀ A ≤ Source.starImage H c.Vgamma, 1 < rank A →
    1 < fixedCodim S.W.quotientRepresentation A
  centers : ∀ A ≤ Source.starImage H c.Vgamma, 1 < rank A →
    ¬ HasCommonCenter S.N.toRepresentation A
  line_not_le : ¬ c.Aone V₁ ≤ S.I
  marked : ∃ h : H,
    inG0 (L := L) (T := T) h⁻¹ • c.second = base L T H false ∧
    c.Vgamma.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom ≤ (S.L₁ ⊔ T).pCoreIn 2 ∧
    (Source.starImage H (c.Vgamma.map (MulAut.conj ((h : G)⁻¹)).toMonoidHom)).map
      S.eH.toMonoidHom ≤ BinaryLinear.radical S.plane
  generation : ∀ F ≤ Source.UH H V₃,
    ¬ F ≤ Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) →
    vertexGroup L T H c.gamma = conjugateSpanBy F (vertexGroup L T H c.gamma) ⊔
      edgeGroup L T H c.gamma c.previous

variable [Finite G] [FiniteDimensional (ZMod 2) U]
  [IsElementaryAbelian 2 (Source.VH H V)]

/-- Check the reversed actor by the same proved source arguments.
`hgeo` and `hcore` are the earlier F.9.11/13/15 conclusions for this pair;
`generation18` is precisely earlier 13.8.18(1), with H=KL₁T already discharged.
Neither nonsplitting, marked radical placement nor A₁ ≰ I is assumed. -/
theorem eligible_of_rank_and_equality
    (S : SourceData L T H V V₃ V₁ ρ) (c : CriticalPair L T H V)
    (hgeo : EarlierGeometry c V₃ V₁)
    (hcore : c.Vgamma ≤ (edgeGroup L T H (base L T H true) c.second).pCoreIn 2)
    (generation18 : ∀ F ≤ Source.UH H V₃,
      ¬ F ≤ Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) →
      vertexGroup L T H c.gamma = conjugateSpanBy F (vertexGroup L T H c.gamma) ⊔
        edgeGroup L T H c.gamma c.previous)
    (hrank : 1 < rank (Source.starImage H (c.Ugamma V₃)))
    (hequal : Module.finrank (ZMod 2) (U ⧸ S.sectionModel.image
      (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))) =
        rank (Source.starImage H (c.Ugamma V₃))) : Eligible S c := by
  have hUV : c.Ugamma V₃ ≤ c.Vgamma := map_mono (conjugateSpanBy_mono S.seed_le le_rfl)
  have hγH := hUV.trans hgeo.Vgamma_H
  have hUJ := (conjugateSpanBy_mono S.seed_le le_rfl).trans hgeo.VH_endpoint
  let _ : IsElementaryAbelian 2 c.Vgamma := IsElementaryAbelian.map _
  have hB : IsElementaryTwo (Source.starImage H c.Vgamma) := by
    refine ⟨?_, starImage_isElementaryAbelian H _ hgeo.Vgamma_H⟩
    intro hbot
    have hle : Source.starImage H (c.Ugamma V₃) ≤ Source.starImage H c.Vgamma :=
      map_mono (subgroupOf_mono H hUV)
    have hz : Source.starImage H (c.Ugamma V₃) = ⊥ := bot_unique (hbot ▸ hle)
    rw [hz, Representation.BinaryOffender.rank_bot] at hrank
    omega
  have hq := (c.quadratic_star_on_Utilde V₃ V₁ S.sectionModel S.seed_le hgeo.VH_endpoint).1
  obtain ⟨haxes, hcenters⟩ := SplittingCyclic.nonsplitting_bounds ρ S.eH S.splitting
    S.chief_factors S.W S.maximal S.nonzero S.unique_maximal
    ⟨S.head, S.head_equivariant⟩ (Source.starImage H c.Vgamma) hB hq
  obtain ⟨k, hk, hplace, _⟩ := exists_second_to_base c S.L₁ ((S.L₁ ⊔ T).pCoreIn 2)
    (by have := hgeo.length; omega) S.edge_eq hcore le_rfl
  have hPH : S.L₁ ⊔ T ≤ H := S.edge_eq.symm.le.trans inf_le_right
  have hrad := source_radical_placement S.sectionModel S.L₀ S.L₁ T c.Vgamma
    S.L₀_le hPH S.cubic S.fixes_seed S.two_group S.seed_stable S.seed_irreducible
    S.seed_dim S.W S.maximal.ne_top S.eH S.head S.head_equivariant k⁻¹
    (by simpa only [Subgroup.coe_inv, inv_inv] using hplace)
  have hnot := SplittingCyclic.SourceNormalizers.criticalPair_Aone_not_le c S.sectionModel
    S.normalizer_line S.line_card hgeo.lines_disjoint hgeo.Vgamma_H S.I S.I_le S.N S.image_I
    S.eH S.natural_irreducible hB S.plane S.plane_dim k
    (by simpa only [SourceData.plane, Subgroup.coe_inv, inv_inv] using hrad)
  have hproper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃ := by
    refine lt_of_le_of_ne (commutatorPreimage_le _ _ _) ?_
    intro he
    rw [S.sectionModel.quotient_finrank _ (S.sectionModel.line_le_DH _ _ hγH),
      he, relIndex_self, Nat.log_one_right] at hequal
    omega
  have hproperγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃ := by
    refine lt_of_le_of_ne (commutatorPreimage_le _ _ _) ?_
    intro he
    have hi := S.sectionModel.Dgamma_relIndex (c.Ugamma V₃) hγH S.faithful
    rw [he, relIndex_self] at hi
    have hz : rank (Source.starImage H (c.Ugamma V₃)) = 0 := by
      rw [rank, ← hi]
      decide
    omega
  exact ⟨hUV, hgeo.Vgamma_H, hUJ, hproper, hproperγ, hrank, hequal, hB, hq,
    haxes, hcenters S.N S.irreducible S.submodule_le, hnot,
    ⟨k⁻¹, by simpa only [inv_inv] using hk,
      by simpa only [Subgroup.coe_inv, inv_inv] using hplace, by simpa only [SourceData.plane] using hrad⟩, generation18⟩

/-- The constructed eligibility discharges all additional inputs of the
proved forward implication. The 13.8.9(1) noncentrality is proved from the
literal flag and generation, not requested again at the reversed pair. -/
theorem Eligible.forward
    (S : SourceData L T H V V₃ V₁ ρ) (c : CriticalPair L T H V)
    (hc : Eligible S c) : ¬ V₁ ≤ c.Ugamma V₃ := by
  obtain ⟨h, _, _, hrad⟩ := hc.marked
  have hUA : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) := by
    apply hc.endpoint_le.trans
    rw [c.vertexGroup_gamma]
    exact (S.sectionModel.centralizes_conjugate_line (c.gb : G)).trans (centralizer_le_normalizer _)
  have hnorm := hc.endpoint_le.trans (c.normalizes_Ugamma V₃)
  have hA : Nat.card (c.Aone V₁) = 2 := by
    rw [CriticalPair.Aone, card_map_of_injective (MulAut.conj _).injective, S.line_card]
  let _ : IsElementaryAbelian 2 V := IsElementaryAbelian.of_le
    (show V ≤ Source.VH H V from le_conjugateSpanBy V H)
  have hedge := c.edge_commutator_le_of_flag V₃ S.seed_le S.flag_index S.noncentral S.edge_normalizes
  obtain ⟨_, _, _, _, _, hline⟩ := forward_noncontainment_of_marked_radical V₃ V₁
    S.sectionModel S.I (vertexGroup L T H c.gamma) (edgeGroup L T H c.gamma c.previous)
    (c.Ugamma V₃) c.Vgamma (c.Aone V₁) S.line_le_I S.I_le S.N S.image_I
    S.eH S.natural_irreducible hc.Ugamma_le hc.Vgamma_le hc.endpoint_le hUA hnorm
    (S.endpoint_centralizer c) hA hc.line_not_le hc.noncyclic hc.centers
    h S.plane S.plane_dim hrad hc.generation
    (fun F hF _ hgen => c.noncentral_of_generation V₃ F S.V_le
      (hF.trans hc.endpoint_le) hgen hedge S.noncentral)
  exact hline

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
