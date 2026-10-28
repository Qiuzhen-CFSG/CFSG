module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Overgroup

/-!
# Conditional group reduction in Aschbacher–Smith 13.8.25

From K/O₂(K) ≃ Lₙ(2), 3 ≤ n ≤ 5, prove n = 4, L/O₂(L) ≃ Â₆,
H* ≃ L₄(2), and H = G₁. The earlier local and appendix results are explicit
inputs; the independent A₇ exclusion is supplied uniformly on Hz.

The parabolic reduction constructs the lower-rank contradictions and leaves
either the covered case or the marked middle-node S₈ action. In the latter
case we turn the deleted flag into the actual line–hyperplane stabilizer.
The literal maximal quotient retains the two-dimensional generating seed;
this excludes natural-plus-dual and yields the natural six-dimensional
module. The universal 13.7.6(3) input forces K to act nontrivially on W.

Both strong-offender branches use actual natural/augmentation sections and
the distinct transposition centers to prove the critical index-two statement
and the six-versus-five contradiction. The remaining rank-one branch uses
the two source hyperplanes and the larger critical actor, transported to
U_H/V₁, for the pointwise-centralizer contradiction. A first-case transvection
is excluded in S₈ using the earlier 13.8.5 alternatives; it is never discarded
from the original dichotomy.

Finally the reduction is applied uniformly to the genuine C-component
extension from 1.2.4 and A.3.12. Its actual quotient images and the component
order bound give K₁ = K, and 13.8.21(3) gives H = G₁. The separate assertion
that the entire U_H/V₁ is natural belongs to the subsequent FourStructure
argument and is not asserted here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.959–960/PDF pp.976–977.
The earlier inputs are Notation 13.2.1, 13.2.2, 13.7.3, 13.7.6(3),
13.8.5,8,13,16,18,21–23, and B.4.2/B.4.5.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open CFSG.Quasithin.Chapter13.Section08
open ComponentSieve.AlternatingAndLinear.LinearReduction
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Orthogonal.SourceTransport

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.SourceReduction

private theorem middleNode_coordinates {G : Type*} [Group G] [Finite G] (H K L₁ T : Subgroup G)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* PSL 4)
    (hm : Parabolics.MiddleNodeMarking H K L₁ T hKH hK e) :
    ∃ (eH : Source.Hstar H ≃* Equiv.Perm (Fin 8))
      (eK : Source.starImage H K ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace)
      (A F : Submodule (ZMod 2) OrthogonalQuotient.FourSpace),
      (Source.starImage H K).map eH.toMonoidHom = alternatingGroup (Fin 8) ∧
      A ≤ F ∧ Module.finrank (ZMod 2) A = 1 ∧
      Module.finrank (ZMod 2) F + 1 = Module.finrank (ZMod 2) OrthogonalQuotient.FourSpace ∧
      ((Source.starImage H L₁ ⊔ (Source.starImage H K ⊓ Source.starImage H T)).subgroupOf
        (Source.starImage H K)).map eK.toMonoidHom = BinaryLinear.parabolic A ⊓ BinaryLinear.parabolic F := by
  obtain ⟨b, i, hi, hp, _, _, _, _, eH, _, heH, _⟩ := hm
  have hi' : i = 1 := Fin.ext (by simpa using hi)
  subst i
  let eK := linearModel (Parabolics.starLinearEquiv H K hKH hK e)
  refine ⟨eH, eK, cutSpace b 0, cutSpace b 2, heH,
    BinaryLinear.InvariantNodeActions.cutSpace_mono b (by decide), ?_, ?_, ?_⟩
  · exact BinaryLinear.InvariantNodeActions.cutSpace_finrank b 0
  · change Module.finrank (ZMod 2) (BinaryLinear.InvariantNodeActions.cutSpace b 2) + 1 = _
    rw [BinaryLinear.InvariantNodeActions.cutSpace_finrank]
    norm_num [OrthogonalQuotient.FourSpace, Module.finrank_pi]
  · have hp' := Parabolics.OuterAction.deletedFlag_linear_image (by decide : 2 ≤ 3)
      (Parabolics.starLinearEquiv H K hKH hK e) b 1
    rw [← hp] at hp'
    change _ = _ at hp'
    rw [inf_comm (Source.starImage H K)]
    change ((Parabolics.OrdinarySource.sourceNode H K L₁ T).subgroupOf (Source.starImage H K)).map
      (linearModel (Parabolics.starLinearEquiv H K hKH hK e)).toMonoidHom = _
    rw [hp']
    change BinaryLinear.InvariantNodeActions.minimalParabolic b 1 = _
    ext g
    simp only [BinaryLinear.InvariantNodeActions.minimalParabolic,
      BinaryLinear.InvariantNodeActions.cutStabilizer, mem_iInf, mem_inf]
    simp [Fin.forall_fin_succ]
    rfl

private theorem binary_model {X : Type*} [Group X] {n : ℕ} (h : ClassicalGroup.IsPSL X n 2) :
    Nonempty (X ≃* PSL n) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact ⟨e.trans (Atlas.fieldEquivPSL n eF)⟩

private theorem triple_cover {X : Type*} [Group X] (h : SolvableExclusion.IsTripleCoverSix X) :
    CFSG.Quasithin.Chapter1.Section02.LocalModels.IsAlternatingCover X 6 := by
  exact ⟨h.1, ⟨mulEquivOfPrimeCardEq h.2.1 (Nat.card_zmod 3)⟩, h.2.2⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.SourceReduction


open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.SourceReduction
open Chapter1 Chapter1.Section02.LocalModels CriticalGeometry
open FourStructure.ChiefFactors FourStructure.CriticalTransfer
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open OrthogonalQuotient.B4Extraction
open Orthogonal.SourceTransport
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The earlier local action, residual identities, 13.8.13, and the complete
component list and supplement of 13.8.21. The three-dimensional clause keeps
the full automorphism group, and every component is relative to its overgroup. -/
structure GroupFacts (L L₁ T V V₁ V₃ G₁ M : Subgroup G) : Prop where
  local_definition : L₁ = one L T V₁
  local_action : Nonempty (Parabolics.OrdinarySource.NaturalSetup L T V V₁) ∨
    (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
      Nonempty (LocalAction.NaturalSetup L T V V₁ V₃))
  base_le_M : L ⊔ T ≤ M
  theta : ∀ H ∈ Source.Hz L₁ T G₁ M,
    L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3}
  local_normal : ∀ H ∈ Source.Hz L₁ T G₁ M, (L₁.subgroupOf (H ⊓ M)).Normal
  covered_factor : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
    one L T V₁ = plus L T V₁ ⊔ zero L
  covered_normalizer : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
    normalizer (zero L : Set G) ≤ M
  solvable_overgroups : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
    Group.IsSolvable J → J ≤ M
  base_le_component : ∀ {J C : Subgroup G}, J ∈ Source.Hz L₁ T G₁ M → C ≤ J →
    (C.subgroupOf J).IsCComponent → L₁ ≤ C
  component_list : ∀ {J C : Subgroup G}, J ∈ Source.Hz L₁ T G₁ M → C ≤ J →
    (C.subgroupOf J).IsCComponent →
    (∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) n 2) ∨
      IsAlternating (C ⧸ pCore 2 C) 6 ∨ IsAlternating (C ⧸ pCore 2 C) 7 ∨
      Nonempty ((C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2)))
  supplement : ∀ {J C : Subgroup G}, J ∈ Source.Hz L₁ T G₁ M → C ≤ J →
    (C.subgroupOf J).IsCComponent → J = C ⊔ T
  component_normal : ∀ {J C : Subgroup G}, J ∈ Source.Hz L₁ T G₁ M → C ≤ J →
    (C.subgroupOf J).IsCComponent → (C.subgroupOf J).Normal
  three_automorphisms : ∀ (J C : Subgroup G), J ∈ Source.Hz L₁ T G₁ M → C ≤ J →
    (C.subgroupOf J).IsCComponent → Nonempty ((C ⧸ pCore 2 C) ≃* PSL 3) →
    Nonempty (Source.Hstar J ≃* MulAut Matrix.PSL3Two.PSL)

variable {L T H V : Subgroup G} (c : CriticalPair L T H V)
  (K L₁ G₁ M V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))

/-- Earlier facts on the literal critical pair and conjugation module.
The seed clauses are those preceding 13.8.22; the alternatives retain both
cases of 13.8.8. The indices are 13.8.23(1), the larger rank is 13.8.18(4),
and the centralizer commutator is 13.7.3(7). The B.4 and 13.7.6 inputs are
universal earlier implications, with actual equivariant model conclusions.

No maximal quotient, orthogonal model, nontrivial K-action on W, rank-one
actor or index bound on C_{Uγ*}(D̃_H) is assumed here. -/
structure ModuleFacts : Prop where
  source_action : IsSourceAction H V₃ V₁ τ
  inside : Source.UH H V₃ ≤ H
  central_denominator : H ≤ centralizer (V₁ : Set G)
  denominator_le : V₁ ≤ Source.UH H V₃
  generated : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆
  seed_stable : ∀ g : (Source.starImage H L₁ ⊔ Source.starImage H T : Subgroup (Source.Hstar H)),
    ∀ v ∈ sourceSeedSpace H V₃ V₁, τ g v ∈ sourceSeedSpace H V₃ V₁
  seed_irreducible : IsAtom (⟨sourceSeedSpace H V₃ V₁, seed_stable⟩ :
    Subrepresentation (τ.comp (Source.starImage H L₁ ⊔ Source.starImage H T).subtype))
  seed_rank : Module.finrank (ZMod 2) (sourceSeedSpace H V₃ V₁) = 2
  seed_commutator : subspaceCommutator τ (sourceSeedSpace H V₃ V₁)
    (Source.starImage H L₁) = sourceSeedSpace H V₃ V₁
  transvection_models : ∀ a : Source.Hstar H, a ≠ 1 → fixedCodim τ (zpowers a) = 1 →
    Seven.LocalGeometry.TransvectionModels τ L
  critical_cases : (∃ a : Source.Hstar H, a ≠ 1 ∧ fixedCodim τ (zpowers a) = 1) ∨
    Seven.LocalGeometry.SecondCase H L₁ T (Source.UH H V₃) (c.Ugamma V₃) c.Vgamma
      (c.Aone V₁) V₁ τ
  seed_flag : V₃ ≤ V
  larger_actor_le : c.Vgamma ≤ H
  critical_line_normalized : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G)
  critical_line_card : Nat.card (c.Aone V₁) = 2
  larger_rank : (∀ a : Source.Hstar H, a ≠ 1 → fixedCodim τ (zpowers a) ≠ 1) →
    1 < rank (Source.starImage H c.Vgamma)
  critical_indices : ∀ W : Subrepresentation τ, IsCoatom W →
    rank (Source.starImage H (c.Ugamma V₃)) = 1 →
    (∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w) →
    (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex (Source.UH H V₃) = 2 ∧
      ((Source.UH H V₃) ⊓ centralizer (c.Ugamma V₃ : Set G)).relIndex
        (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)) = 2
  centralizer_commutator : ⁅Source.UH H V₃ ⊓ centralizer (c.Ugamma V₃ : Set G), c.Vgamma⁆ ≤ c.Aone V₁
  symmetric_modules : ∀ eH : Source.Hstar H ≃* Equiv.Perm (Fin 8),
    (Source.starImage H K).map eH.toMonoidHom = alternatingGroup (Fin 8) →
    SymmetricB4.{u} (Source.starImage H K) eH
  component_modules : ∀ (eH : Source.Hstar H ≃* Equiv.Perm (Fin 8))
    (eK : Source.starImage H K ≃* BinaryLinear.GL OrthogonalQuotient.FourSpace),
    (Source.starImage H K).map eH.toMonoidHom = alternatingGroup (Fin 8) →
    ComponentB4.{u} (Source.starImage H K) eH eK
  alternating_natural : Seven.PairsBranch.CentralAction.AlternatingNaturalImplication L L₁ T G₁ M τ

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.SourceReduction
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.SourceReduction
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
open FourStructure.ChiefFactors FourStructure.CriticalTransfer
open Orthogonal.SourceTransport OrthogonalQuotient.B4Extraction
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open CriticalGeometry
universe u
variable {G : Type u} [Group G] [Finite G]
  {L T H V : Subgroup G} {c : CriticalPair L T H V}
  {K L₁ G₁ M V₃ V₁ : Subgroup G}
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  {τ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁)}

private def sourceSection (d : ModuleFacts c K L₁ G₁ M V₃ V₁ τ) :
    ConjugationSection H (Source.UH H V₃) V₁ τ where
  le := d.inside
  normalizes := le_normalizer_conjugateSpanBy V₃ H
  centralizes := d.central_denominator
  line_le := d.denominator_le
  quotient := {
    toFun u := Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u))
    map_one' := map_one (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))
    map_mul' := map_mul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))) }
  surjective := QuotientGroup.mk'_surjective _
  kernel := QuotientGroup.ker_mk' _
  conjugates := d.source_action

omit [Finite G] in
private theorem no_transvection_s8
    (d : ModuleFacts c K L₁ G₁ M V₃ V₁ τ)
    (eH : Source.Hstar H ≃* Equiv.Perm (Fin 8)) :
    ∀ a : Source.Hstar H, a ≠ 1 → fixedCodim τ (zpowers a) ≠ 1 := by
  intro a ha ht
  have hc : Nat.card (Source.Hstar H) = 40320 := by
    rw [Nat.card_congr eH.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hm := d.transvection_models a ha ht
  unfold Seven.LocalGeometry.TransvectionModels at hm
  rcases hm with hs | hl | hm
  · obtain ⟨e⟩ := hs
    have he := Nat.card_congr e.toEquiv
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at he
    omega
  · obtain ⟨e⟩ := hl
    have hl : Nat.card (PSL 4) = 20160 := by
      rw [Nat.card_congr Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8.toEquiv,
        nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [Nat.card_congr e.toEquiv, hl] at hc
    norm_num at hc
  · obtain ⟨_, e, _, _⟩ := hm
    have he := Nat.card_congr e.toEquiv
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at he
    omega

/-- Exclusion of the marked middle-node outcome, with the actual quotient,
strong sections, critical line and larger actor all constructed internally. -/
theorem exclude_middle_node
    (d : ModuleFacts c K L₁ G₁ M V₃ V₁ τ)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) (hLK : L₁ ≤ K)
    (hT : IsPGroup 2 (Source.starImage H T))
    (e : (K ⧸ pCore 2 K) ≃* PSL 4)
    (hm : Parabolics.MiddleNodeMarking H K L₁ T hKH hK e) : False := by
  obtain ⟨eH, eK, A, F, hKalt, hAF, hA, hF, hmiddle⟩ := middleNode_coordinates H K L₁ T hKH hK e hm
  have hUV : c.Ugamma V₃ ≤ c.Vgamma :=
    map_mono (conjugateSpanBy_mono d.seed_flag le_rfl)
  have hUγ := hUV.trans d.larger_actor_le
  have hnt := no_transvection_s8 d eH
  have hs := d.critical_cases.resolve_left (by rintro ⟨a, ha, ht⟩; exact hnt a ha ht)
  have hindex := hs.2.2.2.1
  have hactor := hs.2.2.2.2.1
  have hq := hs.2.2.2.2.2.1
  have hb := hs.2.2.2.2.2.2.1
  obtain ⟨W, hw⟩ := OrthogonalQuotient.exists_source_quotient H V₃ V₁ L L₁ T G₁ M K
    (c.Ugamma V₃) τ d.source_action hH d.denominator_le hKH hK hLK d.generated
    eH hKalt eK A F hAF hA hF hmiddle hT d.seed_stable d.seed_irreducible d.seed_rank
    d.seed_commutator hactor hq hb (d.symmetric_modules eH hKalt)
    (d.component_modules eH eK hKalt) d.alternating_natural
  let s := sourceSection d
  have hm := OffenderModels.source_offender_model_alternatives H V₃ V₁ K
    (c.Ugamma V₃) (c.Aone V₁) τ s W hw.maximal eH hKalt hw.natural hw.component_moves
    hKH d.generated.symm hactor hq hb hUγ d.critical_line_normalized
    d.critical_line_card hindex (d.symmetric_modules eH hKalt)
    (fun eK => d.component_modules eH eK hKalt)
  obtain ⟨hD, hSdim, hdisp⟩ := critical_linear_data s (c.Ugamma V₃) (c.Aone V₁)
    hUγ d.critical_line_normalized d.critical_line_card hindex
  rcases hm with hstrongQ | ⟨hnoQ, hrest⟩
  · obtain ⟨_, g, ⟨m⟩, _⟩ := hstrongQ
    exact orthogonal_sections_critical_line_contradiction τ W m.J
      (OffenderModels.conjugateMarking eH g) m.model (Or.inl m.quotient_natural)
      (Source.starImage H (c.Ugamma V₃)) m.actor_marking
      (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))) (s.image (c.Aone V₁))
      hD hSdim hdisp
  · rcases hrest with hstrongW | hrank
    · obtain ⟨_, _, g, ⟨m⟩, _⟩ := hstrongW
      exact orthogonal_sections_critical_line_contradiction τ W m.J
        (OffenderModels.conjugateMarking eH g) m.model (Or.inl m.quotient_natural)
        (Source.starImage H (c.Ugamma V₃)) m.actor_marking
        (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))) (s.image (c.Aone V₁))
        hD hSdim hdisp
    · obtain ⟨_, _, _, _, _, g, ⟨t⟩⟩ := hrank
      obtain ⟨hDi, hCi⟩ := d.critical_indices W hw.maximal t.rank_one hw.component_moves
      have hr := rank_one_transport s W (c.Ugamma V₃) c.Vgamma (c.Aone V₁)
        hUγ hUV d.critical_line_normalized d.critical_line_card
        hw.submodule_faithful hw.faithful t.rank_one (d.larger_rank hnt) hDi hCi
        d.centralizer_commutator
      exact rank_one_orthogonal_contradiction τ W t.J
        (OffenderModels.conjugateMarking eH g) t.model (Or.inl t.quotient_natural)
        hr.submodule_faithful hr.quotient_faithful
        (Source.starImage H (c.Ugamma V₃)) (Source.starImage H c.Vgamma)
        hr.actor_ne_bot hr.actor_lt t.actor_marking hr.fixedCodim_eq_two.le
        (s.image (c.Aone V₁)) hr.line_atom hr.displacements

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.SourceReduction

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.SourceReduction
open Subgroup Chapter1 Chapter1.Section02.LocalModels Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open FourStructure.ChiefFactors
open CriticalGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Earlier source data on the actual U_H/V₁ and actual critical pair.
No quotient recognition or desired group conclusion is a field. -/
structure LocalModuleData (L T H V K L₁ G₁ M V₃ V₁ : Subgroup G) where
  denominator_normal : (V₁.subgroupOf (Source.UH H V₃)).Normal
  elementary : letI := denominator_normal; IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)
  pair : CriticalPair L T H V
  representation : letI := denominator_normal; letI := elementary
    Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁)
  earlier : letI := denominator_normal; letI := elementary
    ModuleFacts pair K L₁ G₁ M V₃ V₁ representation

/-- Uniform group reduction before the C-component enlargement. Both cases
of 13.8.8 survive until the marked S₈ action excludes the transvection case;
the other case is eliminated by the actual module/critical-pair argument. -/
theorem binary_reduction
    (L L₁ V V₁ V₃ G₁ M : Subgroup G) (T : Sylow 2 G)
    (groups : GroupFacts L L₁ (T : Subgroup G) V V₁ V₃ G₁ M)
    (modules : ∀ (J C : Subgroup G), J ∈ Source.Hz L₁ (T : Subgroup G) G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent → Nonempty (LocalModuleData L T J V C L₁ G₁ M V₃ V₁))
    {H K : Subgroup G} {n : ℕ}
    (hH : H ∈ Source.Hz L₁ (T : Subgroup G) G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (e : (K ⧸ pCore 2 K) ≃* PSL n) :
    n = 4 ∧ SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
      Nonempty (Source.Hstar H ≃* PSL 4) := by
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hH.1.2
  have hT : IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype hTH, by simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]⟩
  obtain ⟨hn, halt⟩ := Parabolics.source_parabolic_reduction H K L L₁ (T : Subgroup G)
    V V₁ V₃ G₁ M groups.local_definition groups.local_action hH groups.base_le_M hKH hK
    (groups.component_normal hH hKH hK) hT (groups.supplement hH hKH hK).symm
    (groups.theta H hH) (groups.local_normal H hH) groups.covered_factor
    groups.covered_normalizer groups.solvable_overgroups
    (fun J C hJ hCJ hC => groups.base_le_component hJ hCJ hC) groups.three_automorphisms
    hn₀ hn₁ e
  refine ⟨hn, ?_⟩
  rcases halt with ⟨hc, he, _⟩ | ⟨_, hm⟩
  · exact ⟨hc, he⟩
  · obtain ⟨d⟩ := modules H K hH hKH hK
    let := d.denominator_normal
    let := d.elementary
    have hp : IsPGroup 2 (Source.starImage H (T : Subgroup G)) :=
      (T.isPGroup'.comap_subtype).map _
    exact (exclude_middle_node d.earlier hH hKH hK (groups.base_le_component hH hKH hK)
      hp (hn ▸ e) hm).elim

/-- Conditional group and parabolic conclusion of 13.8.25. The uniform
binary reduction required by the genuine 1.2.4 overgroup argument is proved
here. The A₇ exclusion is the independent preceding 13.8.24 input. -/
theorem source_linear_reduction
    (L L₁ V V₁ V₃ G₁ M : Subgroup G) (T : Sylow 2 G)
    (groups : GroupFacts L L₁ (T : Subgroup G) V V₁ V₃ G₁ M)
    (modules : ∀ (J C : Subgroup G), J ∈ Source.Hz L₁ (T : Subgroup G) G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent → Nonempty (LocalModuleData L T J V C L₁ G₁ M V₃ V₁))
    {𝒦 : GroupClass.{u}} (embeddings : Overgroup.EarlierEmbeddings 𝒦)
    (hQ : IsSQTK 𝒦 (G₁ ⧸ pCore 2 G₁))
    (hA7 : ∀ {J C : Subgroup G}, J ∈ Source.Hz L₁ (T : Subgroup G) G₁ M → C ≤ J →
      (C.subgroupOf J).IsCComponent → ¬ IsAlternating (C ⧸ pCore 2 C) 7)
    (hV₁ : V₁ ≠ ⊥) (hp : IsPGroup 2 V₁) (hV₁base : V₁ ≤ L₁ ⊔ (T : Subgroup G))
    (hV₁n : G₁ ≤ normalizer (V₁ : Set G))
    {H K : Subgroup G} {n : ℕ}
    (hH : H ∈ Source.Hz L₁ (T : Subgroup G) G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hn₀ : 3 ≤ n) (hn₁ : n ≤ 5)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) :
    n = 4 ∧ IsAlternatingCover (L ⧸ pCore 2 L) 6 ∧
      Nonempty (Source.Hstar H ≃* PSL 4) ∧ H = G₁ := by
  obtain ⟨e⟩ := binary_model hmodel
  obtain ⟨hn, hc, he⟩ := binary_reduction L L₁ V V₁ V₃ G₁ M T groups modules
    hH hKH hK hn₀ hn₁ e
  have uniform : Overgroup.UniformComponentFacts L L₁ (T : Subgroup G) G₁ M := {
    base_le := groups.base_le_component
    componentList := groups.component_list
    join_eq := groups.supplement
    normal := groups.component_normal
    not_A7 := hA7
    binaryReduction := by
      intro J C m hJ hCJ hC hm₀ hm₁ hmodel
      obtain ⟨eC⟩ := binary_model hmodel
      obtain ⟨hm, hcover, ⟨eJ⟩⟩ := binary_reduction L L₁ V V₁ V₃ G₁ M T groups modules
        hJ hCJ hC hm₀ hm₁ eC
      exact ⟨hm, triple_cover hcover, ⟨ZMod 2, inferInstance, inferInstance,
        Nat.card_zmod 2, ⟨eJ⟩⟩⟩ }
  exact ⟨hn, triple_cover hc, he, Overgroup.eq_overgroup_of_uniform_linear_reduction
    embeddings uniform hH hKH hK (hn ▸ hmodel) hV₁ hp hV₁base hV₁n hQ⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.SourceReduction
