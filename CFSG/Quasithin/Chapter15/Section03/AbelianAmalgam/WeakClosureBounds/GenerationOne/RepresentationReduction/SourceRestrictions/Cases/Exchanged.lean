module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.GroupGeometry
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.LocalComparison

/-!
# Conditional exchanged-component deduction on the literal local quotient

The model comparisons exclude A₅, L₃(2), and the even-exponent orthogonal
SL₂ constituent against E.2.2's actual exchanged models. The last exclusion
first proves equality of defining-field cardinalities. The orbit transport
recovers I_T = I + I^t and literal cross-centralization from the corresponding
F.9.18 image clauses. The specialization below lifts the exchanging element
from H/O₂(H) to an actual element of T outside N_T(K), on U/Z with
U = conjugateSpanBy ZS H. Its action remains the supplied faithful
`LocalQuotientAction`, and its homogeneous section is for K₀.

The complete conditional deduction now starts from all five F.9.18(5)
rows, including the four-copy L₃(2) centralizer-action clause. It constructs
compatible natural pair coordinates and both Borel markings, or identifies
I_T itself with the actual OmegaPlus natural module. The local specialization
uses E.2.2(1)'s J=O₂(H) to identify the actual component and overlap maps,
and returns an exchanger in the original T outside N_T(K).

Earlier inputs remain explicit: the complete F.9.18(5) output, the genuine
E.2.2 exchanged model/clauses, f>1 and Odd f, the finite faithful local
action, the K₀-homogeneous Irr⁺ section, and the component/overlap group
geometry in ExchangedGeometry. GroupGeometry derives the return condition
from an index-two normalizer and identifies K₀ with the T-conjugate span.
The source owner must still establish that group geometry in its local
setup. Neither fixation nor FF exclusions are assumed. Relative subnormality
identifies K/O₂(K) and K₀/O₂(K₀) with their literal action images; the
exported model equivalences then use the same module actor maps.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.65,
printed p.1152; F.9.18(5), pp.325--326; E.2.2, pp.215--216;
and A.1.40--42, pp.31--32.
-/

@[expose] public section
open Representation Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged

section Local
variable {G : Type*} [Group G] {H K K₀ T Z ZS : Subgroup G}

/-- A moved component in the quotient has an actual exchanger in the
original T. Normalization in G would imply normalization of its image. -/
theorem lift_exchanger (hKH : K ≤ H) {t : H ⧸ pCore 2 H}
    (ht : t ∈ actorImage H T)
    (hne : t ∉ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) :
    ∃ s : H, (s : G) ∈ T ∧ (s : G) ∉ normalizer (K : Set G) ∧
      QuotientGroup.mk' (pCore 2 H) s = t := by
  obtain ⟨s, hs, he⟩ := ht
  refine ⟨s, hs, ?_, he⟩
  intro hn
  apply hne
  rw [← he]
  apply (K.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H))
  apply Subgroup.mem_map_of_mem
  rw [← subgroupOf_normalizer_eq hKH]
  exact hn

variable [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]

/-- Literal local specialization of the source-image transport. The
complete restriction alternatives must supply its three image/centralizer
clauses. In particular hpair concerns I_H, not a silently identified I_T. -/
theorem local_pair_of_source_images
    (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z) (hKH : K ≤ H)
    (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy ZS H) ⧸
      Z.subgroupOf (conjugateSpanBy ZS H))))
    (hI : IsIrrPlusWith a.representation (actorImage H K₀) (actorImage H T) I)
    (hK : actorImage H K₀ ≤ normalizer (actorImage H K : Set (H ⧸ pCore 2 H)))
    {t : H ⧸ pCore 2 H} (ht : t ∈ actorImage H T)
    (hne : actorImage H K ≠ (actorImage H K).conjBy t⁻¹)
    (hpair : (orbitSpan a.representation ⊤ I).map
        (fixedSpace a.representation (actorImage H K₀)).mkQ =
      (I ⊔ rightConjugate a.representation I t).map
        (fixedSpace a.representation (actorImage H K₀)).mkQ)
    (hfirst : I.map (fixedSpace a.representation (actorImage H K₀)).mkQ ≤
      (subspaceCommutator a.representation (orbitSpan a.representation ⊤ I)
        (actorImage H K)).map (fixedSpace a.representation (actorImage H K₀)).mkQ)
    (hcentralizer : subspaceCommutator a.representation
        (orbitSpan a.representation ⊤ I) (actorImage H K) =
      orbitSpan a.representation ⊤ I ⊓
        fixedSpace a.representation ((actorImage H K).conjBy t⁻¹)) :
    ∃ s : H, (s : G) ∈ T ∧ (s : G) ∉ normalizer (K : Set G) ∧
      QuotientGroup.mk' (pCore 2 H) s = t ∧
      orbitSpan a.representation (actorImage H T) I =
        I ⊔ rightConjugate a.representation I (QuotientGroup.mk' (pCore 2 H) s) ∧
      subspaceCommutator a.representation I
        ((actorImage H K).conjBy (QuotientGroup.mk' (pCore 2 H) s)⁻¹) = ⊥ := by
  obtain ⟨_, hout, hsum, hcross⟩ := literal_pair_of_source_images a.representation
    hI le_top le_top hK ht hne hpair hfirst hcentralizer
  obtain ⟨s, hs, hn, he⟩ := lift_exchanger hKH ht hout
  exact ⟨s, hs, hn, he, he ▸ hsum, he ▸ hcross⟩

end Local

section LocalAssembly
open RemainingModels BorelReduction BorelReduction.SourceCases
open Representation Representation.BinaryOffender Matrix
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G] {H M K K₀ T Z ZS : Subgroup G}
  [IsElementaryAbelian 2 (conjugateSpanBy ZS H)]
  (a : LocalQuotientAction H (conjugateSpanBy ZS H) Z)
  {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy ZS H) ⧸
    Z.subgroupOf (conjugateSpanBy ZS H)))}
  (hi : IsIrrPlusWith a.representation (actorImage H K₀) (actorImage H T) I)

/-- The natural pair on the literal U/Z, together with an actual element
of T outside N_T(K), not only an element of H/O₂(H). -/
structure LocalNaturalPair {E X : Type*} [Group E] [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) E X) (B' : Subgroup E) where
  marked : MarkedPair a.representation (actorImage H K) (actorImage H K₀)
    (actorImage H T) (actorImage H (M ⊓ K₀)) I hi.invariant σ B'
  element : H
  mem_T : (element : G) ∈ T
  outside : (element : G) ∉ normalizer (K : Set G)
  quotient_element : QuotientGroup.mk' (pCore 2 H) element = marked.element

namespace LocalNaturalPair
variable {a hi} {E X : Type*} [Group E] [AddCommGroup X] [Module (ZMod 2) X]
  {σ : Representation (ZMod 2) E X} {B' : Subgroup E}
  (d : LocalNaturalPair (K := K) (M := M) a hi σ B')

omit [Finite G] in
/-- The source right-conjugating element occurs literally in the sum and
cross-centralization statements, on the exact local quotient action. -/
theorem literal_identities :
    orbitSpan a.representation (actorImage H T) I =
      I ⊔ rightConjugate a.representation I (QuotientGroup.mk' (pCore 2 H) d.element) ∧
    subspaceCommutator a.representation I
      ((actorImage H K).conjBy (QuotientGroup.mk' (pCore 2 H) d.element)⁻¹) = ⊥ := by
  rw [d.quotient_element]
  exact ⟨d.marked.orbit, d.marked.cross⟩

/-- The same module map identifies the intrinsic component quotient with
the actual natural-module group. Relative subnormality supplies the kernel comparison. -/
noncomputable def componentModel (hKH : K ≤ H) (hsub : (K.subgroupOf H).IsSubnormal) :
    (K ⧸ pCore 2 K) ≃* E :=
  (intrinsicCoreActorEquiv hKH hsub).trans d.marked.first.groupEquiv

end LocalNaturalPair

/-- The local alternatives with actual exchangers, natural constituent
identities and literal orthogonal T-orbit identities. -/
inductive LocalConclusion (f : ℕ) : Prop
  | linear (F : Type) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
      (card : Nat.card F = 2 ^ f)
      (pair : LocalNaturalPair (K := K) (M := M) a hi
        (restrictScalars (specialLinearNatural (k := F) 2)) (SpecialLinearGroup.rankOneBorel F))
  | suzuki (m : ℕ) (positive : 0 < m) (exponent : f = 2 * m + 1)
      (pair : LocalNaturalPair (K := K) (M := M) a hi (suzukiNatural m)
        (BenderSuzuki.MatrixGroups.SuzukiBorelSubgroup m))
  | orthogonal (F : Type) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
      (card : Nat.card F = 2 ^ f)
      (identification : MarkedOrthogonal a.representation (F := F) (actorImage H K₀)
        (actorImage H T) (actorImage H (M ⊓ K₀)) I
        (orbitSpan_component_invariant a.representation hi.normalizes hi.isIrrPlus))

/-- Exact specialization of the conditional exchanged deduction. The module
is U/Z with U=conjugateSpanBy ZS H, and faithfulness comes from a.
The source kernel and component-overlap comparisons are constructed from
E.2.2(1)'s kernel equality. The only remaining extra group premises are
the explicit pair/overlap geometry; the full F.9.18(5) output and the
homogeneous section remain earlier source inputs. -/
theorem local_exchanged_cases_of_full_five {f : ℕ}
    (hKH : K ≤ H) (source : ExchangedModel H M K f)
    (clauses : ExchangedClauses H M K T) (hf : 1 < f) (ho : Odd f)
    (geo : ExchangedGeometry (actorImage H K) (actorImage H K₀) (actorImage H T)
      (actorImage H (M ⊓ K₀)) (actorImage H (M ⊓ K)))
    (full : FullFiveConclusion a.representation (actorImage H K) (actorImage H K₀)
      (actorImage H T) geo.component_le I hi.invariant) :
    LocalConclusion (K := K) (M := M) a hi f := by
  have h := exchanged_cases_of_full_five a.representation hi a.faithful source hf ho geo
    (localComponentToSource clauses.kernel_eq)
    (localComponentToSource_overlap clauses.kernel_eq) full
  cases h with
  | linear F hF d =>
    obtain ⟨s, hs, hout, he⟩ := lift_exchanger hKH d.mem_T d.outside
    exact .linear F hF ⟨d, s, hs, hout, he⟩
  | suzuki m hm he d =>
    obtain ⟨s, hs, hout, hs'⟩ := lift_exchanger hKH d.mem_T d.outside
    exact .suzuki m hm he ⟨d, s, hs, hout, hs'⟩
  | orthogonal F hF d => exact .orthogonal F hF d

omit [Finite G] in
/-- The local result feeds the original Borel fixed-space calculation on
the literal I_T, with no new classification or fixation premise. -/
theorem LocalConclusion.fixedSpace_le {f : ℕ} (hf : 1 < f)
    (h : LocalConclusion (K := K) (M := M) a hi f) :
    orbitSpan a.representation (actorImage H T) I ⊓
      fixedSpace a.representation (actorImage H (M ⊓ K₀)) ≤
        fixedSpace a.representation (actorImage H K₀) := by
  apply MarkedConclusion.fixedSpace_le a.representation hi hf
  cases h with
  | linear F hF d => exact .linear F hF d.marked
  | suzuki m hm he d => exact .suzuki m hm he d.marked
  | orthogonal F hF d => exact .orthogonal F hF d

/-- In the orthogonal branch the very same actor map identifies K₀/O₂(K₀)
with the actual OmegaPlus group, not a family label or a further quotient. -/
noncomputable def localOrthogonalGroupEquiv {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (hK₀H : K₀ ≤ H) (hsub : (K₀.subgroupOf H).IsSubnormal)
    (d : MarkedOrthogonal a.representation (F := F) (actorImage H K₀)
      (actorImage H T) (actorImage H (M ⊓ K₀)) I
      (orbitSpan_component_invariant a.representation hi.normalizes hi.isIrrPlus)) :
    (K₀ ⧸ pCore 2 K₀) ≃* ClassicalOrthogonal.OmegaPlus 2 F :=
  (intrinsicCoreActorEquiv hK₀H hsub).trans d.identification.groupEquiv

end LocalAssembly
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged
