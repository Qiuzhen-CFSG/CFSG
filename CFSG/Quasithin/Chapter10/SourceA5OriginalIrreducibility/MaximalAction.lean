module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalIrreducibility.Minimality
public import CFSG.Quasithin.Chapter3.Section02.ModuleConsequences
public import Theory.Representation.BinaryConjugationSection.Irreducible
/-!
# The minimal full central quotient is irreducible for M

Every M-invariant subgroup of the full module is either the whole module
or is centralized by L₀. Indeed, if L moves it the strong reselection
minimality theorem applies, and otherwise T-invariance transports the
centralization to every conjugate of L. Pulling invariant vector subspaces
back through the literal quotient map proves M-irreducibility of
V_M/C_{V_M}(L₀). The source3.2.2 action remains semisimple for L₀.

This is an M-action statement; it does not infer irreducibility for L₀ or L.
Source: Aschbacher–Smith,D.3.21 and3.2.6, printed pp.204–207 and581.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem source_minimal_uniqueness (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
    D.simpleQTKE T D.maximal

local instance fullElementary (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    IsElementaryAbelian 2 D.fullModule := D.fullModule_elementary (source_minimal_uniqueness D)

/-- Subgroup minimality modulo the original L₀-fixed subgroup. -/
theorem source_minimal_fullModule_eq_or_le_centralizer
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hD : D.IsMinimalFullModule)
    (U : Subgroup G) (hU : D.maximalLocal ≤ normalizer (U : Set G))
    (hUD : U ≤ D.fullModule) :
    U = D.fullModule ∨ U ≤ centralizer (localOrbit T L : Set G) := by
  by_cases hm : ⁅U,L⁆ = ⊥
  · right
    apply le_centralizer_iff.mpr
    apply iSup_conjugates_le_of_le_normalizer
    · exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hm)
    · exact ((le_normalizer_componentOrbit L T).trans hU).trans
        (normalizer_le_normalizer_centralizer U)
  · exact Or.inl (source_minimal_fullModule_eq_of_normal_moved D hD U hU hUD hm)

/-- Any action with the literal original conjugation coordinates is M-irreducible. -/
theorem source_minimal_full_quotient_irreducible
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hD : D.IsMinimalFullModule)
    (σ : Representation (ZMod 2) D.maximalLocal (Additive D.fullCentralQuotient))
    (hσ : ∀ (g : D.maximalLocal) (v : D.fullModule),
      σ g (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
        Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
          ⟨(g : G) * (v : G) * (g : G)⁻¹,
            (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule g.property) v).mp
              v.property⟩)) : σ.IsIrreducible := by
  have hn : D.fullCentralizer ≠ ⊤ := by
    intro h
    have hf : D.fullModule ≤ centralizer (localOrbit T L : Set G) := by
      intro v hv
      exact (show (⟨v,hv⟩ : D.fullModule) ∈ D.fullCentralizer from h.symm ▸ mem_top _)
    have hb : D.fullModule = ⊥ := (D.fullModule_eq_commutator
      (source_minimal_uniqueness D)).trans (commutator_eq_bot_iff_le_centralizer.mpr hf)
    exact D.module_ne_bot (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans_eq hb))
  let : Nontrivial D.fullCentralQuotient := QuotientGroup.nontrivial_iff.mpr hn
  let c : BinaryConjugationSection D.maximalLocal D.fullModule
      (D.fullModule ⊓ centralizer (localOrbit T L : Set G)) σ := {
    section_le := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
    kernel_le := inf_le_left
    normalized := D.maximalLocal_normalizes_fullModule
    coordinates := {
      toFun v := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v))
      map_one' := (QuotientGroup.mk' D.fullCentralizer).map_one
      map_mul' := (QuotientGroup.mk' D.fullCentralizer).map_mul }
    onto := QuotientGroup.mk'_surjective _
    kernel_eq := by
      ext x
      change QuotientGroup.mk' D.fullCentralizer x = 1 ↔
        (x : G) ∈ D.fullModule ⊓ centralizer (localOrbit T L : Set G)
      exact (QuotientGroup.eq_one_iff x).trans (and_iff_right x.property).symm
    equivariant := fun g v => (hσ g v).symm }
  apply c.irreducible_of_subgroup_minimal
  intro U hUD hU
  rcases source_minimal_fullModule_eq_or_le_centralizer D hD U hU hUD with h | h
  · exact Or.inl h
  · exact Or.inr (le_inf hUD h)

/-- The chosen source action is irreducible for M and semisimple for L₀. -/
theorem source_minimal_full_quotient_action
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hD : D.IsMinimalFullModule) :
    ∃ σ : Representation (ZMod 2) D.maximalLocal (Additive D.fullCentralQuotient),
      σ.IsIrreducible ∧
      IsSemisimpleRepresentation
        (σ.comp ((localOrbit T L).subgroupOf D.maximalLocal).subtype) ∧
      (∀ (g : D.maximalLocal) (v : D.fullModule),
        σ g (Additive.ofMul (QuotientGroup.mk' D.fullCentralizer v)) =
          Additive.ofMul (QuotientGroup.mk' D.fullCentralizer
            ⟨(g : G) * (v : G) * (g : G)⁻¹,
              (mem_normalizer_iff.mp (D.maximalLocal_normalizes_fullModule g.property) v).mp
                v.property⟩)) := by
  obtain ⟨σ,hs,_,hσ⟩ := D.fullModule_quotient_consequences (source_minimal_uniqueness D)
  exact ⟨σ,source_minimal_full_quotient_irreducible D hD σ hσ,hs,hσ⟩

end CFSG.Quasithin.Chapter10
