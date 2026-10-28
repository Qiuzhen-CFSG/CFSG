module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.Product
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.BinaryThree
public import Theory.Representation.SLHigherNaturalFirstCohomology
public import Theory.Representation.BinarySylowFixedSpace

/-!
# Fixed supplements in the four component branches of B.5.10

Here W is literally [V,L]. Odd Sylow-coset averaging proves the SL2
supplement. Restriction to L transports the actual chosen offender to an
FF-module, so the checked doubled-SL3 and binary central-attachment results
exclude nonsplitting for the doubled module and the four-dimensional cover.
The latter cover has a fixed line below a natural quotient; it is never
identified with the distinct extension above a natural module.

For natural SL3, the connecting map injects V/(W + C_V(L)) into H1(L,W).
The proved cohomology calculation forces the binary field and quotient
dimension exactly one when the supplement fails. The exceptional action
uses an actual field isomorphism and compatible group and vector maps.
No universal earlier-source implication remains a premise of these results.

The marked S5 branch and action-image offender localization are separate
obligations. These lemmas do not assert the complete B.5.10 product.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.10,
printed pp.108–109, citing A.1.39, B.4.8 and I.1.6(4). The intrinsic binary
extension results are reused through ExtensionConsequences.BinaryThree.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open Representation.OneCohomology
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.ProductGeometry
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

noncomputable def restrictedSpace {L : Subgroup G} (s : MovedSection ρ L) :
    Subrepresentation (ρ.comp L.subtype) where
  toSubmodule := s.space.toSubmodule
  apply_mem_toSubmodule g := s.space.apply_mem_toSubmodule g

theorem restrictedSpace_trivialQuotient {L : Subgroup G} (s : MovedSection ρ L) :
    HasTrivialQuotient (restrictedSpace s) := by
  intro g v
  change ρ g v - v ∈ s.space.toSubmodule
  rw [s.space_eq]
  exact Submodule.subset_span ⟨g, g.property, v, Submodule.mem_top, rfl⟩

noncomputable def restrictMovedSection {L : Subgroup G} (s : MovedSection ρ L) :
    MovedSection (ρ.comp L.subtype) ⊤ where
  space := restrictedSpace s
  space_eq := by
    change s.space.toSubmodule = moved (ρ.comp L.subtype) ⊤
    rw [s.space_eq]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      exact Submodule.subset_span ⟨(⟨g, hg⟩ : L), Subgroup.mem_top _, v, hv, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨g, _, v, hv, rfl⟩
      exact Submodule.subset_span ⟨g, g.property, v, hv, rfl⟩
  central :=
    { toSubmodule := s.central.toSubmodule
      apply_mem_toSubmodule g := s.central.apply_mem_toSubmodule g }
  central_eq := by
    ext v
    change v ∈ s.central.toSubmodule ↔ _
    rw [s.central_eq]
    exact ⟨fun h g => h g, fun h g => h ⟨g, Subgroup.mem_top _⟩⟩

theorem restriction_isFF [Module.Finite (ZMod 2) V] {A L : Subgroup G}
    (hA : IsBestOffender ρ A) (hAL : A ≤ L) : IsFFModule (ρ.comp L.subtype) :=
  ⟨A.subgroupOf L, (hA.subgroupOf ρ hAL).isOffender _⟩

theorem sylow_supplement [Finite G] {A L : Subgroup G} (s : MovedSection ρ L)
    (hsyl : ∃ T : Sylow 2 L, A = (T : Subgroup L).map L.subtype)
    (hs : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    s.space.toSubmodule ⊔ fixedSpace ρ L = ⊤ := by
  obtain ⟨T, hT⟩ := hsyl
  apply top_unique
  rw [← hs]
  refine sup_le le_sup_left ?_
  intro v hv
  have ht : v ∈ fixedSpace (ρ.comp L.subtype) (T : Subgroup L) := by
    rwa [fixedSpace_comp_map, ← hT]
  obtain ⟨w, hw, hvw⟩ := BinarySylowFixedSpace.fixed_lift_mod_trivial_quotient
    (ρ.comp L.subtype) T s.space.toSubmodule (restrictedSpace_trivialQuotient s) v ht
  exact Submodule.mem_sup.mpr ⟨v - w, hvw, w, hw, sub_add_cancel v w⟩

theorem doubleThree_supplement [Module.Finite (ZMod 2) V]
    {A L : Subgroup G} (s : MovedSection ρ L) (F : BinaryField)
    (hA : IsBestOffender ρ A) (hAL : A ≤ L)
    (hn : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) F 3 2) :
    s.space.toSubmodule ⊔ fixedSpace ρ L = ⊤ := by
  obtain ⟨e⟩ := hn
  let e' : ActionEquiv
      ((restrictMovedSection s).space.toRepresentation.comp (⊤ : Subgroup L).subtype)
      (repeated (linearNatural F 3) 2) :=
    ⟨Subgroup.topEquiv.trans e.groupEquiv, e.linearEquiv,
      fun g v => e.intertwines g v⟩
  exact codisjoint_iff.mp (doubleThree_isCompl (restrictMovedSection s) F rfl
    (restriction_isFF hA hAL) e').codisjoint

theorem fourCover_supplement [Module.Finite (ZMod 2) V]
    {A L : Subgroup G} (s : MovedSection ρ L) (hfaith : Function.Injective ρ)
    (hA : IsBestOffender ρ A) (hAL : A ≤ L)
    (cover : FourDimensionalCoverSource (s.space.toRepresentation.comp L.subtype)) :
    s.space.toSubmodule ⊔ fixedSpace ρ L = ⊤ := by
  by_contra hns
  have hk := binary_fixed_kernel_of_no_supplement (restrictMovedSection s)
    cover.natural.groupEquiv (hfaith.comp L.subtype_injective)
    (restriction_isFF hA hAL) hns
  have hc : Representation.invariants (s.space.toRepresentation.comp L.subtype) = ⊥ := by
    apply bot_unique
    intro v hv
    have hx : (v : V) ∈ s.space.toSubmodule ⊓ fixedSpace ρ L :=
      ⟨v.property, fun g => congrArg Subtype.val (hv g)⟩
    change (v : V) ∈ (restrictMovedSection s).space.toSubmodule ⊓
      Representation.invariants (ρ.comp L.subtype) at hx
    rw [hk] at hx
    exact Subtype.ext hx
  have hd : Module.finrank (ZMod 2)
      (s.space.toSubmodule ⧸ Representation.invariants (s.space.toRepresentation.comp L.subtype)) = 3 :=
    cover.natural.linearEquiv.finrank_eq.trans (by
      change Module.finrank (ZMod 2) (Fin 3 → ZMod 2) = 3
      simp)
  have hr := (Representation.invariants (s.space.toRepresentation.comp L.subtype)).finrank_quotient_add_finrank
  have hz : Module.finrank (ZMod 2)
      (Representation.invariants (s.space.toRepresentation.comp L.subtype)) = 0 := by rw [hc]; simp
  rw [hd, hz, cover.dimension] at hr
  omega

theorem supplement_quotient_finrank_le [Finite G] [Module.Finite (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) :
    Module.finrank (ZMod 2) (V ⧸ (s.space.toSubmodule ⊔ fixedSpace ρ L)) ≤
      Module.finrank (ZMod 2) (H1 (s.space.toRepresentation.comp L.subtype)) := by
  let f := extensionClass (restrictedSpace s) (restrictedSpace_trivialQuotient s)
  have hk : f.ker = s.space.toSubmodule ⊔ fixedSpace ρ L :=
    ker_extensionClass (restrictedSpace s) (restrictedSpace_trivialQuotient s)
  rw [← hk, f.quotKerEquivRange.finrank_eq]
  exact f.range.finrank_le

theorem naturalThree_supplement_or_exceptional [Finite G] [Module.Finite (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (F : BinaryField)
    (hn : IsLinearNatural (s.space.toRepresentation.comp L.subtype) F 3) :
    s.space.toSubmodule ⊔ fixedSpace ρ L = ⊤ ∨ IsExceptional ρ L s.space := by
  classical
  obtain ⟨e⟩ := hn
  have he := (H1Congr _ _ e.groupEquiv e.linearEquiv e.intertwines).finrank_eq
  have hb := supplement_quotient_finrank_le s
  rw [he, linearNatural, SLHigherNatural.finrank_restrict_sl3_of_card_pow F.degree F.card_eq] at hb
  by_cases hs : s.space.toSubmodule ⊔ fixedSpace ρ L = ⊤
  · exact Or.inl hs
  have hnz : Module.finrank (ZMod 2) (V ⧸ (s.space.toSubmodule ⊔ fixedSpace ρ L)) ≠ 0 := by
    intro hz
    apply hs
    exact Submodule.Quotient.subsingleton_iff.mp ((Module.finrank_zero_iff).mp hz)
  have hF : F.degree = 1 := by
    by_contra hF
    rw [if_neg hF] at hb
    exact hnz (Nat.eq_zero_of_le_zero hb)
  have hdim : Module.finrank (ZMod 2) (V ⧸ (s.space.toSubmodule ⊔ fixedSpace ρ L)) = 1 := by
    rw [if_pos hF] at hb
    omega
  let q := degreeOneNaturalEquiv F hF 3
  refine Or.inr ⟨⟨⟨e.groupEquiv.trans q.groupEquiv,
    e.linearEquiv.trans q.linearEquiv, ?_⟩⟩, hdim⟩
  intro g v
  exact (congrArg q.linearEquiv (e.intertwines g v)).trans
    (q.intertwines (e.groupEquiv g) (e.linearEquiv v))

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.ProductGeometry
