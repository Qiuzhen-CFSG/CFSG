module
public import CFSG.Quasithin.ChapterG.Section06.IrreducibleCentral
public import Theory.Representation.CubicClifford.IndexTwoDisplacement
public import Theory.Representation.CubicClifford.IndexTwoExchange
public import Theory.Representation.BinaryOffender.ActionImage

/-!
# The central rank-two involution on an index-two restriction

Clifford theory gives an irreducible restriction or two simple constituents
exchanged by the specified ambient element. Centrality makes the two
displacement ranks equal, so rank two becomes rank one on each constituent.
Pass to its literal faithful action image before applying G.6.4; the original
normalizer supplies the SQTK cover and its Sylow subgroup supplies the marked
central involution. Both the constituent and the actual exchange are retained.

This reduction is applied to the partner chief section by PairSource. It does
not assert that the normalizer restriction is reducible, or identify the two
component actions with the binary three-dimensional natural actions. Those
remaining recognition steps and the full assembly belong to
qt-e-152-critical-pair.
Source: Aschbacher–Smith 15.2.27(2), printed p.1119; G.6.4, pp.345–346;
Clifford theory, Isaacs, Theorem 6.5.
-/

public section
open Subgroup Representation
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition
universe u
variable {G W : Type u} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- The full action of the stabilizer on both exchanged constituents, with
its faithful image classified at the same central involution. -/
structure ExchangedCentralConstituents (ρ : Representation (ZMod 2) G W)
    (I : Subgroup G) [I.Normal] (t : G) (a : I) where
  constituent : Subrepresentation (ρ.comp I.subtype)
  irreducible : IsIrreducible constituent.toRepresentation
  complementary : IsCompl constituent.toSubmodule
    (constituent.toSubmodule.map (ρ t⁻¹))
  exchange : constituent.toSubmodule.map (ρ t) = constituent.toSubmodule.map (ρ t⁻¹) ∧
    (constituent.toSubmodule.map (ρ t⁻¹)).map (ρ t) = constituent.toSubmodule
  coordinates : Representation.Equiv (ρ.comp I.subtype)
    (constituent.toRepresentation.prod
      (conjugateRep constituent.toRepresentation t))
  displacement : Module.finrank (ZMod 2)
    (LinearMap.range (constituent.toRepresentation a - 1)) = 1
  model : ChapterG.Section06.CentralModel (imageRepresentation constituent.toRepresentation)

/-- Rank-two displacement at a central Sylow involution becomes rank one on
both exchanged constituents of an index-two restriction. G.6.4 recognizes
the faithful image of the same constituent, without assuming its kernel. -/
theorem central_rank_two_restriction
    (ρ : Representation (ZMod 2) G W) [IsIrreducible ρ]
    (hsq : IsSQTK KnownSimple.IsKnownSimple G)
    (I : Subgroup G) [I.Normal] (hi : I.index = 2)
    (t : G) (htI : t ∉ I) (S : Sylow 2 G) (htS : t ∈ S)
    (a : I) (haS : (a : G) ∈ S) (ho : orderOf a = 2)
    (hc : ∀ s ∈ S, Commute (a : G) s)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ (a : G) - 1)) = 2) :
    IsIrreducible (ρ.comp I.subtype) ∨
      Nonempty (ExchangedCentralConstituents ρ I t a) := by
  by_cases hirr : IsIrreducible (ρ.comp I.subtype)
  · exact Or.inl hirr
  right
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨C,hC⟩ := Subrepresentation.irreducible_subrepresentation_of_finite_dimensional
    (ρ.comp I.subtype)
  let : IsIrreducible C.toRepresentation := hC
  obtain ⟨hd,⟨e⟩⟩ := (CubicClifford.Inertia.restriction_dichotomy ρ I hi t htI C hC).resolve_left hirr
  have hrC := CubicClifford.Inertia.constituent_rank_one_of_rank_two ρ I C t a
    (hc t htS).symm e hr
  let τ := C.toRepresentation
  let q := actionHom τ
  let σ := imageRepresentation τ
  have hq : Function.Surjective q := τ.asGroupHom.rangeRestrict_surjective
  let : IsIrreducible σ := (irreducible_comp_surjective_iff q hq σ).mp hC
  have hf := imageRepresentation_injective τ
  have hk : pCore 2 (actionImage τ) = ⊥ := by
    have hle := normal_p_subgroup_le_ker σ (pCore 2 _) pCore_isPGroup
    rw [(MonoidHom.ker_eq_bot_iff σ).mpr hf] at hle
    exact bot_unique hle
  have hqa2 : (q a) ^ 2 = 1 := by
    rw [←map_pow,show a ^ 2 = 1 by simpa only [ho] using pow_orderOf_eq_one a,map_one]
  have hqa : q a ≠ 1 := by
    intro he
    have hh : τ a = 1 := by
      change σ (q a) = 1
      rw [he,map_one]
    rw [hh,sub_self,LinearMap.range_zero,finrank_bot] at hrC
    contradiction
  have hG := ChapterG.Section06.hypotheses_of_irreducible σ q (hsq.subgroup I)
    hq hk hf (q a) hqa2 hqa (by
      change Module.finrank (ZMod 2) (LinearMap.range (τ a - 1)) ≤ 2
      exact hrC.le.trans (by decide : (1 : ℕ) ≤ 2))
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal I
  have haP : a ∈ P := by
    change a ∈ (P : Subgroup I)
    rw [hP]
    exact haS
  let Q := P.mapSurjective (f := q) hq
  have hcent : q a ∈ (center Q).map (Q : Subgroup (actionImage τ)).subtype := by
    refine ⟨⟨q a,mem_map_of_mem q haP⟩,mem_center_iff.mpr ?_,rfl⟩
    rintro ⟨s,hs⟩
    obtain ⟨b,hb,rfl⟩ := hs
    have hbS : (b : G) ∈ S := by
      change b ∈ (P : Subgroup I) at hb
      rw [hP] at hb
      exact hb
    exact Subtype.ext (((show Commute a b from Subtype.ext (hc b hbS).eq).map q).eq.symm)
  exact ⟨⟨C,hC,CubicClifford.Inertia.constituent_isCompl ρ I C t hd e,
    CubicClifford.Inertia.constituent_map_exchange ρ I hi C t,
    e,hrC,((ChapterG.Section06.lemma_G_6_4 hG hrC).2 Q hcent).2⟩⟩
end CFSG.Quasithin.Chapter15.Section02.PartnerChiefRecognition
