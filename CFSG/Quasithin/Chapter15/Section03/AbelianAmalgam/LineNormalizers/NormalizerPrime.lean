module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.OriginalGeometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.StarGeometry
public import Theory.GroupTheory.PrimeRankNormalKernel
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.NormalizerPrime.Containment
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OrthogonalImage

/-!
# The original normalizer bound from the ordinary residual kernel

The actual residual quotient is the rotation subgroup E₉ in the natural
orthogonal action. Modulo the two-core, it is disjoint from the module
centralizer. Quasithinness bounds the ambient three-rank by two, so the
module centralizer has no three-part. The original fixed-plane normalizer
calculation transports that bound to the literal subgroup used by the
terminal contradiction.

This route retains the ordinary residual-kernel identity already contained
in EarlierData. The separate Source49.Original assembly discharges the
extraspecial alternative from the original local hypotheses.
Source: Aschbacher--Smith, 15.3.49(4)--(5), printed pp.1142--1143.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.NormalizerPrime
open TerminalSourceEndgame.OriginalSource
open ThreeAlternatives
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc P E : Subgroup G}

private noncomputable def residualRotationEquiv
    (s : LocalStructure.EarlierData T M Mc P E) :
    (residualY M Mc ⧸ pCore 2 (residualY M Mc)) ≃*
      OrthogonalFourBinary.TerminalLines.RotationCode := by
  let Y := residualY M Mc
  have hYM := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
  let f := s.natural.action.comp (inclusion hYM)
  have hk : f.ker = (centralizer (localModule T M : Set G)).subgroupOf Y := by
    ext y
    change inclusion hYM y ∈ s.natural.action.ker ↔ _
    rw [GoldschmidtCore.LocalRelations.action_ker s.natural]
    rfl
  have hcore : f.ker = pCore 2 Y := by
    apply (map_injective Y.subtype_injective)
    rw [hk, subgroupOf_map_subtype, inf_comm]
    exact s.residual_core_module.symm
  have hr : f.range = GoldschmidtCore.LocalRelations.actionImage s.natural Y := by
    ext a
    constructor
    · rintro ⟨y, rfl⟩
      exact mem_map_of_mem s.natural.action y.property
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  exact (QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans
      ((MulEquiv.subgroupCongr (hr.trans s.residual_image)).trans
        OrthogonalFourBinary.TerminalLines.residualEquiv.symm))

private theorem residual_rank_ge_two
    (s : LocalStructure.EarlierData T M Mc P E) :
    2 ≤ primeRank 3 ((residualY M Mc).subgroupOf M) := by
  rw [primeRank_congr 3 (subgroupOfEquivOfLe
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc))]
  have he := residualRotationEquiv s
  have hc : Nat.card OrthogonalFourBinary.TerminalLines.RotationCode = 3 ^ 2 := by
    norm_num [OrthogonalFourBinary.TerminalLines.RotationCode, Nat.card_prod]
  have hp : ∀ x : OrthogonalFourBinary.TerminalLines.RotationCode, x ^ 3 = 1 := by
    decide +kernel
  have hr := primeRank_ge_of_elementary_embedding hp hc
    (MonoidHom.id OrthogonalFourBinary.TerminalLines.RotationCode) Function.injective_id
  rw [← primeRank_congr 3 he] at hr
  exact hr.trans (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup)

private theorem source_core_intersection
    (s : LocalStructure.EarlierData T M Mc P E)
    (d : NaturalOrthogonalAction M (localModule T M)) :
    (residualY M Mc).subgroupOf M ⊓ d.actor.ker ≤ pCore 2 M := by
  intro x hx
  let Y := residualY M Mc
  have hxC : (x : G) ∈ centralizer (localModule T M : Set G) := by
    have hc : x ∈ d.actor.ker := hx.2
    rw [d.ker_actor] at hc
    exact hc
  have hy : (x : G) ∈ Y.pCoreIn 2 := by
    change (x : G) ∈ twoCoreAmbient (residualY M Mc)
    rw [s.residual_core_module]
    exact ⟨hx.1, hxC⟩
  obtain ⟨y, hycore, hyeq⟩ := hy
  have hq : QuotientGroup.mk' (pCore 2 Y) y = 1 :=
    (QuotientGroup.eq_one_iff y).mpr hycore
  have hs := congrArg (fun z => ((residualCoreQuotientEquivStar M Mc) z : StarGroup M)) hq
  rw [residualCoreQuotientEquivStar_apply_mk, map_one, OneMemClass.coe_one] at hs
  have he : inclusion (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) y = x :=
    Subtype.ext hyeq
  rw [he] at hs
  exact (QuotientGroup.eq_one_iff x).mp hs

omit [Finite G] in
private theorem source_core_le_kernel
    (d : NaturalOrthogonalAction M (localModule T M)) : pCore 2 M ≤ d.actor.ker := by
  have hn : ((pCore 2 M).map d.actor).Normal :=
    (inferInstance : (pCore 2 M).Normal).map _ d.onto
  have hle : (pCore 2 M).map d.actor ≤ pCore 2 OrthogonalActor :=
    le_sSup ⟨hn, pCore_isPGroup.map _⟩
  apply (Subgroup.map_eq_bot_iff _).mp
  exact le_bot_iff.mp (orthogonalActor_twoCore_eq_bot ▸ hle)

/-- The ordinary residual kernel already recorded in the actual earlier
local data forces the module centralizer to have order prime to three. -/
theorem module_centralizer_three_prime
    (s : LocalStructure.EarlierData T M Mc P E)
    {κ : GroupClass} (hG : IsSimpleQTKE κ G) :
    Nat.Coprime 3 (Nat.card (M ⊓ centralizer (localModule T M : Set G) : Subgroup G)) := by
  let := standard_elementary s.natural
  obtain ⟨k⟩ := coordinates_from_standard s.natural
    (definite_of_standard s.natural s.plane_le s.plane_card s.plane_definite)
  let N := (residualY M Mc).subgroupOf M
  let : N.Normal := residualY_normal M Mc
  have hC : Nat.Coprime 3 (Nat.card k.action.actor.ker) :=
    Theory.GroupTheory.coprime_three_card_of_normal_disjoint_mod_core
      N k.action.actor.ker (source_core_le_kernel k.action)
      (source_core_intersection s k.action) (residual_rank_ge_two s)
      ((hG.twoLocal_sqtk s.ordering.1.1.1).stronglyQuasithin 3 Nat.prime_three (by decide))
  have he : (M ⊓ centralizer (localModule T M : Set G)).subgroupOf M =
      k.action.actor.ker := by
    rw [k.action.ker_actor]
    ext x
    exact ⟨fun h => h.2, fun h => ⟨x.property, h⟩⟩
  rw [← Nat.card_congr (subgroupOfEquivOfLe
    (show M ⊓ centralizer (localModule T M : Set G) ≤ M from inf_le_left)).toEquiv, he]
  exact hC

/-- The actual earlier ordinary kernel discharges the prime-to-three input
of the fixed-plane normalizer calculation. -/
theorem normalizer_three_prime_from_earlier
    (s : LocalStructure.EarlierData T M Mc P E)
    {κ : GroupClass} (hG : IsSimpleQTKE κ G)
    (hfixed : centralizer (fixedPlane P (planeStabilizer T P) : Set G) ≤ M) :
    Nat.Coprime 3 (Nat.card
      (normalizer (fixedPlane (localModule T M) (planeStabilizer T P) : Set G))) :=
  fixedPlane_normalizer_three_prime s hfixed (module_centralizer_three_prime s hG)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.NormalizerPrime
