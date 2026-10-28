module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableNoncommutingOriginalSource
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CoreTwoFiftySixExclusion

/-!
# The original nonsolvable generation parameter through core order256

The original module source constructs the residual Context and the full
marked action on H. A commuting pair would have both cores of order at
least512 by the actual quotient and commutator argument. The noncommuting
case instead constructs an elementary subgroup in the same O²(H), with
image four under the original quotient map. Thus n(H)=2.

The earlier original A5 module clause is explicit; no universal Context or
normalization callback is used. The genuine5.2.3 theorem and larger cores
remain separate duties.
Source application: Aschbacher--Smith 13.2.8(1), printed p.880.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside Section02.A5Outside.OriginalCentralization
open Section03.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- The original residual elementary lift and parameter equality, retaining
the actual H and its entire two-core, for every core of order at most256. -/
theorem original_nonsolvable_core_le_twoFiftySix_parameter_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) (hsmall : Nat.card (pCore 2 H) ≤ 256) :
    (∃ A : Subgroup H, IsElementaryAbelian 2 A ∧ A ≤ pResidual 2 H ∧
      Nat.card (A.map (QuotientGroup.mk' (pCore 2 H))) = 4) ∧
      ChapterE.generationParameter H = 2 := by
  obtain ⟨W,W₁,W₂,W₃,e,q,_,hq,hk,_,hr,he⟩ :=
    original_nonsolvable_action_from_modules d hmany hmodules hH hZ hs
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype)
      (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hm : ¬ V ≤ centralizer (W : Set G) := by
    intro hVW
    have hlarge := (original_commuting_pair_core_cards_ge_fiveTwelve d e hjoin hH
      (localActor_surjective_of_omega_movement d hH hZ) q hq hk he hVW).2
    omega
  exact original_nonsolvable_noncommuting_parameter_from_source d hmany hH hZ hs
    e q hq hk hr he hm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
