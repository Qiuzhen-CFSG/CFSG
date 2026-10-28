module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.ComponentFactorIdentification
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.Comparison
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.SeedCore
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.SelfDualModels
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.JankoCentralizer
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank
public import Theory.Mathieu.M22.ReeExclusion
public import Theory.GroupTheory.AmalgamLocalCores

/-!
# The noncubic odd-actor comparison on the original Mathieu residual

The full involution-centralizer residual embeds in the containing normal
C-component Q of C_G(z). Its three-rank makes its two-core quotient
quasisimple. If an actor of prime order greater than three acts nontrivially
on (Q/O₂(Q))/Z(Q/O₂(Q)), its fixed group contains the actual M₂₂ residual
image. The source model sieve, native J₄ centralizer exclusion, degree-eight
cover exclusions and Ree local calculation rule out every such action.

Triviality on the simple section descends to the original two-core
commutator bound. The already proved odd-actor closure comparison then
places Q, and hence the entire original involution-centralizer residual,
in N_G(L). Every projection and full covering component is retained.

The literal Hall consumer constructs this containment for every noncubic
actor. The cubic actor, M₁₂/M₂₂ pushing-up alternatives and identification
of the native Mathieu residual with L_A remain open. In particular, this
reduction does not assert SourceMathieuHallFaithfulAt.

Source: Aschbacher--Smith 4.4.3, printed p.623, applied in 4.4.14,
printed pp.624--625. The native model proofs retain their imported source
attribution; no new model order or simplicity premise is introduced here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4.Section04.OddLocalMathieu

/-- A faithful prime action greater than three cannot fix the full image of
an M22 seed with quasisimple two-core quotient in a source C-model. -/
theorem no_large_prime_mathieu_fixed_seed
    {P S : Type*} [Group P] [Finite P] [Group.IsPerfect P]
    [IsQuasisimple (P ⧸ pCore 2 P)] [Group S] [Finite S]
    (hm : ChapterA.Section02.IsTheoremCModel S)
    (f : P →* S) (hne : f.range ≠ ⊥)
    (e : (f.range ⧸ solvableRadical f.range) ≃* Sporadic.Mathieu.M22)
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (a : MulAut S) (ha : orderOf a = p) (hfix : f.range ≤ a.fixedSubgroup) : False := by
  let g := e.toMonoidHom.comp (QuotientGroup.mk' (solvableRadical f.range))
  have hg : Function.Surjective g := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfixed : HasMathieuFixedSection S p := ⟨a,ha,
    (ChapterA.Section02.IsSectionOf.of_surjective g hg).ambient_injective
      (inclusion hfix) (inclusion_injective hfix)⟩
  have hrows := hfixed.theoremC_rows hp hgt hm
  change RemainingOddLocalRankTwoModel S ∨ Nonempty (S ≃* Janko4.Model) at hrows
  rcases hrows with hr | hj
  · obtain ⟨_,hqs,⟨ez⟩⟩ := rank_two_seed_quasisimple hr f hne e
    let := hqs
    obtain ⟨m,hm,⟨er⟩⟩ := rank_two_mathieu_cover_is_ree hr f.range ez
    exact Sporadic.Mathieu.M22LocalSections.no_embedding_ree g hg hm
      (er.toMonoidHom.comp f.range.subtype) (er.injective.comp f.range.subtype_injective)
  · exact no_janko_mathieu_fixed_section hp hgt (hfixed.of_mulEquiv hj.some)

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 OddLocalMathieu
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

include D in
/-- For an actor of prime order greater than three, the actual ambient
component containing the full M22 seed lies in the original N_G(L). -/
theorem sourceOrbit_mathieu_oddActor_comparison_component
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ sectionCentralizer L)
    (z : G) (hz : orderOf z = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hAz : A ≤ centralizer ({z} : Set G))
    (P : Subgroup (centralizer ({z} : Set G) ⊓ centralizer (A : Set G) : Subgroup G))
    (hP : P.IsCComponent)
    (eP : (P ⧸ solvableRadical P) ≃* Sporadic.Mathieu.M22)
    (Q : Subgroup (centralizer ({z} : Set G))) [Q.Normal]
    [IsQuasisimple (Q ⧸ pCore 2 Q)]
    (hPQ : P.map (inclusion inf_le_left) ≤ Q) :
    Q.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let := hAe
  let C := centralizer ({z} : Set G)
  let E := C ⊓ centralizer (A : Set G)
  let Qg := Q.map C.subtype
  have hz1 : z ≠ 1 := by intro he; rw [he,orderOf_one] at hz; omega
  have hC : IsSQTK KnownSimple.IsKnownSimple C := by
    apply h.simpleQTKE.twoLocal_sqtk
    refine ⟨zpowers z,fun hb => hz1 (mem_bot.mp (hb ▸ mem_zpowers _)),?_,
      (normalizer_zpowers_eq_centralizer_of_order_two _ hz).symm⟩
    exact IsPGroup.of_card (show Nat.card (zpowers z) = 2^1 by rw [Nat.card_zpowers,hz]; rfl)
  have hE : IsSQTK KnownSimple.IsKnownSimple E :=
    (IsSQTK.equiv (subgroupOfEquivOfLe (show E ≤ C from inf_le_left))).mp
      (hC.subgroup (E.subgroupOf C))
  let := hP.perfect
  let : Nontrivial P := (nontrivial_iff_ne_bot _).mpr hP.ne_bot
  let : IsQuasisimple (P ⧸ pCore 2 P) :=
    ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank hE hP
      (mathieu_radical_three_rank eP)
  let j := seedInclusion inf_le_left hPQ
  let f := (projection Q).comp j
  obtain ⟨hfn,_,⟨e⟩⟩ := seed_image j (seedInclusion_injective inf_le_left hPQ) eP
  have htriv : ∀ x : A, simpleAction Q (⟨x,hAz x.property⟩ : C) = 1 := by
    intro x
    by_contra hx
    let a := simpleAction Q (⟨x,hAz x.property⟩ : C)
    have hap : a ^ p = 1 := by
      rw [←map_pow]
      have he : (⟨x,hAz x.property⟩ : C) ^ p = 1 :=
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (x : G) x.property)
      rw [he,map_one]
    apply no_large_prime_mathieu_fixed_seed (simpleSection_model (hC.subgroup Q))
      f hfn e hp hgt a (orderOf_eq_prime hap hx)
    rintro _ ⟨y,rfl⟩
    rw [MulAut.mem_fixedSubgroup]
    change simpleAction Q (⟨x,hAz x.property⟩ : C) (projection Q (j y)) = projection Q (j y)
    rw [simpleAction_projection]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    change (x : G) * ((y : E) : G) * (x : G)⁻¹ = _
    rw [y.val.property.2 (x : G) x.property,mul_inv_cancel_right]
    rfl
  have hc : ⁅A.subgroupOf C,Q⁆ ≤ Q.pCoreIn 2 :=
    commutator_le_of_trivial_simpleAction Q (A.subgroupOf C)
      (fun x => htriv ⟨x,x.property⟩)
  have hcG := map_mono (f := C.subtype) hc
  rw [map_commutator,map_subgroupOf_eq_of_le hAz,
    ←AmalgamLocalCores.pCoreIn_map_of_injective 2 C.subtype C.subtype_injective] at hcG
  have hCQ : C ≤ normalizer (Qg : Set G) := by
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      Q.le_normalizer_map C.subtype
  have ho : Odd (Nat.card A) := by
    obtain ⟨n,hn⟩ := hAe.isPGroup.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two (by omega)).pow
  exact D.sourceOrbit_oddActor_comparison h A hne hA ho Qg (hTz.trans hCQ)
    ((le_sectionCentralizer_iff _ _).mpr ⟨hAz.trans hCQ,hcG⟩)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
/-- The original full component and fixed involution, with its entire
involution-centralizer residual now placed in N_G(L). -/
@[expose] def MathieuJankoComparedResidualCase {G : Type*} [Group G]
    (T L V A : Subgroup G) : Prop :=
  ∃ K : Subgroup (normalizer (A : Set G)),
    IsComponent (normalizer (A : Set G)) K ∧ K.Normal ∧
    ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G) ∧
    V ≤ K.map (normalizer (A : Set G)).subtype ∧
    oddActorResidual L A ≤ K.map (normalizer (A : Set G)).subtype ∧
    ∃ a : JankoNormalizerAction K, a.ResidualSeedFamily ∧
      ∃ z : K, ((z : normalizer (A : Set G)) : G) ∈ V ∧ orderOf z = 2 ∧
        T ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ normalizer (L : Set G)
end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The actual seed case discharges every premise of the noncubic
odd-actor comparison on its original component and original fixed involution. -/
theorem sourceOrbit_mathieu_janko_compared_residual
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ sectionCentralizer L) (hAV : A ≤ centralizer (V : Set G))
    (hc : MathieuJankoSeedResidualCase (T : Subgroup G) L V A
      (D.orbitComponent ⧸ center D.orbitComponent)) :
    MathieuJankoComparedResidualCase (T : Subgroup G) L V A := by
  obtain ⟨K,hK,hn,hKV,hout,hcore,hV,hF,hcent,hr,hsection,a,hi,hAk,hseed,
    z,hzV,hz,hTz,hres,heR,P,hP,hPn,⟨eP⟩,hPm,Q,hQ,hunique⟩ := hc
  let := hQ.2.2.1
  let := hQ.2.2.2
  have hzG : orderOf (((z : normalizer (A : Set G)) : G)) = 2 := by
    rw [orderOf_coe,orderOf_coe]
    exact hz
  have hAz : A ≤ centralizer ({((z : normalizer (A : Set G)) : G)} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr ((hAV hx) _ hzV).symm
  have hQM := D.sourceOrbit_mathieu_oddActor_comparison_component h hp hgt A hne hAe hA
    _ hzG hTz hAz P hP eP Q hQ.2.1
  refine ⟨K,hK,hn,hout,hV,hF,a,hseed,z,hzV,hz,hTz,?_⟩
  rw [←hPm]
  have hh := map_mono (f := (centralizer ({((z : normalizer (A : Set G)) : G)} : Set G)).subtype)
    hQ.2.1
  rw [map_map,subtype_comp_inclusion] at hh
  exact hh.trans hQM
end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04
open ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
open Representation.BinaryOffender
universe u
variable {G : Type u} [instG : Group G] [finG : Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal Hall actor retains only a cubic odd-local action or an
involution-centralizer residual contained in the original N_G(L).
The M12/M22 pushing-up alternatives and native seed identification remain. -/
theorem sourceOrbit_mathieu_hall_compared_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) (hlarge : 1 < ChapterE.generationParameter H)
    (B : Subgroup H) (hBN : B ≤ (normalizer (L : Set G)).subgroupOf H)
    (hHall : IsHallSubgroup oddPrimes
      (B.subgroupOf ((normalizer (L : Set G)).subgroupOf H)))
    (hker : B.map H.subtype ⊓ sectionCentralizer L ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ sectionCentralizer L ∧
      A ≤ centralizer (V : Set G) ∧
      (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
      ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) ∧
      (let X := conjugateSpanBy A (T : Subgroup G)
       IsPPerfect 2 X ∧ X.pCoreIn 2 ≠ ⊥ ∧
         L ⊔ (T : Subgroup G) ≤ normalizer (X : Set G) ∧
         normalizer (X : Set G) ≤ normalizer (L : Set G)) ∧
      (∀ Q : Subgroup G, (T : Subgroup G) ≤ normalizer (Q : Set G) →
        A ≤ sectionCentralizer Q → Q ≤ normalizer (L : Set G)) ∧
      (((Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M12) ∨
          Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* Sporadic.Mathieu.M22)) ∧
          MathieuPushingUpFactoredCase T L V A ∧ MathieuPushingUpFactorGap T L V A) ∨
        (UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)) ∧
          MathieuJankoSeedResidualCase (T : Subgroup G) L V A
            (D.orbitComponent ⧸ center D.orbitComponent) ∧
          (p = 3 ∨ MathieuJankoComparedResidualCase (T : Subgroup G) L V A))) := by
  have hsource :=
    @sourceOrbit_mathieu_hall_small_pushingUp G instG finG T L V D
      h hmany hV hm hnon H hH hlarge B hBN hHall hker
  refine hsource.imp fun p hpA => hpA.imp fun A hA => ?_
  have hp := hA.1
  have ho := hA.2.1
  have hne := hA.2.2.1
  have he := hA.2.2.2.1
  have hAC := hA.2.2.2.2.2.1
  have hAV := hA.2.2.2.2.2.2.1
  revert hA
  iterate 11 apply And.imp_right
  apply Or.imp id
  intro hc
  refine ⟨hc.1,hc.2,?_⟩
  by_cases hp3 : p = 3
  · exact .inl hp3
  · have hpgt : 3 < p := by
      have hp2 := hp.two_le
      have hpne : p ≠ 2 := fun hh => by rw [hh] at ho; norm_num at ho
      omega
    exact .inr (D.sourceOrbit_mathieu_janko_compared_residual h.toHypothesis1221
      hp hpgt A hne he hAC hAV hc.2)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
