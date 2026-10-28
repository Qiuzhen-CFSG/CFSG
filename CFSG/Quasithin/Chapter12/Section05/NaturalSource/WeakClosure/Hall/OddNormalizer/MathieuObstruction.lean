module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Hall.OddNormalizer.JankoResidual
public import Theory.GroupTheory.CComponent.ThreeCore

/-!
# The marked M₂₂ residual cannot lie in the exterior normalizer

The actual PSL₅(2) component in M = N_G(L) has cubic rank two. Any perfect
C-component seed with radical quotient M₂₂ inside M lies in a normal C-component by
1.2.1. Its order is divisible by three, so full-rank component isolation
forces it into L. But eleven divides the seed order and does not divide L:
the literal two-core quotient of L has order 9999360. This is a contradiction.

Apply this to the full residual at the original marked J₄ involution.
Every T-normalized comparison subgroup centralized by the original odd actor
modulo its two-core lies in M. Hence no such comparison subgroup can contain
the marked residual. In this PSL₅(2) specialization this removes the final
component-generation premise. The odd-local construction of the comparison
subgroup remains necessary, as does the separate pushing-up argument on p.612.
OddNormalizer connects the obstruction to the literal Hall counterexample.

Source: Aschbacher--Smith, 4.4.3, printed p.623; 1.2.1, printed pp.502--504.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Chapter4 Chapter4.Section04
open Chapter7.NormalizedSource.MathieuGeneration
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

private theorem no_mathieu_seed_in_normalizer (a : ExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (B : Subgroup a.M) [Group.IsPerfect B]
    (hB : (⊤ : Subgroup B).IsCComponent)
    (eB : (B ⧸ solvableRadical B) ≃* Sporadic.Mathieu.M22) : False := by
  let M := a.M
  let F := L.subgroupOf M
  have hM : IsSQTK KnownSimple.IsKnownSimple M :=
    h.toHypothesis1221.sylow_normalized_sqtk D.sylow_normalizes_component
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hF : F.IsCComponent :=
    h.toHypothesis1221.sylow_normalized_component D.sylow_normalizes_component
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  let eF : F ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let e := (QuotientGroup.congr _ _ eF (pCore_map_iso 2 eF)).trans a.quotientEquiv
  let Five := Representation.SL5TenDimensional.Group
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup Five := Representation.SL5TenDimensional.projectiveEquiv.isSimpleGroup
  let : Group.IsPerfect Five := Atlas.sl_perfect 5 (by decide)
  let : IsSimpleGroup (F ⧸ pCore 2 F) := e.isSimpleGroup
  let : Group.IsPerfect (F ⧸ pCore 2 F) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hz : center (F ⧸ pCore 2 F) = ⊥ := by
    rcases (inferInstance : (center (F ⧸ pCore 2 F)).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp ht)).elim
  let : IsQuasisimple (F ⧸ pCore 2 F) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hrF : 2 ≤ primeRank 3 (F ⧸ pCore 2 F) := by
    rw [primeRank_congr 3 (e.trans Representation.SL5TenDimensional.projectiveEquiv)]
    exact Theory.SpecificGroups.Classical.BinaryFiveRanks.projective_threeRank_ge_two
  have hrB : 2 ≤ primeRank 3 (B ⧸ solvableRadical B) := by
    rw [primeRank_equiv 3 eB, Sporadic.Mathieu.m22_primeRank_three]
  obtain ⟨C,⟨hC,hBC,_,_⟩,_⟩ := Chapter1.Section02.radical_rank_component_source hM B hB hrB
  have hdiv (p : ℕ) (hp : p ∣ 443520) : p ∣ Nat.card B := by
    apply dvd_trans _ (card_quotient_dvd_card (solvableRadical B))
    rwa [Nat.card_congr eB.toEquiv, Sporadic.Mathieu.m22_order]
  have hCF : C = F := by
    by_contra hn
    have hc := hF.other_coprime_three_of_rank hz hrF
      (hM.stronglyQuasithin 3 (by decide) (by decide)) hC hn
    exact Nat.prime_three.coprime_iff_not_dvd.mp hc
      ((hdiv 3 (by decide)).trans (card_dvd_of_le hBC))
  have h11 : 11 ∣ Nat.card F := (hdiv 11 (by decide)).trans (card_dvd_of_le (hCF ▸ hBC))
  have hcard : Nat.card (F ⧸ pCore 2 F) = 9999360 := by
    rw [Nat.card_congr (e.trans Representation.SL5TenDimensional.projectiveEquiv).toEquiv]
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
    calc
      _ = ∏ i : Fin 5, (2 ^ 5 - 2 ^ (i : ℕ)) := by
        simpa only [Nat.card_zmod, Nat.reduceSub, Nat.gcd_one_right, mul_one] using hc
      _ = 9999360 := by decide
  have hcop : Nat.Coprime 11 (Nat.card F) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 F), hcard]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := F)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 11 9999360).mul_right ((by decide : Nat.Coprime 11 2).pow_right n)
  exact (show Nat.Prime 11 by decide).coprime_iff_not_dvd.mp hcop h11

/-- No literal perfect M₂₂ radical seed embeds in the marked normalizer.
The seed is a C-component of its displayed domain U. -/
theorem ExteriorMarking.mathieu_radical_seed_not_le (a : ExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {U : Type*} [Group U] [Finite U] (P : Subgroup U) (hP : P.IsCComponent)
    (eP : (P ⧸ solvableRadical P) ≃* Sporadic.Mathieu.M22)
    (f : U →* G) (hf : Function.Injective f) : ¬ P.map f ≤ a.M := by
  intro hPM
  let B := (P.map f).subgroupOf a.M
  let e : P ≃* B := (P.equivMapOfInjective f hf).trans (subgroupOfEquivOfLe hPM).symm
  let := hP.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hPt : (⊤ : Subgroup P).IsCComponent := by
    simpa only [subgroupOf_self] using hP.subgroupOf (le_refl P)
  have hBt : (⊤ : Subgroup B).IsCComponent := by
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hPt.map_equiv e
  let q := (QuotientGroup.congr _ _ e.symm (map_solvableRadical_equiv e.symm)).trans eP
  exact no_mathieu_seed_in_normalizer a h B hBt q

/-- The full residual of every involution in this same J₄ component escapes M.
The proof uses the actual radical quotient, retaining its covering center. -/
theorem exterior_janko_involution_residual_not_le (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (K : Subgroup (normalizer (A : Set G)))
    (a : JankoNormalizerAction K) (z : K) (hz : orderOf z = 2) :
    ¬ ((solvableResidual (centralizer ({z} : Set K))).map
        (centralizer ({z} : Set K)).subtype).map
          ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ s.marking.M := by
  obtain ⟨hR,⟨eR⟩⟩ := a.involution_residual z hz
  rw [map_map]
  exact s.marking.mathieu_radical_seed_not_le h _ hR eR _
    (((normalizer (A : Set G)).subtype_injective.comp K.subtype_injective).comp
      (centralizer ({z} : Set K)).subtype_injective)

/-- No T-normalized subgroup centralized by the odd actor modulo its two-core
can contain the original marked involution residual. This replaces the source
final generation step in the PSL₅(2) specialization; constructing such a subgroup
still requires the odd-local identification on printed p.623. -/
theorem exterior_janko_marked_residual_obstruction (s : SylowExteriorMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAM : A ≤ s.marking.M)
    (ho : Odd (Nat.card A)) (hAV : A ≤ centralizer (V : Set G))
    (K : Subgroup (normalizer (A : Set G))) (r : ExteriorJankoResidualData s A K) :
    ∃ z : K, ((z : normalizer (A : Set G)) : G) = s.marking.z ∧ orderOf z = 2 ∧
      ¬ ∃ I : Subgroup G, (T : Subgroup G) ≤ normalizer (I : Set G) ∧
        A ≤ sectionCentralizer I ∧
        ((solvableResidual (centralizer ({z} : Set K))).map
          (centralizer ({z} : Set K)).subtype).map
            ((normalizer (A : Set G)).subtype.comp K.subtype) ≤ I := by
  obtain ⟨a,_,_,z,hzG,hz,_⟩ := r
  refine ⟨z,hzG,hz,?_⟩
  rintro ⟨I,hTI,hAI,hRI⟩
  exact exterior_janko_involution_residual_not_le s h A K a z hz
    (hRI.trans (D.sourceOrbit_oddActor_comparison h.toHypothesis1221 A hne
      ((s.marking.centralizing_actor_section hAM hAV).trans inf_le_right) ho I hTI hAI))

end CFSG.Quasithin.Chapter12.Section05.NaturalSource

