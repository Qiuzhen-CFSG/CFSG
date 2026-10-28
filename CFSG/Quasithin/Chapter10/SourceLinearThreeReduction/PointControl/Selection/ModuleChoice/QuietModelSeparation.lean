module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietSeedCubic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.OriginalOddSeparation

/-!
# The nonseparated quiet seed retains an actual binary rank-one model

The quiet source hypotheses give a faithful irreducible action of the
literal component square on the unchanged seed and cubic ratio at most two
in its full normalizer. The Suzuki, Janko and odd-prime square bounds exclude
their catalogue rows. The small odd primes are checked against perfectness
and the actual A5 and SL3(2) isomorphisms. The surviving binary rank-one
quotient is marked over its original finite-field degree, which is at least
three. No Hall context or nonzero component-fixed vector is assumed.

Source: Aschbacher--Smith D.3.7 and 3.2.6, printed pp.197--199 and581,
used in 10.1.1, p.741. The model exclusions adapt the original-seed proofs
in CentralHall/Nonlinear/Modules/SeedAnalysis to the quiet hypotheses.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 CentralHall.Nonlinear.Modules
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary

private theorem quiet_model_cubic
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    {S : Type*} [Group S] (e : (L ⧸ pCore 2 L) ≃* S)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    ∃ σ : Representation (ZMod 2) (S × S) (Additive D.seed),
      σ.IsIrreducible ∧ Function.Injective σ ∧
        cubicRatio (normalizerRepresentation σ) ≤ 2 := by
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_quotient_simple D hn
  let : IsSimpleGroup S := e.symm.isSimpleGroup
  obtain ⟨q,hq,_,hl,hr,σ,hi,hσ⟩ := quiet_seed_product_action D hmany hn hJ e ht htn
  have hf := original_seed_product_faithful_of_not_separated D e ht hsep q hl hr σ hσ
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨q l,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext rfl⟩
  have hb := quiet_seed_normalizer_cubic_of_not_separated D hmany hn hJ ht htn hsep
  refine ⟨σ,hi,hf,?_⟩
  unfold normalizerRepresentation linearNormalizer at hb ⊢
  rwa [himage] at hb

/-- Outside the binary-three row, failure of seed separation forces an actual
binary rank-one quotient of degree at least three. -/
theorem quiet_nonseparated_model_even
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hna : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    ∃ n : ℕ, 3 ≤ n ∧ Nonempty ((L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) := by
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_quotient_simple D hn
  cases component_model D hn with
  | linear_even n hn hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    let f : F ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
      simpa only [Fintype.card_eq_nat_card] using hF.trans (GaloisField.card 2 n (by omega)).symm)
    let a := (e.trans (Atlas.fieldEquivPSL 2 f)).trans (Theory.PSL2.sl2QuotientEquiv _).symm
    have hne : n ≠ 2 := by
      rintro rfl
      exact hna ⟨a.trans ((Theory.PSL2.sl2QuotientEquiv _).trans
        Atlas.Comparisons.Exceptional.psl2FourEquivAlt5)⟩
    exact ⟨n,by omega,⟨a⟩⟩
  | suzuki m hm he =>
    let e := he.some
    obtain ⟨σ,hi,hf,hb⟩ := quiet_model_cubic D hmany hn hJ e ht htn hsep
    exact ((not_le_of_gt (ChapterD.suzuki_square_normalizer_cubicRatio_gt m (by omega)
      (IsSQTK.knownSimple_of_equiv e (original_component_quotient_sqtk D)) σ hi hf)) hb).elim
  | linear_prime p hp ho hm =>
    have hp3 : p ≠ 3 := by
      intro hp3
      obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
      let : Group.IsPerfect (L ⧸ pCore 2 L) := inferInstance
      let : Group.IsPerfect PSL(2,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three
        (hc.trans hp3) inferInstance
    have hp5 : p ≠ 5 := by
      intro hp5
      exact hna (ChapterK.OddCharacteristic.altFive_of_psl2_five (hp5 ▸ hm))
    have hp7 : p ≠ 7 := by
      intro hp7
      obtain ⟨e⟩ := ChapterK.OddCharacteristic.psl3Two_of_psl2_seven (hp7 ▸ hm)
      exact hnot ⟨e.trans (Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm.trans
        Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two)⟩
    have hlarge : 11 ≤ p := by
      by_contra! hsmall
      interval_cases p <;> norm_num at *
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨F,_,_,hF,⟨e₀⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let eF : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp (by
      simpa only [Nat.card_eq_fintype_card] using hF)).symm
    let e := e₀.trans (Atlas.fieldEquivPSL 2 eF)
    let : IsSimpleGroup PSL(2,ZMod p) := e.symm.isSimpleGroup
    let : IsQuasisimple PSL(2,ZMod p) := IsQuasisimple.of_mulEquiv e
    obtain ⟨σ,hi,hf,hb⟩ := quiet_model_cubic D hmany hn hJ e ht htn hsep
    exact ((not_le_of_gt (ChapterD.odd_prime_square_normalizer_cubicRatio_gt hlarge
      (IsSQTK.knownSimple_of_equiv e (original_component_quotient_sqtk D)) σ hi hf)) hb).elim
  | janko he =>
    let e := he.some
    obtain ⟨σ,hi,hf,hb⟩ := quiet_model_cubic D hmany hn hJ e ht htn hsep
    exact ((not_le_of_gt (ChapterD.janko_square_normalizer_cubicRatio_gt
      (IsSQTK.knownSimple_of_equiv e (original_component_quotient_sqtk D)) σ hi hf)) hb).elim

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
