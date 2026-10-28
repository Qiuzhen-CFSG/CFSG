module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.MovedComponent
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalSuzukiExclusion
public import CFSG.Quasithin.ChapterD.Section03.EvenActorConstituent
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.EvenActorFaithful
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.OriginalEvenNatural

/-!
# Original even-linear constituents and moved minimality

A starred cubic actor faithful on the original component quotient has rank at
most the binary field degree. Every irreducible component constituent is then
natural or Hermitian, without any invariance assumption. The natural case is
excluded by the original Hall geometry; the Hermitian case gives moved
minimality on the unchanged module W = [V_M,L].

The exact quotient-action kernel has order prime to three. Excluding both
normalized and exchanged Suzuki support makes the original actor faithful,
so the constituent construction applies in every binary field degree. It
forces even degree, constructs the full separated seed, and proves the
literal Hall exponent in either orientation. The final dichotomy removes
moved minimality from the original even-linear Hall application. Original
seed separation and ambient tensor exclusion, together with the other
source branches, remain with the central Hall assembly owner.

Source: Aschbacher--Smith D.3.9, D.3.21 and 10.1.1--3, pp.199--207,741--742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance evenConstituentMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance evenConstituentMovedFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
  Module.Finite.of_finite
local instance evenConstituentGaloisAlgebra (n : ℕ) :
    Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

private theorem unmark_intertwiner
    {J K V W : Type*} [Group J] [Group K]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) J V) (τ : Representation (ZMod 2) K W)
    (e : J ≃* K) (a : Representation.Equiv (σ.comp e.symm.toMonoidHom) τ) (j : J) (v : W) :
    a.toLinearEquiv.symm (τ (e j) v) = σ j (a.toLinearEquiv.symm v) := by
  have hh := LinearMap.congr_fun (a.symm.isIntertwining' (e j)) v
  change a.toLinearEquiv.symm (τ (e j) v) =
    σ (e.symm (e j)) (a.toLinearEquiv.symm v) at hh
  simpa only [e.symm_apply_apply] using hh

private theorem marked_even_constituent_minimal
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (U : Subrepresentation ((imageRepresentation (movedStabilizerAction D)).comp
      (movedStabilizerComponentImage D).subtype))
    (hU : U.toRepresentation.IsIrreducible)
    (hmodel : SL2.BinarySmall.IsNatural (U.toRepresentation.comp
        (movedImageComponentEquiv D c.nonnormal e).symm.toMonoidHom) ∨
      ∃ s : ℕ, n = 2*s ∧ ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩;
        SL2.BinarySmall.IsHermitian (U.toRepresentation.comp
          (movedImageComponentEquiv D c.nonnormal e).symm.toMonoidHom) s) :
    Even n ∧ MovedMinimal D := by
  let ρ := movedStabilizerAction D
  let K := movedStabilizerComponent D
  let f := ((actionHom ρ).comp K.subtype).rangeRestrict
  let eS := movedImageComponentEquiv D c.nonnormal e
  let I : Subrepresentation ((movedStabilizerAction D).comp K.subtype) := {
    toSubmodule := U.toSubmodule
    apply_mem_toSubmodule k v hv := U.apply_mem_toSubmodule (f k) hv }
  have hI : I.toRepresentation.IsIrreducible := by
    apply (Subrepresentation.irreducible_iff_isAtom I).mpr
    have hh := (irreducible_comp_surjective_iff f (MonoidHom.rangeRestrict_surjective _) _).mpr hU
    exact (Subrepresentation.irreducible_iff_isAtom (U.compActors f)).mp hh
  have hproj (k : K) : eS (f k) = movedNaturalComponentProjection D e k :=
    movedImageComponentProjection_apply D c.nonnormal e k
  rcases hmodel with hmodel | ⟨s,hs,hpos,hmodel⟩
  · obtain ⟨a⟩ := hmodel
    let E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule := a.toLinearEquiv.symm
    have hE (k : K) v : E (naturalComponent e ⟨k.val.val,k.property⟩ v) =
        I.toRepresentation k (E v) := by
      have hh := unmark_intertwiner U.toRepresentation SL2.BinarySmall.natural eS a (f k) v
      exact (congrArg E (SL2AutomorphismNatural.action_conj
        (movedNaturalComponentProjection D e k) v)).trans
        ((congrArg (fun g => E (SL2.BinarySmall.natural g v)) (hproj k).symm).trans hh)
    exact (no_natural_constituent_of_seed_separated D c ht htn hsep n (by omega)
      e I hI E hE).elim
  · let : NeZero s := ⟨hpos.ne'⟩
    obtain ⟨b,⟨a⟩⟩ := hmodel
    let e' := e.trans (Atlas.fieldEquivSL 2 b)
    have hs1 : 1 < s := by
      by_contra! hle
      have hsone : s = 1 := by omega
      have he1 : Nonempty ((L ⧸ pCore 2 L) ≃*
          SL(2,OrthogonalFourMinus.FiniteModel.Field 1)) := by
        exact (congrArg (fun k : ℕ => Nonempty ((L ⧸ pCore 2 L) ≃*
          SL(2,OrthogonalFourMinus.FiniteModel.Field k))) hsone).mp ⟨e'⟩
      exact c.not_a5 ⟨he1.some.trans ((Theory.PSL2.sl2QuotientEquiv _).trans
        Atlas.Comparisons.Exceptional.psl2FourEquivAlt5)⟩
    let E : OrthogonalFourMinus.FiniteModel.Space s ≃ₗ[ZMod 2] I.toSubmodule := a.toLinearEquiv.symm
    have hE (k : K) v : E (SL2.BinarySmall.hermitian s (movedNaturalComponentProjection D e' k) v) =
        I.toRepresentation k (E v) := by
      have hh := unmark_intertwiner U.toRepresentation
        ((SL2.BinarySmall.hermitian s).comp (Matrix.SpecialLinearGroup.map b.toRingHom))
        eS a (f k) v
      exact (congrArg (fun g => E (SL2.BinarySmall.hermitian s
        (Matrix.SpecialLinearGroup.map b.toRingHom g) v)) (hproj k).symm).trans hh
    exact ⟨⟨s,by omega⟩,movedMinimal_of_hermitian_constituent D s c ht htn hsep hs1 e' I hI E hE⟩

/-- A faithful starred actor constructs a Hermitian constituent and proves
moved minimality on the original module; the field degree must be even. -/
theorem even_degree_and_movedMinimal_of_faithful_starred_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hfA : Function.Injective ((movedImageQuotientAction D c.nonnormal e).comp A.subtype)) :
    Even n ∧ MovedMinimal D := by
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let S := movedStabilizerComponentImage D
  let K := movedStabilizerComponent D
  let f := ((actionHom ρ).comp K.subtype).rangeRestrict
  let eS := movedImageComponentEquiv D c.nonnormal e
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : IsSimpleGroup SL(2,GaloisField 2 n) := e.symm.isSimpleGroup
  let : IsQuasisimple SL(2,GaloisField 2 n) := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup S := eS.isSimpleGroup
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv eS.symm
  let : ρ.IsIrreducible := movedStabilizerAction_irreducible D c ht htn hsep
  have hi : σ.IsIrreducible := imageRepresentation_isIrreducible ρ inferInstance
  obtain ⟨U,hU,_hfU⟩ := exists_faithful_normal_simple_constituent σ
    (imageRepresentation_injective ρ) hi S
  have hmove : ¬ A ≤ centralizer (S : Set (actionImage ρ)) := by
    intro hc
    apply hA.1.2.1.1
    apply bot_unique
    intro a ha
    have hk : movedImageQuotientAction D c.nonnormal e a = 1 :=
      (movedImage_component_and_centralizer D c.nonnormal e).2.ge (hc ha)
    exact congrArg (fun a : A => (a : actionImage ρ))
      (hfA (show (movedImageQuotientAction D c.nonnormal e).comp A.subtype ⟨a,ha⟩ =
        (movedImageQuotientAction D c.nonnormal e).comp A.subtype 1 from hk.trans (map_one _).symm))
  have hrank : rank A ≤ n := by
    let : IsElementaryAbelian 2 A := hA.1.2.1.2
    have hr : rank A ≤ primeRank 2 A := by
      have hc := (primeRank_le_iff_elementary_card_le (p := 2) A).mp le_rfl ⊤
        (IsElementaryAbelian.of_injective (p := 2)
          (⊤ : Subgroup A).subtype Subtype.val_injective)
      rw [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup A) ≃* A).toEquiv,
        hA.1.2.1.card_eq_two_pow_rank] at hc
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
    exact hr.trans ((Theory.GroupTheory.primeRank_le_of_injective 2 _ hfA).trans
      (Theory.PSL2.BinaryAutomorphismRank.sl2_automorphism_two_rank_le hn
        (GaloisField.card 2 n (by omega))))
  have hS : IsSQTK KnownSimple.IsKnownSimple S :=
    (original_component_quotient_sqtk D).knownSimple_of_equiv (e.trans eS.symm)
  obtain ⟨_,hmodel⟩ := ChapterD.even_constituent_of_bounded_starred_actor σ
    (imageRepresentation_injective ρ) hi S hS eS n hn (GaloisField.card 2 n (by omega))
    A hA (movedStabilizerAction_cubic_bound D c ht htn hsep) hrank hmove U hU
  exact marked_even_constituent_minimal D c ht htn hsep n hn e U hU hmodel

/-- The original even-degree row requires no constituent or actor-faithfulness
premise once separation in either orientation is established. -/
theorem movedMinimal_of_even_degree_and_seed_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) : MovedMinimal D := by
  have hc := movedStabilizerAction_cubic_bound D c ht htn hsep
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff _).mpr hc
  have h5 : 5 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr e.toEquiv,Atlas.card_sl_two,GaloisField.card 2 n (by omega)]
    apply dvd_mul_of_dvd_right
    obtain ⟨k,rfl⟩ := heven
    have hp : (2 ^ (k+k)) ^ 2 = 16^k := by
      rw [←pow_mul,show (k+k)*2=4*k by omega,pow_mul]
      rfl
    rw [hp]
    exact dvd_trans (by decide : 5 ∣ 16-1)
      (by simpa using Nat.sub_dvd_pow_sub_pow 16 1 k)
  exact (even_degree_and_movedMinimal_of_faithful_starred_actor D c ht htn hsep n hn e
    A hA (even_starred_actor_faithful D c ht htn hsep e h5 A hA)).2

/-- Full/local equality and stability hold for the unchanged even-degree seed
in both orientations; the constituent is constructed from the original actor. -/
theorem separatedSeed_of_even_degree_and_seed_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) : SeparatedSeed D t :=
  separatedSeed_of_separated_and_movedMinimal D
    (movedMinimal_of_even_degree_and_seed_separated D c ht htn hsep n hn heven e)
    ht htn hsep

/-- The literal Hall exponent in the separated even-degree row, with all
constituent, multiplicity and actor-kernel premises discharged. -/
theorem hall_exponent_of_even_degree_and_seed_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 2 ≤ n) (heven : Even n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) :
    ∃ r : ℕ, 1 < r ∧ Monoid.exponent B ∣ 2^r+1 :=
  hall_exponent_of_moved_minimal_and_crossed T D c hnot ht htn
    (movedMinimal_of_even_degree_and_seed_separated D c ht htn hsep n hn heven e)
    (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep)

/-- The surviving odd-degree row has a nontrivial kernel involution in every
starred actor, without assuming any natural constituent. -/
theorem odd_degree_starred_actor_kernel
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 2 ≤ n) (ho : Odd n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D))) :
    ∃ a : actionImage (movedStabilizerAction D), a ∈ A ∧ a ≠ 1 ∧ a^2=1 ∧
      movedImageQuotientAction D c.nonnormal e a = 1 := by
  classical
  by_contra! hnone
  have hf : Function.Injective ((movedImageQuotientAction D c.nonnormal e).comp A.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    apply Subtype.ext
    by_contra hne
    let : IsElementaryAbelian 2 A := hA.1.2.1.2
    exact hnone a.val a.property hne
      (elemPow_eq_one_of_isElementaryAbelian a.val a.property) ha
  exact (Nat.not_even_iff_odd.mpr ho)
    (even_degree_and_movedMinimal_of_faithful_starred_actor D c ht htn hsep n hn e A hA hf).1

/-- The literal Hall consumer in every separated even-linear row. Only an
odd-degree actor kernel remains; no constituent or moved-minimality input remains. -/
theorem hall_exponent_or_odd_degree_actor_kernel
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) :
    (∃ r : ℕ, 1 < r ∧ Monoid.exponent B ∣ 2^r+1) ∨
      (Odd n ∧ ∃ A : Subgroup (actionImage (movedStabilizerAction D)),
        A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
        ∃ a : actionImage (movedStabilizerAction D), a ∈ A ∧ a ≠ 1 ∧ a^2=1 ∧
          movedImageQuotientAction D c.nonnormal e a = 1) := by
  by_cases he : Even n
  · exact Or.inl (hall_exponent_of_even_degree_and_seed_separated D c hnot ht htn hsep n hn he e)
  · have ho := Nat.not_even_iff_odd.mp he
    obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff _).mpr
      (movedStabilizerAction_cubic_bound D c ht htn hsep)
    exact Or.inr ⟨ho,A,hA,odd_degree_starred_actor_kernel D c ht htn hsep n hn ho e A hA⟩

/-- In the separated even-linear row, the original actor itself constructs a
Hermitian constituent. The degree is even and the full moved module is minimal. -/
theorem even_degree_and_movedMinimal_of_even_linear_and_seed_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) : Even n ∧ MovedMinimal D := by
  obtain ⟨A,hA⟩ := (ChapterD.QhatStar_nonempty_iff _).mpr
    (movedStabilizerAction_cubic_bound D c ht htn hsep)
  exact even_degree_and_movedMinimal_of_faithful_starred_actor D c ht htn hsep n hn e A hA
    (moved_starred_actor_faithful D c ht htn hsep e A hA)

/-- The unchanged seed in either separated orientation has the full/local
identity and stabilizer clauses, for every original binary SL2 quotient. -/
theorem separatedSeed_of_even_linear_and_seed_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) : SeparatedSeed D t :=
  separatedSeed_of_separated_and_movedMinimal D
    (even_degree_and_movedMinimal_of_even_linear_and_seed_separated D c ht htn hsep n hn e).2
    ht htn hsep

/-- The literal Hall exponent for the entire separated even-linear row, with
all constituent, actor-kernel and moved-minimality premises discharged. -/
theorem hall_exponent_of_even_linear_and_seed_separated
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 2 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) :
    ∃ r : ℕ, 1 < r ∧ Monoid.exponent B ∣ 2^r+1 :=
  hall_exponent_of_moved_minimal_and_crossed T D c hnot ht htn
    (even_degree_and_movedMinimal_of_even_linear_and_seed_separated D c ht htn hsep n hn e).2
    (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep)

/-- Odd field degree is excluded in either original separated seed orientation. -/
theorem not_seed_separated_of_odd_degree
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (n : ℕ) (hn : 2 ≤ n) (ho : Odd n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) :
    ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) := by
  intro hsep
  exact (Nat.not_even_iff_odd.mpr ho)
    (even_degree_and_movedMinimal_of_even_linear_and_seed_separated D c ht htn hsep n hn e).1

/-- The original even-linear Hall branch now needs no moved-minimality
premise. Its remaining alternative retains the literal seed quotient,
both component markings, and the constituent or natural-tensor model. -/
theorem even_linear_hall_exponent_or_original_analysis
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n)) :
    (∃ r : ℕ, 1 < r ∧ Monoid.exponent B ∣ 2^r+1) ∨
      OriginalEvenNaturalAnalysis D ht n e := by
  by_cases hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)
  · exact Or.inl (hall_exponent_of_even_linear_and_seed_separated D c hnot ht htn hsep n (by omega) e)
  · exact Or.inr (original_even_seed_constituent_or_natural D c n hn e ht htn hsep)
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
