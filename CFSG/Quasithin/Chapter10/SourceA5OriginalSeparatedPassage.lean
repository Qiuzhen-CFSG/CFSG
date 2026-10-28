module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalSeparatedCentralizer
public import CFSG.Quasithin.Chapter10.SourceA5OriginalCentralizerFaithfulness.Complete
public import CFSG.Quasithin.Chapter10.SourceA5SeparatedCoordinates.Original
public import CFSG.Quasithin.Chapter10.SourceA5SeparatedCoordinates.NormalizedModels
public import CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity.NaturalAssembly
public import CFSG.Quasithin.Chapter10.SourceA5SeparatedMultiplicity.DeletedAssembly

/-!
# The separated A₅ full/local passage

For the original minimal full-module setup, the separated seed gives two
complementary homogeneous supports in the faithful full central quotient.
A starred offender acts faithfully on the marked A₅ pair: its centralizer is
a prime-to-fifteen K-group, hence solvable by the complete known-simple
catalogue, and the normal solvable subgroup theorem applies. The literal
natural/deleted support coordinates then bound their common multiplicity by
two. Their commuting endomorphism groups force the pair centralizer to be a
two-group, hence trivial in the reduced actor. The outer automorphism quotient
is a two-group, and original Sylow invariance yields full/local equality.

This completes the separated A₅ branch of Aschbacher--Smith D.3.21, retaining
both original quotient maps. The D.3.5 separated-seed statement and the full
cubic bound are earlier source inputs; the same-seed D.3.9 branch is separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Representation.NormalPairHomogeneous
open Representation.AlternatingFiveMovedPair

private theorem marked_conjugation {S Q : Type*} [Group S] [Group Q]
    (i : S →* Q) (hi : Function.Injective i) (J : Subgroup Q) [J.Normal]
    (hr : i.range = J) (E : Subgroup Q)
    (hf : Function.Injective ((MulAut.conjNormal : Q →* MulAut J).comp E.subtype)) :
    ∃ c : E →* MulAut S, Function.Injective c ∧
      ∀ a z, a.val * i z * a.val⁻¹ = i (c a z) := by
  let u : S ≃* J := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hr)
  let c : E →* MulAut S := (MulAut.congr u.symm).toMonoidHom.comp
    ((MulAut.conjNormal : Q →* MulAut J).comp E.subtype)
  refine ⟨c,(MulAut.congr u.symm).injective.comp hf,?_⟩
  intro a z
  have hu := congrArg (fun y : J => (y : Q))
    (u.apply_symm_apply (MulAut.conjNormal (a : Q) (u z)))
  exact hu.symm

local instance : Algebra (ZMod 2) (OrthogonalFourMinus.FiniteModel.Field 1) := ZMod.algebra _ 2
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
local instance separatedPassageFullElementary : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The actual separated full quotient has at most two copies on each support,
with both original quotient markings retained. -/
theorem source_a5_original_bounded_separated_coordinates
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    SourceA5OriginalBoundedSeparatedCoordinates D e hn ht htn := by
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).normal
  let Q := D.maximalLocal ⧸ centralizer (U : Set D.maximalLocal)
  let q := QuotientGroup.mk' (centralizer (U : Set D.maximalLocal))
  let J := ((localOrbit T L).subgroupOf D.maximalLocal).map q
  let _ : J.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : FiniteDimensional (ZMod 2) (Additive D.fullCentralQuotient) := Module.Finite.of_finite
  obtain ⟨τ,i,hτ,hirr,hboundτ,hi,hnorm,hcomp,_,hmodels,_,hdiagram,hτdiagram⟩ :=
    source_a5_full_separated_coordinates D e hn ht htn hD hsep
  have hratio := hboundτ hbound
  have hs := source_a5_original_actor_centralizer_solvable D e hn ht htn
  obtain ⟨E,hE⟩ := (ChapterD.QhatStar_nonempty_iff τ).mpr hratio
  have hfaith := source_a5_original_actor_starred_conjugation_of_solvable
    D e hn ht htn hs τ hτ E hE
  have hr : i.range = J := source_a5_original_marked_orbit_range D e hn ht htn i hdiagram
  obtain ⟨c,hcfaith,hc⟩ := marked_conjugation i hi J hr E hfaith
  refine ⟨τ,i,hτ,hdiagram,hτdiagram,?_⟩
  rcases hmodels with hnat | hdel
  · obtain ⟨f,⟨C⟩⟩ := hnat
    have hF : Nat.card (OrthogonalFourMinus.FiniteModel.Field 1) = 4 :=
      GaloisField.card 2 2 (by decide)
    have hk := SourceA5SeparatedMultiplicity.natural_multiplicity_le_two_of_starred_actor
      (OrthogonalFourMinus.FiniteModel.Field 1) τ i hF hE c hc hcfaith hcomp f C
    obtain ⟨em⟩ := MixedTypes.natural_marking f
    let B : Coordinates τ i SeparatedCentralizer.natural := Coordinates.changeModel τ i _ C em
    have hkB : B.multiplicity ≤ 2 := by
      simpa only [B, Coordinates.changeModel_multiplicity] using hk
    exact Or.inl ⟨B.multiplicity,hkB,B.productEquiv τ i _ hcomp,
      B.productEquiv_intertwines τ i _ hcomp⟩
  · obtain ⟨C⟩ := hdel
    have hk := SourceA5SeparatedMultiplicity.deleted_multiplicity_le_two_of_starred_actor
      τ i hE c hc hcfaith hcomp C
    let B : Coordinates τ i SeparatedCentralizer.deleted :=
      Coordinates.changeModel τ i _ C MixedTypes.core_deleted
    have hkB : B.multiplicity ≤ 2 := by
      simpa only [B, Coordinates.changeModel_multiplicity] using hk
    exact Or.inr ⟨B.multiplicity,hkB,B.productEquiv τ i _ hcomp,
      B.productEquiv_intertwines τ i _ hcomp⟩

include D e in
/-- The separated minimal original A₅ setup has equal full and local modules. -/
theorem source_a5_full_eq_local_of_separated_seed
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    D.fullModule = D.moduleSubgroup :=
  source_a5_full_eq_local_of_bounded_separated_coordinates D e hn ht htn
    (source_a5_original_bounded_separated_coordinates D e hn ht htn hD hbound hsep)

local instance separatedPassageMovedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- The full/local passage concludes the literal original moved-quotient
irreducibility and cross-centralization in the separated source branch. -/
theorem source_a5_original_irreducible_of_minimal_separated_seed
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (L : Set G))
    (hD : D.IsMinimalFullModule) (hbound : SourceFullModuleCubicBound D)
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    (originalMovedQuotientAction D e).IsIrreducible ∧
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  source_a5_original_irreducible_of_bounded_separated_coordinates D e hn ht htn hsep
    (source_a5_original_bounded_separated_coordinates D e hn ht htn hD hbound hsep)

end CFSG.Quasithin.Chapter10
