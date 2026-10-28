module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalPrime
public import Theory.Representation.SL2.NaturalCentralizerDouble
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.ThreeFree

/-!
# Cubic actors cannot lie in the natural action kernel

The homogeneous natural SL₂ action has two root displacements whose kernels
split the entire module into two identical modules for its literal component
centralizer. This works for arbitrary natural multiplicity and arbitrary
mixing of its copies. A cubic actor contained in that centralizer would then
be an FF-offender on one of these two summands. The actual kernel has trivial
two-core and three-free order, and its SQTK cover is inherited from the original
normalizer. The proved B.5 three-free exclusion rules out that offender.

The final source application refines the existing natural branch: its same
starred actor has a proper nontrivial intersection with the marked quotient
kernel, and still moves the extracted genuine component orbit there. Source
separation, constituent recognition and exclusion of this remaining actor
branch stay with qt-d-10-nona5-central-hall-orders. This does not assert
SeedAnalysisAt or SourceNonnormalCentralHallAt.
Source: Aschbacher--Smith D.3.9(2), D.3.21 and B.5.6,
printed pp.200--201,205--206 and105.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance naturalKernelCubicElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance naturalKernelCubicFinite : FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
  Module.Finite.of_finite
private theorem component_le_stabilizer : L ≤ D.maximalLocal ⊓ normalizer (L : Set G) :=
  le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
local instance naturalKernelCubicNormal : (movedStabilizerComponent D).Normal :=
  (normal_subgroupOf_iff_le_normalizer (component_le_stabilizer D)).mpr inf_le_right

/-- The faithful full-normalizer action image has the actual original SQTK cover. -/
theorem movedStabilizerImage_sqtkQuotient :
    Nonempty (ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple
      (actionImage (movedStabilizerAction D))) := by
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let ρ := movedStabilizerAction D
  have hM := D.simpleQTKE.twoLocal_sqtk
    (source_module_nonsolvable_uniqueness D).normalizer_maximal.1
  let f := inclusion (show N ≤ D.maximalLocal from inf_le_left)
  have hN : IsSQTK KnownSimple.IsKnownSimple N :=
    ⟨hM.stronglyQuasithin.of_injective f (inclusion_injective _),
      hM.isKGroup.of_injective f (inclusion_injective _)⟩
  exact ⟨{ Cover := N
           kernel := (actionHom ρ).ker
           sqtk := hN
           equiv := QuotientGroup.quotientKerEquivOfSurjective (actionHom ρ)
             ρ.asGroupHom.rangeRestrict_surjective }⟩

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance naturalKernelCubicAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- The literal marked quotient kernel acts on two identical invariant summands. -/
theorem naturalImageQuotientAction_kernel_double
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v)) :
    let τ : Representation (ZMod 2)
        (movedNaturalImageQuotientAction D e I E hE).ker
        (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
      (imageRepresentation (movedStabilizerAction D)).comp
      (movedNaturalImageQuotientAction D e I E hE).ker.subtype
    ∃ U : Subrepresentation τ, Nonempty (τ.Equiv (U.toRepresentation.prod U.toRepresentation)) := by
  let ρ := movedStabilizerAction D
  let K := movedStabilizerComponent D
  let q := movedNaturalComponentProjection D e
  let α := movedNaturalImageQuotientAction D e I E hE
  let τ := (imageRepresentation ρ).comp α.ker.subtype
  let : ρ.IsIrreducible := movedStabilizerAction_irreducible D c ht htn hsep
  have hcoords (l : K) (v : Fin 2 → F) :
      E ((q l).val.mulVec v) = I.toRepresentation l (E v) := by
    rw [←hE]
    congr 1
    exact (SL2AutomorphismNatural.action_conj _ _).symm
  have hhom := SL2AutomorphismNatural.homogeneous_natural_of_irreducible
    ρ K q (movedNaturalQuotientAction D e) (movedNaturalComponentProjection_conj D e)
    I hI E hcoords
  obtain ⟨_,hcent⟩ := movedNaturalImage_component_and_centralizer D e I E hE
  apply SL2AutomorphismNatural.natural_commuting_double (ρ.comp K.subtype) q
    (movedNaturalComponentProjection_surjective D e) I E hcoords hhom τ
  intro a k w
  have ha : a.val ∈ centralizer (movedStabilizerComponentImage D : Set (actionImage ρ)) :=
    hcent ▸ a.property
  have hh := (mem_centralizer_iff.mp ha) (actionHom ρ k)
    (show actionHom ρ k ∈ movedStabilizerComponentImage D from ⟨k,rfl⟩)
  have he := congrArg (fun z : actionImage ρ => imageRepresentation ρ z w) hh.symm
  simpa only [map_mul,Module.End.mul_apply,imageRepresentation_actionHom,
    τ,MonoidHom.comp_apply,Subgroup.subtype_apply] using he

private theorem no_cubic_of_three_free_double
    {C W : Type*} [Group C] [Finite C] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (τ : Representation (ZMod 2) C W) (hf : Function.Injective τ)
    (hcore : pCore 2 C = ⊥)
    (cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple C)
    (h3 : Nat.Coprime 3 (Nat.card C))
    (U : Subrepresentation τ) (e : τ.Equiv (U.toRepresentation.prod U.toRepresentation))
    (A : Subgroup C) (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim τ A := by
  have huf : Function.Injective U.toRepresentation := by
    intro a b hab
    apply hf
    apply LinearMap.ext
    intro v
    apply e.toLinearEquiv.injective
    have ha := LinearMap.congr_fun (e.isIntertwining' a) v
    have hb := LinearMap.congr_fun (e.isIntertwining' b) v
    exact ha.trans ((Prod.ext (LinearMap.congr_fun hab _)
      (LinearMap.congr_fun hab _)).trans hb.symm)
  have hn := ChapterB.SourceInduction.no_ff_of_three_free huf hcore cover h3
  have he := fixedCodim_map_equivariant τ (U.toRepresentation.prod U.toRepresentation)
    (MonoidHom.id C) e.toLinearEquiv
    (fun a v => LinearMap.congr_fun (e.isIntertwining' a) v) A
  rw [Subgroup.map_id,fixedCodim_prod] at he
  have hlt : rank A < fixedCodim U.toRepresentation A := by
    by_contra! hle
    exact hn ⟨A,hA,hle⟩
  omega

/-- Every nontrivial elementary actor inside the literal kernel has ratio greater than two. -/
theorem naturalImageQuotientAction_kernel_no_cubic
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (A : Subgroup (movedNaturalImageQuotientAction D e I E hE).ker)
    (hA : IsElementaryTwo A) :
    2 * rank A < fixedCodim ((imageRepresentation (movedStabilizerAction D)).comp
      (movedNaturalImageQuotientAction D e I E hE).ker.subtype) A := by
  let ρ := movedStabilizerAction D
  let α := movedNaturalImageQuotientAction D e I E hE
  obtain ⟨U,⟨a⟩⟩ := naturalImageQuotientAction_kernel_double D c ht htn hsep e I hI E hE
  apply no_cubic_of_three_free_double ((imageRepresentation ρ).comp α.ker.subtype)
    ((imageRepresentation_injective ρ).comp α.ker.subtype_injective)
    (naturalImageQuotientAction_ker_twoCore_eq_bot D c ht htn hsep e I E hE)
    ((movedStabilizerImage_sqtkQuotient D).some.subgroup α.ker) ?_ U a A hA
  apply naturalImageQuotientAction_ker_card_coprime D c ht htn hsep e I E hE 3 (by decide)
  rw [Nat.card_congr e.toEquiv]
  exact Theory.SpecificGroups.three_dvd_card_sl_two _


/-- Every cubic actor moves the marked component quotient. Its kernel need not
be solvable and its full normalizer quotient need not be a two-group. -/
theorem natural_cubic_actor_not_le_quotient_kernel
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (A : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : IsElementaryTwo A)
    (hb : fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A) :
    ¬ A ≤ (movedNaturalImageQuotientAction D e I E hE).ker := by
  intro hAC
  let C := (movedNaturalImageQuotientAction D e I E hE).ker
  let : IsElementaryAbelian 2 A := hA.2
  have hAs : IsElementaryTwo (A.subgroupOf C) := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hAC⟩
    intro hz
    have hh := congrArg (map C.subtype) hz
    rw [map_subgroupOf_eq_of_le hAC,Subgroup.map_bot] at hh
    exact hA.1 hh
  have h := naturalImageQuotientAction_kernel_no_cubic D c ht htn hsep e I hI E hE
    (A.subgroupOf C) hAs
  rw [fixedCodim_subgroupOf _ hAC,rank_subgroupOf hAC] at h
  omega

local instance naturalKernelCubicGaloisAlgebra (n : ℕ) :
    Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

omit [Field F] [Finite F] [CharP F 2] in
/-- In the surviving source branch the same starred actor both moves the
component quotient and has a nontrivial kernel on it. The extracted moved
component is retained in that proper kernel. -/
theorem source_natural_starred_actor_mixed_kernel
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v)) :
    Odd n ∧ ∃ A : Subgroup (actionImage (movedStabilizerAction D)),
      A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
      1 < rank A ∧
      ⊥ < A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker ∧
      A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker < A ∧
      ∃ J : Subgroup (actionImage (movedStabilizerAction D)),
        IsComponent _ J ∧ J ≤ (movedNaturalImageQuotientAction D e I E hE).ker ∧
        Nat.Coprime 3 (Nat.card J) ∧ 5 ∣ Nat.card J ∧
        ⁅componentOrbit J A,A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker⁆ =
          componentOrbit J A ∧ componentOrbit J A ≠ ⊥ := by
  obtain ⟨ho,A,hA,hr,J,hJ,hJK,h3,h5,hm,hne⟩ :=
    source_natural_starred_actor_five_component D c ht htn hsep n hn e I hI E hE
  have hb : fixedCodim (imageRepresentation (movedStabilizerAction D)) A ≤ 2 * rank A :=
    (actionRatio_le_nat_iff _ hA.1.2.1 2).mp
      (hA.1.2.2.2.le.trans (movedStabilizerAction_cubic_bound D c ht htn hsep))
  have hnot := natural_cubic_actor_not_le_quotient_kernel D c ht htn hsep e I hI E hE
    A hA.1.2.1 hb
  have hnker : A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker ≠ ⊥ := by
    intro hz
    rw [hz,commutator_bot_right] at hm
    exact hne hm.symm
  refine ⟨ho,A,hA,hr,bot_lt_iff_ne_bot.mpr hnker,?_,J,hJ,hJK,h3,h5,hm,hne⟩
  exact lt_of_le_of_ne inf_le_left (fun he => hnot (inf_eq_left.mp he))

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
