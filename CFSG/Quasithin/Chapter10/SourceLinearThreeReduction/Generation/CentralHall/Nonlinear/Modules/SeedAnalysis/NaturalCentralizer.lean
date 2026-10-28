module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalKernel
public import Theory.Representation.SL2.NaturalImageStructure
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCentralizerPrime
public import Theory.Representation.NormalComponentConstituents

/-!
# The genuine component in a nonfaithful natural actor kernel

The fixed SL₂ marking identifies the component image in the faithful
normalizer action and identifies its literal centralizer with the quotient
action kernel. Original minimality gives irreducibility for this whole action;
normality and nontriviality of the component imply full movement.

The starred actor from the original cubic bound cannot have rank one: a
centralizing displacement of dimension at most two would be fixed by the
perfect component. D.2.13 therefore removes the five-core alternative in
D.3.9. The previously proved three-free kernel removes the three-core
alternative, leaving an actual moved component orbit inside that kernel.
In particular the kernel cannot be solvable. No component model or seed
separation is asserted by this reduction.

The literal Hall-context applications retain either seed orientation and
feed NaturalPrime. The remaining separation and nonsolvable component
exclusion stay with qt-d-10-nona5-central-hall-orders.
Source: Aschbacher--Smith D.3.9(2), D.3.21(3), printed pp.200--201,205--206.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
private theorem component_le_stabilizer : L ≤ D.maximalLocal ⊓ normalizer (L : Set G) :=
  le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer
local instance : (movedStabilizerComponent D).Normal :=
  (normal_subgroupOf_iff_le_normalizer (component_le_stabilizer D)).mpr inf_le_right

/-- The image of the original component in the full moved normalizer action. -/
abbrev movedStabilizerComponentImage :=
  ((actionHom (movedStabilizerAction D)).comp (movedStabilizerComponent D).subtype).range

/-- The component image is normal in the faithful full normalizer image. -/
instance movedStabilizerComponentImage_normal : (movedStabilizerComponentImage D).Normal := by
  have he : movedStabilizerComponentImage D =
      (movedStabilizerComponent D).map (actionHom (movedStabilizerAction D)) := by
    rw [movedStabilizerComponentImage,MonoidHom.range_comp,Subgroup.range_subtype]
  rw [he]
  exact Subgroup.Normal.map inferInstance _ (movedStabilizerAction D).asGroupHom.rangeRestrict_surjective

/-- The full faithful normalizer image inherits the complete known-simple
K-group hypothesis from the original proper two-local subgroup. -/
theorem movedStabilizerImage_isKGroup : IsKGroup KnownSimple.IsKnownSimple (actionImage (movedStabilizerAction D)) := by
  have hM := (D.simpleQTKE.twoLocal_sqtk
    (source_module_nonsolvable_uniqueness D).normalizer_maximal.1).isKGroup
  have hN := hM.of_injective
    (inclusion (show D.maximalLocal ⊓ normalizer (L : Set G) ≤ D.maximalLocal from inf_le_left))
    (inclusion_injective _)
  exact hN.of_surjective (actionHom (movedStabilizerAction D))
    (movedStabilizerAction D).asGroupHom.rangeRestrict_surjective

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- The original quotient marks the actual component image, and its automorphism
kernel is exactly that image's centralizer on the whole moved module. -/
theorem movedNaturalImage_component_and_centralizer
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* movedStabilizerComponentImage D) ∧
      (movedNaturalImageQuotientAction D e I E hE).ker =
        centralizer (movedStabilizerComponentImage D : Set (actionImage (movedStabilizerAction D))) := by
  have hcoords (l : movedStabilizerComponent D) (v : Fin 2 → F) :
      E ((movedNaturalComponentProjection D e l).val.mulVec v) = I.toRepresentation l (E v) := by
    rw [←hE]
    congr 1
    exact (SL2AutomorphismNatural.action_conj _ _).symm
  have hk : (movedNaturalComponentProjection D e).ker ≤
      ((actionHom (movedStabilizerAction D)).comp (movedStabilizerComponent D).subtype).ker := by
    intro l hl
    have hlcore : (⟨l.val.val,l.property⟩ : L) ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply e.map_eq_one_iff.mp
      exact hl
    apply (actionHom_eq_one_iff (movedStabilizerAction D) l).mpr
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l.val : G) * (w.toMul : G) * (l.val : G)⁻¹ = (w.toMul : G)
    have hc := mem_centralizer_iff.mp (source_component_core_centralizes_fullModule D
      (mem_map_of_mem L.subtype hlcore)) w.toMul (moved_le_fullModule D w.toMul.property)
    change (w.toMul : G) * (l.val : G) = (l.val : G) * (w.toMul : G) at hc
    rw [←hc,mul_inv_cancel_right]
  obtain ⟨⟨eS⟩,hc⟩ := SL2AutomorphismNatural.natural_image_component_and_centralizer
    (movedStabilizerAction D) (movedStabilizerComponent D)
    (movedNaturalComponentProjection D e) (movedNaturalComponentProjection_surjective D e)
    (movedNaturalQuotientAction D e) (movedNaturalComponentProjection_conj D e) I E hcoords hk
  exact ⟨⟨e.trans eS.symm⟩,hc⟩

local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

omit [Field F] [Finite F] [CharP F 2] in
/-- Every surviving natural branch has a starred actor of rank at least two
moving a genuine ordinary component orbit in its quotient-action kernel. -/
theorem source_natural_starred_actor_component
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
    let α := movedNaturalImageQuotientAction D e I E hE
    ∃ A : Subgroup (actionImage (movedStabilizerAction D)),
      A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
      1 < rank A ∧ ∃ J : Subgroup (actionImage (movedStabilizerAction D)),
        IsComponent _ J ∧ J ≤ α.ker ∧
        ⁅componentOrbit J A,A ⊓ α.ker⁆ = componentOrbit J A ∧
        componentOrbit J A ≠ ⊥ := by
  let ρ := movedStabilizerAction D
  let σ := imageRepresentation ρ
  let α := movedNaturalImageQuotientAction D e I E hE
  let S := movedStabilizerComponentImage D
  obtain ⟨⟨eS⟩,hC⟩ := movedNaturalImage_component_and_centralizer D e I E hE
  let := D.quasisimple
  let : IsQuasisimple S := IsQuasisimple.of_mulEquiv eS
  let : ρ.IsIrreducible := movedStabilizerAction_irreducible D c ht htn hsep
  have hi : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom ρ) ρ.asGroupHom.rangeRestrict_surjective σ).mp
      (inferInstance : ρ.IsIrreducible)
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : Nontrivial S := eS.injective.nontrivial
  have hSn : S ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot S).mp inferInstance
  have hfull := subspaceCommutator_top_eq_top_of_normal_faithful_irreducible σ
    (imageRepresentation_injective ρ) hi S hSn
  have hcore := movedStabilizerImage_twoCore_eq_bot D c ht htn hsep
  obtain ⟨_,h3,A,hA,a,ha,hne,_,hker⟩ :=
    source_natural_starred_actor_kernel D c ht htn hsep n hn e I hI E hE
  have hAn : A ⊓ centralizer (S : Set (actionImage ρ)) ≠ ⊥ := by
    intro hz
    have hm : a ∈ A ⊓ centralizer (S : Set (actionImage ρ)) := ⟨ha,hC ▸ hker⟩
    exact hne (mem_bot.mp (hz ▸ hm))
  have hr : 1 < rank A := by
    have hn1 : rank A ≠ 1 := fun he => hAn
      (ChosenSource325.rank_one_starred_component_centralizer_eq_bot σ
        (imageRepresentation_injective ρ) S hfull hA he)
    have hp := hA.1.2.1.rank_pos
    omega
  obtain ⟨X,hXC,_,hXn,hXB,hcase⟩ :=
    ChosenSource325.exists_starred_moved_subgroup_in_component_centralizer σ
      (imageRepresentation_injective ρ) S hcore hfull hA hAn
  rcases hcase with ⟨_,hXp⟩ | ⟨J,hJ,hJC,hXJ⟩
  · have hXK : X ≤ α.ker := hXC.trans hC.symm.le
    have hcX : Nat.Coprime 3 (Nat.card X) := h3.of_dvd_right (card_dvd_of_le hXK)
    obtain ⟨k,hk⟩ := hXp.exists_card_eq
    apply False.elim
    apply hXn
    apply Subgroup.card_eq_one.mp
    rw [hk] at hcX ⊢
    exact Nat.eq_one_of_dvd_coprimes (hcX.pow_left k) dvd_rfl dvd_rfl
  · refine ⟨A,hA,hr,J,hJ,hJC.trans hC.symm.le,?_,?_⟩
    · change ⁅componentOrbit J A,A ⊓ α.ker⁆ = componentOrbit J A
      rw [hC]
      simpa only [hXJ] using hXB
    · simpa only [hXJ] using hXn

omit [Field F] [Finite F] [CharP F 2] in
/-- The solvable centralizer alternative is excluded from the original
separated natural Hall context, without a five-free kernel assumption. -/
theorem naturalImageQuotientAction_kernel_not_solvable
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
    ¬ Group.IsSolvable (movedNaturalImageQuotientAction D e I E hE).ker := by
  intro hs
  let := hs
  obtain ⟨A,_,_,J,hJ,hJK,_,_⟩ :=
    source_natural_starred_actor_component D c ht htn hsep n hn e I hI E hE
  exact hJ.isCComponent.not_isSolvable
    (Group.isSolvable_of_isSolvable_injective (f := inclusion hJK) (inclusion_injective hJK))

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
