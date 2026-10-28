module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalSuzukiDegree
public import Theory.Representation.Suzuki.ExchangedDisplacement
public import Theory.Representation.BinaryOffender.FixedSpaceMovement

/-!
# Displacement and actor ranks for the original exchanged Suzuki pair

A primitive-prime commutator of the genuine exchanger lies in the literal
natural quotient kernel. Its two identical invariant summands give
exchanger displacement at least `4*(2*r+1)` on the original moved module.
Together with the cubic bound, and the Suzuki automorphism two-rank,
this forces a nontrivial pointwise centralizer in the same starred actor.

Every nonidentity element of that centralizer has a nonzero displacement
submodule for the fully moving pair. The checked pair degree bound then
raises the actor rank to at least `4*(2*r+1)` and the orbit-centralizer rank
to at least `6*r+2`. Both original seed orientations, the fixed original
module, the concrete Suzuki marking and all quotient maps are preserved.
No constituent is assumed invariant under the exchanger.

The same centralizer has a nonzero fixed space moved by the starred actor.
D.2.7 therefore gives strict ratio decrease on that literal fixed space.
Its actual restricted actor has rank at most `2*r+2`, since the centralizer
lies in the pointwise kernel of this restriction.
The resulting reduced pair action remains for the tensor exclusion.
Source separation, constituent construction and final
SeedAnalysisAt/SourceNonnormalCentralHallAt assembly remain with
qt-d-10-nona5-central-hall-orders.
Source: Aschbacher--Smith D.3.7--9 and D.3.21, printed pp.197--201,204--207;
application 10.1.1, p.741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance naturalDisplacementElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D
local instance naturalDisplacementFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) := Module.Finite.of_finite
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance naturalDisplacementAlgebra : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- The genuine exchanger moves at least four times the Suzuki field degree
on the original module, using the actual natural quotient-kernel double. -/
theorem natural_suzuki_exchanger_displacement
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
    (J : Subgroup (actionImage (movedStabilizerAction D)))
    (hJ : IsComponent _ J) (hJK : J ≤ (movedNaturalImageQuotientAction D e I E hE).ker)
    (a : actionImage (movedStabilizerAction D))
    (han : a ∉ normalizer (J : Set (actionImage (movedStabilizerAction D))))
    (r : ℕ) (hr : 0 < r) (eJ : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :
    4 * (2*r+1) ≤ fixedCodim (imageRepresentation (movedStabilizerAction D)) (zpowers a) := by
  obtain ⟨U,⟨eU⟩⟩ := naturalImageQuotientAction_kernel_double D c ht htn hsep e I hI E hE
  exact Representation.Suzuki.exchanged_component_displacement_of_double
    (imageRepresentation (movedStabilizerAction D)) (imageRepresentation_injective _)
    J hJ a han r hr eJ (movedNaturalImageQuotientAction D e I E hE).ker hJK U eU

/-- Cubic movement forces a large pointwise kernel on the exchanged pair:
its binary rank is at least `6*r+2`, hence at least eight. -/
theorem natural_starred_suzuki_actor_bounds
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
    (A J : Subgroup (actionImage (movedStabilizerAction D)))
    (hA : A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)))
    (hJ : IsComponent _ J) (hJK : J ≤ (movedNaturalImageQuotientAction D e I E hE).ker)
    (hindex : (normalizer (J : Set (actionImage (movedStabilizerAction D)))).index = 2)
    (a : actionImage (movedStabilizerAction D)) (ha : a ∈ A)
    (han : a ∉ normalizer (J : Set (actionImage (movedStabilizerAction D))))
    (horbit : componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom)
    (hm : subspaceCommutator (imageRepresentation (movedStabilizerAction D)) ⊤ J = ⊤)
    (r : ℕ) (hr : 0 < r) (eJ : J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) :
    4 * (2*r+1) ≤ fixedCodim (imageRepresentation (movedStabilizerAction D)) (zpowers a) ∧
      4 * (2*r+1) ≤ rank A ∧
      6*r+2 ≤ rank (A ⊓ centralizer (componentOrbit J A : Set (actionImage (movedStabilizerAction D)))) := by
  let σ := imageRepresentation (movedStabilizerAction D)
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hlo := natural_suzuki_exchanger_displacement D c ht htn hsep e I hI E hE J hJ hJK a han r hr eJ
  change 4 * (2*r+1) ≤ fixedCodim σ (zpowers a) at hlo
  have hfix := Submodule.finrank_mono (fixedSpace_antitone σ (zpowers_le.mpr ha))
  have hc := fixedCodim_add_finrank σ A
  have hca := fixedCodim_add_finrank σ (zpowers a)
  have hb : fixedCodim σ A ≤ 2 * rank A :=
    (actionRatio_le_nat_iff _ hA.1.2.1 2).mp
      (hA.1.2.2.2.le.trans (movedStabilizerAction_cubic_bound D c ht htn hsep))
  have hrank := Representation.Suzuki.exchanged_actor_rank_le J A hindex r hr eJ
  let C := A ⊓ centralizer (componentOrbit J A : Set (actionImage (movedStabilizerAction D)))
  change rank A ≤ rank C + (2*r+1) + 1 at hrank
  have hlarge : 2 * (2*r+1) ≤ rank A := by omega
  have hCpos : 0 < rank C := by omega
  have hCn : C ≠ ⊥ := by
    intro he
    have hz : rank C = 0 := by simp only [he,rank,Subgroup.card_bot,Nat.log_one_right]
    omega
  obtain ⟨b,hbC,hbnot⟩ := SetLike.not_le_iff_exists.mp
    (show ¬ C ≤ ⊥ from fun h => hCn (bot_unique h))
  have hb1 : b ≠ 1 := fun h => hbnot (mem_bot.mpr h)
  have hbc : b ∈ centralizer ((J ⊔ J.map (MulAut.conj a).toMonoidHom :
      Subgroup (actionImage (movedStabilizerAction D))) : Set (actionImage (movedStabilizerAction D))) :=
    horbit ▸ hbC.2
  have hi : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom (movedStabilizerAction D))
      (movedStabilizerAction D).asGroupHom.rangeRestrict_surjective σ).mp
        (movedStabilizerAction_irreducible D c ht htn hsep)
  have hbdis := Representation.Suzuki.pair_centralizer_displacement σ
    (imageRepresentation_injective _) hi J hJ hindex a han hm r hr eJ b hbc hb1
  have hbfix := Submodule.finrank_mono
    (fixedSpace_antitone σ (zpowers_le.mpr hbC.1))
  have hcb := fixedCodim_add_finrank σ (zpowers b)
  refine ⟨hlo,by omega,?_⟩
  change 6*r+2 ≤ rank C
  omega

local instance naturalDisplacementGaloisAlgebra (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) :=
  ZMod.algebra _ 2

omit [Field F] [Finite F] [CharP F 2] in
/-- Apply both bounds to the actual starred actor and Suzuki pair from the
original Hall context. All quotient-kernel and full-movement data are retained. -/
theorem source_natural_starred_actor_suzuki_displacement
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
    Odd n ∧ ∃ (A J : Subgroup (actionImage (movedStabilizerAction D))) (r : ℕ),
      A ∈ ChapterD.QhatStar (imageRepresentation (movedStabilizerAction D)) ∧
      ⊥ < A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker ∧
      A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker < A ∧
      IsComponent _ J ∧ J ≤ (movedNaturalImageQuotientAction D e I E hE).ker ∧
      0 < r ∧ Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
      ⁅componentOrbit J A,A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker⁆ =
        componentOrbit J A ∧ componentOrbit J A ≠ ⊥ ∧
      (normalizer (J : Set (actionImage (movedStabilizerAction D)))).index = 2 ∧
      4 * (2*r+1) ≤ rank A ∧
      6*r+2 ≤ rank (A ⊓ centralizer (componentOrbit J A : Set (actionImage (movedStabilizerAction D)))) ∧
      (let σ := imageRepresentation (movedStabilizerAction D)
       let C := A ⊓ centralizer (componentOrbit J A : Set (actionImage (movedStabilizerAction D)))
       rank (restrictedSubgroup σ (fixedSpace σ C) A) ≤ 2*r+2 ∧
       restrictedSubgroup σ (fixedSpace σ C) A ∈ ChapterD.Qhat (subspaceImageRepresentation σ (fixedSpace σ C)) ∧
         actionRatio (subspaceImageRepresentation σ (fixedSpace σ C))
           (restrictedSubgroup σ (fixedSpace σ C) A) < cubicRatio σ) ∧
      ∃ a : actionImage (movedStabilizerAction D), a ∈ A ∧
        a ∉ normalizer (J : Set (actionImage (movedStabilizerAction D))) ∧
        componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom ∧
        subspaceCommutator (imageRepresentation (movedStabilizerAction D)) ⊤ J = ⊤ ∧
        subspaceCommutator (imageRepresentation (movedStabilizerAction D)) ⊤
          (J.map (MulAut.conj a).toMonoidHom) = ⊤ ∧
        4 * (2*r+1) ≤ fixedCodim (imageRepresentation (movedStabilizerAction D)) (zpowers a) := by
  obtain ⟨ho,A,J,hA,_,hbot,hproper,hJ,hJK,⟨r,hr,⟨eJ⟩⟩,hm,hne,hi,a,ha,han,horbit,hmJ,hmK⟩ :=
    source_natural_starred_actor_suzuki_full_movement D c ht htn hsep n hn e I hI E hE
  obtain ⟨hdis,hrank,hcentral⟩ := natural_starred_suzuki_actor_bounds D c ht htn hsep e I hI E hE
    A J hA hJ hJK hi a ha han horbit hmJ r hr eJ
  let σ := imageRepresentation (movedStabilizerAction D)
  let X := componentOrbit J A
  let C := A ⊓ centralizer (X : Set (actionImage (movedStabilizerAction D)))
  have hirr : σ.IsIrreducible :=
    (irreducible_comp_surjective_iff (actionHom (movedStabilizerAction D))
      (movedStabilizerAction D).asGroupHom.rangeRestrict_surjective σ).mp
        (movedStabilizerAction_irreducible D c ht htn hsep)
  let : σ.IsIrreducible := hirr
  let := Subrepresentation.irreducible_module_nontrivial σ
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion (show C ≤ A from inf_le_left)) (inclusion_injective _)
  let : X.Normal := by
    change (componentOrbit J A).Normal
    rw [horbit]
    exact sup_conjugate_normal_of_normalizer_index_two J hi a han
  have hXA : ⁅X,A⁆ = X := by
    apply le_antisymm (commutator_le_left X A)
    calc
      X = ⁅X,A ⊓ (movedNaturalImageQuotientAction D e I E hE).ker⁆ := hm.symm
      _ ≤ ⁅X,A⁆ := commutator_mono le_rfl inf_le_left
  have hfixJ := full_component_pair_fixed_eq_bot σ hirr J hJ hi a han hmJ
  have hfixX : fixedSpace σ X = ⊥ := bot_unique
    ((fixedSpace_antitone σ (le_componentOrbit J A)).trans hfixJ.le)
  have hCn : C ≠ ⊥ := by
    intro he
    have hz : rank C = 0 := by simp only [he,rank,Subgroup.card_bot,Nat.log_one_right]
    change 6*r+2 ≤ rank C at hcentral
    omega
  have hmove := fixedSpace_moved_of_commutator_eq σ X A C
    (IsElementaryAbelian.isPGroup 2 C)
    (le_centralizer_iff.mp (show C ≤ centralizer (X : Set (actionImage (movedStabilizerAction D))) from inf_le_right))
    hfixX hXA
  have hdrop := ChapterD.QhatStar.fixedSpace_ratio_drop σ hA
    (show C ≤ A from inf_le_left) hCn hmove
  have hsum := rank_subspaceKernel_add_image σ (fixedSpace σ C) A
    (fixedSpace_subactor_stabilized σ hA.1.2.1 (show C ≤ A from inf_le_left))
    (IsElementaryAbelian.isPGroup 2 A)
  have hCK : rank C ≤ rank (subspaceKernel σ (fixedSpace σ C) A) :=
    Nat.log_mono_right (card_le_of_le
      (subactor_le_fixedSpace_kernel σ (show C ≤ A from inf_le_left)))
  have hupper := Representation.Suzuki.exchanged_actor_rank_le J A hi r hr eJ
  change rank A ≤ rank C + (2*r+1) + 1 at hupper
  have hrestricted : rank (restrictedSubgroup σ (fixedSpace σ C) A) ≤ 2*r+2 := by omega
  exact ⟨ho,A,J,r,hA,hbot,hproper,hJ,hJK,hr,⟨eJ⟩,hm,hne,hi,hrank,hcentral,
    ⟨hrestricted,hdrop⟩,a,ha,han,horbit,hmJ,hmK,hdis⟩

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
