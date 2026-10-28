module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.Recognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.TrialityPresentation.Evaluation
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.Triality

/-!
# Root-marked triality recognition on the literal source quotient

The proved presentation constructs an equivalence from X/Q.D to the genuine
binary triality carrier. Original short and long parameters retain the supplied
Frobenius-compatible cubic marking and its induced fixed-field marking.
Normalizers identify the whole source Borel. The two actual Weyl quotient
classes identify both standard parabolics, in either orientation, by their
Borel-plus-representative generators.

Restricting this one ambient equivalence gives all three amalgam maps. Composing
with Q.markedIso retains its original quotient, endpoint-disjoint kernels and
proved whole-overlap intersection; no intersection argument is inferred merely
from the kernels. The numerator may be an original group or a geometric
completion. Source equations, generation and placements remain explicit inputs.
Source: DGS Theorem D, printed p.224; GLS3 2.3.5 and 2.4.5, 2.4.7–8.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Triality.Standard Triality.Standard.RootPresentationRecognition
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation
variable {X F : Type*} [Group X] [Field F] {Psrc : Fin 2 → Subgroup X}
variable {Q : MarkedQuotient Psrc} {split : SplitData Q.tits}
variable {m : ℕ} {hm : 0 < m} {σ : F ≃+* F}
local notation "P" => binaryParameters m hm

theorem quotient_nontrivial (Q : MarkedQuotient Psrc) : Nontrivial (X ⧸ Q.D) := by
  by_contra h
  let : Subsingleton (X ⧸ Q.D) := not_nontrivial_iff_subsingleton.mp h
  exact (show (0 : Fin 2) ≠ 1 by decide)
    (Q.simple_injective (Subsingleton.elim (Q.simple 0) (Q.simple 1)))

namespace BruhatRootData
variable {d : PositiveRootData Q split m hm σ} (b : BruhatRootData d)

/-- The actual source quotient, recognized using only its explicit root relations. -/
def quotientEquiv : (X ⧸ Q.D) ≃* BinaryCarrier m hm :=
  let := quotient_nontrivial Q
  b.signed.roots.equivalence b.relations b.generates

theorem quotientEquiv_short (s : Bool) (i : Fin 3) (t : F) :
    b.quotientEquiv (if s then d.shortRoot i (.ofAdd t) else b.signed.negativeShort i (.ofAdd t)) =
      (SignedModel.roots m hm).shortSigned s i (d.scalars.extension t) := by
  let := quotient_nontrivial Q
  have h := b.signed.roots.equivalence_short b.relations b.generates s i (d.scalars.extension t)
  have he := b.presentationHom_short s i t
  rw [BruhatRootData.presentationHom, Presentation.lift_short] at he
  exact (congrArg b.quotientEquiv he.symm).trans h

theorem quotientEquiv_long (s : Bool) (i : Fin 3) (t : ScalarMarking.SourceFixed (σ := σ)) :
    b.quotientEquiv (if s then d.longRoot i (.ofAdd t) else b.signed.negativeLong i (.ofAdd t)) =
      (SignedModel.roots m hm).longSigned s i (d.scalars.fixed t) := by
  let := quotient_nontrivial Q
  have h := b.signed.roots.equivalence_long b.relations b.generates s i (d.scalars.fixed t)
  have he := b.presentationHom_long s i t
  rw [BruhatRootData.presentationHom, Presentation.lift_long] at he
  exact (congrArg b.quotientEquiv he.symm).trans h

theorem quotientEquiv_nA (t) :
    b.quotientEquiv (b.signed.roots.nA t) = (SignedModel.roots m hm).nA t := by
  let := quotient_nontrivial Q
  exact b.signed.roots.equivalence_nA b.relations b.generates t

theorem quotientEquiv_nB (t) :
    b.quotientEquiv (b.signed.roots.nB t) = (SignedModel.roots m hm).nB t := by
  let := quotient_nontrivial Q
  exact b.signed.roots.equivalence_nB b.relations b.generates t

theorem quotientEquiv_torus (p) :
    b.quotientEquiv (b.signed.roots.torus p) = (SignedModel.roots m hm).torus p := by
  let := quotient_nontrivial Q
  exact b.signed.roots.equivalence_torus b.relations b.generates p

theorem quotientEquiv_unipotent : split.U.map b.quotientEquiv.toMonoidHom = Parabolics.unipotent P := by
  let := quotient_nontrivial Q
  rw [← d.positive]
  exact b.signed.roots.equivalence_positive b.relations b.generates

/-- Parameterized arm Weyl words retain the original cubic-field unit. -/
theorem quotientEquiv_original_nA (t : Fˣ) :
    b.quotientEquiv (d.shortRoot 0 (.ofAdd t.val) * b.signed.negativeShort 0 (.ofAdd (t⁻¹).val) *
      d.shortRoot 0 (.ofAdd t.val)) =
    (SignedModel.roots m hm).nA (Units.map d.scalars.extension.toMonoidHom t) := by
  have hp (x : F) : b.quotientEquiv (d.shortRoot 0 (.ofAdd x)) =
      (SignedModel.roots m hm).shortValue 0 (d.scalars.extension x) :=
    b.quotientEquiv_short true 0 x
  have hn (x : F) : b.quotientEquiv (b.signed.negativeShort 0 (.ofAdd x)) =
      (SignedModel.roots m hm).negativeShortValue 0 (d.scalars.extension x) :=
    b.quotientEquiv_short false 0 x
  simp only [map_mul,hp,hn,SignedRoots.nA,← map_inv]
  rfl

/-- Parameterized central Weyl words use the induced fixed-field marking. -/
theorem quotientEquiv_original_nB (t : (ScalarMarking.SourceFixed (σ := σ))ˣ) :
    b.quotientEquiv (d.longRoot 0 (.ofAdd t.val) * b.signed.negativeLong 0 (.ofAdd (t⁻¹).val) *
      d.longRoot 0 (.ofAdd t.val)) =
    (SignedModel.roots m hm).nB (Units.map d.scalars.fixed.toMonoidHom t) := by
  have hp (x : ScalarMarking.SourceFixed (σ := σ)) : b.quotientEquiv (d.longRoot 0 (.ofAdd x)) =
      (SignedModel.roots m hm).longValue 0 (d.scalars.fixed x) :=
    b.quotientEquiv_long true 0 x
  have hn (x : ScalarMarking.SourceFixed (σ := σ)) : b.quotientEquiv (b.signed.negativeLong 0 (.ofAdd x)) =
      (SignedModel.roots m hm).negativeLongValue 0 (d.scalars.fixed x) :=
    b.quotientEquiv_long false 0 x
  simp only [map_mul,hp,hn,SignedRoots.nB,← map_inv]
  rfl

/-- Full normalizers identify the entire Borel, not just its positive subgroup. -/
theorem quotientEquiv_borel : Q.tits.B.map b.quotientEquiv.toMonoidHom = Parabolics.borel P := by
  rw [← split.normalizer_eq, map_normalizer_eq_of_bijective _ b.quotientEquiv.bijective,
    b.quotientEquiv_unipotent, ConcreteBruhat.normalizer_unipotent_eq_borel P rfl]
end BruhatRootData

/-- Literal Weyl markings on the same quotient; no parabolic/model equality is input. -/
structure RootData (Q : MarkedQuotient Psrc) (split : SplitData Q.tits)
    (m : ℕ) (hm : 0 < m) (σ : F ≃+* F) (armIndex : Fin 2) where
  positive : PositiveRootData Q split m hm σ
  bruhat : BruhatRootData positive
  arms_mem : bruhat.signed.roots.nA 1 ∈ Q.tits.N
  arms_class : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
    ⟨bruhat.signed.roots.nA 1,arms_mem⟩ = Q.simple armIndex
  central_mem : bruhat.signed.roots.nB 1 ∈ Q.tits.N
  central_class : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N)
    ⟨bruhat.signed.roots.nB 1,central_mem⟩ = Q.simple (1-armIndex)

private theorem singleton_eq_sup {Y : Type*} [Group Y]
    (T : Theory.AlgebraicGroup.TitsSystem (X := Y)) (n : T.N) :
    T.standardParabolic {QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n} =
      T.B ⊔ Subgroup.closure {(n : Y)} := by
  let s := QuotientGroup.mk' ((T.B ⊓ T.N).subgroupOf T.N) n
  have hncell : (n : Y) ∈ T.bruhatCell s := T.representative_mem_bruhatCell s n rfl
  apply le_antisymm
  · apply T.standardParabolic_le _ le_sup_left
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst t
    exact T.bruhatCell_subset_of_mem _ le_sup_left hncell
      (Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton _)))
  · apply sup_le (T.B_le_standardParabolic _)
    apply (Subgroup.closure_le _).mpr
    rintro g (rfl : g = _)
    exact T.bruhatCell_subset_standardParabolic_of_mem (Set.mem_singleton s) hncell

namespace RootData
variable {armIndex : Fin 2} (d : RootData Q split m hm σ armIndex)

/-- Both oriented endpoints are determined by the exact quotient Weyl classes. -/
theorem quotientEquiv_arms :
    (Q.tits.standardParabolic {Q.simple armIndex}).map d.bruhat.quotientEquiv.toMonoidHom =
      Parabolics.parabolic P .arms := by
  rw [← d.arms_class, singleton_eq_sup, Subgroup.map_sup, MonoidHom.map_closure,
    Set.image_singleton, d.bruhat.quotientEquiv_borel]
  change Parabolics.borel P ⊔ Subgroup.closure {d.bruhat.quotientEquiv (d.bruhat.signed.roots.nA 1)} = _
  rw [d.bruhat.quotientEquiv_nA, SignedModel.nA_one,
    ← ConcreteBruhat.borel_sup_negativeGenerators_eq P rfl,
    ConcreteBruhat.negativeGenerators_generate P rfl]

theorem quotientEquiv_central :
    (Q.tits.standardParabolic {Q.simple (1-armIndex)}).map d.bruhat.quotientEquiv.toMonoidHom =
      Parabolics.parabolic P .central := by
  rw [← d.central_class, singleton_eq_sup, Subgroup.map_sup, MonoidHom.map_closure,
    Set.image_singleton, d.bruhat.quotientEquiv_borel]
  change Parabolics.borel P ⊔ Subgroup.closure {d.bruhat.quotientEquiv (d.bruhat.signed.roots.nB 1)} = _
  rw [d.bruhat.quotientEquiv_nB, SignedModel.nB_one,
    ← ConcreteBruhat.borel_sup_negativeGenerators_eq P rfl,
    ConcreteBruhat.negativeGenerators_generate P rfl]
end RootData

def flagVertex (m : ℕ) (hm : 0 < m) (armIndex i : Fin 2) : Subgroup (BinaryCarrier m hm) :=
  if i = armIndex then Parabolics.parabolic (binaryParameters m hm) .arms else Parabolics.parabolic (binaryParameters m hm) .central

theorem borel_le_flagVertex (m : ℕ) (hm : 0 < m) (armIndex i : Fin 2) :
    Parabolics.borel (binaryParameters m hm) ≤ flagVertex m hm armIndex i := by
  unfold flagVertex
  split <;> apply Parabolics.borel_le_parabolic

def flagAmalgam (m : ℕ) (hm : 0 < m) (armIndex : Fin 2) :
    RankTwoAmalgam (flagVertex m hm armIndex 0) (Parabolics.borel (binaryParameters m hm)) (flagVertex m hm armIndex 1) :=
  RankTwoAmalgam.ofSubgroups _ _ _ (borel_le_flagVertex m hm armIndex 0)
    (borel_le_flagVertex m hm armIndex 1)

namespace RootData
variable {armIndex : Fin 2} (d : RootData Q split m hm σ armIndex)

theorem quotientEquiv_vertex (i : Fin 2) :
    (Q.tits.standardParabolic {Q.simple i}).map d.bruhat.quotientEquiv.toMonoidHom =
      flagVertex m hm armIndex i := by
  by_cases h : i = armIndex
  · subst i
    simpa [flagVertex] using d.quotientEquiv_arms
  · have hi : i = 1 - armIndex := by
      fin_cases i <;> fin_cases armIndex <;> simp_all
    rw [flagVertex,if_neg h,hi]
    exact d.quotientEquiv_central

def restrictEquiv {Y Z : Type*} [Group Y] [Group Z] (e : Y ≃* Z)
    (A : Subgroup Y) (C : Subgroup Z) (h : A.map e.toMonoidHom = C) : A ≃* C :=
  (A.equivMapOfInjective e.toMonoidHom e.injective).trans (MulEquiv.subgroupCongr h)

/-- One ambient equivalence restricts to both endpoints and the whole Borel. -/
def markedIso : RankTwoAmalgam.Iso Q.standardAmalgam (flagAmalgam m hm armIndex) where
  left := restrictEquiv d.bruhat.quotientEquiv _ _ (d.quotientEquiv_vertex 0)
  middle := restrictEquiv d.bruhat.quotientEquiv _ _ d.bruhat.quotientEquiv_borel
  right := restrictEquiv d.bruhat.quotientEquiv _ _ (d.quotientEquiv_vertex 1)
  left_commutes b := by
    apply Subtype.ext
    change d.bruhat.quotientEquiv (Q.standardAmalgam.left b : X ⧸ Q.D) = d.bruhat.quotientEquiv (b : X ⧸ Q.D)
    obtain ⟨c,rfl⟩ := Q.markedIso.middle.surjective b
    rw [← Q.markedIso.left_commutes, Q.markedIso_left_apply, Q.markedIso_middle_apply]
    rfl
  right_commutes b := by
    apply Subtype.ext
    change d.bruhat.quotientEquiv (Q.standardAmalgam.right b : X ⧸ Q.D) = d.bruhat.quotientEquiv (b : X ⧸ Q.D)
    obtain ⟨c,rfl⟩ := Q.markedIso.middle.surjective b
    rw [← Q.markedIso.right_commutes, Q.markedIso_right_apply, Q.markedIso_middle_apply]
    rfl

@[simp] theorem markedIso_left_apply (a : Q.tits.standardParabolic {Q.simple 0}) :
    (d.markedIso.left a : BinaryCarrier m hm) = d.bruhat.quotientEquiv a := rfl
@[simp] theorem markedIso_middle_apply (a : Q.tits.B) :
    (d.markedIso.middle a : BinaryCarrier m hm) = d.bruhat.quotientEquiv a := rfl
@[simp] theorem markedIso_right_apply (a : Q.tits.standardParabolic {Q.simple 1}) :
    (d.markedIso.right a : BinaryCarrier m hm) = d.bruhat.quotientEquiv a := rfl

/-- Compose the actual quotient map, preserving its endpoint-disjoint kernels and full overlap. -/
def quotientMarkedIso : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (Psrc 0) (Psrc 0 ⊓ Psrc 1) (Psrc 1) inf_le_left inf_le_right)
    (flagAmalgam m hm armIndex) := Q.markedIso.trans d.markedIso

@[simp] theorem quotientMarkedIso_left_apply (a : Psrc 0) :
    (d.quotientMarkedIso.left a : BinaryCarrier m hm) = d.bruhat.quotientEquiv (Q.q a) := by
  change d.bruhat.quotientEquiv (Q.markedIso.left a : X ⧸ Q.D) = _
  rw [Q.markedIso_left_apply]
@[simp] theorem quotientMarkedIso_middle_apply (a : (Psrc 0 ⊓ Psrc 1 : Subgroup X)) :
    (d.quotientMarkedIso.middle a : BinaryCarrier m hm) = d.bruhat.quotientEquiv (Q.q a) := by
  change d.bruhat.quotientEquiv (Q.markedIso.middle a : X ⧸ Q.D) = _
  rw [Q.markedIso_middle_apply]
@[simp] theorem quotientMarkedIso_right_apply (a : Psrc 1) :
    (d.quotientMarkedIso.right a : BinaryCarrier m hm) = d.bruhat.quotientEquiv (Q.q a) := by
  change d.bruhat.quotientEquiv (Q.markedIso.right a : X ⧸ Q.D) = _
  rw [Q.markedIso_right_apply]
end RootData
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.TrialityPresentation
