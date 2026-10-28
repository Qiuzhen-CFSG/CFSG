module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ShortRootCentralizer
public import Theory.GroupTheory.NormalSubgroupTwoClassCover
/-!
# Exhaustive long and short classes in the binary plane radical

The literal long-root centralizer is the point endpoint. In the plane
endpoint its centralizer has order 192, while the short-root centralizer
has order 96. Their plane classes therefore have sizes five and ten.
Normality of the order-sixteen radical and these counts prove that its
nonidentity elements are precisely those two distinct classes.

Source: Aschbacher–Smith F.4.27 and F.4.43, ordinary U₄(2), pp.287 and 296.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.GroupTheory.CentralizerSmallKernelTransport
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.ModelClasses
open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour
open CFSG.Quasithin.ChapterF.UnitaryTwo
open ShortRootFixedFour ShortRootQuotient ShortRootFusion
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "L" => L2Matrix 1 hn
local notation "P" => pointParabolic 1 hn
local notation "R" => planeParabolic 1 hn
local notation "M" => ProjectiveGroup 1 hn

theorem matrix_long_centralizer_le_point :
    centralizer ({(longLocal F σ hσ).val} : Set (MatrixGroup 1 hn)) ≤ pointParabolicMatrix 1 hn := by
  intro g hg
  have he := congrArg (fun a : MatrixGroup 1 hn => a.val.val)
    (mem_centralizer_singleton_iff.mp hg)
  change g.val.val * unipotentMatrix F (longParameter F σ).val =
    unipotentMatrix F (longParameter F σ).val * g.val.val at he
  have h10 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 1 3) he
  have h20 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 2 3) he
  have h30 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 3 3) he
  simp [unipotentMatrix,longParameter,mul_apply,Fin.sum_univ_succ] at h10 h20 h30
  change g ∈ pointParabolicSU F (form F σ hσ)
  exact (mem_pointParabolicSU F (form F σ hσ) g).mpr ⟨h10,h20,h30⟩

theorem model_long_centralizer : centralizer ({longPoint.val} : Set M) = P := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g,rfl⟩ := project_surjective F (standardForm 1 hn) x
    refine ⟨g,matrix_long_centralizer_le_point ?_,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply projection_injective 1 hn
    have he := mem_centralizer_singleton_iff.mp hx
    change projection 1 hn g * projection 1 hn (longLocal F σ hσ).val =
      projection 1 hn (longLocal F σ hσ).val * projection 1 hn g at he
    exact (map_mul (projection 1 hn) _ _).trans (he.trans (map_mul (projection 1 hn) _ _).symm)
  · intro g hg
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mem_center_iff.mp (PointCore.rootSubgroup_central longPoint_mem_root) ⟨g,hg⟩))

def longRight : R := matrixPlaneEquiv modelLong
def shortRight : R := matrixPlaneEquiv modelShort

theorem right_long_centralizer : centralizer ({longRight} : Set R) = (P).subgroupOf R := by
  ext x
  rw [mem_centralizer_singleton_iff]
  change _ ↔ x.val ∈ P
  rw [← model_long_centralizer,mem_centralizer_singleton_iff]
  exact Subtype.ext_iff

theorem right_long_centralizer_card : Nat.card (centralizer ({longRight} : Set R)) = 192 := by
  rw [right_long_centralizer,← inf_subgroupOf_right,exact_overlap]
  exact (Nat.card_congr (subgroupOfEquivOfLe (show overlap 1 hn ≤ R by rw [← exact_overlap]; exact inf_le_right)).toEquiv).trans
    BinaryCompletion.middle_card

theorem local_long_centralizer_card : Nat.card (centralizer ({modelLong} : Set L)) = 192 :=
  (Nat.card_congr (centralizerEquiv matrixPlaneEquiv modelLong).toEquiv).trans right_long_centralizer_card

theorem local_short_centralizer_card : Nat.card (centralizer ({modelShort} : Set L)) = 96 :=
  ShortRoot.centralizer_card

theorem local_long_ne_one : modelLong ≠ 1 := by
  intro he
  have h := congrArg (fun x : L => x.val.val.val 0 3) he
  exact one_ne_zero h

theorem local_short_ne_one : modelShort ≠ 1 := by
  intro he
  have h := congrArg (fun x : L => x.val.val.val 0 2) he
  exact one_ne_zero h

theorem local_long_short_nonconjugate : ¬ IsConj modelLong modelShort := by
  intro hh
  obtain ⟨g,hg⟩ := isConj_iff.mp hh
  have he := Nat.card_congr (centralizerEquiv (MulAut.conj g) modelLong).toEquiv
  change Nat.card (centralizer ({modelLong} : Set L)) =
    Nat.card (centralizer ({g * modelLong * g⁻¹} : Set L)) at he
  rw [hg,local_long_centralizer_card,local_short_centralizer_card] at he
  omega

theorem local_long_class_card : Nat.card {x : L // IsConj modelLong x} = 5 := by
  have h := ConjClasses.nat_card_carrier_mul_card_centralizer modelLong
  have hl : Nat.card L = 960 :=
    (Nat.card_congr matrixPlaneEquiv.toEquiv).trans BinaryCompletion.plane_card
  rw [local_long_centralizer_card,hl] at h
  change Nat.card {x : L // IsConj modelLong x} * 192 = 960 at h
  omega

theorem local_short_class_card : Nat.card {x : L // IsConj modelShort x} = 10 := by
  have h := ConjClasses.nat_card_carrier_mul_card_centralizer modelShort
  have hl : Nat.card L = 960 :=
    (Nat.card_congr matrixPlaneEquiv.toEquiv).trans BinaryCompletion.plane_card
  rw [local_short_centralizer_card,hl] at h
  change Nat.card {x : L // IsConj modelShort x} * 96 = 960 at h
  omega

theorem local_radical_classes (x : L) (hx : x ∈ radical F σ hσ) :
    x = 1 ∨ IsConj modelLong x ∨ IsConj modelShort x := by
  apply Subgroup.ConjugacyClassCover.two_class_cover (radical F σ hσ) modelLong modelShort
    (radicalEquiv F σ hσ (Multiplicative.ofAdd (longParameter F σ))).property
    (radicalEquiv F σ hσ (Multiplicative.ofAdd (shortParameter F σ))).property
    local_long_ne_one local_short_ne_one local_long_short_nonconjugate _ x hx
  change 1 + Nat.card {x : L // IsConj modelLong x} + Nat.card {x : L // IsConj modelShort x} = _
  rw [local_long_class_card,local_short_class_card]
  exact (L2MatrixRadical_card 1 hn).symm

end CFSG.Quasithin.ChapterF.UnitaryTwo.ModelClasses
