module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.FactorPanelAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryLocal

/-!
# Actual unitary normal subgroups of the local permutation group

For every positive binary parameter, the projective factor acts faithfully
on the same marked panel. For a special-unitary factor, the exact central
kernel from FactorPanelAction equals the kernel of the literal scalar map
SU₃ → PSU₃. Descending through this surjection gives an injective PSU₃ map
with normal image and the original factor representative equation.

These embeddings do not use (2B), perfectness, or q > 2. Thus the binary
case retains a genuine normal PSU₃(2), rather than an unrelated type label.
If (2B) is supplied, the proved root/Sylow count makes the embeddings onto.
The resulting equivalences are used by UnitaryFactorComparisons to transport
both original cover squares. No type-VI exclusion or ambient recognition is
claimed here.
Source: Fong--Seitz I (2A)--(2B), (5B)--(5C); AS F.1.1--3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
open HermitianForm
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  [Finite (L i)] (T : Sylow 2 (L i))
  (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
  {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 0 < n) (hc : Nat.card E = (2^n)^2)
  (hconj : ∀ x, J.conj x = x^(2^n))

def projectiveUnitaryFactorLocalMap
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    ProjectiveSpecialUnitaryMatrixGroup J →* localGroup Q split i :=
  (factorQuotientLocalMap Q e h split i).comp μ.symm.toMonoidHom

include hT hn hc hconj in
theorem projectiveUnitaryFactorLocalMap_injective
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Function.Injective (projectiveUnitaryFactorLocalMap Q e h split i J μ) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro z hz
  have hm : μ.symm z ∈ (factorQuotientLocalMap Q e h split i).ker := hz
  rw [factorQuotientLocalMap_ker Q e h split i T hT] at hm
  have hh := MulEquivClass.apply_mem_center μ hm
  change μ (μ.symm z) ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) at hh
  rwa [MulEquiv.apply_symm_apply,EvenProjectiveComparison.center_eq_bot J hn hc hconj] at hh

omit [Finite (L i)] [Finite E] in
@[simp] theorem projectiveUnitaryFactorLocalMap_mk
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) (a : L i) :
    projectiveUnitaryFactorLocalMap Q e h split i J μ
      (μ (QuotientGroup.mk' (pCore 2 (L i)) a)) =
      factorQuotientLocalMap Q e h split i (QuotientGroup.mk' (pCore 2 (L i)) a) := by
  change factorQuotientLocalMap Q e h split i (μ.symm (μ _)) = _
  rw [MulEquiv.symm_apply_apply]

omit [Finite (L i)] [Finite E] in
theorem projectiveUnitaryFactorLocalMap_range
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    (projectiveUnitaryFactorLocalMap Q e h split i J μ).range =
      (factorQuotientLocalMap Q e h split i).range := by
  rw [projectiveUnitaryFactorLocalMap,MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr μ.symm.surjective,← MonoidHom.range_eq_map]

omit [Finite (L i)] [Finite E] in
theorem projectiveUnitaryFactorLocalMap_range_normal
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    (projectiveUnitaryFactorLocalMap Q e h split i J μ).range.Normal := by
  rw [projectiveUnitaryFactorLocalMap_range]
  exact factorQuotientLocalMap_range_normal Q e h split i

include hT hn hc hconj in
private theorem special_factor_scalar_kernel
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    ((factorQuotientLocalMap Q e h split i).comp ν.symm.toMonoidHom).ker =
      J.specialToProjective.ker := by
  rw [← MonoidHom.comap_ker, factorQuotientLocalMap_ker Q e h split i T hT,
    J.specialToProjective_ker_eq_center (EvenProjectiveComparison.center_eq_bot J hn hc hconj)]
  ext z
  constructor
  · intro hz
    have hh := MulEquivClass.apply_mem_center ν hz
    change ν (ν.symm z) ∈ center J.specialSubgroup at hh
    simpa only [MulEquiv.apply_symm_apply] using hh
  · exact MulEquivClass.apply_mem_center ν.symm

def specialUnitaryFactorLocalMap
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    ProjectiveSpecialUnitaryMatrixGroup J →* localGroup Q split i :=
  J.specialToProjective.liftOfSurjective J.specialToProjective_surjective
    ⟨(factorQuotientLocalMap Q e h split i).comp ν.symm.toMonoidHom,
      (special_factor_scalar_kernel Q e h split i T hT J hn hc hconj ν).ge⟩

@[simp] theorem specialUnitaryFactorLocalMap_special
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) (z : J.specialSubgroup) :
    specialUnitaryFactorLocalMap Q e h split i T hT J hn hc hconj ν (J.specialToProjective z) =
      factorQuotientLocalMap Q e h split i (ν.symm z) := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem specialUnitaryFactorLocalMap_injective
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    Function.Injective (specialUnitaryFactorLocalMap Q e h split i T hT J hn hc hconj ν) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro z hz
  obtain ⟨a,rfl⟩ := J.specialToProjective_surjective z
  change specialUnitaryFactorLocalMap Q e h split i T hT J hn hc hconj ν (J.specialToProjective a) = 1 at hz
  rw [specialUnitaryFactorLocalMap_special] at hz
  have hh : a ∈ ((factorQuotientLocalMap Q e h split i).comp ν.symm.toMonoidHom).ker := hz
  rw [special_factor_scalar_kernel Q e h split i T hT J hn hc hconj ν] at hh
  exact hh

@[simp] theorem specialUnitaryFactorLocalMap_mk
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) (a : L i) :
    specialUnitaryFactorLocalMap Q e h split i T hT J hn hc hconj ν
      (J.specialToProjective (ν (QuotientGroup.mk' (pCore 2 (L i)) a))) =
      factorQuotientLocalMap Q e h split i (QuotientGroup.mk' (pCore 2 (L i)) a) := by
  rw [specialUnitaryFactorLocalMap_special,MulEquiv.symm_apply_apply]

theorem specialUnitaryFactorLocalMap_range
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    (specialUnitaryFactorLocalMap Q e h split i T hT J hn hc hconj ν).range =
      (factorQuotientLocalMap Q e h split i).range := by
  ext z
  constructor
  · rintro ⟨x,rfl⟩
    obtain ⟨a,rfl⟩ := J.specialToProjective_surjective x
    exact ⟨ν.symm a,(specialUnitaryFactorLocalMap_special Q e h split i T hT J hn hc hconj ν a).symm⟩
  · rintro ⟨x,rfl⟩
    refine ⟨J.specialToProjective (ν x),?_⟩
    rw [specialUnitaryFactorLocalMap_special,MulEquiv.symm_apply_apply]

theorem specialUnitaryFactorLocalMap_range_normal
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    (specialUnitaryFactorLocalMap Q e h split i T hT J hn hc hconj ν).range.Normal := by
  rw [specialUnitaryFactorLocalMap_range]
  exact factorQuotientLocalMap_range_normal Q e h split i

variable (hV : simpleRemainder Q split i ≤ localKernel Q i)

include hT hn hc hconj hV in
theorem projectiveUnitaryFactorLocalMap_surjective
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    Function.Surjective (projectiveUnitaryFactorLocalMap Q e h split i J μ) := by
  exact (factorQuotientLocalMap_surjective Q e h split i T hT hV
    (projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hc hconj μ)).comp
      μ.symm.surjective

def projectiveUnitaryFactorLocalEquiv
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  (MulEquiv.ofBijective (projectiveUnitaryFactorLocalMap Q e h split i J μ)
    ⟨projectiveUnitaryFactorLocalMap_injective Q e h split i T hT J hn hc hconj μ,
      projectiveUnitaryFactorLocalMap_surjective Q e h split i T hT J hn hc hconj hV μ⟩).symm

theorem projectiveUnitaryFactorLocalEquiv_factor
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (z : (L i) ⧸ pCore 2 (L i)) :
    projectiveUnitaryFactorLocalEquiv Q e h split i T hT J hn hc hconj hV μ
      (factorQuotientLocalMap Q e h split i z) = μ z := by
  have he : factorQuotientLocalMap Q e h split i z =
      projectiveUnitaryFactorLocalMap Q e h split i J μ (μ z) := by
    change _ = factorQuotientLocalMap Q e h split i (μ.symm (μ z))
    rw [MulEquiv.symm_apply_apply]
  rw [he]
  exact MulEquiv.symm_apply_apply _ _

include hV in
theorem specialUnitaryFactorLocalMap_surjective
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    Function.Surjective (specialUnitaryFactorLocalMap Q e h split i T hT J hn hc hconj ν) := by
  intro y
  obtain ⟨x,rfl⟩ := factorQuotientLocalMap_surjective Q e h split i T hT hV
    (specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J hn hc hconj ν) y
  refine ⟨J.specialToProjective (ν x),?_⟩
  rw [specialUnitaryFactorLocalMap_special,MulEquiv.symm_apply_apply]

def specialUnitaryFactorLocalEquiv
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  (MulEquiv.ofBijective (specialUnitaryFactorLocalMap Q e h split i T hT J hn hc hconj ν)
    ⟨specialUnitaryFactorLocalMap_injective Q e h split i T hT J hn hc hconj ν,
      specialUnitaryFactorLocalMap_surjective Q e h split i T hT J hn hc hconj hV ν⟩).symm

theorem specialUnitaryFactorLocalEquiv_factor
    (ν : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup)
    (z : (L i) ⧸ pCore 2 (L i)) :
    specialUnitaryFactorLocalEquiv Q e h split i T hT J hn hc hconj hV ν
      (factorQuotientLocalMap Q e h split i z) = J.specialToProjective (ν z) := by
  have he : factorQuotientLocalMap Q e h split i z =
      specialUnitaryFactorLocalMap Q e h split i T hT J hn hc hconj ν (J.specialToProjective (ν z)) := by
    rw [specialUnitaryFactorLocalMap_special,MulEquiv.symm_apply_apply]
  rw [he]
  exact MulEquiv.symm_apply_apply _ _

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
