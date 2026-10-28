module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RegularFactorCover

/-!
# The original factor's faithful projective panel image

The original factor map followed by the local permutation action has exactly
Z(L/O₂(L)) as kernel. The forward inclusion uses the already proved central
cover kernel and the injective factor-cover map. Conversely, a central
quotient element fixes every Sylow-normalizer coset; transport through the
literal original Borel-panel bijection gives the reverse inclusion.

Its image is normal in the same local group. No perfectness or (2B) is used
for either assertion. With (2B) and equality of root and quotient-Sylow
orders, the map is onto, both cover kernels equal their centers, and the
original root/action square commutes. UnitaryFactorAction uses these results
to retain the actual projective and scalar kernels, including q = 2.
Source: Fong--Seitz I (2A)--(2B), (5B)--(5C); AS F.1.1--3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)

/-- The literal factor two-core quotient acting on the original panel. -/
def factorQuotientLocalMap : ((L i) ⧸ pCore 2 (L i)) →* localGroup Q split i :=
  (LocalCover.projection Q split i).comp (factorQuotientCoverMap Q e h split i)

/-- Original factor representatives retain their actual panel action. -/
@[simp] theorem factorQuotientLocalMap_mk (a : L i) :
    (factorQuotientLocalMap Q e h split i (QuotientGroup.mk' (pCore 2 (L i)) a) :
      Equiv.Perm (Panel Q i)) = localAction Q split i (factorIntoClosure Q e h split i a) := by
  change (LocalCover.projection Q split i (factorQuotientCoverMap Q e h split i
    (QuotientGroup.mk' (pCore 2 (L i)) a)) : Equiv.Perm (Panel Q i)) = _
  rw [factorQuotientCoverMap_mk, LocalCover.projection_mk]

variable [Finite (L i)]
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)

include hT in
/-- The full action kernel on the original factor quotient is exactly its center. -/
theorem factorQuotientLocalMap_ker :
    (factorQuotientLocalMap Q e h split i).ker = center ((L i) ⧸ pCore 2 (L i)) := by
  apply le_antisymm
  · intro z hz
    have hc := LocalCover.projection_ker_central Q split i hz
    apply mem_center_iff.mpr
    intro x
    apply factorQuotientCoverMap_injective Q e h split i
    simp only [map_mul]
    exact mem_center_iff.mp hc _
  · intro z hz
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (L i)) z
    have hfix : ∀ c : ((L i) ⧸ pCore 2 (L i)) ⧸ sylowNormalizer (quotientSylow T),
        QuotientGroup.mk' (pCore 2 (L i)) a • c = c := by
      intro c
      induction c using Quotient.inductionOn with
      | h c =>
        change QuotientGroup.mk (QuotientGroup.mk' (pCore 2 (L i)) a * c) = QuotientGroup.mk c
        rw [← mem_center_iff.mp hz c]
        apply QuotientGroup.eq.mpr
        have hn := center_le_normalizer (quotientSylow T : Set _) hz
        simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] using
          (sylowNormalizer (quotientSylow T)).inv_mem hn
    change factorQuotientLocalMap Q e h split i (QuotientGroup.mk' _ a) = 1
    apply Subtype.ext
    ext c
    rw [factorQuotientLocalMap_mk, localAction_eq_panelAction]
    obtain ⟨ω,rfl⟩ := (localBorelPanel Q e h i).surjective c
    have he : (inclusion (localClosure_le_parabolic Q split i))
        (factorIntoClosure Q e h split i a) = factorInEndpoint Q e i a := by
      apply Subtype.ext
      exact factorIntoClosure_coe Q e h split i a
    change inclusion (localClosure_le_parabolic Q split i)
      (factorIntoClosure Q e h split i a) • localBorelPanel Q e h i ω = _
    rw [he]
    rw [← localBorelPanel_smul]
    apply congrArg (localBorelPanel Q e h i)
    apply (localBorelCosetEquiv (L i) S T hT).injective
    rw [localBorelCosetEquiv_smul]
    exact hfix _

omit [Finite (L i)] in
/-- The factor image is normal in the same faithful local group, before (2B). -/
theorem factorQuotientLocalMap_range_normal : (factorQuotientLocalMap Q e h split i).range.Normal := by
  let A := (factorMap Q e i).range
  let C := localClosure Q split i
  have hn : (A.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    ((localClosure_le_parabolic Q split i).trans (factor_parabolic_normalizes Q e h i))
  have hr : (factorIntoClosure Q e h split i).range = A.subgroupOf C := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨a,(factorIntoClosure_coe Q e h split i a).symm⟩
    · rintro ⟨a,ha⟩
      exact ⟨a,Subtype.ext ((factorIntoClosure_coe Q e h split i a).trans ha)⟩
  have he : (factorQuotientLocalMap Q e h split i).range =
      (A.subgroupOf C).map (localAction Q split i).rangeRestrict := by
    rw [← hr, ← MonoidHom.range_comp]
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (L i)) z
      exact ⟨a,Subtype.ext (factorQuotientLocalMap_mk Q e h split i a).symm⟩
    · rintro ⟨a,rfl⟩
      exact ⟨QuotientGroup.mk' (pCore 2 (L i)) a,
        Subtype.ext (factorQuotientLocalMap_mk Q e h split i a)⟩
  rw [he]
  exact hn.map _ (localAction Q split i).rangeRestrict_surjective

variable (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T))

/-- The regular factor-cover equivalence commutes with the original panel action. -/
theorem factorQuotientLocalMap_cover (z : (L i) ⧸ pCore 2 (L i)) :
    factorQuotientLocalMap Q e h split i z = LocalCover.projection Q split i
      (factorQuotientCoverEquiv Q e h split i T hT hV hc z) := by
  induction z using QuotientGroup.induction_on with
  | H z =>
    change LocalCover.projection Q split i (factorQuotientCoverMap Q e h split i
      (QuotientGroup.mk' _ z)) = LocalCover.projection Q split i
        (factorQuotientCoverEquiv Q e h split i T hT hV hc (QuotientGroup.mk' _ z))
    rw [factorQuotientCoverMap_mk,factorQuotientCoverEquiv_mk]

include hT hV hc in
/-- The actual factor action fills the local group once the regularity premise holds. -/
theorem factorQuotientLocalMap_surjective :
    Function.Surjective (factorQuotientLocalMap Q e h split i) := by
  intro y
  obtain ⟨x,rfl⟩ := LocalCover.projection_surjective Q split i y
  refine ⟨(factorQuotientCoverEquiv Q e h split i T hT hV hc).symm x,?_⟩
  rw [factorQuotientLocalMap_cover Q e h split i T hT hV hc,MulEquiv.apply_symm_apply]

/-- The root comparison uses the same panel action, even when scalars survive. -/
theorem factorQuotientLocalMap_regularRoot (r : rankOne Q split i) :
    factorQuotientLocalMap Q e h split i (regularFactorRootEquiv Q e h split i T hT hV hc r) =
      RootLocalCover.projection Q split i r := by
  rw [factorQuotientLocalMap_cover Q e h split i T hT hV hc,
    regularFactorRootEquiv_cover]
  apply Subtype.ext
  rw [LocalCover.projection_mk,RootLocalCover.projection_apply]

/-- The root/action square after pulling back through the original endpoint marking. -/
theorem factorQuotientLocalMap_originalRoot (r : originalRankOne Q e split i) :
    factorQuotientLocalMap Q e h split i
      (regularOriginalFactorRootEquiv Q e h split i T hT hV hc r) =
        originalRootProjection Q e split i r := by
  rw [regularOriginalFactorRootEquiv_apply]
  rw [factorQuotientLocalMap_regularRoot]
  apply Subtype.ext
  rw [RootLocalCover.projection_apply,originalRootProjection_apply]

include e h hT hV hc in
/-- The exact whole-cover kernel, including all central scalar covers. -/
theorem regular_cover_projection_ker_eq_center :
    (LocalCover.projection Q split i).ker = center (LocalCover.CoverGroup Q split i) := by
  apply le_antisymm (LocalCover.projection_ker_central Q split i)
  intro z hz
  let a := factorQuotientCoverEquiv Q e h split i T hT hV hc
  have hc' := MulEquivClass.apply_mem_center a.symm hz
  have hk : a.symm z ∈ (factorQuotientLocalMap Q e h split i).ker := by
    rw [factorQuotientLocalMap_ker Q e h split i T hT]
    exact hc'
  change factorQuotientLocalMap Q e h split i (a.symm z) = 1 at hk
  rw [factorQuotientLocalMap_cover Q e h split i T hT hV hc] at hk
  change LocalCover.projection Q split i (a (a.symm z)) = 1 at hk
  change LocalCover.projection Q split i z = 1
  simpa only [MulEquiv.apply_symm_apply] using hk

include e h hT hV hc in
/-- The canonical root action has exactly its center as kernel, without perfectness. -/
theorem regular_root_projection_ker_eq_center :
    (RootLocalCover.projection Q split i).ker = center (rankOne Q split i) := by
  apply le_antisymm (RootLocalCover.projection_ker_central Q split i)
  intro z hz
  let a := RootLocalCover.coverEquiv Q split i hV
  have hc' := MulEquivClass.apply_mem_center a hz
  have hk : a z ∈ (LocalCover.projection Q split i).ker := by
    rw [regular_cover_projection_ker_eq_center Q e h split i T hT hV hc]
    exact hc'
  change LocalCover.projection Q split i (a z) = 1 at hk
  change RootLocalCover.projection Q split i z = 1
  apply Subtype.ext
  have he := congrArg Subtype.val hk
  change (LocalCover.projection Q split i (RootLocalCover.coverEquiv Q split i hV z) :
    Equiv.Perm (Panel Q i)) = 1 at he
  rw [RootLocalCover.coverEquiv_apply,LocalCover.projection_mk] at he
  rw [RootLocalCover.projection_apply]
  exact he

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
