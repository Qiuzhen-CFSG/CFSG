module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OddOuterPanel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearLocal
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex

/-!
# Fong--Seitz (2B) for original Suzuki endpoints of positive parameter

The actual original factor is normal in the entire marked parabolic and
supplements its full Borel. Transport its two-core quotient and Sylow
through the same injective factor map. The odd-outer panel theorem then
applies to the concrete Suzuki quotient: its center is trivial, its full
outer index is odd, and the already proved panel count identifies its
quotient-Sylow order with the canonical root order.

Thus the canonical remainder lies in the full panel kernel for every
positive Suzuki parameter, without assuming the original factor perfect.
Pullback identifies the remainder with the original parabolic two-core.
On the perfect-factor branch, positivity is proved from the original
quotient; substituting (2B) into the checked local recognition removes the
extra premise from both the permutation-group and whole-root-cover
isomorphisms, retaining all original quotient representatives.

Source: Fong--Seitz I (2B), pp.7--9, and (5C), pp.25--26;
Aschbacher--Smith F.1.1--3, pp.259--260. The Suzuki outer calculation is
GLS3 2.5.12(b--f), as used in GLS4 4.3.1. Parameter zero, the nonlinear
unitary branch, full endpoint recognition and seven-row assembly remain
separate obligations. The original full-Borel amalgam marking and split
quotient remain genuine earlier-source inputs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
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
  [Finite (L i)]
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)

include e h hT in
/-- Transfer the odd-outer criterion through the original factor and its
actual two-core quotient, preserving the full endpoint and Borel. -/
theorem remainder_le_kernel_of_factor_odd_outer
    (hz : center ((L i) ⧸ pCore 2 (L i)) = ⊥)
    (ho : Odd (MulAut.conj : ((L i) ⧸ pCore 2 (L i)) →*
      MulAut ((L i) ⧸ pCore 2 (L i))).range.index)
    (hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T)) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let f := factorMap Q e i
  let A := f.range
  let a : L i ≃* A := MonoidHom.ofInjective (factorMap_injective Q e i)
  let c := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let T' := T.mapSurjective (f := a.toMonoidHom) a.surjective
  have hTA : (T' : Subgroup A).map A.subtype = (T : Subgroup (L i)).map f := by
    change ((T : Subgroup (L i)).map a.toMonoidHom).map A.subtype = _
    rw [map_map]
    rfl
  have hTU : (T : Subgroup (L i)).map f ≤ split.U := by
    apply map_le_iff_le_comap.mpr
    rw [factor_unipotent_comap Q e h split i, ← hT]
    intro t ht
    exact mem_map_of_mem (L i).subtype ht
  have hgen : A ⊔ Q.tits.B = Q.tits.standardParabolic {Q.simple i} := by
    have he := congrArg (Subgroup.map (Q.tits.standardParabolic {Q.simple i}).subtype)
      (factorInEndpoint_generates_panel Q e h i)
    rw [Subgroup.map_sup, ← MonoidHom.range_comp,
      map_subgroupOf_eq_of_le (Q.tits.B_le_standardParabolic _),
      ← MonoidHom.range_eq_map, range_subtype] at he
    exact he
  apply PanelKernel.remainder_le_kernel_of_odd_outer Q split i A
    (factor_parabolic_normalizes Q e h i) hgen T' (hTA ▸ hTU)
  · apply eq_bot_iff.mpr
    intro z hz'
    have hz'' := MulEquivClass.apply_mem_center c.symm hz'
    change c.symm z ∈ center ((L i) ⧸ pCore 2 (L i)) at hz''
    rw [hz, mem_bot] at hz''
    exact c.symm.injective (hz''.trans c.symm.map_one.symm)
  · change Odd (Nat.card (MulAut.Outer (A ⧸ pCore 2 A)))
    rw [← Nat.card_congr (MulAut.outerCongr c).toEquiv]
    exact ho
  · rw [hc]
    change Nat.card ((T : Subgroup (L i)).map (QuotientGroup.mk' (pCore 2 (L i)))) = _
    rw [← relIndex_ker, QuotientGroup.ker_mk',
      ← relIndex_ker, QuotientGroup.ker_mk']
    change (pCore 2 (L i)).relIndex T =
      (pCore 2 A).relIndex ((T : Subgroup (L i)).map a.toMonoidHom)
    rw [← pCore_map_iso 2 a]
    exact (relIndex_map_map_of_injective (f := a.toMonoidHom) _ _ a.injective).symm

include e h hT in
/-- Positive Suzuki parameters satisfy (2B), independently of original perfectness. -/
theorem suzuki_remainder_le_kernel {m : ℕ} (hm : 0 < m)
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  have hz : center (SuzukiMatrixGroup m) = ⊥ := by
    let : IsSimpleGroup (SuzukiMatrixGroup m) :=
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    rcases (inferInstance : (center (SuzukiMatrixGroup m)).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exfalso
      apply BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm
      exact Group.isSolvable_of_comm (fun x y => by
        have hx : x ∈ center (SuzukiMatrixGroup m) := hz ▸ mem_top x
        exact (mem_center_iff.mp hx y).symm)
  apply remainder_le_kernel_of_factor_odd_outer Q e h split i T hT
  · apply eq_bot_iff.mpr
    intro z hz'
    have hz'' := MulEquivClass.apply_mem_center μ hz'
    change μ z ∈ center (SuzukiMatrixGroup m) at hz''
    rw [hz, mem_bot] at hz''
    exact μ.injective (hz''.trans μ.map_one.symm)
  · change Odd (Nat.card (MulAut.Outer ((L i) ⧸ pCore 2 (L i))))
    rw [Nat.card_congr (MulAut.outerCongr μ).toEquiv]
    exact suzuki_odd_outer_index m hm
  · exact suzuki_simpleRoot_card_eq_quotientSylow Q e h split i T hT μ

include e h hT in
/-- Perfectness excludes the parameter-zero model, so no bound is an extra input. -/
theorem suzuki_remainder_le_kernel_of_perfect (hp : Group.IsPerfect (L i))
    {m : ℕ} (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    simpleRemainder Q split i ≤ localKernel Q i :=
  suzuki_remainder_le_kernel Q e h split i T hT (suzuki_parameter_pos i hp μ) μ

include e h hT in
/-- The remainder is the original endpoint two-core, not the whole panel kernel. -/
theorem suzuki_remainder_comap {m : ℕ} (hm : 0 < m)
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    (simpleRemainder Q split i).comap (endpointMap Q e i) = pCore 2 (parabolic L S i) :=
  remainder_comap_of_containment Q e split i
    (suzuki_remainder_le_kernel Q e h split i T hT hm μ)

/-- The actual Suzuki local permutation group, with its (2B) premise proved. -/
def regularSuzukiLocalEquiv (hp : Group.IsPerfect (L i))
    {m : ℕ} (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    localGroup Q split i ≃* SuzukiMatrixGroup m :=
  suzukiLocalEquiv Q e h split i hp T hT μ
    (suzuki_remainder_le_kernel_of_perfect Q e h split i T hT hp μ)

@[simp] theorem regularSuzukiLocalEquiv_projection (hp : Group.IsPerfect (L i))
    {m : ℕ} (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (r : rankOne Q split i) :
    regularSuzukiLocalEquiv Q e h split i T hT hp μ (RootLocalCover.projection Q split i r) =
      μ (QuotientGroup.mk' (pCore 2 (L i)) (rankOneLift Q e h split i hp r)) :=
  suzukiLocalEquiv_projection Q e h split i hp T hT μ _ r

/-- The original whole-root cover now needs no separate local kernel premise. -/
def regularOriginalSuzukiCoverEquiv (hp : Group.IsPerfect (L i))
    {m : ℕ} (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m) :
    letI := originalRadicalInClosure_normal Q e h split i
    (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃*
      SuzukiMatrixGroup m :=
  originalSuzukiCoverEquiv Q e h split i hp T hT μ
    (suzuki_remainder_le_kernel_of_perfect Q e h split i T hT hp μ)

@[simp] theorem regularOriginalSuzukiCoverEquiv_mk (hp : Group.IsPerfect (L i))
    {m : ℕ} (μ : ((L i) ⧸ pCore 2 (L i)) ≃* SuzukiMatrixGroup m)
    (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    regularOriginalSuzukiCoverEquiv Q e h split i T hT hp μ
      (QuotientGroup.mk' (originalRadicalInClosure Q e split i)
        (inclusion (originalRankOne_le_localClosure Q e split i) r)) =
      μ (QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp (originalRankOneEquiv Q e split i r))) :=
  originalSuzukiCoverEquiv_mk Q e h split i hp T hT μ _ r

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
