module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelAssembly
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Quotient
public import Theory.SpecificGroups.PSL3Two.InvolutoryLift
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityThreeReduction

/-!
# Separating the Sylow factors in dimensions three and five

The map L/[O₂(L),L] → L/O₂(L) has central two-group kernel and perfect
domain. In dimension three the elementary radical supplies a square-one
lift with nontrivial image; the binary SL₃ central-cover theorem therefore
kills the kernel. In dimension five the checked universal-cover calculation
kills it directly. The literal block layer is V, giving O₂(L)=V and hence
the required disjointness of T∩L and C_T(L). The resulting centralizer
records discharge the common calculation in these two dimensions; the
three-dimensional record is applied to the actual radical centralizer.

The companion LocalConfigurationRigidityKernelComplete module closes the
dimension-four central-cover obstruction and assembles the all-dimensional
record. The later elimination of C_T(L), rigidity and parabolic assembly
belong to qt-d-12213-local-rigidity.

Source: Aschbacher--Smith, original 12.2.25, printed p.805, the Sylow
product after (*); C.1.8 and the binary linear Schur-cover calculations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityKernel
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}

/-- Faithfulness of the canonical block projection identifies the actual two-core. -/
theorem core_eq_of_blockProjection_injective
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U)
    (hi : Function.Injective (ChapterC.blockCoreProjection (L := L))) :
    L.pCoreIn 2 = V := by
  have hk := (MonoidHom.ker_eq_bot_iff _).mpr hi
  rw [ChapterC.blockCoreProjection_ker, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hk
  have he : pCore 2 L = ChapterC.blockU L := le_antisymm hk ChapterC.blockU_le_core
  rw [pCoreIn, he, LiteralNaturalBlock.blockLayer_eq D A C]

omit [Finite G] in
/-- A central Sylow intersection lies in O₂(L), so the fixed-free V kills it. -/
theorem sylow_disjoint_of_component_core
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hcore : L.pCoreIn 2 = V) :
    Disjoint ((T : Subgroup G) ⊓ L)
      ((T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let B := ((T : Subgroup G) ⊓ L) ⊓ ((T : Subgroup G) ⊓ centralizer (L : Set G))
  have hBT : B ≤ (T : Subgroup G) := inf_le_left.trans inf_le_left
  have hBL : B ≤ L := inf_le_left.trans inf_le_right
  have hBC : B ≤ centralizer (L : Set G) := inf_le_right.trans inf_le_right
  have hBV : B ≤ V := by
    rw [← hcore]
    exact le_pCoreIn_of_normalizes (T.isPGroup'.to_le hBT) hBL
      ((le_centralizer_iff.mp hBC).trans (Subgroup.centralizer_le_normalizer _))
  apply disjoint_iff.mpr
  exact bot_unique ((le_inf hBV hBC).trans_eq (A.fixed_eq_bot D))

/-- An involutory lift excludes the exceptional central SL₃ cover. -/
theorem three_component_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 3) : L.pCoreIn 2 = V := by
  subst d
  let := h.quasisimple
  let q := ChapterC.blockCoreProjection (L := L)
  have hq : Function.Surjective q := ChapterC.blockCoreProjection_surjective
  have hqc : q.ker ≤ center (L ⧸ ChapterC.blockU L) := by
    rw [ChapterC.blockCoreProjection_ker]
    exact ChapterC.blockU_core_image_le_center
  have hqp : IsPGroup 2 q.ker := by
    rw [ChapterC.blockCoreProjection_ker]
    exact pCore_isPGroup.map _
  let : Group.IsPerfect (L ⧸ ChapterC.blockU L) :=
    IsPPerfect.isPerfect_of_surjective_pGroup_kernel
      (C.block.2.1.quotient_twoPerfect _) q hq hqp
  obtain ⟨e, _, _⟩ := A.natural
  let f := e.toMonoidHom.comp q
  have hk : f.ker = q.ker := MonoidHom.ker_comp_of_injective _ _ e.injective
  obtain ⟨l, hlR, hlV⟩ := exists_component_radical_noncentral h D structural A C hnone
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let : IsElementaryAbelian 2 R := radical_elementary h D structural A C hnone
  have hl2 : l ^ 2 = 1 := Subtype.ext
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := R) (l : G) hlR)
  let x := QuotientGroup.mk' (ChapterC.blockU L) l
  have hfx : f x ≠ 1 := by
    intro hx
    have he : QuotientGroup.mk' (pCore 2 L) l = 1 := e.injective (by
      simpa only [f, q, x, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, ChapterC.blockCoreProjection, QuotientGroup.mk'_apply,
        QuotientGroup.lift_mk, map_one] using hx)
    have hlcore : l ∈ pCore 2 L := (QuotientGroup.eq_one_iff l).mp he
    exact hlV (D.core_centralizes
      ((pCoreIn_mono_of_normalizes le_sup_left
        (sup_le L.le_normalizer D.sylow_normalizes_component))
        (mem_map_of_mem L.subtype hlcore)))
  have hf := BinaryLinearThree.CentralCover.kernel_eq_bot_of_involution f
    (e.surjective.comp hq) (hk ▸ hqc) (hk ▸ hqp) x
    (by simpa only [map_pow, map_one] using congrArg (QuotientGroup.mk' (ChapterC.blockU L)) hl2) hfx
  exact core_eq_of_blockProjection_injective D A C
    ((MonoidHom.ker_eq_bot_iff _).mp (hk ▸ hf))

/-- The complete common-centralizer record in dimension three. -/
theorem three_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 3) : LocalRigidityCentralizers T L V U P :=
  centralizers_of_sylow_disjoint h D structural A C hnone
    (sylow_disjoint_of_component_core D A (three_component_core h D structural A C hnone hd))

private def slFiveEquivProjective : SL(5,ZMod 2) ≃* PSL(5,ZMod 2) := by
  have hz : center SL(5,ZMod 2) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Atlas.ExceptionalSupport.card_sl_center (ι := Fin 5) (F := ZMod 2)]
    norm_num [Nat.card_eq_fintype_card]
  exact MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨by
    apply (QuotientGroup.mk' _).ker_eq_bot_iff.mp
    rw [QuotientGroup.ker_mk',hz], QuotientGroup.mk'_surjective _⟩

/-- The universal binary SL₅ cover is trivial, for the original block projection. -/
theorem five_blockProjection_injective
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hd : d = 5) : Function.Injective (ChapterC.blockCoreProjection (L := L)) := by
  subst d
  let := h.quasisimple
  let q := ChapterC.blockCoreProjection (L := L)
  have hq : Function.Surjective q := ChapterC.blockCoreProjection_surjective
  have hqc : q.ker ≤ center (L ⧸ ChapterC.blockU L) := by
    rw [ChapterC.blockCoreProjection_ker]
    exact ChapterC.blockU_core_image_le_center
  have hqp : IsPGroup 2 q.ker := by
    rw [ChapterC.blockCoreProjection_ker]
    exact pCore_isPGroup.map _
  let : Group.IsPerfect (L ⧸ ChapterC.blockU L) :=
    IsPPerfect.isPerfect_of_surjective_pGroup_kernel
      (C.block.2.1.quotient_twoPerfect _) q hq hqp
  let : IsQuasisimple (L ⧸ ChapterC.blockU L) :=
    PerfectCentralCovering.Cover.isQuasisimple
      { toMonoidHom := q, surjective := hq, ker_le_center := hqc, isPerfect := inferInstance }
  let e := A.natural.choose.trans slFiveEquivProjective
  let : IsQuasisimple PSL(5,ZMod 2) :=
    Theory.SpecificGroups.PSL5Two.UniversalCover.isQuasisimple (ZMod 2)
  let c : Covering (L ⧸ ChapterC.blockU L) PSL(5,ZMod 2) :=
    { toMonoidHom := e.toMonoidHom.comp q, surjective := e.surjective.comp hq }
  have hu := Theory.SpecificGroups.PSL5Two.UniversalCover.identity_isUniversal.{u}
  let s := hu.lift c
  have hs := hu.lift_fac c
  have he (a : PSL(5,ZMod 2)) : c (s a) = a :=
    congrArg (fun k : Covering _ _ => k a) hs
  intro x y hxy
  obtain ⟨a,rfl⟩ := s.surjective x
  obtain ⟨b,rfl⟩ := s.surjective y
  have hab : a = b := by
    rw [← he a,← he b]
    exact congrArg e hxy
  rw [hab]


/-- In dimension five the two-core is the original chosen subgroup. -/
theorem five_component_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (C : CyclicLocalAnalysis T L V d H P U) (hd : d = 5) : L.pCoreIn 2 = V :=
  core_eq_of_blockProjection_injective D A C (five_blockProjection_injective h A C hd)

/-- The complete common-centralizer record in dimension five. -/
theorem five_centralizers
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) (hd : d = 5) : LocalRigidityCentralizers T L V U P :=
  centralizers_of_sylow_disjoint h D structural A C hnone
    (sylow_disjoint_of_component_core D A (five_component_core h D A C hd))

/-- Actual dimension-three consumer: the radical's ambient centralizer,
with the common-centralizer premise discharged. -/
theorem three_radical_selfCentralizing
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 3) (C : CyclicLocalAnalysis T L V 3 H P U)
    (hnone : NoEscape L V) :
    centralizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) =
      (T : Subgroup G) ⊓ centralizer (U : Set G) :=
  ThreeRigidity.radical_selfCentralizing h C (three_centralizers h D structural A C hnone rfl)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.RigidityKernel
