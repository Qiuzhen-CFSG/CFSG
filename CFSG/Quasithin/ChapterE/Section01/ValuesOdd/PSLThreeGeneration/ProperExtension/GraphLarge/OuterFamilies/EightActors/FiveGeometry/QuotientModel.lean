module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.Unmarked
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.PrimeCentralizer
public import Theory.SpecificGroups.PSL2.FiveProjectivePermutation
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# The literal prime-five centralizer quotient

For an inner involution in the PSL₃(F) graph extension with |F| = 5,
the inner centralizer is the actual GL₂(F) block: the scalar kernel of
SL₃(F) → PSL₃(F) is trivial. The full centralizer has order dividing 960,
and its solvable residual is SL₂(F), of order 120. Thus its quotient by
the residual is a two-group, so the given ambient Sylow subgroup supplements
the residual and the literal subgroup C^∞T equals C.

The normal inner centralizer modulo its own radical is PGL₂(F) ≃ S₅.
Its inclusion induces an injection of S₅ into C/R(C). Conversely, the
already proved simple socle PSL₂(F) ≃ A₅ gives a faithful conjugation action
of C/R(C) on five letters. The two injections make this action bijective.
The construction retains the intrinsic radical and the quotient map;
cardinality is used only to prove surjectivity of the actual action.

The final theorem connects this model to the separately supplied unmarked
actor geometry. It does not assert existence of that geometry.

Source: Aschbacher--Smith, A.3.21(a), printed p.55, and the local
centralizer argument for E.1.14(7), printed p.214, using E.1.8 and E.1.10,
pp.210--213. The concrete projective and permutation comparisons retain
the source attribution and ATLAS license of their imported modules.
-/

public section
open Subgroup Theory.GroupTheory GorensteinWalter Matrix
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
open CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveQuotientModel
variable (F : Type*) [Field F] [Finite F]

local instance : Finite (PGL2 F) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

private theorem two_ne_zero (hF : Nat.card F = 5) : (2 : F) ≠ 0 := by
  let := Fintype.ofFinite F
  intro hz
  have hc := CharP.ringChar_of_prime_eq_zero Nat.prime_two hz
  have he := FiniteField.even_card_iff_char_two.mp hc
  rw [← Nat.card_eq_fintype_card, hF] at he
  norm_num at he

private theorem pgl_radical (hF : Nat.card F = 5) : solvableRadical (PGL2 F) = ⊥ := by
  let L := (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
  let e := psl2EquivToPGLRange F
  let : IsSimpleGroup (PSL2 F) := ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup L := e.symm.isSimpleGroup
  let : Group.IsPerfect (PSL2 F) := psl2_isPerfect_of_card_gt_three F (by omega)
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : L.Normal := by
    rw [show L = _root_.commutator (PGL2 F) from
      (pgl2_commutator_eq_psl2_range_of_card_gt_three F
        ⟨5, 1, by decide, by decide, le_rfl, by simpa using hF⟩ (by omega)).symm]
    infer_instance
  exact SimpleSocle.radical_eq_bot L (pgl2_psl2Range_centralizer_eq_bot F
    ⟨5, 1, by decide, by decide, le_rfl, by simpa using hF⟩)

private noncomputable def glRadicalEquiv (hF : Nat.card F = 5) :
    GL (Fin 2) F ⧸ solvableRadical (GL (Fin 2) F) ≃* PGL2 F := by
  let f : GL (Fin 2) F →* PGL2 F := ProjGenLinGroup.mk
  let : Group.IsSolvable f.ker := by
    rw [show f.ker = center (GL (Fin 2) F) from ProjGenLinGroup.ker_mk]
    exact Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
  exact (solvableRadicalQuotientEquiv f ProjGenLinGroup.mk_surjective).trans
    ((QuotientGroup.quotientMulEquivOfEq (pgl_radical F hF)).trans QuotientGroup.quotientBot)

variable [IsSimpleGroup PSL(3,F)]

/-- The inner centralizer is the literal GL₂ block, transported through
its canonical projective projection and the marked inner embedding. -/
noncomputable def innerEquiv (hF : Nat.card F = 5)
    (z : graphExtension F) (hzL : z ∈ innerPart F) (hz : orderOf z = 2) :
    innerCentralizer F z ≃* GL (Fin 2) F := by
  apply Classical.choice
  let t := (innerPartEquiv F).symm ⟨z, hzL⟩
  have ht : orderOf t = 2 := ((innerPartEquiv F).symm.orderOf_eq _).trans
    ((orderOf_submonoid _).symm.trans hz)
  obtain ⟨x, hx, he⟩ := PSL3.OddInvolutionFixed.involution_lift t ht
  have hinj : Function.Injective (PSL3.projection F) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply Subgroup.eq_bot_of_card_eq
    rw [PSL3.card_projectionKernel, hF]
    decide
  let e := MulEquiv.ofBijective (PSL3.OddInvolutionFixed.centralizerProjection x)
    ⟨fun a b h => Subtype.ext (hinj (congrArg Subtype.val h)),
      PSL3.OddInvolutionFixed.centralizerProjection_surjective x (hx ▸ pow_orderOf_eq_one x)⟩
  exact ⟨(innerCentralizerEquiv F z hzL).trans
    ((MulEquiv.subgroupCongr (congrArg (fun w => centralizer ({w} : Set PSL(3,F))) he.symm)).trans
      (e.symm.trans (SL3.involutionCentralizerEquiv F x hx (two_ne_zero F hF))))⟩

private theorem centralizer_card_dvd (hF : Nat.card F = 5)
    (z : graphExtension F) (hzL : z ∈ innerPart F) (hz : orderOf z = 2) :
    Nat.card (centralizer ({z} : Set (graphExtension F))) ∣ 960 := by
  let C := centralizer ({z} : Set (graphExtension F))
  let N := innerCentralizer F z
  have hN : Nat.card N = 480 := by
    let : Fintype F := Fintype.ofFinite F
    rw [Nat.card_congr (innerEquiv F hF z hzL hz).toEquiv, Matrix.card_GL_field]
    norm_num [Fin.prod_univ_two, ← Nat.card_eq_fintype_card, hF]
  have hi : N.index ∣ 2 :=
    ((innerPart F).relIndex_dvd_index_of_normal C).trans (quotient_card_dvd_two F)
  have hh := Nat.mul_dvd_mul_left 480 hi
  rw [← hN, N.card_mul_index, hN] at hh
  exact hh

/-- At five the full centralizer has two-group quotient by its residual,
so the specified ambient Sylow subgroup fills the residual supplement. -/
theorem supplement_eq_centralizer (hF : Nat.card F = 5)
    {T : Sylow 2 (graphExtension F)} {z : graphExtension F}
    (hzL : z ∈ innerPart F) (hz : orderOf z = 2)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _)) :
    CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.centralizerResidualOvergroup T z =
      centralizer ({z} : Set (graphExtension F)) := by
  let C := centralizer ({z} : Set (graphExtension F))
  let D := solvableResidual C
  obtain ⟨e⟩ := inner_centralizer_residual_equiv F (hF ▸ (by decide : Odd 5))
    (by omega) z hzL hz
  have hD : Nat.card D = 120 := by
    rw [Nat.card_congr e.toEquiv]
    rw [sl2_card_formula, hF]
    norm_num
  have hi : D.index ∣ 8 := by
    have hd := centralizer_card_dvd F hF z hzL hz
    rw [← D.card_mul_index, hD] at hd
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 120)).mp hd
  have hq : IsPGroup 2 (C ⧸ D) := IsPGroup.of_card_dvd_pow (n := 3) hi
  have hs := (T.subtype hTz).sup_eq_top_of_quotient_isPGroup D hq
  have hm := congrArg (Subgroup.map C.subtype) hs
  rw [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTz,
    ← MonoidHom.range_eq_map, range_subtype] at hm
  change D.map C.subtype ⊔ (T : Subgroup _) = C
  simpa only [sup_comm] using hm

/-- The intrinsic radical quotient of the exact residual--Sylow join is S₅.
No additional quasithinness or assumed quotient identification is needed. -/
theorem residual_quotient_model (hF : Nat.card F = 5)
    {T : Sylow 2 (graphExtension F)} {z : graphExtension F}
    (hzL : z ∈ innerPart F) (hz : orderOf z = 2)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _)) :
    let K := CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.centralizerResidualOvergroup T z
    Nonempty ((K ⧸ solvableRadical K) ≃* Equiv.Perm (Fin 5)) := by
  dsimp only
  rw [supplement_eq_centralizer F hF hzL hz hTz]
  let C := centralizer ({z} : Set (graphExtension F))
  let N := innerCentralizer F z
  let Q := C ⧸ solvableRadical C
  let q := QuotientGroup.mk' (solvableRadical C)
  let ec := innerEquiv F hF z hzL hz
  let en : N ⧸ solvableRadical N ≃* PGL2 F :=
    (QuotientGroup.congr _ _ ec (map_solvableRadical_equiv ec)).trans (glRadicalEquiv F hF)
  let enS := en.trans (Theory.PSL2.exists_pgl2_five_equiv F hF).some
  let ei := normalRadicalQuotientEquivImage N
  let j : Equiv.Perm (Fin 5) →* Q :=
    (N.map q).subtype.comp (ei.toMonoidHom.comp enS.symm.toMonoidHom)
  have hj : Function.Injective j :=
    (N.map q).subtype_injective.comp (ei.injective.comp enS.symm.injective)
  have hstr := EightActors.residual_quotient_structure F (hF ▸ (by decide : Odd 5))
    (by omega) hzL hz hTz
  dsimp only at hstr
  rw [supplement_eq_centralizer F hF hzL hz hTz] at hstr
  obtain ⟨_, hs, ⟨es⟩, _⟩ := hstr
  let : IsSimpleGroup (generalizedFitting Q) := hs
  let : Group.IsPerfect (PSL2 F) := psl2_isPerfect_of_card_gt_three F (by omega)
  let : Group.IsPerfect (generalizedFitting Q) :=
    Group.IsPerfect.ofSurjective (f := es.symm.toMonoidHom) es.symm.surjective
  have hc : centralizer (generalizedFitting Q : Set Q) = ⊥ :=
    SimpleSocle.centralizer_eq_bot (Group.IsPerfect.not_isMulCommutative _)
  let : Fintype F := Fintype.ofFinite F
  let eF : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F (by decide) (by simpa using hF)
  let eA : generalizedFitting Q ≃* alternatingGroup (Fin 5) :=
    es.trans ((psl2RingEquiv eF).symm.trans alternatingGroupFive_equiv_PSL2.some.symm)
  let f := Theory.SpecificGroups.Alternating.FiveExtensionAction.action (generalizedFitting Q) eA
  have hf := Theory.SpecificGroups.Alternating.FiveExtensionAction.action_injective
    (generalizedFitting Q) eA hc
  have hcard : Nat.card Q = Nat.card (Equiv.Perm (Fin 5)) :=
    Nat.le_antisymm (Nat.card_le_card_of_injective f hf) (Nat.card_le_card_of_injective j hj)
  exact ⟨MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩)⟩

/-- The actual quotient model marks the independently constructed actor
outside the derived subgroup, discharging the model premise of the local
prime-five geometry consumer. -/
theorem fiveGeometryAt_of_unmarked_five (hF : Nat.card F = 5)
    {T : Sylow 2 (graphExtension F)} {z : graphExtension F}
    (hzL : z ∈ innerPart F) (hz : orderOf z = 2)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _))
    (Ω : Set (Subgroup (graphExtension F)))
    (hgeometry : EightActors.UnmarkedFiveGeometryAt F T Ω z) :
    EightActors.FiveGeometryAt F T Ω z :=
  EightActors.fiveGeometryAt_of_unmarked F T Ω z hgeometry
    (residual_quotient_model F hF hzL hz hTz)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveQuotientModel
