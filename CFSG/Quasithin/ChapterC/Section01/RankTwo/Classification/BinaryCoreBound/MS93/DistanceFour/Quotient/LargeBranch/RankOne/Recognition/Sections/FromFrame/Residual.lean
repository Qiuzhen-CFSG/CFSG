module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.Cubic
import Theory.SpecificGroups.PSL2.TwoResidual
import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
import Theory.SpecificGroups.SymmetricTwoResidual
import Theory.GroupTheory.PCoreSurjective
import Theory.GroupTheory.OddSubgroupLift
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# The marked residual quotient and its cubic supplement

For the residual attached to a marked frame, the source projection restricts to
the model parabolic and then to its rank-one residual.  Quotienting the model
parabolic by its intrinsic two-core and using the supplied weak-BN model
equivalence identifies this residual with the literal derived subgroup
`SL₂(2)'`.  Transport through `residualEquiv` preserves the marking, so the
kernel is exactly the subgroup `Q_beta` prescribed by the frame edge.

The resulting quotient map is surjective.  The odd-subgroup lift gives an
actual subgroup of order three mapping onto the residual, and the elementary
kernel--supplement argument records the ambient decomposition used by the
second section proof.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12)(1)--(2), printed p.910, with the marked residual and
parabolic model from pp.905 and 908.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable (source : LocalSource L R) (f : Frame source)
noncomputable section

theorem perm_three_residual :
    pResidual 2 (Equiv.Perm (Fin 3)) = commutator (Equiv.Perm (Fin 3)) := by
  let r : Equiv.Perm (Fin 3) := ⁅Equiv.swap (0 : Fin 3) 1, Equiv.swap (1 : Fin 3) 2⁆
  have hr : r ^ 3 = 1 := by decide +kernel
  have hrmem : r ∈ commutator (Equiv.Perm (Fin 3)) :=
    commutator_mem_commutator (mem_top _) (mem_top _)
  have hcases : ∀ a b : Equiv.Perm (Fin 3),
      ⁅a,b⁆ = 1 ∨ ⁅a,b⁆ = r ∨ ⁅a,b⁆ = r ^ 2 := by decide +kernel
  have hsquares : ∀ a : Equiv.Perm (Fin 3),
      a ^ 2 = 1 ∨ a ^ 2 = r ∨ a ^ 2 = r ^ 2 := by decide +kernel
  have hR : r ∈ pResidual 2 (Equiv.Perm (Fin 3)) :=
    mem_pResidual_of_orderOf_coprime ((by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hr))
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, ?_⟩
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator (Equiv.Perm (Fin 3))) q
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    rcases hsquares g with h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hrmem
    · rw [h]; exact pow_mem hrmem _
  · rw [commutator_def]
    apply commutator_le.mpr
    intro a _ b _
    rcases hcases a b with h | h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hR
    · rw [h]; exact pow_mem hR _

theorem sl2_twoResidual_eq_commutator :
    pResidual 2 (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) =
      commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.map_pResidual, map_commutator_eq,
    MonoidHom.range_eq_top.mpr e.surjective]
  exact perm_three_residual


theorem sl2_twoResidual_card :
    Nat.card (commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) = 3 := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let ec := e.toMonoidHom.comp
    (commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))).subtype
  have hec : ec.range = commutator (Equiv.Perm (Fin 3)) := by
    rw [ec.range_eq_map]
    change Subgroup.map (e.toMonoidHom.comp
      (commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))).subtype) ⊤ = _
    rw [← Subgroup.map_map, ← MonoidHom.range_eq_map
      (commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))).subtype,
      Subgroup.range_subtype, map_commutator_eq,
      MonoidHom.range_eq_top.mpr e.surjective]
    change commutator (Equiv.Perm (Fin 3)) = _
    rfl
  have hecinj : Function.Injective ec := by
    intro a b h
    apply Subtype.ext
    exact e.injective h
  let ee : commutator (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ≃*
      commutator (Equiv.Perm (Fin 3)) :=
    (MonoidHom.ofInjective hecinj).trans (MulEquiv.subgroupCongr hec)
  rw [Nat.card_congr ee.toEquiv, ← perm_three_residual,
    Equiv.Perm.twoResidual_eq_alternating, nat_card_alternatingGroup, Nat.card_fin]
  decide

def modelParabolicMap :
    parabolic source.projection source.flag f.orientation →*
      modelParabolic source.flag f.orientation :=
  (source.projection.comp (parabolic source.projection source.flag f.orientation).subtype).codRestrict
    (modelParabolic source.flag f.orientation) (fun x => x.property)

omit [Finite M] in
theorem modelParabolicMap_surjective : Function.Surjective (modelParabolicMap source f) := by
  intro x
  obtain ⟨m, hm⟩ := source.projection_surjective x
  refine ⟨⟨m, ?_⟩, ?_⟩
  · change source.projection m ∈ modelParabolic source.flag f.orientation
    simp [hm, x.property]
  exact Subtype.ext hm

omit [Finite M] in
theorem modelParabolicMap_ker :
    (modelParabolicMap source f).ker =
      source.projection.ker.subgroupOf (parabolic source.projection source.flag f.orientation) := by
  ext x
  simp only [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

def modelResidualMap :
    rankOne (parabolic source.projection source.flag f.orientation) →*
      pResidual 2 (modelParabolic source.flag f.orientation) :=
  ((modelParabolicMap source f).comp
    ((rankOne (parabolic source.projection source.flag f.orientation)).subtype.codRestrict
      (parabolic source.projection source.flag f.orientation)
      (fun x => map_subtype_le _ x.property))).codRestrict
      (pResidual 2 (modelParabolic source.flag f.orientation)) (by
        intro x
        have hres := Subgroup.map_pResidual_of_surjective 2
          (modelParabolicMap source f) (modelParabolicMap_surjective source f)
        exact (show ((modelParabolicMap source f) (
            ((rankOne (parabolic source.projection source.flag f.orientation)).subtype.codRestrict
              (parabolic source.projection source.flag f.orientation)
              (fun x => map_subtype_le _ x.property)) x)) ∈
            pResidual 2 (modelParabolic source.flag f.orientation) from by
          rw [← hres]
          have hrank := rankOne_parabolic_eq source.projection source.projection_surjective
            (by rw [source.projection_kernel]; exact pCore_isPGroup) source.flag f.orientation
          have hx : (x : M) ∈
              (pResidual 2 (parabolic source.projection source.flag f.orientation)).map
                (parabolic source.projection source.flag f.orientation).subtype := by
            rw [← hrank]
            exact x.property
          obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
          refine ⟨z, hz, ?_⟩
          have heq : z = ((rankOne (parabolic source.projection source.flag f.orientation)).subtype.codRestrict
              (parabolic source.projection source.flag f.orientation)
              (fun x => map_subtype_le _ x.property)) x := by
            apply Subtype.ext
            exact hzx
          rw [heq]
          ))

theorem modelResidualMap_surjective : Function.Surjective (modelResidualMap source f) := by
  intro y
  have hres := Subgroup.map_pResidual_of_surjective 2
    (modelParabolicMap source f) (modelParabolicMap_surjective source f)
  have hy : (y : modelParabolic source.flag f.orientation) ∈
      (pResidual 2 (parabolic source.projection source.flag f.orientation)).map
        (modelParabolicMap source f) := by
    rw [hres]
    exact y.property
  obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
  refine ⟨⟨x, ?_⟩, ?_⟩
  · rw [rankOne_parabolic_eq source.projection source.projection_surjective
      (by rw [source.projection_kernel]; exact pCore_isPGroup) source.flag f.orientation]
    exact ⟨x, hx, rfl⟩
  · apply Subtype.ext
    exact hxy

def quotientModelMap :
    modelParabolic source.flag f.orientation →*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  (Classical.choice (source.weakBN.rank_one f.orientation)).toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 (modelParabolic source.flag f.orientation)))

omit [Finite M] in
theorem quotientModelMap_surjective : Function.Surjective (quotientModelMap source f) := by
  intro x
  obtain ⟨y, hy⟩ := (Classical.choice (source.weakBN.rank_one f.orientation)).surjective x
  obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective (pCore 2 (modelParabolic source.flag f.orientation)) y
  refine ⟨z, ?_⟩
  change (Classical.choice (source.weakBN.rank_one f.orientation))
      ((QuotientGroup.mk' (pCore 2 (modelParabolic source.flag f.orientation))) z) = x
  rw [hz]
  exact hy

omit [Finite M] in
theorem quotientModelMap_ker :
    (quotientModelMap source f).ker = pCore 2 (modelParabolic source.flag f.orientation) := by
  let e := Classical.choice (source.weakBN.rank_one f.orientation)
  ext x
  change e ((QuotientGroup.mk' (pCore 2 (modelParabolic source.flag f.orientation))) x) = 1 ↔
    x ∈ pCore 2 (modelParabolic source.flag f.orientation)
  constructor
  · intro h
    have hq : (QuotientGroup.mk' (pCore 2 (modelParabolic source.flag f.orientation))) x = 1 := by
      apply e.injective
      simpa using h
    exact (QuotientGroup.eq_one_iff _).mp hq
  · intro h
    have hq := (QuotientGroup.eq_one_iff _).mpr h
    calc
      e ((QuotientGroup.mk' (pCore 2 (modelParabolic source.flag f.orientation))) x) = e 1 :=
        congrArg e hq
      _ = 1 := e.map_one

def modelResidualToC :
    pResidual 2 (modelParabolic source.flag f.orientation) →*
      BinarySL2Residual.C := by
  let a := (quotientModelMap source f).subgroupMap (pResidual 2
    (modelParabolic source.flag f.orientation))
  have ha : (pResidual 2 (modelParabolic source.flag f.orientation)).map
      (quotientModelMap source f) = BinarySL2Residual.C := by
    rw [Subgroup.map_pResidual_of_surjective 2 (quotientModelMap source f)
      (quotientModelMap_surjective source f), sl2_twoResidual_eq_commutator]
  exact (MulEquiv.subgroupCongr ha).toMonoidHom.comp a

omit [Finite M] in
theorem modelResidualToC_ker :
    (modelResidualToC source f).ker =
      (pCore 2 (modelParabolic source.flag f.orientation)).subgroupOf
        (pResidual 2 (modelParabolic source.flag f.orientation)) := by
  ext x
  have ha : (pResidual 2 (modelParabolic source.flag f.orientation)).map
      (quotientModelMap source f) = BinarySL2Residual.C := by
    rw [Subgroup.map_pResidual_of_surjective 2 (quotientModelMap source f)
      (quotientModelMap_surjective source f), sl2_twoResidual_eq_commutator]
  let e := MulEquiv.subgroupCongr ha
  change e ((quotientModelMap source f).subgroupMap
      (pResidual 2 (modelParabolic source.flag f.orientation)) x) = 1 ↔ _
  rw [← e.map_one, e.injective.eq_iff]
  change (quotientModelMap source f).subgroupMap
      (pResidual 2 (modelParabolic source.flag f.orientation)) x = 1 ↔
      (x : modelParabolic source.flag f.orientation) ∈
        pCore 2 (modelParabolic source.flag f.orientation)
  constructor
  · intro h
    have hq : (quotientModelMap source f) (x : modelParabolic source.flag f.orientation) = 1 :=
      congrArg Subtype.val h
    have hk : (x : modelParabolic source.flag f.orientation) ∈
        (quotientModelMap source f).ker := MonoidHom.mem_ker.mpr hq
    rw [quotientModelMap_ker source f] at hk
    exact hk
  · intro h
    have hk : (x : modelParabolic source.flag f.orientation) ∈
        (quotientModelMap source f).ker := by
      rw [quotientModelMap_ker source f]
      exact h
    apply Subtype.ext
    exact MonoidHom.mem_ker.mp hk

omit [Finite M] in
theorem modelResidualToC_surjective : Function.Surjective (modelResidualToC source f) := by
  intro c
  let a := (quotientModelMap source f).subgroupMap (pResidual 2
    (modelParabolic source.flag f.orientation))
  have ha : (pResidual 2 (modelParabolic source.flag f.orientation)).map
      (quotientModelMap source f) = BinarySL2Residual.C := by
    rw [Subgroup.map_pResidual_of_surjective 2 (quotientModelMap source f)
      (quotientModelMap_surjective source f), sl2_twoResidual_eq_commutator]
  let e := MulEquiv.subgroupCongr ha
  obtain ⟨y, hy⟩ := e.surjective c
  have hy' : (y : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∈
      (pResidual 2 (modelParabolic source.flag f.orientation)).map
        (quotientModelMap source f) := y.property
  obtain ⟨x, hx, hxy⟩ := mem_map.1 hy'
  let x' : pResidual 2 (modelParabolic source.flag f.orientation) := ⟨x, hx⟩
  refine ⟨x', ?_⟩
  change e ⟨quotientModelMap source f x, ?_⟩ = c
  rw [show (⟨quotientModelMap source f x, hxy ▸ y.property⟩ :
      (pResidual 2 (modelParabolic source.flag f.orientation)).map
        (quotientModelMap source f)) = y by
    apply Subtype.ext
    exact hxy]
  exact hy

def sourceResidualToC :
    rankOne (parabolic source.projection source.flag f.orientation) →*
      BinarySL2Residual.C :=
  (modelResidualToC source f).comp (modelResidualMap source f)

theorem sourceResidualToC_ker :
    (sourceResidualToC source f).ker =
      ((pCore 2 (parabolic source.projection source.flag f.orientation)).map
        (parabolic source.projection source.flag f.orientation).subtype).subgroupOf
          (rankOne (parabolic source.projection source.flag f.orientation)) := by
  have hkerP : IsPGroup 2 (modelParabolicMap source f).ker := by
    rw [modelParabolicMap_ker source f, source.projection_kernel]
    exact pCore_isPGroup.comap_subtype
  have hpre := (modelParabolicMap source f).comap_pCore_of_ker_isPGroup
    (modelParabolicMap_surjective source f) hkerP
  ext x
  have hcore := modelResidualToC_ker source f
  change modelResidualToC source f (modelResidualMap source f x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, hcore]
  change (modelResidualMap source f x : modelParabolic source.flag f.orientation) ∈
      pCore 2 (modelParabolic source.flag f.orientation) ↔ _
  let ax := ((rankOne (parabolic source.projection source.flag f.orientation)).subtype.codRestrict
      (parabolic source.projection source.flag f.orientation)
      (fun z => map_subtype_le _ z.property)) x
  change (modelParabolicMap source f ax) ∈
      pCore 2 (modelParabolic source.flag f.orientation) ↔ _
  change ax ∈ Subgroup.comap (modelParabolicMap source f)
      (pCore 2 (modelParabolic source.flag f.orientation)) ↔ _
  rw [show Subgroup.comap (modelParabolicMap source f)
      (pCore 2 (modelParabolic source.flag f.orientation)) =
        pCore 2 (parabolic source.projection source.flag f.orientation) from hpre]
  rw [mem_subgroupOf]
  constructor
  · intro hx
    exact ⟨ax, hx, rfl⟩
  · intro hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    have heq : z = ax := by
      apply Subtype.ext
      exact hzx
    simpa [heq] using hz

theorem sourceResidualToC_surjective : Function.Surjective (sourceResidualToC source f) :=
  by
    intro c
    obtain ⟨y, hy⟩ := modelResidualToC_surjective source f c
    obtain ⟨x, hx⟩ := modelResidualMap_surjective source f y
    exact ⟨x, (congrArg (modelResidualToC source f) hx).trans hy⟩

def markedResidualProjection :
    flagResidual source f.orientation →* BinarySL2Residual.C :=
  (sourceResidualToC source f).comp (residualEquiv source f.orientation).symm.toMonoidHom

theorem markedResidualProjection_ker :
    (markedResidualProjection source f).ker =
      (Q R (beta R)).subgroupOf (flagResidual source f.orientation) := by
  have hsource := sourceResidualToC_ker source f
  ext g
  change sourceResidualToC source f ((residualEquiv source f.orientation).symm g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, hsource, mem_subgroupOf]
  change ((residualEquiv source f.orientation).symm g : M) ∈
      (pCore 2 (parabolic source.projection source.flag f.orientation)).map
        (parabolic source.projection source.flag f.orientation).subtype ↔
    (g : FreeAmalgam R) ∈ Q R (beta R)
  have hflag : flagKernel source f.orientation = Q R (beta R) := f.edge_kernel
  constructor
  · intro hg
    have hmem : embedM R ((residualEquiv source f.orientation).symm g) ∈
        flagKernel source f.orientation := by
      rw [flagKernel]
      exact mem_map.mpr ⟨(residualEquiv source f.orientation).symm g, hg, rfl⟩
    rw [hflag] at hmem
    simpa [residualEquiv_symm_apply] using hmem
  · intro hg
    have hmem : embedM R ((residualEquiv source f.orientation).symm g) ∈
        flagKernel source f.orientation := by
      rw [hflag]
      simpa [residualEquiv_symm_apply] using hg
    rw [flagKernel] at hmem
    obtain ⟨z, hz, hzg⟩ := mem_map.mp hmem
    have heq : z = ((residualEquiv source f.orientation).symm g : M) :=
      embedM_injective R hzg
    simpa [heq] using hz


theorem markedResidualProjection_surjective :
    Function.Surjective (markedResidualProjection source f) :=
  (sourceResidualToC_surjective source f).comp
    (residualEquiv source f.orientation).symm.surjective

theorem markedResidualProjection_normal :
    ((Q R (beta R)).subgroupOf (flagResidual source f.orientation)).Normal := by
  rw [← markedResidualProjection_ker source f]
  infer_instance

instance markedResidualProjection_normal_instance :
    ((Q R (beta R)).subgroupOf (flagResidual source f.orientation)).Normal :=
  markedResidualProjection_normal source f

noncomputable def markedResidualQuotientEquiv :
    flagResidual source f.orientation ⧸
        (Q R (beta R)).subgroupOf (flagResidual source f.orientation) ≃*
      BinarySL2Residual.C :=
  by
    letI : ((Q R (beta R)).subgroupOf (flagResidual source f.orientation)).Normal :=
      markedResidualProjection_normal source f
    exact (QuotientGroup.quotientMulEquivOfEq
        (markedResidualProjection_ker source f).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (markedResidualProjection source f) (markedResidualProjection_surjective source f))

theorem markedResidualQuotientEquiv_mk (g : flagResidual source f.orientation) :
    markedResidualQuotientEquiv source f
      (@QuotientGroup.mk' _ _ ((Q R (beta R)).subgroupOf (flagResidual source f.orientation))
          (markedResidualProjection_normal source f) g) =
      markedResidualProjection source f g := by
  rfl

set_option linter.style.haveILetI false in
theorem exists_marked_cubic :
    ∃ T : Subgroup (flagResidual source f.orientation), Nat.card T = 3 ∧
      T.map (markedResidualProjection source f) = ⊤ := by
  letI : Finite (flagResidual source f.orientation) :=
    Finite.of_injective (residualEquiv source f.orientation).symm
      (residualEquiv source f.orientation).symm.injective
  have hk : IsPGroup 2 (markedResidualProjection source f).ker := by
    rw [markedResidualProjection_ker source f]
    rw [← f.edge_kernel]
    exact ((pCore_isPGroup.map (parabolic source.projection source.flag f.orientation).subtype).map
      (embedM R)).comap_subtype
  have hodd : Odd (Nat.card (⊤ : Subgroup BinarySL2Residual.C)) := by
    rw [Subgroup.card_top, sl2_twoResidual_card]
    decide
  obtain ⟨T, hT, hTinj, hTcard, hcover⟩ :=
    MonoidHom.exists_odd_subgroup_lift (markedResidualProjection source f)
      (markedResidualProjection_surjective source f) hk (⊤ : Subgroup BinarySL2Residual.C) hodd
  refine ⟨T, ?_, hT⟩
  simpa [sl2_twoResidual_card] using hTcard

theorem marked_cubic_supplement (T : Subgroup (flagResidual source f.orientation))
    (_hT : Nat.card T = 3)
    (hTmap : T.map (markedResidualProjection source f) = ⊤) :
    (Q R (beta R)).subgroupOf (flagResidual source f.orientation) ⊔ T = ⊤ := by
  have hmapker : (markedResidualProjection source f).ker.map
      (markedResidualProjection source f) = ⊥ := by
    apply le_antisymm
    · rw [map_le_iff_le_comap]
      exact le_rfl
    · exact bot_le
  let S := (markedResidualProjection source f).ker ⊔ T
  have hmapS : S.map (markedResidualProjection source f) = ⊤ := by
    dsimp [S]
    rw [Subgroup.map_sup, hmapker, hTmap, bot_sup_eq]
  have hkerS : (markedResidualProjection source f).ker ≤ S := le_sup_left
  have hcomap : Subgroup.comap (markedResidualProjection source f)
      (S.map (markedResidualProjection source f)) = S :=
    Subgroup.comap_map_eq_self hkerS
  have htop := congrArg (Subgroup.comap (markedResidualProjection source f)) hmapS
  rw [hcomap] at htop
  dsimp [S] at htop
  simpa [markedResidualProjection_ker source f] using htop

end
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
