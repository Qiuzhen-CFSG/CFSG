module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.AbelianExclusion
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.SourceSetup.BinaryFullCover
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
Transport the exact natural derived subgroup and doubled-dual central quotient
of the intrinsic distance-four core into the original ambient component.
The whole center is retained: its fixed part only contributes zero component
displacement. All module coordinates preserve the supplied quotient marking.
Source: Aschbacher--Smith15.3.23, p.1129, and MS93(4.6.12).
-/

@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FullCover
open CoreActions ChapterC
variable {G : Type*} [Group G] {L : Subgroup G}
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
local notation "W" => Fin 3 → ZMod 2

theorem block_map : (blockU L).map L.subtype = commutatorCore L := by
  change (⁅pCore 2 L, (⊤ : Subgroup L)⁆).map L.subtype = _
  rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
  rfl

def coreEquiv : blockU L ≃* commutatorCore L :=
  ((blockU L).equivMapOfInjective L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr block_map)

theorem coreEquiv_val (x : blockU L) : (coreEquiv x : G) = (x : L) := rfl

theorem coreEquiv_symm_val (x : commutatorCore L) :
    ((coreEquiv.symm x : blockU L) : L).val = x :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply x)

theorem derived_map :
    (_root_.commutator (blockU L)).map (L.subtype.comp (blockU L).subtype) =
      ⁅commutatorCore L,commutatorCore L⁆ := by
  rw [←map_map,map_subtype_commutator,map_commutator,block_map]

def derivedEquiv : _root_.commutator (blockU L) ≃*
    (⁅commutatorCore L,commutatorCore L⁆ : Subgroup G) :=
  ((_root_.commutator (blockU L)).equivMapOfInjective
    (L.subtype.comp (blockU L).subtype)
    (L.subtype_injective.comp (blockU L).subtype_injective)).trans
      (MulEquiv.subgroupCongr derived_map)

theorem derivedEquiv_val (x : _root_.commutator (blockU L)) :
    (derivedEquiv x : G) = (x.val : L) := rfl

theorem derivedEquiv_symm_val (x : (⁅commutatorCore L,commutatorCore L⁆ : Subgroup G)) :
    (((derivedEquiv.symm x).val : L) : G) = x :=
  congrArg Subtype.val (derivedEquiv.apply_symm_apply x)

def oneCopy : Multiplicative W ≃* Multiplicative (Fin 1 → W) where
  toFun v := Multiplicative.ofAdd (fun _ => v.toAdd)
  invFun v := Multiplicative.ofAdd (v.toAdd 0)
  left_inv _ := rfl
  right_inv v := by
    change (fun _ : Fin 1 => v.toAdd 0) = v.toAdd
    funext i
    exact congrArg v.toAdd (Subsingleton.elim _ _)
  map_mul' _ _ := rfl

variable (c : BinaryMS.FullCoreDoubleDualCover L)

/-- The natural module in the source is the actual characteristic derived subgroup. -/
def naturalDerived : LayerModel L ⁅commutatorCore L,commutatorCore L⁆ ⊥
    c.marking (NaturalCopies (ZMod 2) 1) := by
  let D := ⁅commutatorCore L,commutatorCore L⁆
  have hn : L ≤ normalizer (D : Set G) := by
    dsimp only [D]
    rw [←(commutatorCore L).map_subtype_commutator]
    exact (normalizer_commutator_ge_right _ _).trans
      (normalizer_le_normalizer_characteristic_image _ _)
  let q : D ≃* Multiplicative (Fin 1 → W) :=
    derivedEquiv.symm.trans (c.derivedEquiv.trans oneCopy)
  refine {
    lower_le := bot_le
    normalized := hn
    lower_normal := by rw [bot_subgroupOf]; infer_instance
    quotientIso := ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf D)).trans
      (QuotientGroup.quotientBot (G := D))).trans q
    intertwining := ?_ }
  intro l x
  change (q (layerConjugate L D hn l x)).toAdd =
    NaturalCopies (ZMod 2) 1 (c.marking (QuotientGroup.mk' _ l)) (q x).toAdd
  have he := c.derivedAction l (derivedEquiv.symm x)
    (derivedEquiv.symm (layerConjugate L D hn l x)) (by
      apply Subtype.ext
      apply Subtype.ext
      change (((derivedEquiv.symm (layerConjugate L D hn l x)).val : L) : G) =
        l.val * (((derivedEquiv.symm x).val : L) : G) * l.val⁻¹
      rw [derivedEquiv_symm_val,derivedEquiv_symm_val]
      rfl)
  funext i
  exact he

include c in
/-- The fixed part of the center is retained, while its component displacement
is entirely contained in the natural derived subgroup. -/
theorem center_commutator_le_derived :
    ⁅coreCenter L,L⁆ ≤ ⁅commutatorCore L,commutatorCore L⁆ := by
  let D := ⁅commutatorCore L,commutatorCore L⁆
  have hDC : D ≤ L := (commutator_le_self _).trans
    ((commutatorCore_le L).trans (L.pCoreIn_le 2))
  have hn : L ≤ normalizer (D : Set G) := (naturalDerived c).normalized
  have hZ : coreCenter L ≤ D ⊔ centralizer (L : Set G) := by
    rintro z ⟨z,hz,rfl⟩
    let zi : center (blockU L) := (centerCongr coreEquiv.symm) ⟨z,hz⟩
    obtain ⟨x,hx⟩ := c.center_decomposition zi
    have hv : (((zi : blockU L) : L) : G) = (z : G) := coreEquiv_symm_val z
    have hc : (z : G) * (((x.val : L) : G))⁻¹ ∈ centralizer (L : Set G) := by
      intro l hl
      have he := congrArg Subtype.val (mem_center_iff.mp hx ⟨l,hl⟩)
      simpa only [Subgroup.coe_mul,Subgroup.coe_inv,hv] using he
    have hd : (((x.val : L) : G)) ∈ D := (derivedEquiv x).property
    have hh := (D ⊔ centralizer (L : Set G)).mul_mem (mem_sup_right hc) (mem_sup_left hd)
    change (z : G) ∈ D ⊔ centralizer (L : Set G)
    simpa only [inv_mul_cancel_right] using hh
  have hCD : centralizer (L : Set G) ≤ centralizer (D : Set G) := centralizer_le hDC
  have hND : D ⊔ centralizer (L : Set G) ≤ normalizer (D : Set G) :=
    sup_le D.le_normalizer (hCD.trans (Subgroup.centralizer_le_normalizer _))
  apply (commutator_mono hZ le_rfl).trans
  exact commutator_sup_le_of_relative_normal _ D (centralizer (L : Set G)) L D
    hND le_sup_left le_sup_right (le_normalizer_iff_commutator_le_left.mp hn)
      (by rw [commutator_eq_bot_iff_le_centralizer.mpr le_rfl]; exact bot_le)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FullCover

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FullCover
open CoreActions ChapterC
variable {G : Type*} [Group G] {L : Subgroup G}
local notation "W" => Fin 3 → ZMod 2

def dualCopiesEquiv : Multiplicative (W × W) ≃*
    Multiplicative (Fin 2 → Module.Dual (ZMod 2) W) where
  toFun v := Multiplicative.ofAdd ![
    BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv v.toAdd.1,
    BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv v.toAdd.2]
  invFun v := Multiplicative.ofAdd (
    BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv.symm (v.toAdd 0),
    BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv.symm (v.toAdd 1))
  left_inv v := by
    change Multiplicative.ofAdd (
      BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv.symm
        (BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv v.toAdd.1),
      BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv.symm
        (BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv v.toAdd.2)) = v
    rw [LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]
    rfl
  right_inv v := by
    change ![_,_] = v.toAdd
    funext i
    fin_cases i <;> exact LinearEquiv.apply_symm_apply _ _
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> exact BinaryLinearThree.AutomorphismAction.graphNaturalDual.toLinearEquiv.map_add _ _

theorem dualCopiesEquiv_action (g : BinaryLinearThree.Group) (v : W × W) :
    (dualCopiesEquiv (Multiplicative.ofAdd (BinaryMS.dualPair g v))).toAdd =
      DualCopies (ZMod 2) 2 g (dualCopiesEquiv (Multiplicative.ofAdd v)).toAdd := by
  funext i
  fin_cases i
  · exact LinearMap.congr_fun
      (BinaryLinearThree.AutomorphismAction.graphNaturalDual.isIntertwining' g) v.1
  · exact LinearMap.congr_fun
      (BinaryLinearThree.AutomorphismAction.graphNaturalDual.isIntertwining' g) v.2

variable (n : BinaryMS.NaturalCenterDoubleDualQuotient L)

def dualProjection : commutatorCore L →* Multiplicative (Fin 2 → Module.Dual (ZMod 2) W) :=
  dualCopiesEquiv.toMonoidHom.comp (n.quotient.comp coreEquiv.symm.toMonoidHom)

theorem dualProjection_kernel : (dualProjection n).ker =
    (coreCenter L).subgroupOf (commutatorCore L) := by
  ext x
  change dualCopiesEquiv (n.quotient (coreEquiv.symm x)) = 1 ↔ (x : G) ∈ coreCenter L
  rw [← dualCopiesEquiv.map_one,dualCopiesEquiv.injective.eq_iff]
  change coreEquiv.symm x ∈ n.quotient.ker ↔ _
  rw [n.kernel]
  constructor
  · intro hx
    have he := (centerCongr coreEquiv ⟨coreEquiv.symm x,hx⟩).property
    change coreEquiv (coreEquiv.symm x) ∈ center (commutatorCore L) at he
    rw [coreEquiv.apply_symm_apply] at he
    exact ⟨x,he,rfl⟩
  · rintro ⟨z,hz,hz'⟩
    have he : z = x := Subtype.ext hz'
    subst z
    exact (centerCongr coreEquiv.symm ⟨x,hz⟩).property

/-- The exact quotient by the full center retains the same dual marking. -/
def dualLayer : LayerModel L (commutatorCore L) (coreCenter L)
    n.marking (DualCopies (ZMod 2) 2) := by
  have hn := dualProjection_kernel n ▸ (inferInstance : (dualProjection n).ker.Normal)
  let _ := hn
  refine {
    lower_le := map_subtype_le _
    normalized := normalizer_commutator_ge_right _ _
    lower_normal := hn
    quotientIso := (QuotientGroup.quotientMulEquivOfEq (dualProjection_kernel n).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (dualProjection n)
        (dualCopiesEquiv.surjective.comp (n.onto.comp coreEquiv.symm.surjective)))
    intertwining := ?_ }
  intro l x
  change (dualProjection n (layerConjugate L (commutatorCore L) (normalizer_commutator_ge_right _ _) l x)).toAdd =
    DualCopies (ZMod 2) 2 (n.marking (QuotientGroup.mk' _ l)) (dualProjection n x).toAdd
  have he : coreEquiv.symm (layerConjugate L (commutatorCore L) (normalizer_commutator_ge_right _ _) l x) =
      blockConjugate L l (coreEquiv.symm x) := by
    apply Subtype.ext
    apply Subtype.ext
    change ((coreEquiv.symm (layerConjugate L (commutatorCore L) (normalizer_commutator_ge_right _ _) l x) : L) : G) =
      l.val * ((coreEquiv.symm x : L) : G) * l.val⁻¹
    rw [coreEquiv_symm_val,coreEquiv_symm_val]
    rfl
  change (dualCopiesEquiv (n.quotient (coreEquiv.symm (layerConjugate L (commutatorCore L) (normalizer_commutator_ge_right _ _) l x)))).toAdd = _
  rw [he]
  have ha := n.quotient_action l (coreEquiv.symm x)
  have hb := dualCopiesEquiv_action (n.marking (QuotientGroup.mk' _ l))
    (n.quotient (coreEquiv.symm x)).toAdd
  change (n.quotient (blockConjugate L l (coreEquiv.symm x))).toAdd =
    BinaryMS.dualPair (n.marking (QuotientGroup.mk' _ l))
      (n.quotient (coreEquiv.symm x)).toAdd at ha
  rw [←ha] at hb
  exact hb
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.OriginalSource.FullCover
