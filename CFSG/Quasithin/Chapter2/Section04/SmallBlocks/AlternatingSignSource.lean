module
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingCharacteristicCoreSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingRelativeIndicesSource
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.ElementaryStabilizerSign
public import Theory.ElementaryAbelian.Injective

/-!
# The factor-sign kernel containing the original A5 two-subgroup

In the trivial block-centralizer branch, the original two-core P is O2(M).
The natural elementary sixteen U is normal in the selected subgroup R, and
P has relative index two in U. Thus U intersect P is an R-invariant elementary
eight. Its singular plane in the actual square quotient forces R into the
kernel of the product of the two factor signs of the canonical conjugation
action. The quaternion coordinates are arbitrary; no plane marking is added
to the original source assumptions.

Source: Aschbacher--Smith 2.4.29, printed pp.545--546.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter2
open ChapterC ChapterC.Section05.ConjugateSource ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem MinimalBlockSetup.single_alternating_factorSign_source
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block)
    (hA : IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T : Subgroup G) ⊓ centralizer (d.block.map d.H.subtype : Set G) = ⊥)
    (dq : QuaternionCentralProductData (pCore 2 M)) :
    ((d.S : Subgroup d.H).map d.H.subtype).subgroupOf M ≤
      (BinaryFourPlus.factorSign.comp (dq.quotientWreathAction.comp MulAut.conjNormal)).ker := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let R := (d.S : Subgroup d.H).map d.H.subtype
  let U := sourceModule (d.block.map d.H.subtype)
  let Ui := (blockU d.block).map d.block.subtype
  let Q := pCore 2 M
  let j : Q →* G := M.subtype.comp Q.subtype
  have hj : Function.Injective j := M.subtype_injective.comp Q.subtype_injective
  have hcore : M.pCoreIn 2 = P :=
    (d.single_alternating_maximal_core_of_centralizer_bot hG T hM hTM hu hST hsingle hA hD).1
  have hrange : j.range = P := by
    rw [MonoidHom.range_comp,range_subtype]
    exact hcore
  let : d.block.Normal := hsingle ▸ d.L0_normal
  let : Ui.Normal := inferInstanceAs (((blockU d.block).map d.block.subtype).Normal)
  have hUi : Ui.map d.H.subtype=U :=
    (moduleLayer_map d.H.subtype d.H.subtype_injective d.block).symm
  have hUn : R ≤ normalizer (U : Set G) := by
    have hi := Ui.le_normalizer_map d.H.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hUi] at hi
    exact (map_subtype_le _).trans hi
  let : IsElementaryAbelian 2 U := by
    let := hA.2.1.elementary
    exact IsElementaryAbelian.map (d.block.map d.H.subtype).subtype
  have hcU : Nat.card U=16 := by
    obtain ⟨_,eU,_⟩ := d.single_alternating_marked_action hsingle hA
    rw [←hUi,card_map_of_injective d.H.subtype_injective,Nat.card_congr eU.toEquiv,
      Nat.card_congr Multiplicative.toAdd,Module.natCard_eq_pow_finrank (K:=ZMod 2),
      BinaryPermutation.finrank_core]
    norm_num
  have hi : P.relIndex U=2 := by
    have hh := (d.single_alternating_core_relative_indices hG T hM hTM hu hST hsingle hA).1
    simpa only [hD,sup_bot_eq] using hh
  have hcUP : Nat.card (U ⊓ P : Subgroup G)=8 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (U⊓P) U bot_le inf_le_left
    rw [relIndex_bot_left,inf_relIndex_left,hi,relIndex_bot_left,hcU] at hh
    omega
  let E := U.comap j
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.comap_of_injective j hj U
  have hcE : Nat.card E=8 := by
    rw [←card_map_of_injective (K:=E) hj,map_comap_eq,hrange]
    simpa only [inf_comm] using hcUP
  intro s hs
  change BinaryFourPlus.factorSign (dq.quotientWreathAction (MulAut.conjNormal s))=1
  apply dq.quotientWreathAction_factorSign_one_of_elementary_eight E hcE
  intro x hx
  change j ((MulAut.conjNormal s : MulAut Q) x)∈U
  have he : j ((MulAut.conjNormal s : MulAut Q) x)=
      (s:G)*j x*(s:G)⁻¹ := by
    change M.subtype ((MulAut.conjNormal s : MulAut Q) x)=_
    rw [MulAut.conjNormal_apply,map_mul,map_mul,map_inv]
    rfl
  rw [he]
  exact (mem_normalizer_iff.mp (hUn hs) (j x)).mp hx
end CFSG.Quasithin.Chapter2
