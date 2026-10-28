module

public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallCorePlacement
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The central line in the solvable small-pair branch

The pair core's order-two center equals the marked intersection of the chosen
module with the center of the ambient two-core. The source residual-centralization
hypothesis makes the module normal in the minimal-parabolic maximal subgroup,
which therefore fixes that line. The pair also fixes it, and together these two
subgroups generate the ambient group. Thus the line is ambient central.

This supplies the common central quotient in Aschbacher--Smith, E.2.17,
printed p.229. It uses the actual original witness and its quotient action.
-/

public section

open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.QuotientLift
variable {H : Type*} [Group H] [Finite H]
  {T : Sylow 2 H} {M V : Subgroup H}

omit [Finite H] in
theorem Pair.twoCore_le_core_normalizer (w : Pair T M V)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H)) :
    pCore 2 H ≤ normalizer (w.subgroup.pCoreIn 2 : Set H) := by
  have he : V ⊔ V.map (MulAut.conj (w.conjugator : H)).toMonoidHom = w.subgroup := by
    have hh := congrArg (fun A : Subgroup w.subgroup => A.map w.subgroup.subtype) w.generate
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le w.le,
      ← MonoidHom.range_eq_map, range_subtype] at hh
    rw [map_map] at hh
    have hm : w.subgroup.subtype.comp (MulAut.conj w.conjugator).toMonoidHom =
        (MulAut.conj (w.conjugator : H)).toMonoidHom.comp w.subgroup.subtype := by
      ext x
      rfl
    rw [hm, ← map_map, map_subgroupOf_eq_of_le w.le] at hh
    exact hh
  exact (he ▸ ChapterE.twoCore_le_normalizer_conjugate_join T V hTV (w.conjugator : H)).trans
    (normalizer_le_normalizer_characteristic_image w.subgroup (pCore 2 w.subgroup))

theorem Pair.core_center_eq_marked_ambient_center (w : Pair T M V)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hfit : generalizedFitting H = pCore 2 H)
    (hPQ : w.subgroup.pCoreIn 2 ≤ pCore 2 H)
    (hCV : w.subgroup.pCoreIn 2 ⊓ centralizer (V : Set H) = w.subgroup.pCoreIn 2 ⊓ V)
    (hZ : Nat.card (center (w.subgroup.pCoreIn 2)) = 2) :
    (center (w.subgroup.pCoreIn 2)).map (w.subgroup.pCoreIn 2).subtype =
      V ⊓ (center (pCore 2 H)).map (pCore 2 H).subtype := by
  let P := w.subgroup.pCoreIn 2
  let Q := pCore 2 H
  let Z := (center P).map P.subtype
  have hZI : w.subgroup ≤ centralizer (Z : Set H) := by
    apply le_trans ?_ (normalizer_le_centralizer_of_card_two Z (by
      rw [card_map_of_injective P.subtype_injective]; exact hZ))
    apply le_trans ?_ (normalizer_le_normalizer_characteristic_image P (center P))
    exact w.subgroup.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image w.subgroup (pCore 2 w.subgroup))
  have hZV : Z ≤ V := by
    have hh : Z ≤ P ⊓ centralizer (V : Set H) :=
      le_inf (map_subtype_le _) (le_centralizer_iff.mp (w.le.trans hZI))
    exact (hh.trans_eq hCV).trans inf_le_right
  have hZQ : Q ≤ centralizer (Z : Set H) :=
    ((w.twoCore_le_core_normalizer hTV).trans
      (normalizer_le_normalizer_characteristic_image P (center P))).trans
      (normalizer_le_centralizer_of_card_two Z (by
        rw [card_map_of_injective P.subtype_injective]; exact hZ))
  have hcentral : w.subgroup ⊓ centralizer (P : Set H) ≤ P := by
    intro x hx
    have hc : (⟨x,hx.1⟩ : w.subgroup) ∈ centralizer (pCore 2 w.subgroup : Set w.subgroup) := by
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.mp hx.2 y
        (mem_map_of_mem w.subgroup.subtype hy))
    have hh : (⟨x,hx.1⟩ : w.subgroup) ∈ pCore 2 w.subgroup := by
      rw [←w.fitting hTV hfit]
      exact centralizer_generalizedFitting_le w.subgroup (by
        simpa only [w.fitting hTV hfit] using hc)
    exact mem_map_of_mem w.subgroup.subtype hh
  change Z = V ⊓ (center Q).map Q.subtype
  apply le_antisymm
  · intro z hz
    have hzQ : z ∈ Q := hPQ ((map_subtype_le (center P)) hz)
    refine ⟨hZV hz,⟨⟨z,hzQ⟩,?_,rfl⟩⟩
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext ((mem_centralizer_iff.mp (hZQ q.property)) z hz).symm
  · rintro x ⟨hxV,y,hy,rfl⟩
    have hcQ : (y : H) ∈ centralizer (Q : Set H) := by
      intro q hq
      exact congrArg Subtype.val (mem_center_iff.mp hy ⟨q,hq⟩)
    have hcP : (y : H) ∈ centralizer (P : Set H) := centralizer_le hPQ hcQ
    have hyP : (y : H) ∈ P := hcentral ⟨w.le hxV,hcP⟩
    refine ⟨⟨y,hyP⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro p
    exact Subtype.ext (mem_centralizer_iff.mp hcP p p.property)
theorem Pair.core_center_le_ambient_center (w : Pair T M V)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H))
    (hfit : generalizedFitting H = pCore 2 H)
    (hPQ : w.subgroup.pCoreIn 2 ≤ pCore 2 H)
    (hCV : w.subgroup.pCoreIn 2 ⊓ centralizer (V : Set H) = w.subgroup.pCoreIn 2 ⊓ V)
    (hZ : Nat.card (center (w.subgroup.pCoreIn 2)) = 2)
    (hM : IsCoatom M) (hMV : M ≤ normalizer (V : Set H))
    (hne : Nat.card (w.subgroup ⧸ (M.subgroupOf w.subgroup).normalCore) ≠ 1) :
    (center (w.subgroup.pCoreIn 2)).map (w.subgroup.pCoreIn 2).subtype ≤ center H := by
  let P := w.subgroup.pCoreIn 2
  let Z := (center P).map P.subtype
  have hcard : Nat.card Z = 2 := by
    rw [card_map_of_injective P.subtype_injective]
    exact hZ
  have hZI : w.subgroup ≤ normalizer (Z : Set H) :=
    (w.subgroup.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image w.subgroup (pCore 2 w.subgroup))).trans
      (normalizer_le_normalizer_characteristic_image P (center P))
  have hZM : M ≤ normalizer (Z : Set H) := by
    rw [show Z = V ⊓ (center (pCore 2 H)).map (pCore 2 H).subtype from
      w.core_center_eq_marked_ambient_center hTV hfit hPQ hCV hZ]
    apply le_trans (le_inf hMV ?_) inf_normalizer_le_normalizer_inf
    exact (le_top.trans le_normalizer_of_normal).trans
      (normalizer_le_normalizer_characteristic_image (pCore 2 H) (center (pCore 2 H)))
  have hIM : ¬ w.subgroup ≤ M := by
    intro hi
    apply hne
    have he : M.subgroupOf w.subgroup = ⊤ := top_unique (fun x _ => hi x.property)
    rw [he,normalCore_eq_self]
    simp
  have hgen : M ⊔ w.subgroup = ⊤ := hM.2 _ (lt_of_le_of_ne le_sup_left (by
    intro he
    exact hIM ((show w.subgroup ≤ M ⊔ w.subgroup from le_sup_right).trans_eq he.symm)))
  apply centralizer_eq_top_iff_subset.mp
  apply top_unique
  rw [←hgen]
  exact (sup_le hZM hZI).trans (normalizer_le_centralizer_of_card_two Z hcard)

end CFSG.Quasithin.ChapterE.Witnesses.QuotientLift

namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
  {S : Sylow 2 H} {W U : Subgroup H} [IsElementaryAbelian 2 W] {n : ℕ}
theorem OriginalWitness.small_center_of_solvable
    {κ : GroupClass} (hH : IsSQTK κ H)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) (hs : Group.IsSolvable H)
    (w : OriginalWitness S (ChapterB.minimalParabolicMax S hP) W n)
    (hWS : W ≤ (S : Subgroup H))
    (hSW : (S : Subgroup H) ≤ normalizer (W : Set H))
    (hcore : W ≤ (ChapterB.minimalParabolicMax S hP).pCoreIn 2)
    (hout : ¬ W ≤ ChapterB.minimalParabolicCore S hP)
    (hfit : generalizedFitting H = pCore 2 H) (hW : Nat.card W = 16)
    (hSU : (S : Subgroup H) ≤ U) (hU : U ≤ normalizer (W : Set H))
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (W : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U W hU q hq hk))
    (hres : (pResidual 2 (ChapterB.minimalParabolicMax S hP)).map
      (ChapterB.minimalParabolicMax S hP).subtype ≤ centralizer (W : Set H)) :
    let Z := (center (w.pair.subgroup.pCoreIn 2)).map (w.pair.subgroup.pCoreIn 2).subtype
    Z ≤ center H ∧ Z = W ⊓ (center (pCore 2 H)).map (pCore 2 H).subtype := by
  let M := ChapterB.minimalParabolicMax S hP
  have hSM : (S : Subgroup H) ≤ M := (ChapterB.minimalParabolicMax_spec S hP).2
  have hMV : M ≤ normalizer (W : Set H) := by
    have he := congrArg (Subgroup.map M.subtype) (pResidual_sup_sylow_eq_top (S.subtype hSM))
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hSM,
      ←MonoidHom.range_eq_map,range_subtype] at he
    rw [←he]
    exact sup_le (hres.trans (Subgroup.centralizer_le_normalizer _)) hSW
  have hn := ChapterE.minimalParabolic_normalizer_le S hP W
    (IsElementaryAbelian.isPGroup 2 W) hSW hout
  have hplacement := w.small_core_placement_of_solvable hH hP hs hWS hSW hcore hout
    hfit hW hSU hU q hq hk hD hratio
  have hsmall := w.small_quaternion_core hWS hSW hcore hn hfit hW hSU hU q hq hk hD hratio
  obtain ⟨d⟩ := hsmall.1
  exact ⟨w.pair.core_center_le_ambient_center hSW hfit hplacement.1 hsmall.2.2.1
      d.center_card (ChapterB.minimalParabolicMax_spec S hP).1 hMV w.model.card_ne_one,
    w.pair.core_center_eq_marked_ambient_center hSW hfit hplacement.1 hsmall.2.2.1
      d.center_card⟩
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
