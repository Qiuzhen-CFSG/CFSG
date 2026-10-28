module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Targets
/-!
# The fixed-preimage index from one natural moving plane

Suppose Y = W [Y,P], Y/U is abelian, and the full-actor fixed preimage D
meets W inside U. An element of P fixing W modulo U puts every element
of D in W times the fixed preimage in ([Y,P] U)/U. When that moving
factor is the binary natural plane and the element acts nontrivially,
its fixed space has at most two elements. Relative product and intersection
indices therefore give |D/U| ≤ 2.

This avoids a splitting of the entire Y/U: the natural coordinates are
used only on the supplied moving factor. Normality remains inside Y.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank
two* (1993), (4.6.8), printed p.907.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreIndex

private theorem binary_fixed_card : ∀ a : SL2, a ≠ 1 →
    Nat.card {v : Multiplicative (Fin 2 → ZMod 2) // a.val.mulVec v.toAdd = v.toAdd} ≤ 2 := by
  simp only [Nat.card_eq_fintype_card]
  decide +kernel

private theorem natural_fixed_index_le_two {G : Type*} [Group G]
    {P S U E : Subgroup G} (n : RankOnePairing.RankOneFactor P S U)
    (hSN : S ≤ normalizer U) (e : P) (heE : (e:G) ∈ E)
    (he : n.projection e ≠ 1) :
    U.relIndex (commutatorPreimage S E U) ≤ 2 := by
  let F := commutatorPreimage S E U
  let I := (F.subgroupOf S).map n.coordinates
  have hF : F ≤ S := commutatorPreimage_le _ _ _
  have hfix (v : I) : (n.projection e).val.mulVec v.val.toAdd = v.val.toAdd := by
    obtain ⟨x,hx,hxv⟩ := v.property
    let y : S := ⟨(e:G) * (x:G) * (e:G)⁻¹,
      (mem_normalizer_iff.mp (n.normalized e.property) _).mp x.property⟩
    have hk : y * x⁻¹ ∈ n.coordinates.ker := by
      rw [n.kernel]
      have hc := commutator_commutatorPreimage_le S E U hSN
      rw [commutator_comm] at hc
      exact hc (commutator_mem_commutator heE hx)
    have hc : n.coordinates y = n.coordinates x := by
      have hh := MonoidHom.mem_ker.mp hk
      rwa [map_mul, map_inv, mul_inv_eq_one] at hh
    rw [← hxv, ← n.action e x y rfl, hc]
  let j : I → {v : Multiplicative (Fin 2 → ZMod 2) //
      (n.projection e).val.mulVec v.toAdd = v.toAdd} := fun v => ⟨v, hfix v⟩
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : {v : Multiplicative (Fin 2 → ZMod 2) //
      (n.projection e).val.mulVec v.toAdd = v.toAdd} => z.val) h
  have hcard : Nat.card I = U.relIndex F := by
    rw [← relIndex_ker, n.kernel, relIndex_subgroupOf hF]
  rw [← hcard]
  exact (Nat.card_le_card_of_injective j hj).trans (binary_fixed_card _ he)

private theorem index_le_of_intersection {G : Type*} [Group G]
    (Y D W U F : Subgroup G) [Finite Y]
    (hDY : D ≤ Y) (hWY : W ≤ Y) (hUD : U ≤ D) (hFY : F ≤ Y)
    (hUN : Y ≤ normalizer U) (hYY : ⁅Y,Y⁆ ≤ U)
    (hDU : D ⊓ W ≤ U) (hDF : D ≤ W ⊔ F) : U.relIndex D ≤ U.relIndex F := by
  let B := W ⊔ U
  have hUY := hUD.trans hDY
  have hBY : B ≤ Y := sup_le hWY hUY
  have hBFY : B ⊔ F ≤ Y := sup_le hBY hFY
  let : Finite ↥(B ⊔ F) := Finite.of_injective (inclusion hBFY) (inclusion_injective _)
  let : Finite F := Finite.of_injective (inclusion hFY) (inclusion_injective _)
  have hinter : B ⊓ D = U := by
    apply le_antisymm ?_ (le_inf le_sup_right hUD)
    rintro x ⟨hx,hxD⟩
    have hp : x ∈ (W : Set G) * (U : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ (hWY.trans hUN)]
      exact hx
    obtain ⟨w,hw,u,hu,rfl⟩ := hp
    have hwD : w ∈ D := by
      simpa only [mul_inv_cancel_right] using D.mul_mem hxD (D.inv_mem (hUD hu))
    exact U.mul_mem (hDU ⟨hwD,hw⟩) hu
  have hBN : Y ≤ normalizer B := le_normalizer_iff_commutator_le_right.mpr
    (((commutator_mono le_rfl hBY).trans hYY).trans le_sup_right)
  let : (B.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer hBN
  have hjoin : B.relIndex (B ⊔ F) = B.relIndex F := by
    have hh := relIndex_sup_left (F.subgroupOf Y) (B.subgroupOf Y)
    rwa [← subgroupOf_sup hBY hFY, relIndex_subgroupOf hBFY,
      relIndex_subgroupOf hFY] at hh
  calc
    U.relIndex D = B.relIndex D := by rw [← inf_relIndex_right B D, hinter]
    _ ≤ B.relIndex (B ⊔ F) := relIndex_le_of_le_right
      (hDF.trans (sup_le_sup le_sup_left le_rfl)) index_ne_zero_of_finite
    _ = B.relIndex F := hjoin
    _ ≤ U.relIndex F := relIndex_le_of_le_left le_sup_right index_ne_zero_of_finite

/-- A nonidentity natural-plane action fixing W modulo U bounds D/U by two.
This uses only the moving plane, not an action descent or a splitting on Y/U. -/
theorem fixed_index_le_two {G : Type*} [Group G]
    (P Y W U : Subgroup G) [Finite Y]
    (n : RankOnePairing.RankOneFactor P (⁅Y,P⁆ ⊔ U) U)
    (hYP : Y ≤ P) (hUY : U ≤ Y) (hPY : P ≤ normalizer Y)
    (hPU : P ≤ normalizer U) (hgen : Y = W ⊔ ⁅Y,P⁆)
    (hYY : ⁅Y,Y⁆ ≤ U)
    (hinter : commutatorPreimage Y P U ⊓ W ≤ U)
    (e : P) (he : n.projection e ≠ 1) (hWE : ⁅W, zpowers (e:G)⁆ ≤ U) :
    U.relIndex (commutatorPreimage Y P U) ≤ 2 := by
  let S := ⁅Y,P⁆ ⊔ U
  let E := zpowers (e:G)
  let F := commutatorPreimage S E U
  have hSY : S ≤ Y := sup_le (le_normalizer_iff_commutator_le_left.mp hPY) hUY
  have hWY : W ≤ Y := hgen ▸ le_sup_left
  have hYN : Y ≤ normalizer U := hYP.trans hPU
  have hWS : W ≤ normalizer S :=
    (le_inf (hWY.trans (normalizer_commutator_ge_left Y P))
      (hWY.trans hYN)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hgen' : Y = W ⊔ S := by
    dsimp [S]
    rw [← sup_assoc, ← hgen, sup_eq_left.mpr hUY]
  have hEP : E ≤ P := zpowers_le.mpr e.property
  have hDU : U ≤ commutatorPreimage Y P U := le_commutatorPreimage hUY
    (le_normalizer_iff_commutator_le_left.mp hPU)
  have hDF : commutatorPreimage Y P U ≤ W ⊔ F := by
    let C := commutatorPreimage Y E U
    have hDC : commutatorPreimage Y P U ≤ C := le_commutatorPreimage
      (commutatorPreimage_le _ _ _)
      ((commutator_mono le_rfl hEP).trans (commutator_commutatorPreimage_le _ _ _ hYN))
    have hWC : W ≤ C := le_commutatorPreimage hWY hWE
    intro d hd
    have hp : d ∈ (W : Set G) * (S : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hWS, ← hgen']
      exact commutatorPreimage_le _ _ _ hd
    obtain ⟨w,hw,s,hs,rfl⟩ := hp
    have hsC : s ∈ C := by
      simpa only [inv_mul_cancel_left] using C.mul_mem (C.inv_mem (hWC hw)) (hDC hd)
    have hCF : S ⊓ C ≤ F := le_commutatorPreimage inf_le_left
      ((commutator_mono inf_le_right le_rfl).trans
        (commutator_commutatorPreimage_le Y E U hYN))
    exact (W ⊔ F).mul_mem (mem_sup_left hw) (mem_sup_right (hCF ⟨hs,hsC⟩))
  exact (index_le_of_intersection Y _ W U F (commutatorPreimage_le _ _ _)
    hWY hDU ((commutatorPreimage_le _ _ _).trans hSY) hYN hYY hinter hDF).trans
      (natural_fixed_index_le_two n (hSY.trans hYN) e (mem_zpowers _) he)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.CoreIndex
