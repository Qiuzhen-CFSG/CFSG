module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Cyclic displacements in separated quadratic actions

Suppose a group acts quadratically on C = V A, with A normal. If b fixes A
and q fixes V, the displacement of bq is the join of the two individual
displacements. If C is abelian and those displacements are disjoint, their
orders multiply. The proof keeps both factors: it expands commutators on
V and A and uses quadraticity to control all powers of each actor.

This is a general group-action calculation used for the original-radical
comparison in Meierfrankenfeld--Stellmacher (1993), (3.7), pp.872--875.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

/-- Controlling the generator controls all powers when it normalizes the target. -/
theorem cyclic_commutator_le_of_normalizes (C N : Subgroup G) (b : G)
    (hn : b ∈ normalizer (N : Set G))
    (hc : ∀ c ∈ C, ⁅c,b⁆ ∈ N) : ⁅C,zpowers b⁆ ≤ N := by
  apply commutator_le.mpr
  intro c hcC y hy
  obtain ⟨m,rfl⟩ := mem_zpowers_iff.mp hy
  have hb : ⁅c,b⁆ ∈ N := hc c hcC
  have hbi : ⁅c,b⁻¹⁆ ∈ N := by
    rw [commutatorElement_inv_right,←commutatorElement_inv]
    simpa only [inv_inv] using (mem_normalizer_iff.mp ((normalizer _).inv_mem hn) _).mp (N.inv_mem hb)
  apply zpow_induction_left (P := fun x => ⁅c,x⁆ ∈ N) (by simp)
  · intro x hx
    rw [commutatorElement_mul_right_eq_mul_conj]
    simpa only [mul_assoc] using N.mul_mem hb ((mem_normalizer_iff.mp hn _).mp hx)
  · intro x hx
    rw [commutatorElement_mul_right_eq_mul_conj]
    simpa only [mul_assoc] using N.mul_mem hbi ((mem_normalizer_iff.mp ((normalizer _).inv_mem hn) _).mp hx)

/-- In a quadratic action, actors fixing the opposite factors have independent
cyclic displacements on their sum. -/
theorem separated_cyclic_displacement (C V A T : Subgroup G) [A.Normal]
    (hC : C = V ⊔ A) (hquad : ⁅⁅C,T⁆,T⁆ = ⊥)
    (b q : G) (hb : b ∈ T) (hq : q ∈ T)
    (hbA : b ∈ centralizer (A : Set G)) (hqV : q ∈ centralizer (V : Set G)) :
    ⁅C,zpowers (b*q)⁆ = ⁅C,zpowers b⁆ ⊔ ⁅C,zpowers q⁆ := by
  let W := ⁅C,T⁆
  have hWT : W ≤ centralizer (T : Set G) := commutator_eq_bot_iff_le_centralizer.mp hquad
  have hn (N : Subgroup G) (hN : N ≤ W) (x : G) (hx : x ∈ T) :
      x ∈ normalizer (N : Set G) :=
    Subgroup.centralizer_le_normalizer _ (fun v hv => (hWT (hN hv) x hx).symm)
  have hrow (x : G) (hx : x ∈ T) : ⁅C,zpowers x⁆ ≤ W :=
    commutator_mono le_rfl (zpowers_le.mpr hx)
  have hV : V ≤ C := le_sup_left.trans_eq hC.symm
  have hA : A ≤ C := le_sup_right.trans_eq hC.symm
  have hsplit (x : G) (hx : x ∈ T) (L J : Subgroup G) [J.Normal]
      (he : C = L ⊔ J) (hfix : x ∈ centralizer (J : Set G)) :
      ⁅C,zpowers x⁆ = ⁅L,zpowers x⁆ := by
    have hLC : L ≤ C := le_sup_left.trans_eq he.symm
    have hNW : ⁅L,zpowers x⁆ ≤ W := (commutator_mono hLC le_rfl).trans (hrow x hx)
    apply le_antisymm _ (commutator_mono hLC le_rfl)
    apply cyclic_commutator_le_of_normalizes _ _ x (hn _ hNW x hx)
    intro c hc
    rw [he] at hc
    obtain ⟨l,hl,j,hj,rfl⟩ := mem_sup_of_normal_right.mp hc
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr (hfix j hj),mul_one,mul_inv_cancel,one_mul]
    exact commutator_mem_commutator hl (mem_zpowers x)
  have hCb := hsplit b hb V A hC hbA
  have hCq : ⁅C,zpowers q⁆ = ⁅A,zpowers q⁆ := by
    apply le_antisymm _ (commutator_mono hA le_rfl)
    apply cyclic_commutator_le_of_normalizes _ _ q
      (hn _ ((commutator_mono hA le_rfl).trans (hrow q hq)) q hq)
    intro c hc
    rw [hC,sup_comm] at hc
    obtain ⟨a,ha,v,hv,rfl⟩ := mem_sup_of_normal_left.mp hc
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr (hqV v hv),mul_one,mul_inv_cancel,one_mul]
    exact commutator_mem_commutator ha (mem_zpowers q)
  have hprod := hrow (b*q) (T.mul_mem hb hq)
  apply le_antisymm
  · apply cyclic_commutator_le_of_normalizes _ _ (b*q)
      (hn _ (sup_le (hrow b hb) (hrow q hq)) _ (T.mul_mem hb hq))
    intro c hc
    rw [commutatorElement_mul_right_eq_mul_conj]
    simpa only [mul_assoc] using (⁅C,zpowers b⁆ ⊔ ⁅C,zpowers q⁆).mul_mem
      (mem_sup_left (commutator_mem_commutator hc (mem_zpowers b)))
      (mem_sup_right ((mem_normalizer_iff.mp (hn _ (hrow q hq) b hb) _).mp
        (commutator_mem_commutator hc (mem_zpowers q))))
  · apply sup_le
    · rw [hCb]
      apply cyclic_commutator_le_of_normalizes _ _ b (hn _ hprod b hb)
      intro v hv
      have he : ⁅v,b*q⁆ = ⁅v,b⁆ := by
        rw [commutatorElement_mul_right_eq_mul_conj,
          commutatorElement_eq_one_iff_commute.mpr (hqV v hv)]
        simp
      exact he ▸ commutator_mem_commutator (hV hv) (mem_zpowers (b*q))
    · rw [hCq]
      apply cyclic_commutator_le_of_normalizes _ _ q (hn _ hprod q hq)
      intro a ha
      have he : ⁅a,b*q⁆ = ⁅a,q⁆ := by
        rw [commutatorElement_mul_right_eq_mul_conj,
          commutatorElement_eq_one_iff_commute.mpr (hbA a ha),one_mul,
          (hWT (hrow q hq (commutator_mem_commutator (hA ha) (mem_zpowers q))) b hb),
          mul_inv_cancel_right]
      exact he ▸ commutator_mem_commutator (hA ha) (mem_zpowers (b*q))
/-- Disjoint displacements in an abelian group multiply their orders. -/
theorem separated_cyclic_displacement_card [Finite G]
    (C V A T : Subgroup G) [C.Normal] [A.Normal] [IsMulCommutative C]
    (hC : C = V ⊔ A) (hquad : ⁅⁅C,T⁆,T⁆ = ⊥)
    (b q : G) (hb : b ∈ T) (hq : q ∈ T)
    (hbA : b ∈ centralizer (A : Set G)) (hqV : q ∈ centralizer (V : Set G))
    (hdis : Disjoint ⁅C,zpowers b⁆ ⁅C,zpowers q⁆) :
    Nat.card (⁅C,zpowers (b*q)⁆ : Subgroup G) =
      Nat.card (⁅C,zpowers b⁆ : Subgroup G) * Nat.card (⁅C,zpowers q⁆ : Subgroup G) := by
  rw [separated_cyclic_displacement C V A T hC hquad b q hb hq hbA hqV]
  apply card_sup_eq_mul_of_normalizes_of_disjoint _ _ _ hdis
  exact (commutator_le_left _ _).trans
    ((C.le_centralizer.trans (centralizer_le (commutator_le_left _ _))).trans
      (Subgroup.centralizer_le_normalizer _))
/-- Inclusion of literal conjugation images gives inclusion of displacements. -/
theorem commutator_le_of_conjNormal_image_le (C L J : Subgroup G) [C.Normal]
    (h : L.map (MulAut.conjNormal (H := C)) ≤ J.map (MulAut.conjNormal (H := C))) :
    ⁅C,L⁆ ≤ ⁅C,J⁆ := by
  apply commutator_le.mpr
  intro c hc a ha
  obtain ⟨b,hb,he⟩ := h (mem_map_of_mem _ ha)
  have hv := congrArg Subtype.val (DFunLike.congr_fun he (⟨c,hc⟩ : C))
  change b*c*b⁻¹=a*c*a⁻¹ at hv
  have hd : ⁅b,c⁆=⁅a,c⁆ := by
    simpa only [commutatorElement_def,mul_assoc] using congrArg (fun x : G => x*c⁻¹) hv
  have hd' := congrArg Inv.inv hd
  rw [commutatorElement_inv,commutatorElement_inv] at hd'
  rw [←hd']
  exact commutator_mem_commutator hc hb
end Subgroup
