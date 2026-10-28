module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# A centralizer supplement from an invariant conjugate

Let W be an abelian subgroup normalized by R and contained in Q=C_R(W).
An automorphism preserving R gives a conjugate W' whose R-centralizer has
order |Q|. If C_R(W') lies in W'Q, its order calculation identifies
[Q:C_Q(W')] with [W':W'∩Q]. A sharp bound by [W:C_W(W')] then forces
Q=W C_Q(W'). No elementary or commutative hypothesis on Q is required.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
3.3.28, printed p.601. The literal G₂ application is in Chapter12's
FusionReducibleNormalizerBlockCentralizerG2Factorization.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem fixedIndex_join_eq (Q W C : Subgroup G)
    (hWQ : W ≤ Q) (hCQ : C ≤ Q) (hi : C.relIndex Q ≤ C.relIndex W) :
    Q = W ⊔ C := by
  have hs : W ⊔ C ≤ Q := sup_le hWQ hCQ
  have he : C.relIndex (W ⊔ C) = C.relIndex Q := le_antisymm
    (relIndex_le_of_le_right hs index_ne_zero_of_finite)
    (hi.trans (relIndex_le_of_le_right le_sup_left index_ne_zero_of_finite))
  have hm := relIndex_mul_relIndex C (W ⊔ C) Q le_sup_right hs
  rw [he] at hm
  have hp : 0 < C.relIndex Q := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hu : (W ⊔ C).relIndex Q = 1 :=
    Nat.mul_left_cancel hp (hm.trans (Nat.mul_one _).symm)
  exact le_antisymm (relIndex_eq_one.mp hu) hs

omit [Finite G] in
private theorem centralizer_map_equiv (W : Subgroup G) (e : G ≃* G) :
    (centralizer (W : Set G)).map e.toMonoidHom =
      centralizer (W.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- Equal conjugate-centralizer orders and a sharp fixed index give the
original core as the product of the module and its conjugate fixed subgroup. -/
theorem centralizer_supplement_of_conjugate_sharp_index
    (R Q W : Subgroup G) [IsMulCommutative W] (e : G ≃* G)
    (hWQ : W ≤ Q) (hRW : R ≤ normalizer (W : Set G))
    (hQ : Q = R ⊓ centralizer (W : Set G))
    (hR : R.map e.toMonoidHom = R)
    (hcover : R ⊓ centralizer (W.map e.toMonoidHom : Set G) ≤
      W.map e.toMonoidHom ⊔ Q)
    (hsharp : Q.relIndex (W.map e.toMonoidHom) ≤
      (centralizer (W.map e.toMonoidHom : Set G)).relIndex W) :
    Q = W ⊔ (Q ⊓ centralizer (W.map e.toMonoidHom : Set G)) := by
  let B := W.map e.toMonoidHom
  let C := Q ⊓ centralizer (B : Set G)
  let K := R ⊓ centralizer (B : Set G)
  have hQR : Q ≤ R := hQ.le.trans inf_le_left
  have hBR : B ≤ R := (map_mono (hWQ.trans hQR)).trans_eq hR
  have hRQ : R ≤ normalizer (Q : Set G) := by
    intro r hr
    have hrW : W.map (MulAut.conj r).toMonoidHom = W :=
      mem_normalizer_iff_map_conj_eq.mp (hRW hr)
    have hrR : R.map (MulAut.conj r).toMonoidHom = R :=
      mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer hr)
    apply mem_normalizer_iff_map_conj_eq.mpr
    change Q.map (MulAut.conj r).toMonoidHom = Q
    rw [hQ, map_inf _ _ _ (MulAut.conj r).injective,
      centralizer_map_equiv W (MulAut.conj r), hrW, hrR]
  have hmap : Q.map e.toMonoidHom = K := by
    rw [hQ, map_inf _ _ _ e.injective, hR, centralizer_map_equiv]
  have hcard : Nat.card K = Nat.card Q :=
    hmap ▸ card_map_of_injective (f := e.toMonoidHom) e.injective
  have hK : K = B ⊔ C := by
    apply le_antisymm
    · intro x hx
      have hxp : x ∈ (B : Set G) * (Q : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right B Q (hBR.trans hRQ)]
        exact hcover hx
      obtain ⟨b, hb, q, hq, rfl⟩ := hxp
      have hqc : q ∈ centralizer (B : Set G) := by
        simpa only [inv_mul_cancel_left] using
          (centralizer (B : Set G)).mul_mem
            ((centralizer (B : Set G)).inv_mem (B.le_centralizer hb)) hx.2
      exact mul_mem_sup hb ⟨hq, hqc⟩
    · exact sup_le (le_inf hBR B.le_centralizer)
        (le_inf (inf_le_left.trans hQR) inf_le_right)
  have hBC : B ⊓ C = B ⊓ Q := by
    apply le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans B.le_centralizer))
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes B C
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  rw [hBC, ← hK, hcard] at hp
  have hBcard : Nat.card (B ⊓ Q : Subgroup G) * Q.relIndex B = Nat.card B := by
    simpa only [relIndex_bot_left, inf_relIndex_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) (B ⊓ Q) B bot_le inf_le_left
  have hc : Nat.card C * Q.relIndex B = Nat.card Q := by
    apply Nat.mul_left_cancel (Nat.card_pos (α := (B ⊓ Q : Subgroup G)))
    calc
      Nat.card (B ⊓ Q : Subgroup G) * (Nat.card C * Q.relIndex B) =
          (Nat.card (B ⊓ Q : Subgroup G) * Q.relIndex B) * Nat.card C := by ac_rfl
      _ = Nat.card B * Nat.card C := by rw [hBcard]
      _ = _ := hp
  have hCQ : C ≤ Q := inf_le_left
  have hcQ := relIndex_mul_relIndex (⊥ : Subgroup G) C Q bot_le hCQ
  simp only [relIndex_bot_left] at hcQ
  have hi : C.relIndex Q = Q.relIndex B :=
    Nat.mul_left_cancel (Nat.card_pos (α := C)) (hcQ.trans hc.symm)
  have hCW : C.relIndex W = (centralizer (B : Set G)).relIndex W := by
    rw [← inf_relIndex_right C W, ← inf_relIndex_right (centralizer (B : Set G)) W]
    congr 1
    ext x
    exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨hWQ hx.2, hx.1⟩, hx.2⟩⟩
  exact fixedIndex_join_eq Q W C hWQ hCQ (by rw [hi, hCW]; exact hsharp)
end Subgroup
