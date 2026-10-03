module

public import Stellmacher.Recognition.Parrott.DerivedTQuotient
public import Stellmacher.Recognition.Parrott.CoreQuotientAction

/-!
# The derived quotient image of the first centralizer

The image of C_T(t)′ in J/J′ has order four. The square-fixed calculation
bounds it above by four. For the lower bound, displacements of the order-eight
image of C_J(t) lift to commutators in C_T(t). Their kernel has at most two
elements, the fixed points of the order-four actor on J/J′.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.676–677, especially the computation of K′ on p.677.
-/

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- The actual derived centralizer has image of order four in J/J′. -/
public theorem t_centralizer_derived_quotient_card
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let i := H.subtype.comp J.subtype
    let E := (commutator J).map i
    let q := QuotientGroup.mk' (commutator J)
    ∀ t ∈ E, t ∉ zpowers z →
      let C := (d.sylow : Subgroup G) ⊓ centralizer ({t} : Set G)
      Nat.card C = 1024 →
      Nat.card ((((commutator C).map C.subtype).comap i).map q) = 4 := by
  intro H J i E q t ht htz C hC
  let D := (commutator C).map C.subtype
  let V := (D.comap i).map q
  let W := J ⧸ commutator J
  obtain ⟨hElem, hWcard⟩ := parrott_core_abelianization_structure z h
  let : IsElementaryAbelian 2 W := hElem
  obtain ⟨f, hf, heval⟩ := parrott_core_quotient_action z h
  obtain ⟨y, hy, hyorder, hbound⟩ :=
    d.t_centralizer_derived_quotient_square_fixed h t ht htz hC f hf heval
  let a : MulAut W := f (QuotientGroup.mk' J y)
  obtain ⟨φ, hφ, ⟨e⟩⟩ := h.quotient_model
  have hcards : Nat.card (FixedPoints.subgroup (zpowers a) W) = 2 ∧
      Nat.card (FixedPoints.subgroup (zpowers (a ^ 2)) W) = 4 := by
    have hh := Theory.GroupAction.five_four_sixteen_order_four_fixed_cards hWcard φ hφ
      (f.comp e.symm.toMonoidHom) (hf.comp e.symm.injective)
      (e (QuotientGroup.mk' J y)) ((e.orderOf_eq _).trans hyorder)
    have heq : (f.comp e.symm.toMonoidHom) (e (QuotientGroup.mk' J y)) = a := by
      change f (e.symm (e (QuotientGroup.mk' J y))) = f (QuotientGroup.mk' J y)
      rw [e.symm_apply_apply]
    exact (congrArg (fun b : MulAut W =>
      Nat.card (FixedPoints.subgroup (zpowers b) W) = 2 ∧
        Nat.card (FixedPoints.subgroup (zpowers (b ^ 2)) W) = 4) heq).mp hh
  have hupper : Nat.card V ≤ 4 := by
    apply (card_le_of_le (show V ≤ FixedPoints.subgroup (zpowers (a ^ 2)) W from ?_)).trans_eq hcards.2
    rintro _ ⟨b, hb, rfl⟩
    apply (MulAut.mem_fixed_zpowers_iff _ _).mpr
    exact hbound b hb
  let U := ((centralizer ({t} : Set G)).comap i).map q
  have hUcard : Nat.card U = 8 :=
    (parrott_derived_core_centralizer_hyperplane z h t ht htz).2.2
  let s : W →* W := {
    toFun := fun w => a w * w⁻¹
    map_one' := by simp
    map_mul' := by intros; simp only [map_mul, mul_inv_rev]; ac_rfl }
  have hker : s.ker = FixedPoints.subgroup (zpowers a) W := by
    ext w
    rw [MonoidHom.mem_ker, MulAut.mem_fixed_zpowers_iff]
    change a w * w⁻¹ = 1 ↔ a w = w
    exact mul_inv_eq_one
  have hlow : U.map s ≤ V := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨b, hb, rfl⟩ := hu
    let b' : J := ⟨y * (b : H) * y⁻¹,
      Subgroup.Normal.conj_mem (inferInstance : J.Normal) b b.property y⟩
    have heq : s (q b) = q (b' * b⁻¹) := by
      change a (q b) * (q b)⁻¹ = q (b' * b⁻¹)
      rw [map_mul, map_inv, show a (q b) = q b' from heval y b b' rfl]
    rw [heq]
    apply mem_map_of_mem
    change i (b' * b⁻¹) ∈ D
    rw [show D = ⁅C, C⁆ from map_subtype_commutator C]
    exact commutator_mem_commutator hy
      ⟨d.core_le_sylow (mem_map_of_mem H.subtype b.property), hb⟩
  have hkerle : Nat.card (U ⊓ s.ker : Subgroup W) ≤ 2 := by
    have hh := card_le_of_le (show U ⊓ s.ker ≤ s.ker from inf_le_right)
    exact hh.trans_eq (by rw [hker, hcards.1])
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup W) (U ⊓ s.ker) U bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, relIndex_ker, hUcard] at hcount
  have hle := card_le_of_le hlow
  change Nat.card V = 4
  nlinarith

end Stellmacher.Recognition.ParrottSecondElementaryData
