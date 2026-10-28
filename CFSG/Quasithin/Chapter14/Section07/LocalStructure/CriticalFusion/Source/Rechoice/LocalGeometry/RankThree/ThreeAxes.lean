module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.ThreeAxes.Coordinates
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.ThreeAxes.Transport

/-!
# The actual three-axis action in the moved-plane argument

If an element of T moves E, the points V₁, Zα and Zαᵗ span the literal
commutator F. The two core axis actions and the conjugate reciprocal action
therefore give all automorphisms of F. The generated ambient subgroup is
exactly Y_E joined with Y_Eᵗ, and its action is literal conjugation. A cubic
image fixing the original point has a lift in its centralizer; no order-three
lift in the ambient group is assumed.

Source: Aschbacher–Smith, proof of 14.7.70, printed pp.1073–1074.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.ThreeAxes
open Subgroup Representation Chapter12.Section08
open scoped commutatorElement
noncomputable section
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

def source_action (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (h : Preliminary d c) (h15 : ⁅F.U, F.H.pCoreIn 2⁆ ≤ F.Vi 1)
    (axes : CoreAxes c) (t : G) (ht : t ∈ (T : Subgroup G))
    (hm : t ∉ normalizer (E c : Set G)) : MovedPlane.ThreeAxisAction d c h t := by
  let A := Fcomm c
  let C := YE c ⊔ conjugate (YE c) t
  let a := MulAut.conj t⁻¹
  have hAt : A.map a.toMonoidHom = A :=
    (conjugate_eq_iff _ _).mpr (h.commutator_normalized ht)
  have hY : YE c ≤ normalizer (A : Set G) := h.YE_normalizes_commutator h15
  have hYt : conjugate (YE c) t ≤ normalizer (A : Set G) := by
    change (YE c).map a.toMonoidHom ≤ _
    have hh := (map_mono hY).trans (le_normalizer_map a.toMonoidHom)
    simpa only [hAt] using hh
  have hC : C ≤ normalizer (A : Set G) := sup_le hY hYt
  let P : Fin 3 → Subgroup G := ![F.Vi 1, c.Zα, conjugate c.Zα t]
  have hPA : ∀ i, P i ≤ A := by
    intro i
    fin_cases i
    · exact h.point_le
    · exact h.opposite_le
    · exact (map_mono h.opposite_le).trans_eq hAt
  have hcP : ∀ i, Nat.card (P i) = 2 := by
    intro i
    fin_cases i
    · exact F.card 1 (by decide)
    · exact opposite_card c
    · change Nat.card (c.Zα.map a.toMonoidHom) = 2
      rw [card_map_of_injective a.injective, opposite_card c]
  have h2 : ¬ P 2 ≤ P 0 ⊔ P 1 := by
    intro hh
    have hle : A ≤ E c := by
      rw [show A = movedSpan c t from (h.moved_span_eq_commutator t ht hm).symm]
      exact sup_le le_rfl hh
    have hc := card_le_of_le hle
    rw [h.commutator_card, h.E_card] at hc
    omega
  letI : IsElementaryAbelian 2 A := by
    let := d.U_elementary
    exact IsElementaryAbelian.of_le (h.commutator_le.trans inf_le_left)
  let e : Linear.Model ≃* A := Classical.choose
    (coordinates A h.commutator_card P hPA hcP h.opposite_disjoint_point h2)
  have he : ∀ i, ((Linear.axis i).map e.toMonoidHom).map A.subtype = P i :=
    Classical.choose_spec (coordinates A h.commutator_card P hPA hcP h.opposite_disjoint_point h2)
  have haxes : ∀ i, RealizesAxis A (P i) C := by
    intro i
    fin_cases i
    · exact realizesAxis_mono axes.original (le_sup_left.trans le_sup_left)
    · exact realizesAxis_mono axes.reciprocal (le_sup_right.trans le_sup_left)
    · apply realizesAxis_mono (realizesAxis_map A c.Zα c.Qα a hAt axes.reciprocal)
      exact (map_mono le_sup_right).trans le_sup_right
  let ρ : C →* MulAut A := A.normalizerMonoidHom.comp (inclusion hC)
  have hfull : Function.Surjective ρ := Linear.full_action A e C hC P he haxes
  have hcubic : ∃ q : C, orderOf (ρ q) = 3 ∧
      (q : G) ∈ centralizer ({d.z} : Set G) := by
    obtain ⟨f,hf,hfix⟩ := Linear.exists_cubic_fixing_first A e P he
    obtain ⟨q,hq⟩ := hfull f
    have hzP : d.z ∈ P 0 := by
      change d.z ∈ F.Vi 1
      rw [d.point]
      exact mem_zpowers _
    let zA : A := ⟨d.z,h.point_le hzP⟩
    have hzfix : ρ q zA = zA := by rw [hq]; exact hfix zA hzP
    have hzconj : (q : G) * d.z * (q : G)⁻¹ = d.z := congrArg Subtype.val hzfix
    have hqcent : (q : G) ∈ centralizer ({d.z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have hh := congrArg (fun w => w * (q : G)) hzconj
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
    refine ⟨q,?_,hqcent⟩
    rw [hq]
    exact hf
  refine {
    axes := axes
    carrier := C
    action := ρ
    carrier_normalizes := hC
    centralizer_to_H := ?_
    full := hfull
    cubic := hcubic }
  intro q hq
  rwa [d.centralizer_eq]
end
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.ThreeAxes
