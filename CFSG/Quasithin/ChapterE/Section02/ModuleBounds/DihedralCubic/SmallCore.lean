module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallAutomizer
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoQuaternion
public import Theory.GroupTheory.QuaternionCentralProductIntrinsic

/-!
# Intrinsic quaternion factors for the E.2.17 pair core

For the small automizer action, fixed codimension three on V of order sixteen
forces C_V(A)=Z. Writing P=BA then puts Z(P) inside A. The center is normal
in the two-conjugate group, so conjugacy of B and A also puts it inside B;
hence Z(P)=Z. The actual central quotient P/Z is elementary abelian, and
the order-thirty-two core is extraspecial. Its marked elementary eight B
then supplies two embedded quaternion factors generating P.

This proves the first paragraph's Q₈∘Q₈ geometry directly in the actual
pair core. It retains the dihedral quotient premise and does not identify
the pair with the full ambient normal closure.

Source: Aschbacher–Smith, E.2.17, printed p.229. The source application is
SmallCoreAction, using the original quotient map and chosen V.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X D Q : Type*} [Group X] [Finite X] [Group D] [Finite D]
  [Group Q] [Finite Q] [IsElementaryAbelian 2 Q]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

/-- The actual V-fixed subgroup of A is its intersection with the conjugate V. -/
theorem V_inf_centralizer_A_eq_Z_of_small_automizer
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2)
    (hV : Nat.card V = 16)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (hD : Nat.card D ≤ 4) (hq : 1 < cubicRatio ρ) :
    V ⊓ centralizer (A V M g : Set X) = Z V g := by
  have hr := h.actor_rank_two_of_small_automizer hproper hfit hcard e ρ hρ f ha hD hq
  have hc := h.small_automizer_core_orders hproper hfit hcard hV e ρ hρ f ha hD hq
  have hqdim : Module.finrank (ZMod 2) (Additive Q) = 4 := by
    have hp := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Q)
    rw [← Nat.card_congr (Additive.ofMul : Q ≃ Additive Q),
      ← Nat.card_congr e.toEquiv, hV, Nat.card_zmod] at hp
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hp.symm
  have hfdim : Module.finrank (ZMod 2) (fixedSpace ρ f.range) = 1 := by
    have hb := fixedCodim_add_finrank ρ f.range
    rw [hr.2.2.2, hqdim] at hb
    omega
  have hfc : Nat.card (fixedSpace ρ f.range) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hfdim]
    decide
  let C := V ⊓ centralizer (A V M g : Set X)
  let j : C → fixedSpace ρ f.range := fun c =>
    ⟨Additive.ofMul (e ⟨c, c.property.1⟩),
      (h.mem_fixedSpace_actor e ρ f ha _).mpr (by
        simpa only [toMul_ofMul, e.symm_apply_apply] using
          (show (c : X) ∈ centralizer (A V M g : Set X) from c.property.2))⟩
  have hj : Function.Injective j := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun v : V => (v : X))
      (e.injective (congrArg (fun z : fixedSpace ρ f.range => z.val.toMul) he))
  have hCc := Nat.card_le_card_of_injective j hj
  rw [hfc] at hCc
  apply (eq_of_le_of_card_ge ?_ ?_).symm
  · exact le_inf inf_le_left
      ((h.core_geometry.2.2.trans inf_le_right).trans (center_le_centralizer _))
  · exact hc.2.2.1 ▸ hCc

/-- A self-centralizing factor determines the center of the pair core. -/
theorem center_P_eq_Z_of_V_fixed
    (h : Hypotheses T V M g)
    (hfix : V ⊓ centralizer (A V M g : Set X) = Z V g) :
    (center (P V M g)).map (P V M g).subtype = Z V g := by
  let := h.A_elementary
  let := h.core_geometry.1
  let C := (center (P V M g)).map (P V M g).subtype
  have hCA : C ≤ A V M g := by
    rintro x ⟨x, hx, rfl⟩
    obtain ⟨b, hb, a, ha, he⟩ := Set.mem_mul.mp
      (h.core_geometry.2.1 ▸ (show (x : X) ∈ (P V M g : Set X) from x.property))
    have hxCA : (x : X) ∈ centralizer (A V M g : Set X) := by
      intro a ha
      exact congrArg Subtype.val ((mem_center_iff.mp hx) ⟨a, mem_sup_right ha⟩)
    have haCA : a ∈ centralizer (A V M g : Set X) := (A V M g).le_centralizer ha
    have hbCA : b ∈ centralizer (A V M g : Set X) := by
      have hm := (centralizer (A V M g : Set X)).mul_mem hxCA
        ((centralizer _).inv_mem haCA)
      rwa [← he, mul_inv_cancel_right] at hm
    have hbZ : b ∈ Z V g := hfix ▸ ⟨hb.2, hbCA⟩
    change (x : X) ∈ A V M g
    rw [← he]
    exact (A V M g).mul_mem (h.Z_le_B_inf_A hbZ).2 ha
  apply le_antisymm
  · intro x hx
    have hxB : x ∈ B V M := by
      have hcg := hCA ((inferInstance : C.Normal).conj_mem x hx g)
      obtain ⟨b, hb, he⟩ := hcg
      have he' : (MulAut.conj g) b = (MulAut.conj g) x := he
      exact (MulAut.conj g).injective he' ▸ hb
    exact h.B_inf_A_eq_Z ▸ ⟨hxB, hCA hx⟩
  · intro z hz
    refine ⟨⟨z, (h.core_geometry.2.2 hz).1⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro p
    exact Subtype.ext ((mem_center_iff.mp (h.core_geometry.2.2 hz).2) p)

/-- The pair core is intrinsically extraspecial once its center is determined. -/
theorem P_extraspecial_of_center
    (h : Hypotheses T V M g)
    (hcenter : (center (P V M g)).map (P V M g).subtype = Z V g)
    (hZ : Nat.card (Z V g) = 2) (hP : Nat.card (P V M g) = 32) :
    IsExtraspecial 2 (P V M g) := by
  let := h.Z_normal
  let q := QuotientGroup.mk' (Z V g)
  let F := q.comp (P V M g).subtype
  have hker : F.ker = center (P V M g) := by
    ext x
    change (x : X) ∈ (QuotientGroup.mk' (Z V g)).ker ↔ x ∈ center (P V M g)
    rw [QuotientGroup.ker_mk']
    constructor
    · intro hx
      rw [← hcenter] at hx
      obtain ⟨y, hy, he⟩ := hx
      exact (P V M g).subtype_injective he ▸ hy
    · intro hx
      rw [← hcenter]
      exact mem_map_of_mem (P V M g).subtype hx
  have hF : F.range = (P V M g).map q := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact mem_map_of_mem q y.property
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let : IsElementaryAbelian 2 F.range := hF.symm ▸ h.quotient_direct_sum.1
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange F)
  have hc : Nat.card (center (P V M g)) = 2 := by
    rw [← card_map_of_injective (P V M g).subtype_injective, hcenter]
    exact hZ
  refine ⟨hc, IsElementaryAbelian.of_injective e.toMonoidHom e.injective, ?_⟩
  apply Finite.one_lt_card_iff_nontrivial.mp
  have hi := (center (P V M g)).card_mul_index
  rw [hc, hP] at hi
  change 1 < (center (P V M g)).index
  omega

/-- The actual elementary factor B identifies the plus-type central product. -/
theorem P_quaternion_factors_of_center
    (h : Hypotheses T V M g)
    (hcenter : (center (P V M g)).map (P V M g).subtype = Z V g)
    (hZ : Nat.card (Z V g) = 2) (hB : Nat.card (B V M) = 8)
    (hP : Nat.card (P V M g) = 32) :
    Nonempty (QuaternionCentralProductData (P V M g)) := by
  let := h.P_extraspecial_of_center hcenter hZ hP
  let := h.B_elementary
  let E := (B V M).subgroupOf (P V M g)
  have hBP : B V M ≤ P V M g := le_sup_left
  have hn : P V M g ≤ normalizer (B V M : Set X) :=
    sup_le (B V M).le_normalizer
      (le_normalizer_iff_commutator_le_right.mpr
        (h.commutator_A_B_le_Z.trans (h.Z_le_B_inf_A.trans inf_le_left)))
  let : E.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hBP
  have hE : Nat.card E = 8 := (Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv).trans hB
  have hZE : center (P V M g) ≤ E := by
    intro z hz
    have hzZ : (z : X) ∈ Z V g := hcenter ▸ mem_map_of_mem (P V M g).subtype hz
    exact (h.Z_le_B_inf_A hzZ).1
  obtain ⟨L, R, hL, hR, hgen, hint, hcomm⟩ :=
    exists_quaternion_factors_of_extraspecial_thirty_two_elementary hP E hE hZE
  exact ⟨⟨L, R, hL, hR, hint, hcomm, hgen⟩⟩

/-- The small-automizer branch produces quaternion factors inside the actual
pair core; the central product is not an unmarked replacement group. -/
theorem small_automizer_quaternion_core
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2)
    (hV : Nat.card V = 16)
    (e : V ≃* Q) (ρ : Representation (ZMod 2) D (Additive Q))
    (hρ : Function.Injective ρ) (f : A V M g →* D)
    (ha : ∀ (a : A V M g) (v : V),
      (e.symm (ρ (f a) (Additive.ofMul (e v))).toMul : X) =
        (a : X) * v * (a : X)⁻¹)
    (hD : Nat.card D ≤ 4) (hq : 1 < cubicRatio ρ) :
    (center (P V M g)).map (P V M g).subtype = Z V g ∧
      IsExtraspecial 2 (P V M g) ∧ Nonempty (QuaternionCentralProductData (P V M g)) := by
  have hc := h.small_automizer_core_orders hproper hfit hcard hV e ρ hρ f ha hD hq
  have hfix := h.V_inf_centralizer_A_eq_Z_of_small_automizer
    hproper hfit hcard hV e ρ hρ f ha hD hq
  have hcenter := h.center_P_eq_Z_of_V_fixed hfix
  exact ⟨hcenter, h.P_extraspecial_of_center hcenter hc.2.2.1 hc.2.2.2.1,
    h.P_quaternion_factors_of_center hcenter hc.2.2.1 hc.2.1 hc.2.2.2.1⟩

end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
