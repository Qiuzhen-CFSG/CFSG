module

public import CFSG.Quasithin.ChapterG.Section02.Binary.Completion

/-!
# The opposite core in the binary almost-special configuration

The natural S₃ module on S/S₂ identifies the kernel of U on the opposite
factor Wᵍ/S₂. Since O₂(H) centralizes U modulo the original point, this
kernel is exactly Wᵍ ∩ O₂(H)=S₂. Thus the elementary intersection S₂ has
index at most twice |T:O₂(H)| in U. If the Sylow image of H/O₂(H) is cyclic,
the opposite image is also elementary, so that index is at most four.

These are the literal G.2.3 quotient and conjugation maps. The U-containment
and commutator assumptions are the preceding G.2.2 conclusions; no core
intersection or elementary-index conclusion is assumed. The original
Chapter 14 index-five and normal Bender branches use these bounds.

Source: Aschbacher–Smith G.2.2–3, printed pp.332–334, and the calculation
in 12.8.9(3–5), pp.852–853, specialized to the selected local overgroup.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.ChapterG.Section02.Setup

variable {G : Type*} [Group G] [Finite G] {D : Setup G}

omit [Finite G] in
private theorem relIndex_ker_le_two_of_cyclic_image
    {K : Type*} [Group K] (f : G →* K) (A B : Subgroup G) (hBA : B ≤ A)
    [IsCyclic (A.map f)] (hsq : ∀ x ∈ B, f (x ^ 2) = 1) :
    f.ker.relIndex B ≤ 2 := by
  let : IsCyclic (B.map f) := isCyclic_of_le (map_mono hBA)
  have he : Monoid.exponent (B.map f) ∣ 2 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      rintro ⟨_, x, hx, rfl⟩
      apply Subtype.ext
      change f x ^ 2 = 1
      simpa only [← map_pow] using hsq x hx)
  rw [IsCyclic.exponent_eq_card] at he
  rw [relIndex_ker]
  exact Nat.le_of_dvd (by decide) he

theorem binary_source_core_intersection_and_index
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUQ : D.U ≤ D.QH) (hcomm : ⁅D.U, D.QH⁆ ≤ D.V₁)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    conjugate (D.W g) g ⊓ D.QH = D.S₂ g ∧
      IsElementaryAbelian 2 (D.S₂ g) ∧
      (D.S₂ g).relIndex D.U ≤ 2 * D.QH.relIndex D.T := by
  obtain ⟨hI, he, hnorm, hindex, hgI⟩ := binary_source_inputs h b hUT g hgL hgN
  obtain ⟨hN, hA, σ, d, hS, hprod, hVE, hES, hVcentral, hVN, hEN,
    hEC, hEE, hcoord, hfinite, hcompl, htensor, hcard, hmarks, hfix⟩ :=
    D.binary_source_clauses_three_to_seven h b hUT hf g hgL hgN hI
      (binarySourceCoreEquiv h b hUT g hgL hgN) hnorm hindex
  let := hN
  let := hA
  have hWS : D.W g ≤ D.S g := inf_le_right
  have hXS : conjugate (D.W g) g ≤ D.S g := le_sup_right.trans hS.ge
  have hEW : D.S₂ g ≤ D.W g := le_inf inf_le_left hES
  have hEX : D.S₂ g ≤ conjugate (D.W g) g := by
    rw [D.binary_marked_intersection g hgI hES]
    exact inf_le_right
  have hUneW : ¬ D.U ≤ D.W g := by
    intro hu
    have heq : D.W g = D.U := le_antisymm inf_le_left hu
    rw [heq, relIndex_self] at hindex
    omega
  obtain ⟨u, hu, huw⟩ := SetLike.not_le_iff_exists.mp hUneW
  let ui : D.I g := ⟨u, mem_sup_left hu⟩
  have heq : conjugate (D.W g) g ⊓ D.QH = D.S₂ g := by
    apply le_antisymm ?_ (le_inf hEX (inf_le_left.trans hUQ))
    intro x hx
    let xs : D.S g := ⟨x, hXS hx.1⟩
    have hxc : (d.coordinates xs).toAdd ∈ d.imageSpace (conjugate (D.W g) g) :=
      (d.mem_imageSpace_iff _ _).mpr ⟨xs, hx.1, rfl⟩
    have hxf : σ (D.binaryCoreProjection g
        (binarySourceCoreEquiv h b hUT g hgL hgN) ui) (d.coordinates xs).toAdd =
        (d.coordinates xs).toAdd := by
      exact d.fixed_on_imageSpace_of_commutator_le D.U D.QH
        (hcomm.trans (h.point_le.trans hVE)) ui hu _
        ((d.mem_imageSpace_iff _ _).mpr ⟨xs, hx.2, rfl⟩)
    have hxw : (d.coordinates xs).toAdd ∈ d.imageSpace (D.W g) := by
      rw [← (hmarks ui hu huw).1]
      exact sub_eq_zero.mpr hxf
    have hzero : (d.coordinates xs).toAdd = 0 := by
      have hh := hcompl.disjoint.le_bot (show (d.coordinates xs).toAdd ∈
        d.imageSpace (D.W g) ⊓ d.imageSpace (conjugate (D.W g) g) from ⟨hxw, hxc⟩)
      exact hh
    exact (d.coordinates_eq_one_iff xs).mp hzero
  have hST : D.S g ≤ D.T :=
    (binary_S_le_LT_core hUT g hgL (binaryStarEquiv h.toBaseHypothesis b hUT)
      (binary_source_star_generation h b hUT g hgL hgN)).trans
      h.toBaseHypothesis.binary_core_le_T
  have hcW : Nat.card (conjugate (D.W g) g) = Nat.card (D.W g) :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have hiW : (D.S₂ g).relIndex (D.W g) =
      (D.S₂ g).relIndex (conjugate (D.W g) g) := by
    have hleft := ((D.S₂ g).subgroupOf (D.W g)).card_mul_index
    have hright := ((D.S₂ g).subgroupOf (conjugate (D.W g) g)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hEW).toEquiv] at hleft
    rw [Nat.card_congr (subgroupOfEquivOfLe hEX).toEquiv] at hright
    rw [hcW] at hright
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := D.S₂ g)) (hleft.trans hright.symm)
  have hiX : (D.S₂ g).relIndex (conjugate (D.W g) g) ≤ D.QH.relIndex D.T := by
    rw [← heq, inf_relIndex_left]
    exact relIndex_le_of_le_right (hXS.trans hST) (D.QH.subgroupOf D.T).index_ne_zero_of_finite
  refine ⟨heq, hEE, ?_⟩
  rw [← relIndex_mul_relIndex (D.S₂ g) (D.W g) D.U hEW
    (show D.W g ≤ D.U from inf_le_left), hindex, hiW]
  omega

theorem binary_source_elementary_index_le_four_of_cyclic
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUQ : D.U ≤ D.QH) (hcomm : ⁅D.U, D.QH⁆ ≤ D.V₁)
    (hcyclic : IsCyclic ((D.T.subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))))
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    IsElementaryAbelian 2 (D.S₂ g) ∧ (D.S₂ g).relIndex D.U ≤ 4 := by
  obtain ⟨heq, hEE, _⟩ := binary_source_core_intersection_and_index h b hUT hf hUQ hcomm g hgL hgN
  obtain ⟨hI, he, hnorm, hindex, hgI⟩ := binary_source_inputs h b hUT g hgL hgN
  obtain ⟨hN, hA, σ, d, hS, _, _, hES, _⟩ :=
    D.binary_source_clauses_three_to_seven h b hUT hf g hgL hgN hI
      (binarySourceCoreEquiv h b hUT g hgL hgN) hnorm hindex
  have hEW : D.S₂ g ≤ D.W g := le_inf inf_le_left hES
  have hEX : D.S₂ g ≤ conjugate (D.W g) g := by
    rw [D.binary_marked_intersection g hgI hES]
    exact inf_le_right
  have hXS : conjugate (D.W g) g ≤ D.S g := le_sup_right.trans hS.ge
  have hST : D.S g ≤ D.T :=
    (binary_S_le_LT_core hUT g hgL (binaryStarEquiv h.toBaseHypothesis b hUT)
      (binary_source_star_generation h b hUT g hgL hgN)).trans
      h.toBaseHypothesis.binary_core_le_T
  have hTH : D.T ≤ D.H := le_sup_right.trans h.local_le
  have hXH : conjugate (D.W g) g ≤ D.H := (hXS.trans hST).trans hTH
  have hsq : ∀ x ∈ conjugate (D.W g) g, x ^ 2 ∈ D.QH := by
    rintro x ⟨w, hw, rfl⟩
    have hwU : w ∈ D.U := hw.1
    let : Fact (IsPGroup 2 D.U) := ⟨h.toBaseHypothesis.binary_U_isPGroup hUT⟩
    have hw2 : w ^ 2 ∈ D.V₁ := hf (mem_map_of_mem D.U.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨w, hwU⟩ : D.U)))
    have hVg : D.V.map (MulAut.conj g⁻¹).toMonoidHom = D.V :=
      mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (D.V : Set G)).inv_mem (b.L_normalizes_V hgL))
    have hxV := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom (h.point_le hw2)
    rw [hVg] at hxV
    exact hUQ (le_conjugateSpanBy D.V D.H (by simpa only [map_pow] using hxV))
  let q := QuotientGroup.mk' (pCore 2 D.H)
  let A := D.T.subgroupOf D.H
  let B := (conjugate (D.W g) g).subgroupOf D.H
  let : IsCyclic (A.map q) := hcyclic
  have hsmall : q.ker.relIndex B ≤ 2 :=
    relIndex_ker_le_two_of_cyclic_image q A B
      (subgroupOf_mono D.H (hXS.trans hST)) (by
        intro x hx
        apply (QuotientGroup.eq_one_iff _).mpr
        obtain ⟨y, hy, hyx⟩ := hsq x hx
        exact (show x ^ 2 = y from Subtype.ext hyx.symm) ▸ hy)
  rw [QuotientGroup.ker_mk'] at hsmall
  have hiQ : D.QH.relIndex (conjugate (D.W g) g) ≤ 2 := by
    have hh := relIndex_map_map_of_injective (pCore 2 D.H) B D.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hXH] at hh
    change D.QH.relIndex (conjugate (D.W g) g) = (pCore 2 D.H).relIndex B at hh
    rwa [hh]
  have hiX : (D.S₂ g).relIndex (conjugate (D.W g) g) ≤ 2 := by
    rw [← heq, inf_relIndex_left]
    exact hiQ
  have hcW : Nat.card (conjugate (D.W g) g) = Nat.card (D.W g) :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have hiW : (D.S₂ g).relIndex (D.W g) =
      (D.S₂ g).relIndex (conjugate (D.W g) g) := by
    have hleft := ((D.S₂ g).subgroupOf (D.W g)).card_mul_index
    have hright := ((D.S₂ g).subgroupOf (conjugate (D.W g) g)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hEW).toEquiv] at hleft
    rw [Nat.card_congr (subgroupOfEquivOfLe hEX).toEquiv, hcW] at hright
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := D.S₂ g)) (hleft.trans hright.symm)
  refine ⟨hEE, ?_⟩
  rw [← relIndex_mul_relIndex (D.S₂ g) (D.W g) D.U hEW
    (show D.W g ≤ D.U from inf_le_left), hindex, hiW]
  omega

/-- The literal opposite image is elementary and measures the intersection index exactly. -/
theorem binary_source_opposite_image
    (h : D.Hypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUQ : D.U ≤ D.QH) (hcomm : ⁅D.U, D.QH⁆ ≤ D.V₁)
    (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁) :
    let E := ((conjugate (D.W g) g).subgroupOf D.H).map
      (QuotientGroup.mk' (pCore 2 D.H))
    IsElementaryAbelian 2 E ∧ (D.S₂ g).relIndex D.U = 2 * Nat.card E := by
  obtain ⟨heq, hEE, _⟩ := binary_source_core_intersection_and_index h b hUT hf hUQ hcomm g hgL hgN
  obtain ⟨hI, he, hnorm, hindex, hgI⟩ := binary_source_inputs h b hUT g hgL hgN
  obtain ⟨hN, hA, σ, d, hS, _, _, hES, _⟩ :=
    D.binary_source_clauses_three_to_seven h b hUT hf g hgL hgN hI
      (binarySourceCoreEquiv h b hUT g hgL hgN) hnorm hindex
  have hEW : D.S₂ g ≤ D.W g := le_inf inf_le_left hES
  have hEX : D.S₂ g ≤ conjugate (D.W g) g := by
    rw [D.binary_marked_intersection g hgI hES]
    exact inf_le_right
  have hXS : conjugate (D.W g) g ≤ D.S g := le_sup_right.trans hS.ge
  have hST : D.S g ≤ D.T :=
    (binary_S_le_LT_core hUT g hgL (binaryStarEquiv h.toBaseHypothesis b hUT)
      (binary_source_star_generation h b hUT g hgL hgN)).trans
      h.toBaseHypothesis.binary_core_le_T
  have hTH : D.T ≤ D.H := le_sup_right.trans h.local_le
  have hXH : conjugate (D.W g) g ≤ D.H := (hXS.trans hST).trans hTH
  have hsq : ∀ x ∈ conjugate (D.W g) g, x ^ 2 ∈ D.QH := by
    rintro x ⟨w, hw, rfl⟩
    have hwU : w ∈ D.U := hw.1
    let : Fact (IsPGroup 2 D.U) := ⟨h.toBaseHypothesis.binary_U_isPGroup hUT⟩
    have hw2 : w ^ 2 ∈ D.V₁ := hf (mem_map_of_mem D.U.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨w, hwU⟩ : D.U)))
    have hVg : D.V.map (MulAut.conj g⁻¹).toMonoidHom = D.V :=
      mem_normalizer_iff_map_conj_eq.mp
        ((normalizer (D.V : Set G)).inv_mem (b.L_normalizes_V hgL))
    have hxV := mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom (h.point_le hw2)
    rw [hVg] at hxV
    exact hUQ (le_conjugateSpanBy D.V D.H (by simpa only [map_pow] using hxV))
  let q := QuotientGroup.mk' (pCore 2 D.H)
  let B := (conjugate (D.W g) g).subgroupOf D.H
  let E := B.map q
  have hp : ∀ x : E, x ^ 2 = 1 := by
    rintro ⟨_, x, hx, rfl⟩
    apply Subtype.ext
    change q x ^ 2 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨y, hy, hyx⟩ := hsq x hx
    exact (show x ^ 2 = y from Subtype.ext hyx.symm) ▸ hy
  have helem : IsElementaryAbelian 2 E := {
    toIsMulCommutative := ⟨⟨fun x y =>
      Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hp z)) x y⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hp }
  have hiQ : D.QH.relIndex (conjugate (D.W g) g) = Nat.card E := by
    have hh := relIndex_map_map_of_injective (pCore 2 D.H) B D.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hXH] at hh
    change D.QH.relIndex (conjugate (D.W g) g) = (pCore 2 D.H).relIndex B at hh
    rw [hh]
    simpa only [q, QuotientGroup.ker_mk'] using (relIndex_ker B q)
  have hiX : (D.S₂ g).relIndex (conjugate (D.W g) g) = Nat.card E := by
    rw [← heq, inf_relIndex_left]
    exact hiQ
  have hcW : Nat.card (conjugate (D.W g) g) = Nat.card (D.W g) :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have hiW : (D.S₂ g).relIndex (D.W g) =
      (D.S₂ g).relIndex (conjugate (D.W g) g) := by
    have hleft := ((D.S₂ g).subgroupOf (D.W g)).card_mul_index
    have hright := ((D.S₂ g).subgroupOf (conjugate (D.W g) g)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hEW).toEquiv] at hleft
    rw [Nat.card_congr (subgroupOfEquivOfLe hEX).toEquiv, hcW] at hright
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := D.S₂ g)) (hleft.trans hright.symm)
  refine ⟨helem, ?_⟩
  change (D.S₂ g).relIndex D.U = 2 * Nat.card E
  calc
    (D.S₂ g).relIndex D.U = (D.S₂ g).relIndex (D.W g) * (D.W g).relIndex D.U :=
      (relIndex_mul_relIndex (D.S₂ g) (D.W g) D.U hEW inf_le_left).symm
    _ = Nat.card E * 2 := by rw [hiW, hiX, hindex]
    _ = 2 * Nat.card E := Nat.mul_comm _ _


end CFSG.Quasithin.ChapterG.Section02.Setup
