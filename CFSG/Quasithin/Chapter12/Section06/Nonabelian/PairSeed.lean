module
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Perpendicular
public import CFSG.Quasithin.ChapterF.Section09.ConjugatePair.Quaternion
public import Theory.GroupTheory.ConjugatePairSeed.Supplement
public import Theory.ElementaryAbelian.CentralPair

/-!
# The extraspecial pair seed of order 512

For the original six-space, each perpendicular seed has order 32. A
non-two conjugate pair has intersection exactly the original point line.
The F.9 central commutators give normalization, and the centralizer bounds
identify the center of the seed join with that line. Counting gives order
512; the two elementary generating factors give an elementary central
quotient, so this actual seed is extraspecial.

Its centralizer supplements it inside U_H. The two original module
actors centralize that supplement modulo V1, so their kernel on the
seed quotient is exactly their intersection with O2(H). No abstract
model or faithfulness premise is substituted for these constructions.
The plus-type identification and dihedral order restriction remain open.

Source: Aschbacher--Smith, F.9.5(5--6.ii), printed p.319, and the opening
of 12.6.26, printed p.831.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
variable {G : Type*} [Group G] [Finite G] (E : Setup G) {H : Subgroup G}

/-- The actual join of the two original point perpendiculars. -/
noncomputable def pairSeed (g : G) : Subgroup G :=
  E.V₅ ⊔ E.V₅.map (MulAut.conj g).toMonoidHom

/-- The original non-two pair has an extraspecial seed of order 512 and center V1. -/
theorem pair_seed_structure (h : (E.f9 H).Hypothesis) (hz : E.z ≠ 1)
    (hp : ∀ g ∈ H, E.V₁ < E.V ⊓ E.V.map (MulAut.conj g).toMonoidHom →
      IsPGroup 2 (E.V ⊔ E.V.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (hC : centralizer (E.V₅ : Set G) = centralizer (E.V : Set G))
    (g : G) (hg : g ∈ H)
    (hn : ¬ IsPGroup 2 (E.V ⊔ E.V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    (center (E.pairSeed g)).map (E.pairSeed g).subtype = E.V₁ ∧
      Nat.card (E.pairSeed g) = 2 ^ 9 ∧ IsExtraspecial 2 (E.pairSeed g) := by
  let := E.elementary
  let : IsElementaryAbelian 2 E.V₅ := IsElementaryAbelian.of_le E.V₅_le
  let f := (MulAut.conj g).toMonoidHom
  let B := E.V₅.map f
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  let P := E.pairSeed g
  have hBU : B ≤ E.UH H := ChapterF.Section09.Setup.Hypothesis.pair_seed_conjugate_le_closure (D := E.f9 H) g hg
  have hPU : P ≤ E.UH H := sup_le (le_conjugateSpanBy _ _) hBU
  have hB5 : ⁅E.V₅,B⁆ ≤ E.V₁ :=
    (commutator_mono (le_conjugateSpanBy _ _) (hBU.trans h.UH_le_QH)).trans
      h.commutator_UH_QH_le_point
  have hnorm : B ≤ normalizer (E.V₅ : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr (hB5.trans E.V₁_le_V₅)
  have hcent : (center P).map P.subtype = E.V₁ := by
    apply h.pair_seed_center hp _ g hg hn
    have hh : ⁅E.V,H ⊓ centralizer (E.V₅ : Set G)⁆ = ⊥ := by
      rw [hC,commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
    exact hh.le.trans bot_le
  have hzmap : E.V₁.map f = E.V₁ := mem_normalizer_iff_map_conj_eq.mp
    ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hg)
  have hint : E.V₅ ⊓ B = E.V₁ := by
    apply le_antisymm
    · exact (inf_le_inf E.V₅_le (map_mono E.V₅_le)).trans
        (h.pair_intersection_eq_point hp g hg hn).le
    · exact le_inf E.V₁_le_V₅ (hzmap.symm.le.trans (map_mono E.V₁_le_V₅))
  have hcard : Nat.card P = 2 ^ 9 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes E.V₅ B hnorm
    have hb : Nat.card B = 2 ^ 5 :=
      (card_map_of_injective (MulAut.conj g).injective).trans (E.perpendicular_card hz)
    rw [E.perpendicular_card hz,hb,hint,E.point_card hz] at hh
    change 2^5*2^5=2*Nat.card P at hh
    omega
  have hZ : Nat.card (center P) = 2 := by
    rw [←card_map_of_injective P.subtype_injective,hcent,E.point_card hz]
  let C := E.V₅.subgroupOf P
  let F := B.subgroupOf P
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.subgroupOf (show E.V₅ ≤ P from le_sup_left)
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf (show B ≤ P from le_sup_right)
  have hgen : C ⊔ F = ⊤ := by
    rw [←subgroupOf_sup (show E.V₅ ≤ P from le_sup_left) (show B ≤ P from le_sup_right)]
    exact subgroupOf_self P
  have hc : ⁅C,F⁆ ≤ center P := by
    apply (map_le_map_iff_of_injective P.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le (show E.V₅ ≤ P from le_sup_left),
      map_subgroupOf_eq_of_le (show B ≤ P from le_sup_right),hcent]
    exact hB5
  have hquot := elementary_central_quotient_of_generating_pair C F hgen hc
  refine ⟨hcent,hcard,?_⟩
  refine { center_order_p := hZ
           quotient_elementary_abelian := hquot
           quotient_nontrivial := QuotientGroup.nontrivial_iff.mpr ?_ }
  intro he
  rw [he,Nat.card_congr topEquiv.toEquiv,hcard] at hZ
  norm_num at hZ

end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup

namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}

/-- The literal pair kernel once the actual seed is proved extraspecial.
This is dimension-independent; the original six-space application below
constructs the extraspecial seed of order 512. -/
theorem pair_seed_kernel_of_extraspecial (h : D.Hypothesis)
    (hc : ⁅D.V,D.H ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (g : G) (hg : g ∈ D.H)
    (hs : IsExtraspecial 2 (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (hz : (center (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom : Subgroup G)).map
      (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom).subtype = D.V₁) :
    commutatorPreimage (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom)
      (D.Vplus ⊔ D.Vplus.map (MulAut.conj g).toMonoidHom) D.V₁ =
      (D.V ⊔ D.V.map (MulAut.conj g).toMonoidHom) ⊓ D.QH := by
  let f := (MulAut.conj g).toMonoidHom
  let B := D.V.map f
  let E := D.Vplus.map f
  let I := D.V ⊔ B
  let P := D.Vplus ⊔ E
  let R := D.UH ⊓ centralizer (P : Set G)
  have hBH : B ≤ D.H := by
    rintro _ ⟨a,ha,rfl⟩
    exact D.H.mul_mem (D.H.mul_mem hg (h.V_le_H ha)) (D.H.inv_mem hg)
  have hIH : I ≤ D.H := sup_le h.V_le_H hBH
  have hPU : P ≤ D.UH := sup_le (le_conjugateSpanBy _ _)
    (ChapterF.Section09.Setup.Hypothesis.pair_seed_conjugate_le_closure (D := D) g hg)
  let : IsExtraspecial 2 P := hs
  have hUP : ⁅D.UH,P⁆ ≤ D.V₁ :=
    (commutator_mono le_rfl (hPU.trans h.UH_le_QH)).trans h.commutator_UH_QH_le_point
  have hs : P ⊔ R = D.UH := extraspecial_sup_centralizer_eq P D.UH D.V₁ hPU
    hz hUP
  have hR1 : R ≤ D.H ⊓ centralizer (D.Vplus : Set G) :=
    le_inf (inf_le_left.trans h.UH_le_H) (inf_le_right.trans (centralizer_le (show D.Vplus ≤ P from le_sup_left)))
  have hR2 : R ≤ D.H ⊓ centralizer (E : Set G) :=
    le_inf (inf_le_left.trans h.UH_le_H) (inf_le_right.trans (centralizer_le (show E ≤ P from le_sup_right)))
  have hHZ : D.H ≤ normalizer (D.V₁ : Set G) :=
    h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hIR : ⁅I,R⁆ ≤ D.V₁ := by
    have hm : I ≤ commutatorPreimage D.H R D.V₁ := sup_le
      (le_commutatorPreimage h.V_le_H ((commutator_mono le_rfl hR1).trans hc))
      (le_commutatorPreimage hBH ((commutator_mono le_rfl hR2).trans
        (h.pair_conjugate_centralizer_bound hc g hg)))
    exact (commutator_mono hm le_rfl).trans
      (commutator_commutatorPreimage_le D.H R D.V₁ hHZ)
  have he := commutatorPreimage_eq_of_centralizer_supplement I P D.UH D.V₁
    (hIH.trans hHZ) (h.UH_le_H.trans hHZ) hPU hs hIR
  change commutatorPreimage I P D.V₁ = I ⊓ D.QH
  rw [he]
  ext x
  rw [mem_commutatorPreimage_iff I D.UH D.V₁ (hIH.trans hHZ)]
  constructor
  · rintro ⟨hx,hxc⟩
    refine ⟨hx,?_⟩
    rw [←h.kernel_UH_eq_QH]
    apply (h.mem_kernel_iff h.UH_le_H).mpr
    refine ⟨hIH hx,fun u hu => ?_⟩
    rw [←commutatorElement_inv]
    exact D.V₁.inv_mem (hxc u hu)
  · rintro ⟨hx,hxq⟩
    refine ⟨hx,fun u hu => ?_⟩
    rw [←commutatorElement_inv]
    exact D.V₁.inv_mem (h.commutator_UH_QH_le_point (commutator_mem_commutator hu hxq))
end CFSG.Quasithin.Chapter12.Section06.Nonabelian
