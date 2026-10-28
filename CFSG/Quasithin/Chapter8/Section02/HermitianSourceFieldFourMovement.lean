module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCore
public import Theory.GroupTheory.PResidual.FixedNormalCenter
public import Theory.GroupTheory.PResidual.PrimeToAction
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCore

/-!
# Residual movement of the selected field-four core

The central core quotient has no global fixed points: the two-conjugate
fixed-space identity places a fixed element in each complementary elementary
factor. A residual-fixed normal two-subgroup would meet the global center,
so the two-residual also has no fixed point on this quotient.

At selected parameter one the actual quotient by the core is odd dihedral.
Its two-residual has odd order, so the residual conjugation image on the
central core quotient has odd order. Coprime decomposition then moves the
whole quotient. Lifting through the same quotient map gives
P = [P,O²(I)] U and C_P(O²(I)) = U for the original intersection U.
No classification of the containing normalizer is assumed.

The Chapter 12 extension applies both identities to the original tensor and
its rank-four fixed subgroup. Selection, E.2.14 and the remaining argument
through 8.2.13 stay with the source assembly.

Source: Aschbacher–Smith E.2.10(2,6), E.2.14 and the opening of §8.2.2,
printed pp.222–227,717–718 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
  {H M I : Subgroup G} {i : I} {S : Sylow 2 I}

private theorem pair_section_inf_center {X : Type*} [Group X] [Finite X]
    {R : Sylow 2 X} {W N : Subgroup X} {g : X}
    (h : TwoConjugate.Hypotheses R W N g) :
    let := h.Z_normal
    (TwoConjugate.P W N g).map (QuotientGroup.mk' (TwoConjugate.Z W g)) ⊓
      center (X ⧸ TwoConjugate.Z W g) = ⊥ := by
  let := h.Z_normal
  let q := QuotientGroup.mk' (TwoConjugate.Z W g)
  apply bot_unique
  rintro x ⟨hx,hxc⟩
  obtain ⟨r,hr,rfl⟩ := hx
  have hrB : r ∈ TwoConjugate.B W N := by
    have hh : q r ∈ (TwoConjugate.B W N).map q := h.quotient_fixed_eq_B ▸
      (show q r ∈ (TwoConjugate.P W N g).map q ⊓ centralizer (W.map q : Set _) from
        ⟨mem_map_of_mem q hr, center_le_centralizer _ hxc⟩)
    have hh' : r ∈ ((TwoConjugate.B W N).map q).comap q := hh
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr
      (h.Z_le_B_inf_A.trans inf_le_left)] at hh'
    exact hh'
  have hrA : r ∈ TwoConjugate.A W N g := by
    have hg : g*r*g⁻¹ ∈ TwoConjugate.A W N g :=
      mem_map_of_mem (MulAut.conj g).toMonoidHom hrB
    have hd : g*r*g⁻¹*r⁻¹ ∈ TwoConjugate.Z W g := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (g*r*g⁻¹*r⁻¹) = 1
      rw [map_mul,map_mul,map_mul,map_inv,map_inv,
        (mem_center_iff.mp hxc) (q g),mul_inv_cancel_right,mul_inv_cancel]
    have hh := (TwoConjugate.A W N g).mul_mem
      ((TwoConjugate.A W N g).inv_mem ((h.Z_le_B_inf_A hd).2)) hg
    have he : (g*r*g⁻¹*r⁻¹)⁻¹*(g*r*g⁻¹) = r := by group
    rwa [he] at hh
  exact (QuotientGroup.eq_one_iff r).mpr (h.B_inf_A_eq_Z ▸ ⟨hrB,hrA⟩)

private theorem residual_fixed_eq_bot {X : Type*} [Group X] [Finite X]
    (E : Subgroup X) [E.Normal] (hE : IsPGroup 2 E)
    (hfix : E ⊓ center X = ⊥) :
    E ⊓ centralizer (pResidual 2 X : Set X) = ⊥ := by
  let C := E ⊓ centralizer (pResidual 2 X : Set X)
  let : C.Normal := inferInstance
  by_contra hc
  have hp : IsPGroup 2 C := hE.to_le inf_le_left
  let R : Sylow 2 X := Classical.choice inferInstance
  obtain ⟨x,hx,hxn,hxc⟩ := exists_nontrivial_center_mem_normal_of_residual_centralizes
    R C hp hc (le_centralizer_iff.mp inf_le_right)
  exact hxn (hfix.le ⟨hx.1,hxc⟩)

/-- The selected pair has no fixed point on its central core quotient,
even after restricting to its actual two-residual. -/
theorem selected_one_section_residual_fixed
    (s : Selected H T M V I 1 i S) :
    let := s.twoConjugate.Z_normal
    let q := QuotientGroup.mk' (TwoConjugate.Z (V.subgroupOf I) i⁻¹)
    (pCore 2 I).map q ⊓ centralizer ((pResidual 2 I).map q : Set _) = ⊥ := by
  let := s.twoConjugate.Z_normal
  let q := QuotientGroup.mk' (TwoConjugate.Z (V.subgroupOf I) i⁻¹)
  have hp := selected_one_native_core s
  let E := (pCore 2 I).map q
  let : E.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have he : E ⊓ center (I ⧸ TwoConjugate.Z (V.subgroupOf I) i⁻¹) = ⊥ := by
    dsimp only [E]
    rw [←hp]
    exact pair_section_inf_center s.twoConjugate
  change E ⊓ centralizer ((pResidual 2 I).map q : Set _) = ⊥
  rw [map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
  exact residual_fixed_eq_bot E (pCore_isPGroup.map q) he

private theorem odd_residual_of_dihedral {X : Type*} [Group X] [Finite X]
    (m : ℕ) (hm : 0 < m) (ho : Odd m) (e : X ≃* DihedralGroup m) :
    Odd (Nat.card (pResidual 2 X)) := by
  let : NeZero m := ⟨by omega⟩
  let A : Subgroup (DihedralGroup m) := zpowers (DihedralGroup.r 1)
  have hc : Nat.card A = m := by
    change Nat.card (zpowers (DihedralGroup.r 1 : DihedralGroup m)) = m
    rw [Nat.card_zpowers,DihedralGroup.orderOf_r_one]
  have hi : A.index = 2 := by
    have hh := A.index_mul_card
    rw [hc,DihedralGroup.nat_card] at hh
    exact Nat.eq_of_mul_eq_mul_right hm hh
  let := A.normal_of_index_eq_two hi
  have hp : pResidual 2 (DihedralGroup m) ≤ A :=
    (pResidual_le_iff_isPGroup_quotient 2 A).mpr
      (IsPGroup.of_card (n := 1) (by rw [← index_eq_card,pow_one]; exact hi))
  have hmapped := map_pResidual_of_surjective 2 e.toMonoidHom e.surjective
  rw [← card_map_of_injective (K := pResidual 2 X) (f := e.toMonoidHom) e.injective,hmapped]
  have hodd : Odd (Nat.card A) := by rw [hc]; exact ho
  exact hodd.of_dvd_nat (card_dvd_of_le hp)

private theorem odd_residual_image_of_dihedral {X D : Type*}
    [Group X] [Finite X] [Group D]
    (f : X →* D) (hk : pCore 2 X ≤ f.ker)
    (m : ℕ) (hm : 0 < m) (ho : Odd m) (e : (X ⧸ pCore 2 X) ≃* DihedralGroup m) :
    Odd (Nat.card ((pResidual 2 X).map f)) := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let a := QuotientGroup.lift (pCore 2 X) f hk
  have hh : a.comp q = f := rfl
  rw [←hh,←map_map,map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)]
  exact (odd_residual_of_dihedral m hm ho e).of_dvd_nat (card_map_dvd _ _)

/-- The two-residual moves the whole selected central core quotient. -/
theorem selected_one_section_residual_moved
    (s : Selected H T M V I 1 i S) :
    let := s.twoConjugate.Z_normal
    let q := QuotientGroup.mk' (TwoConjugate.Z (V.subgroupOf I) i⁻¹)
    ⁅(pCore 2 I).map q,(pResidual 2 I).map q⁆ = (pCore 2 I).map q := by
  let := s.twoConjugate.Z_normal
  let q := QuotientGroup.mk' (TwoConjugate.Z (V.subgroupOf I) i⁻¹)
  let Y := I ⧸ TwoConjugate.Z (V.subgroupOf I) i⁻¹
  let E := (pCore 2 I).map q
  let R := (pResidual 2 I).map q
  let : E.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hEl : IsElementaryAbelian 2 E := by
    have hh := s.twoConjugate.quotient_direct_sum.1
    rw [selected_one_native_core s] at hh
    exact hh
  let := hEl
  let f : I →* MulAut E := (MulAut.conjNormal : Y →* MulAut E).comp q
  have hk : pCore 2 I ≤ f.ker := by
    intro x hx
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change q x * (v : Y) * (q x)⁻¹ = v
    have hh := congrArg Subtype.val (mul_comm (⟨q x,mem_map_of_mem q hx⟩ : E) v)
    change q x * (v : Y) = (v : Y) * q x at hh
    rw [hh,mul_inv_cancel_right]
  obtain ⟨m,hm,ho,em⟩ : ∃ m : ℕ, 0 < m ∧ Odd m ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup m) := by
    rcases s.models.models.2 with ⟨m,hm,ho,_,e⟩ | h | ⟨m,hm,h,_⟩
    · exact ⟨m,hm,ho,e⟩
    · omega
    · omega
  obtain ⟨em⟩ := em
  have hfodd := odd_residual_image_of_dihedral f hk m hm ho em
  have hn : R ≤ normalizer (E : Set Y) := le_normalizer_of_normal
  let a := E.normalizerMonoidHom.comp (inclusion hn)
  have hrange : a.range = (pResidual 2 I).map f := by
    change ((MulAut.conjNormal : Y →* MulAut E).comp R.subtype).range = _
    rw [MonoidHom.range_comp,R.range_subtype,map_map]
  have hc : Nat.Coprime (Nat.card a.range) (Nat.card E) := by
    rw [hrange]
    obtain ⟨d,hd⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_card_eq
    rw [hd]
    exact hfodd.coprime_two_right.pow_right d
  have hh := (commutator_centralizer_decomposition_of_coprime_image E R hn hc).1
  have hfix : E ⊓ centralizer (R : Set Y) = ⊥ := selected_one_section_residual_fixed s
  rw [hfix,sup_bot_eq] at hh
  exact hh

/-- The original two-core is its residual commutator times the original
central intersection, the opening identity in source subsection 8.2.2. -/
theorem selected_one_core_residual_product
    (s : Selected H T M V I 1 i S) :
    I.pCoreIn 2 = ⁅I.pCoreIn 2,(pResidual 2 I).map I.subtype⁆ ⊔
      (V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom) := by
  let := s.twoConjugate.Z_normal
  let Z := TwoConjugate.Z (V.subgroupOf I) i⁻¹
  let q := QuotientGroup.mk' Z
  have hm := selected_one_section_residual_moved s
  change ⁅(pCore 2 I).map q,(pResidual 2 I).map q⁆ = (pCore 2 I).map q at hm
  rw [←map_commutator] at hm
  have he := congrArg (Subgroup.comap q) hm
  have hZ : Z ≤ pCore 2 I :=
    (s.twoConjugate.core_geometry.2.2.trans inf_le_left).trans s.twoConjugate.P_le_twoCore
  rw [comap_map_eq,comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hZ] at he
  have he' := congrArg (Subgroup.map I.subtype) he.symm
  rw [Subgroup.map_sup,map_commutator,
    selected_intersection_image I V (s.generate ▸ le_sup_left) i] at he'
  exact he'

/-- The original central intersection is precisely the fixed subgroup of
the two-residual on the selected core. -/
theorem selected_one_core_residual_centralizer
    (s : Selected H T M V I 1 i S) :
    I.pCoreIn 2 ⊓ centralizer ((pResidual 2 I).map I.subtype : Set G) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  let := s.twoConjugate.Z_normal
  let Z := TwoConjugate.Z (V.subgroupOf I) i⁻¹
  let q := QuotientGroup.mk' Z
  have hz : Z.map I.subtype = V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom :=
    selected_intersection_image I V (s.generate ▸ le_sup_left) i
  rw [←hz]
  apply le_antisymm
  · rintro _ ⟨⟨x,hx,rfl⟩,hc⟩
    have hqc : q x ∈ centralizer ((pResidual 2 I).map q : Set _) := by
      rintro _ ⟨r,hr,rfl⟩
      have hh : r*x=x*r := Subtype.ext (hc r.val (mem_map_of_mem I.subtype hr))
      simpa only [map_mul] using congrArg q hh
    have hh : q x ∈ (pCore 2 I).map q ⊓ centralizer ((pResidual 2 I).map q : Set _) :=
      ⟨mem_map_of_mem q hx,hqc⟩
    have hf := selected_one_section_residual_fixed s
    change (pCore 2 I).map q ⊓ centralizer ((pResidual 2 I).map q : Set _) = ⊥ at hf
    rw [hf] at hh
    exact mem_map_of_mem I.subtype ((QuotientGroup.eq_one_iff x).mp hh)
  · rintro _ ⟨z,hz,rfl⟩
    refine ⟨mem_map_of_mem I.subtype
      (s.twoConjugate.P_le_twoCore (s.twoConjugate.core_geometry.2.2 hz).1),?_⟩
    rintro _ ⟨r,hr,rfl⟩
    exact congrArg Subtype.val ((mem_center_iff.mp (s.twoConjugate.core_geometry.2.2 hz).2) r)
end CFSG.Quasithin.Chapter8.Section02.HermitianSource
