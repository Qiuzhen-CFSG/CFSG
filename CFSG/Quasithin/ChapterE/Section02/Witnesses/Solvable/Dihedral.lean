module
public import Theory.GroupTheory.ElementaryConjugatePrimePair
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.ChapterE.Section02.TwoConjugate.OddDihedral.Recognition
/-!
# The actual odd dihedral quotient of an elementary conjugate pair

An odd cyclic subgroup normalized by an elementary two-subgroup has a
central fixed hyperplane when every element acts by identity or inversion.
The elementary subgroup’s normal core is exactly this hyperplane. The
quotient is therefore the dihedral group with the original rotation order.

Source: Aschbacher–Smith, E.2.7 and the solvable case of E.2.9.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterE.Witnesses.Solvable
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem rotation_disjoint (V : Subgroup G) [IsElementaryAbelian 2 V]
    (g : G) (ho : Odd (orderOf g)) : Disjoint (zpowers g) V := by
  apply disjoint_def.mpr
  intro x hx hv
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr ho)
    (orderOf_dvd_of_pow_eq_one (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hv))
    (orderOf_dvd_of_mem_zpowers hx)

omit [Finite G] in
private theorem core_eq_fixed (V : Subgroup G) [IsElementaryAbelian 2 V]
    (g : G) (ho : Odd (orderOf g)) (hgen : zpowers g ⊔ V = ⊤)
    (hn : V ≤ normalizer (zpowers g : Set G)) :
    V.normalCore = V ⊓ centralizer ({g} : Set G) := by
  let C := V ⊓ centralizer ({g} : Set G)
  have hcent : C ≤ center G := by
    rw [← centralizer_univ, ← coe_top, ← hgen]
    apply le_centralizer_iff.mp
    refine sup_le ?_ ?_
    · apply zpowers_le.mpr
      intro x hx
      exact mem_centralizer_singleton_iff.mp hx.2
    · exact V.le_centralizer.trans (centralizer_le inf_le_left)
  let : C.Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [(mem_center_iff.mp (hcent hx)) y, mul_inv_cancel_right]
    exact hx
  refine le_antisymm ?_ (normal_le_normalCore.mpr inf_le_left)
  intro x hx
  have hxV := V.normalCore_le hx
  have hxg : g*x*g⁻¹ ∈ V := V.normalCore_le ((inferInstance : V.normalCore.Normal).conj_mem x hx g)
  have hmV : g*x*g⁻¹*x⁻¹ ∈ V := V.mul_mem hxg (V.inv_mem hxV)
  have hmD : g*x*g⁻¹*x⁻¹ ∈ zpowers g := by
    have hh := (mem_normalizer_iff.mp (hn hxV) g⁻¹).mp ((zpowers g).inv_mem (mem_zpowers g))
    simpa only [mul_assoc] using (zpowers g).mul_mem (mem_zpowers g) hh
  have he := disjoint_def.mp (rotation_disjoint V g ho) hmD hmV
  refine ⟨hxV,mem_centralizer_singleton_iff.mpr ?_⟩
  have hh := commutatorElement_eq_one_iff_mul_comm.mp he
  exact hh.symm

omit [Finite G] in
private theorem fixed_index_two (V : Subgroup G) [IsElementaryAbelian 2 V]
    (g v : G) (hv : v ∈ V) (ho : Odd (orderOf g)) (hg : g ≠ 1)
    (hi : v*g*v⁻¹ = g⁻¹)
    (hsign : ∀ w ∈ V, w*g*w⁻¹ = g ∨ w*g*w⁻¹ = g⁻¹) :
    ((V ⊓ centralizer ({g} : Set G)).subgroupOf V).index = 2 := by
  let C := (V ⊓ centralizer ({g} : Set G)).subgroupOf V
  have hginv : g ≠ g⁻¹ := by
    intro he
    have hsq : g^2 = 1 := by rw [pow_two]; nth_rw 1 [he]; exact inv_mul_cancel g
    exact hg (orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr ho)
        (orderOf_dvd_of_pow_eq_one hsq) (dvd_refl _)))
  apply C.index_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨⟨v,hv⟩, ?_, ?_⟩
  · intro hc
    have hvcomm : v*g = g*v := mem_centralizer_singleton_iff.mp hc.2
    have hfix : v*g*v⁻¹ = g := by rw [hvcomm,mul_inv_cancel_right]
    exact hginv (hfix.symm.trans hi)
  · intro w
    rcases hsign w w.property with hw | hw
    · right
      exact ⟨w.property, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hw)⟩
    · left
      have he : (v*w)*g*(v*w)⁻¹ = g := by
        calc
          _ = v*((w:G)*g*(w:G)⁻¹)*v⁻¹ := by group
          _ = v*g⁻¹*v⁻¹ := by rw [hw]
          _ = g := by simpa only [mul_inv_rev,inv_inv,mul_assoc] using congrArg Inv.inv hi
      exact ⟨V.mul_mem hv w.property, mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp he)⟩

/-- The literal quotient by the elementary factor's normal core is the odd
dihedral group with rotation order equal to the chosen odd element. -/
theorem quotient_equiv_dihedral (V : Subgroup G) [IsElementaryAbelian 2 V]
    (g v : G) (hv : v ∈ V) (ho : Odd (orderOf g)) (hg : g ≠ 1)
    (hgen : zpowers g ⊔ V = ⊤) (hi : v*g*v⁻¹ = g⁻¹)
    (hsign : ∀ w ∈ V, w*g*w⁻¹ = g ∨ w*g*w⁻¹ = g⁻¹) :
    Nonempty ((G ⧸ V.normalCore) ≃* DihedralGroup (orderOf g)) := by
  let J := V.normalCore
  let q := QuotientGroup.mk' J
  have hn := Theory.GroupTheory.normalizes_cyclic_of_identity_or_inversion V g hsign
  have hJ := core_eq_fixed V g ho hgen hn
  have hVcard : Nat.card (V.map q) = 2 := by
    rw [← relIndex_ker,QuotientGroup.ker_mk',relIndex]
    change (V.normalCore.subgroupOf V).index = 2
    rw [hJ]
    exact fixed_index_two V g v hv ho hg hi hsign
  have heq := Theory.GroupTheory.conjugate_join_eq_cyclic_sup V g v hv ho hi
  have hpair : V ⊔ V.map (MulAut.conj g).toMonoidHom = ⊤ := heq.trans hgen
  obtain ⟨a,ha1,hall⟩ := (Nat.card_eq_two_iff' (1 : V.map q)).mp hVcard
  have han : (a : G ⧸ J) ≠ 1 := fun he => ha1 (Subtype.ext he)
  have ha2 : (a : G ⧸ J)^2 = 1 := by
    let : IsElementaryAbelian 2 (V.map q) := IsElementaryAbelian.map q
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : G ⧸ J) a.property
  have haV : V.map q = zpowers (a : G ⧸ J) := by
    refine le_antisymm ?_ (zpowers_le.mpr a.property)
    intro x hx
    by_cases he : x = 1
    · rw [he]; exact one_mem _
    · have hh := hall ⟨x,hx⟩ (fun hh => he (congrArg Subtype.val hh))
      have heq : x = (a : G ⧸ J) := congrArg Subtype.val hh
      rw [heq]
      exact mem_zpowers _
  let b := MulAut.conj (q g) (a : G ⧸ J)
  have hb2 : b^2 = 1 := by dsimp only [b]; rw [← map_pow,ha2,map_one]
  have hmap : (V.map (MulAut.conj g).toMonoidHom).map q =
      (V.map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
  have hab : zpowers (a : G ⧸ J) ⊔ zpowers b = ⊤ := by
    have hh := congrArg (fun A : Subgroup G => A.map q) hpair
    rw [Subgroup.map_sup,hmap,haV,MonoidHom.map_zpowers,
      map_top_of_surjective q (QuotientGroup.mk'_surjective J)] at hh
    exact hh
  obtain ⟨m,hm,_,⟨e⟩,_⟩ := TwoConjugate.OddDihedral.recognition han ha2 hb2 hab
    (isConj_iff.mpr ⟨q g,rfl⟩)
  have hGcard : Nat.card G = orderOf g * Nat.card V := by
    have hh := card_sup_eq_mul_of_normalizes_of_disjoint (zpowers g) V hn (rotation_disjoint V g ho)
    simpa only [hgen,card_top,Nat.card_zpowers] using hh
  have hVidx : (J.subgroupOf V).index = 2 := by
    change (V.normalCore.subgroupOf V).index = 2
    rw [hJ]
    exact fixed_index_two V g v hv ho hg hi hsign
  have hVJcard : Nat.card V = Nat.card J * 2 := by
    have hh := (J.subgroupOf V).card_mul_index
    rw [hVidx,Nat.card_congr (subgroupOfEquivOfLe (normalCore_le V)).toEquiv] at hh
    exact hh.symm
  have hquotcard : Nat.card (G ⧸ J) = 2 * orderOf g := by
    have hh := J.card_mul_index
    rw [index_eq_card,hGcard,hVJcard] at hh
    have hpos : 0 < Nat.card J := Nat.card_pos
    nlinarith
  have hmEq : m = orderOf g := by
    have hh := Nat.card_congr e.toEquiv
    rw [hquotcard,DihedralGroup.nat_card] at hh
    omega
  exact ⟨e.trans (by subst m; exact MulEquiv.refl _)⟩
end CFSG.Quasithin.ChapterE.Witnesses.Solvable
