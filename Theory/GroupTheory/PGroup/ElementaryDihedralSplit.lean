module
public import Theory.ElementaryAbelian.BinaryInvolutionPlaneComplement
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.InvolutionFixedLineDihedral
public import Mathlib.GroupTheory.Commutator.Basic


/-!
# Splitting a binary transvection extension

An elementary subgroup Q with an external involution r, whose nontrivial
commutators lie in a central line, splits as a fixed elementary factor
and a moved four-group. The moved four-group and r form an actual D₈.
The two generators and its central involution remain marked in the ambient
group. The proof uses an invariant complement to the binary Jordan plane.

Source application: Aschbacher–Smith C.6.4, printed p.168, the initial
dihedral decomposition before choosing a maximal overgroup.
-/

public noncomputable section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A binary Jordan plane splits off an actual dihedral factor. -/
theorem elementary_dihedral_split (P Q : Subgroup G) [IsElementaryAbelian 2 Q]
    (r u z : G) (hu : u ∈ Q) (hz : z ∈ Q) (hz1 : z ≠ 1)
    (hr2 : r ^ 2 = 1) (hrQ : r ∉ Q)
    (hgen : P = Q ⊔ zpowers r)
    (hQr : r ∈ normalizer (Q : Set G))
    (hzP : z ∈ centralizer (P : Set G))
    (hcomm : ⁅r,u⁆ = z)
    (hrow : ∀ q ∈ Q, ⁅r,q⁆ ∈ zpowers z) :
    ∃ E D : Subgroup G, E ≤ Q ∧ IsElementaryAbelian 2 E ∧
      E ≤ centralizer (P : Set G) ∧ P = E ⊔ D ∧ Disjoint E D ∧
      D = zpowers u ⊔ zpowers r ∧
      Nonempty (D ≃* DihedralGroup 4) ∧
      D ⊓ centralizer (D : Set G) = zpowers z := by
  have hQP : Q ≤ P := hgen ▸ le_sup_left
  have hrP : r ∈ P := hgen ▸ mem_sup_right (mem_zpowers r)
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian u hu
  have hz2 : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z hz
  have huc : u ∉ centralizer ({r} : Set G) := by
    intro h
    exact hz1 (hcomm.symm.trans (commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_singleton_iff.mp h).symm))
  have hu1 : u ≠ 1 := by intro h; exact huc (h ▸ (centralizer _).one_mem)
  have huz : u ≠ z := by
    intro h
    apply huc
    rw [h]
    exact mem_centralizer_singleton_iff.mpr (hzP r hrP).symm
  let W := closure ({u,z} : Set G)
  have hWQ : W ≤ Q := (closure_le _).mpr (by
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact hu
    · exact (Set.mem_singleton_iff.mp ha) ▸ hz)
  have hW : Nat.card W = 4 := (isKleinFour_closure_pair_of_orderOf u z
    (orderOf_eq_prime hu2 hu1) (orderOf_eq_prime hz2 hz1) huz (setLike_mul_comm hu hz)).card_four
  have huW : u ∈ W := subset_closure (Set.mem_insert _ _)
  have hzW : z ∈ W := subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hzcomm : r * z = z * r := hzP r hrP
  have hconju : r * u * r⁻¹ = z * u := by
    rw [← hcomm]
    simp only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
  have hconjz : r * z * r⁻¹ = z := by rw [hzcomm, mul_inv_cancel_right]
  have hrW : r ∈ normalizer (W : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj r).injective])
    rw [MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro _ ⟨a,ha,rfl⟩
    rcases Set.mem_insert_iff.mp ha with ha | ha
    · rw [ha]
      change r*u*r⁻¹ ∈ W
      rw [hconju]
      exact W.mul_mem hzW huW
    · have ha : a=z := Set.mem_singleton_iff.mp ha
      rw [ha]
      change r*z*r⁻¹ ∈ W
      rwa [hconjz]
  have hfixed : W ⊓ centralizer ({r} : Set G) = zpowers z := by
    apply le_antisymm ?_ (le_inf (zpowers_le.mpr hzW)
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hzcomm.symm)))
    intro a ha
    rcases (mem_closure_pair_iff u z (by simpa only [pow_two] using hu2)
      (by simpa only [pow_two] using hz2) (setLike_mul_comm hu hz) a).mp ha.1 with
      rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact (huc ha.2).elim
    · exact mem_zpowers _
    · have hzc : z ∈ centralizer ({r} : Set G) := mem_centralizer_singleton_iff.mpr hzcomm.symm
      exact (huc ((centralizer ({r} : Set G)).mul_mem_cancel_right hzc |>.mp ha.2)).elim
  obtain ⟨e,_,_,_,_⟩ := exists_marked_dihedral_extension_of_involution_fixed_line
    W hW z r hzW (orderOf_eq_prime hz2 hz1)
    (orderOf_eq_prime hr2 (fun he => hrQ (he ▸ Q.one_mem)))
    (fun hr => hrQ (hWQ hr)) hrW hfixed
  obtain ⟨E,hEQ,hd,hWE,hrE⟩ :=
    exists_invariant_complement_of_normalizing_involution_four Q W hWQ hW r hr2 hQr hrW
      (fun hc => huc (mem_centralizer_singleton_iff.mpr (hc u huW)))
  have hEZ : Disjoint E (zpowers z) := hd.symm.mono_right (zpowers_le.mpr hzW)
  have hrEC : r ∈ centralizer (E : Set G) := by
    intro a ha
    have hcaE : ⁅r,a⁆ ∈ E := by
      exact E.mul_mem ((mem_normalizer_iff.mp hrE a).mp ha) (E.inv_mem ha)
    have hca : ⁅r,a⁆ = 1 := disjoint_def.mp hEZ hcaE (hrow a (hEQ ha))
    exact (commutatorElement_eq_one_iff_mul_comm.mp hca).symm
  have hEP : E ≤ centralizer (P : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hgen]
    exact sup_le ((le_centralizer Q).trans (centralizer_le hEQ)) (zpowers_le.mpr hrEC)
  let D := W ⊔ zpowers r
  have hDP : D ≤ P := sup_le (hWQ.trans hQP) (hgen ▸ le_sup_right)
  have hprod : P = E ⊔ D := by
    dsimp [D]
    rw [← sup_assoc, sup_comm E W, hWE, hgen]
  have hdisj : Disjoint E D := by
    apply disjoint_def.mpr
    intro a haE haD
    have hnr : zpowers r ≤ normalizer (W : Set G) := zpowers_le.mpr hrW
    obtain ⟨w,hw,b,hb,rfl⟩ := (show ∃ w ∈ W, ∃ b ∈ zpowers r, w*b=a from by
      change a ∈ ((W ⊔ zpowers r : Subgroup G) : Set G) at haD
      rwa [coe_mul_of_right_le_normalizer_left W (zpowers r) hnr] at haD)
    have hbQ : b ∈ Q := (Q.mul_mem_cancel_left (hWQ hw)).mp (hEQ haE)
    have hbr : b=1 ∨ b=r := by
      classical
      rw [mem_zpowers_iff_mem_range_orderOf,
        orderOf_eq_prime hr2 (fun he => hrQ (he ▸ Q.one_mem))] at hb
      obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hb
      have hn' := Finset.mem_range.mp hn
      interval_cases n <;> simp_all
    rcases hbr with rfl | rfl
    · simp only [mul_one] at haE ⊢
      exact disjoint_def.mp hd hw haE
    · exact (hrQ hbQ).elim
  have hDgen : D = zpowers u ⊔ zpowers r := by
    have huD : u ∈ D := mem_sup_left huW
    have hrD : r ∈ D := mem_sup_right (mem_zpowers r)
    apply le_antisymm ?_ (sup_le (zpowers_le.mpr huD) (zpowers_le.mpr hrD))
    refine sup_le ((closure_le _).mpr ?_) le_sup_right
    intro a ha
    rcases Set.mem_insert_iff.mp ha with ha | ha
    · rw [ha]
      exact mem_sup_left (mem_zpowers u)
    · rw [Set.mem_singleton_iff.mp ha, ← hcomm]
      let B := zpowers u ⊔ zpowers r
      have hru : r ∈ B := mem_sup_right (mem_zpowers r)
      have huu : u ∈ B := mem_sup_left (mem_zpowers u)
      exact B.mul_mem (B.mul_mem (B.mul_mem hru huu) (B.inv_mem hru)) (B.inv_mem huu)
  have hZ : D ⊓ centralizer (D : Set G) = zpowers z := by
    have hzcD : z ∈ centralizer (D : Set G) := centralizer_le hDP hzP
    have hle : zpowers z ≤ D ⊓ centralizer (D : Set G) :=
      zpowers_le.mpr ⟨mem_sup_left hzW,hzcD⟩
    apply (eq_of_le_of_card_ge hle ?_).symm
    have hcard : Nat.card (D ⊓ centralizer (D : Set G) : Subgroup G) = 2 := by
      have hc : (centralizer (D : Set G)).subgroupOf D = center D := by
        ext x
        constructor
        · intro hx
          exact mem_center_iff.mpr (fun y => Subtype.ext (hx y y.property))
        · intro hx y hy
          exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)
      rw [inf_comm, ← Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : centralizer (D : Set G) ⊓ D ≤ D)).toEquiv,
        inf_subgroupOf_right, hc, Nat.card_congr (centerCongr e).toEquiv, Nat.card_eq_fintype_card]
      decide
    rw [hcard,Nat.card_zpowers,orderOf_eq_prime hz2 hz1]
  exact ⟨E,D,hEQ,IsElementaryAbelian.of_injective (inclusion hEQ) (inclusion_injective hEQ),
    hEP,hprod,hdisj,hDgen,⟨e⟩,hZ⟩
end Subgroup
