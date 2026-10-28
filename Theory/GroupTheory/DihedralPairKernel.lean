module

public import Theory.GroupTheory.DihedralPresentation
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral

/-!
# A dihedral pair whose quotient retains the rotation order

The actual pair of involutions generates eight elements when its rotation
has order four. If the given quotient retains that order, the image also
has eight elements, making the original restriction injective and its
intersection with the literal kernel trivial.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G Q : Type*} [Group G] [Group Q]

private theorem pair_card [Finite G] (x s : G) (hx : x^2=1) (hs : s^2=1)
    (hrot : orderOf (x*s)=4) : Nat.card (closure ({x,s}:Set G))=8 := by
  let r := x*s
  have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hx)
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hs)
  have hinv : s*r*s⁻¹=r⁻¹ := by
    dsimp [r]
    rw [mul_inv_rev,hxi,hsi]
    simp only [mul_assoc,←pow_two,hs,mul_one]
  have hsnot : s∉zpowers r := by
    rintro ⟨n,hn⟩
    have hcomm : Commute s r := by rw [←hn]; exact (Commute.refl r).zpow_left n
    have he : r=r⁻¹ := by rw [hcomm.eq,mul_inv_cancel_right] at hinv; exact hinv
    have hh : r^2=1 := calc
      r^2=r*r := pow_two r
      _=r*r⁻¹ := congrArg (r*·) he
      _=1 := mul_inv_cancel r
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [hrot] at hd
    norm_num at hd
  obtain ⟨e⟩ := nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted
    (zpowers r) s inferInstance hs hsnot (by
      rintro a ⟨n,rfl⟩
      change (MulAut.conj s) (r^n)=(r^n)⁻¹
      rw [map_zpow,show (MulAut.conj s) r=r⁻¹ from hinv,inv_zpow])
  have hjoin : closure ({x,s}:Set G)=zpowers r⊔zpowers s := by
    apply le_antisymm
    · apply (closure_le _).mpr
      intro a ha
      rcases Set.mem_insert_iff.mp ha with ha | ha
      · subst a
        change x∈zpowers r⊔zpowers s
        have hh := (zpowers r⊔zpowers s).mul_mem
          (mem_sup_left (mem_zpowers r)) (mem_sup_right (mem_zpowers s))
        simpa only [r,mul_assoc,←pow_two,hs,mul_one] using hh
      · rw [Set.mem_singleton_iff.mp ha]
        exact mem_sup_right (mem_zpowers s)
    · refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
      · exact subset_closure (by simp)
  rw [hjoin,Nat.card_congr e.toEquiv,DihedralGroup.nat_card,Nat.card_zpowers,hrot]

/-- Retaining the rotation order makes the quotient injective on the
literal dihedral pair subgroup, with the actual kernel disjoint. -/
theorem dihedral_pair_kernel_disjoint [Finite G] [Finite Q]
    (q : G→*Q) (x s : G) (hx : x^2=1) (hs : s^2=1)
    (h4 : (x*s)^4=1) (hqo : orderOf (q (x*s))=4) :
    Nat.card (closure ({x,s}:Set G))=8 ∧
      Disjoint q.ker (closure ({x,s}:Set G)) := by
  have ho : orderOf (x*s)=4 := Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one h4) (hqo ▸ orderOf_map_dvd q (x*s))
  have hc := pair_card x s hx hs ho
  let K := closure ({x,s}:Set G)
  have himage : K.map q=closure ({q x,q s}:Set Q) := by
    rw [MonoidHom.map_closure]
    simp only [Set.image_pair]
  have hqc : Nat.card (K.map q)=8 := by
    rw [himage]
    exact pair_card (q x) (q s) (by rw [←map_pow,hx,map_one])
      (by rw [←map_pow,hs,map_one]) (by rwa [←map_mul])
  let f : K→*K.map q := (q.comp K.subtype).codRestrict _ (by
    intro a
    exact mem_map_of_mem q a.property)
  have hf : Function.Surjective f := by
    rintro ⟨a,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  have hfi : Function.Injective f :=
    (hf.bijective_of_nat_card_le (by rw [hc,hqc])).1
  refine ⟨hc,disjoint_def.mpr ?_⟩
  intro a ha haK
  have he : f ⟨a,haK⟩=f 1 := by
    apply Subtype.ext
    change q a=q 1
    rw [map_one]
    exact ha
  exact congrArg Subtype.val (hfi he)

end Theory.GroupTheory
