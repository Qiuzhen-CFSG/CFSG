module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormSylow
public import Theory.GroupTheory.DisjointCommutingProduct
/-!
# The norm diagonal is the pair centralizer

Two distinct simple components commute and intersect trivially. Multiplication
therefore gives their exact product coordinates. A swapping involution fixes a
product precisely when its two coordinates are conjugate, so its centralizer
in the pair is the literal norm image.

Source: Aschbacher–Smith, E.1.11, printed p.213, norm-diagonal construction.
-/

public section
open Subgroup
namespace Theory.GroupTheory.NormPair
variable {G : Type*} [Group G] {K : Subgroup G} {a : G}

lemma norm_eq_pair_centralizer (hK : IsComponent G K)
    (hm : K.map (MulAut.conj a).toMonoidHom ≠ K) [IsSimpleGroup K]
    (ha : a ^ 2 = 1) :
    normRange hK hm = (K ⊔ K.map (MulAut.conj a).toMonoidHom) ⊓ centralizer ({a} : Set G) := by
  apply le_antisymm
  · exact le_inf (norm_le_pair hK hm) (componentSwapNorm_range_le_centralizer hK hm ha)
  let D := K.map (MulAut.conj a).toMonoidHom
  have hc : K ≤ centralizer (D : Set G) := commutator_eq_bot_iff_le_centralizer.mp
    (hK.commutator_eq_bot_of_ne (hK.map_conj a) hm.symm)
  let := hK.2
  have hz : center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) inferInstance with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative K (center_eq_top_iff.mp h)).elim
  have hd : Disjoint K D := by
    apply disjoint_def.mpr
    intro x hxK hxD
    have hxz : (⟨x,hxK⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext ((hc y.property x hxD).symm)
    have hx1 := mem_bot.mp (hz ▸ hxz)
    exact congrArg Subtype.val hx1
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting K D hd hc
  rintro x ⟨hxP,hxc⟩
  obtain ⟨⟨k,d⟩,hex⟩ := e.surjective ⟨x,hxP⟩
  have hx : (k:G)*(d:G)=x := (he k d).symm.trans (congrArg Subtype.val hex)
  obtain ⟨y,hy,hyd⟩ := d.property
  have hda : (d:G)=a*y*a⁻¹ := hyd.symm
  have haa : a⁻¹=a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha)
  have heq : (k:G)*(d:G) = y*(a*k*a⁻¹) := by
    calc
      _ = x := hx
      _ = a*x*a⁻¹ := (mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_singleton_iff.mp hxc).symm).symm
      _ = y*(a*k*a⁻¹) := by
        rw [← hx, hda, haa]
        have hyc : (a*k*a⁻¹)*y = y*(a*k*a⁻¹) :=
          hc hy _ (mem_map_of_mem _ k.property)
        rw [haa] at hyc
        calc
          _ = (a*k*a)*y := by
            have hs : a*a=1 := by simpa [pow_two] using ha
            calc
              _ = (a*k*a)*y*(a*a) := by group
              _ = _ := by rw [hs,mul_one]
          _ = _ := hyc
  have hid : (k,d) = (⟨y,hy⟩,⟨a*k*a⁻¹,mem_map_of_mem _ k.property⟩) :=
    mul_injective_of_disjoint hd heq
  refine ⟨k, ?_⟩
  change (k:G)*(a*k*a⁻¹)=x
  have hde := congrArg (fun p : K × D => (p.2:G)) hid
  exact (congrArg ((k:G)*·) hde).symm.trans hx

end Theory.GroupTheory.NormPair
