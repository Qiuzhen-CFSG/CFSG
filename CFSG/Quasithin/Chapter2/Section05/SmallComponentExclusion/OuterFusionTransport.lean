module
public import Theory.SpecificGroups.PSL3Three.EightGeometry.Transport
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Fusion in the marked central product with Aut(PSL₃(3))

Two crossing equations fuse an inner involution to an outer one and carry a
product with the central involution to a second such product. Conjugacy of
inner involutions in PSL₃(3) and of outer involutions in its automorphism group
then gives both ambient fusion classes on the literal complement and its
other coset. The second outer involution is obtained from the crossing itself;
no separate square equation for a displacement is required.

Source: Aschbacher--Smith, Lemma 2.5.15, printed pp.558--559, outer case.
The original-source producer supplies the marked complement and crossings.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem central_mul_isConj {A : Subgroup G} (t : G)
    (ht : t ∈ centralizer (A : Set G)) (a b : A) (h : IsConj a b) :
    IsConj (t * (a:G)) (t * (b:G)) := by
  obtain ⟨c,hc⟩ := isConj_iff.mp h
  refine isConj_iff.mpr ⟨(c:G), ?_⟩
  have hct : (c:G) * t = t * (c:G) := ht c c.property
  have he : (c:G) * (a:G) * (c:G)⁻¹ = (b:G) := congrArg Subtype.val hc
  calc
    (c:G) * (t * (a:G)) * (c:G)⁻¹ = t * ((c:G) * (a:G) * (c:G)⁻¹) := by
      rw [← mul_assoc, hct]; group
    _ = t * (b:G) := congrArg (t * ·) he

/-- Two crossing equations give both source fusion conclusions in the marked
central product with Aut(PSL₃(3)). -/
theorem linear_three_outer_fusion_transport
    {H K A : Subgroup G} (hKA : K ≤ A)
    (eK : K ≃* Matrix.PSL3Three.PSL)
    (eA : A ≃* MulAut Matrix.PSL3Three.PSL)
    (hinner : (MulAut.innerSubgroup Matrix.PSL3Three.PSL).comap eA.toMonoidHom =
      K.subgroupOf A)
    (t : G) (ht : orderOf t = 2)
    (hH : H = zpowers t ⊔ A) (hdis : Disjoint (zpowers t) A)
    (hcomm : zpowers t ≤ centralizer (A : Set G))
    (e z : K) (he : orderOf e = 2) (hz : orderOf z = 2)
    (y : A) (hy : (y:G) ∉ K) (x : G)
    (hxt : x⁻¹ * t * x = t * (z:G))
    (hxe : x⁻¹ * (e:G) * x = (e:G) * (y:G)) :
    (∀ a ∈ A, orderOf a = 2 → IsConj a (z:G)) ∧
    (∀ a ∈ H, a ∉ A → orderOf a = 2 → IsConj a t) := by
  classical
  have htC : t ∈ centralizer (A : Set G) := hcomm (mem_zpowers t)
  have ht2 : t ^ 2 = 1 := by rw [←ht]; exact pow_orderOf_eq_one t
  have heG : orderOf (e:G) = 2 := (Subgroup.orderOf_coe e).trans he
  have he2 : (e:G)^2 = 1 := by rw [←heG]; exact pow_orderOf_eq_one (e:G)
  have hinner_conj (a : G) (ha : a ∈ K) (hao : orderOf a = 2) :
      IsConj (⟨a,hKA ha⟩ : A) (⟨z,hKA z.property⟩ : A) := by
    let f := eK.trans Matrix.PSL3Three.equiv.symm
    let aK : K := ⟨a,ha⟩
    have haoK : orderOf aK = 2 := (Subgroup.orderOf_mk _ _).trans hao
    have hs := Matrix.SL3.involutions_isConj (ZMod 3) (f aK) (f z)
      ((f.orderOf_eq aK).trans haoK) ((f.orderOf_eq z).trans hz) (by decide)
    have hk : IsConj aK z := by
      simpa only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        MulEquiv.symm_apply_apply] using f.symm.toMonoidHom.map_isConj hs
    exact (inclusion hKA).map_isConj hk
  have houter (a : A) (ha : (a:G) ∉ K) :
      eA a ∉ MulAut.innerSubgroup Matrix.PSL3Three.PSL := by
    intro hh
    apply ha
    have hm : a ∈ (MulAut.innerSubgroup Matrix.PSL3Three.PSL).comap eA.toMonoidHom := hh
    rw [hinner] at hm
    exact hm
  let d : A := ⟨(e:G) * (y:G), A.mul_mem (hKA e.property) y.property⟩
  have hdK : (d:G) ∉ K := by
    intro hd
    apply hy
    simpa only [d, inv_mul_cancel_left] using K.mul_mem (K.inv_mem e.property) hd
  have hxd : MulAut.conj x⁻¹ (e:G) = (d:G) := by
    simpa only [MulAut.conj_apply,inv_inv] using hxe
  have hdoG : orderOf (d:G) = 2 := by
    rw [←hxd]
    exact ((MulAut.conj x⁻¹).orderOf_eq (e:G)).trans heG
  have hdo : orderOf d = 2 := (Subgroup.orderOf_coe d).symm.trans hdoG
  have hed : IsConj (e:G) (d:G) := isConj_iff.mpr ⟨x⁻¹, by
    simpa only [inv_inv] using hxe⟩
  have hez : IsConj (e:G) (z:G) := A.subtype.map_isConj (hinner_conj e e.property heG)
  have hdz : IsConj (d:G) (z:G) := hed.symm.trans hez
  have hte2 : (t * (e:G))^2 = 1 := by
    have hc : Commute t (e:G) := (htC e (hKA e.property)).symm
    rw [hc.mul_pow,ht2,he2,mul_one]
  have htz : IsConj t (t * (z:G)) := isConj_iff.mpr ⟨x⁻¹, by
    simpa only [inv_inv] using hxt⟩
  have hte : IsConj (t * (e:G)) t :=
    (central_mul_isConj t htC _ _ (hinner_conj e e.property heG)).trans htz.symm
  let b : A := ⟨(z:G) * (d:G), A.mul_mem (hKA z.property) d.property⟩
  have hbK : (b:G) ∉ K := by
    intro hb
    apply hdK
    simpa only [b,inv_mul_cancel_left] using K.mul_mem (K.inv_mem z.property) hb
  have hxb : MulAut.conj x⁻¹ (t * (e:G)) = t * (b:G) := by
    rw [map_mul,hxd]
    simp only [MulAut.conj_apply,inv_inv]
    change (x⁻¹ * t * x) * (d:G) = t * ((z:G) * (d:G))
    rw [hxt,mul_assoc]
  have hb2 : (b:G)^2 = 1 := by
    have hp : (t * (b:G))^2 = 1 := by
      rw [←hxb,←map_pow,hte2,map_one]
    have hc : Commute t (b:G) := (htC b b.property).symm
    simpa only [hc.mul_pow,ht2,one_mul] using hp
  have hboG : orderOf (b:G) = 2 := orderOf_eq_prime hb2 (fun hh => hbK (hh ▸ K.one_mem))
  have hbo : orderOf b = 2 := (Subgroup.orderOf_coe b).symm.trans hboG
  have hbt : IsConj (t * (b:G)) t :=
    (isConj_iff.mpr ⟨x⁻¹, by simpa only [MulAut.conj_apply] using hxb⟩).symm.trans hte
  constructor
  · intro a ha hao
    by_cases hak : a ∈ K
    · exact A.subtype.map_isConj (hinner_conj a hak hao)
    · have hc := Matrix.PSL3Three.EightGeometry.outer_involutions_conjugate_of_equiv
        eA (⟨a,ha⟩ : A) d ((Subgroup.orderOf_mk _ _).trans hao) hdo
        (houter ⟨a,ha⟩ hak) (houter d hdK)
      exact (A.subtype.map_isConj hc).trans hdz
  · intro a ha han hao
    obtain ⟨p,hp⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting (zpowers t) A hdis hcomm
    obtain ⟨⟨u,v⟩,huv⟩ := p.surjective ⟨a,hH ▸ ha⟩
    have hav : (u:G) * (v:G) = a := (hp u v).symm.trans (congrArg Subtype.val huv)
    have hu : (u:G) = 1 ∨ (u:G) = t := by
      have hu := mem_zpowers_iff_mem_range_orderOf.mp u.property
      rw [ht] at hu
      obtain ⟨n,hn,heq⟩ := Finset.mem_image.mp hu
      have hn' : n < 2 := Finset.mem_range.mp hn
      interval_cases n
      · exact Or.inl (by simpa only [pow_zero] using heq.symm)
      · exact Or.inr (by simpa only [pow_one] using heq.symm)
    rcases hu with hu | hu
    · apply False.elim
      apply han
      rw [hu,one_mul] at hav
      exact hav ▸ v.property
    rw [hu] at hav
    have hva2 : (v:G)^2 = 1 := by
      have hpow : (t * (v:G))^2 = 1 := by rw [hav,←hao]; exact pow_orderOf_eq_one a
      have hc : Commute t (v:G) := (htC v v.property).symm
      simpa only [hc.mul_pow,ht2,one_mul] using hpow
    by_cases hv1 : (v:G) = 1
    · rw [←hav,hv1,mul_one]
    have hvoG : orderOf (v:G) = 2 := orderOf_eq_prime hva2 hv1
    have hvo : orderOf v = 2 := (Subgroup.orderOf_coe v).symm.trans hvoG
    rw [←hav]
    by_cases hvK : (v:G) ∈ K
    · exact (central_mul_isConj t htC _ _ (hinner_conj v hvK hvoG)).trans htz.symm
    · exact (central_mul_isConj t htC v b
        (Matrix.PSL3Three.EightGeometry.outer_involutions_conjugate_of_equiv eA v b
          hvo hbo (houter v hvK) (houter b hbK))).trans hbt

/-- The same fusion criterion with the outer conjugate supplied directly. -/
theorem linear_three_outer_fusion_of_crossing
    {H K A : Subgroup G} (hKA : K ≤ A)
    (eK : K ≃* Matrix.PSL3Three.PSL)
    (eA : A ≃* MulAut Matrix.PSL3Three.PSL)
    (hinner : (MulAut.innerSubgroup Matrix.PSL3Three.PSL).comap eA.toMonoidHom =
      K.subgroupOf A)
    (t : G) (ht : orderOf t = 2)
    (hH : H = zpowers t ⊔ A) (hdis : Disjoint (zpowers t) A)
    (hcomm : zpowers t ≤ centralizer (A : Set G))
    (e z : K) (he : orderOf e = 2) (hz : orderOf z = 2)
    (f : A) (hf : (f:G) ∉ K) (x : G)
    (hxt : x⁻¹ * t * x = t * (z:G))
    (hxe : x⁻¹ * (e:G) * x = (f:G)) :
    (∀ a ∈ A, orderOf a = 2 → IsConj a (z:G)) ∧
    (∀ a ∈ H, a ∉ A → orderOf a = 2 → IsConj a t) := by
  let y : A := ⟨(e:G)⁻¹ * (f:G), A.mul_mem (A.inv_mem (hKA e.property)) f.property⟩
  have hy : (y:G) ∉ K := by
    intro hy
    apply hf
    simpa only [y,mul_inv_cancel_left] using K.mul_mem e.property hy
  apply linear_three_outer_fusion_transport hKA eK eA hinner t ht hH hdis hcomm
    e z he hz y hy x hxt
  simpa only [y,mul_inv_cancel_left] using hxe

end CFSG.Quasithin.Chapter2.Section05
