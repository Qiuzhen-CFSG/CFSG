module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.SylowConjugates
public import Theory.GroupTheory.SylowElementConjugacy
public import Theory.GroupTheory.SylowNormalRestriction
/-!
# Campbell Theorem 6: commuting conjugates under all two-elements

The characteristic group J(H) has a Sylow subgroup obtained by restricting
the original Sylow S. Conjugate any two-element of J(H) into that restriction,
apply the original Sylow commutation theorem and conjugate back. Thus each
conjugate of F^α commutes with its conjugate by every two-element of J(H).
Consequently the orbit span under any actual two-subgroup of J(H) is
elementary abelian. This supplies the orbit theorem used in II.6.4 and II.7.2.
Source: Campbell, *Pushing up in Finite Groups* (1979), Theorem 6,
printed p.31, specialized to the Aut(S) case needed in C.1.18.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {H : Type*} [Group H] [Finite H] (S : Subgroup H)

omit [Finite H] in
private theorem conj_map_mul (A : Subgroup H) (x g : H) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      A.map (MulAut.conj (x*g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply,mul_assoc]

theorem InLocalClass.two_element_conjugates_commute (h : InLocalClass S.subtype) (hB : IsBaumannFixed S)
    (a : MulAut S) (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (t g : H) (htK : t ∈ Campbell.J (⊤ : Subgroup H)) (ht2 : ∃ n, orderOf t=2^n)
    (hg : g ∈ Campbell.J (⊤ : Subgroup H)) :
    let Y := automorphismImage S a (Campbell.F H)
    ⁅Y.map (MulAut.conj g).toMonoidHom,Y.map (MulAut.conj (t*g)).toMonoidHom⁆=⊥ := by
  let K := Campbell.J (⊤ : Subgroup H)
  let : K.Normal := by
    change (elementaryAbelianMaxJ (⊤ : Subgroup H)).Normal
    let : (elementaryAbelianMaxJ (⊤ : Subgroup H)).Characteristic := elementaryAbelianMaxJ_top_characteristic
    infer_instance
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  obtain ⟨P,hP⟩ := T.exists_sylow_map_eq_inf_of_normal K
  let tk : K := ⟨t,htK⟩
  obtain ⟨n,hn⟩ := ht2
  have horder : orderOf tk=2^n := by rwa [←Subgroup.orderOf_coe]
  obtain ⟨y,hy⟩ := P.exists_isConj_of_orderOf_eq_prime_pow horder
  obtain ⟨c,hc⟩ := isConj_iff.mp hy
  have hct : (c:H)*t*(c:H)⁻¹ ∈ S := by
    have hc' : (c:H)*t*(c:H)⁻¹=(y:K) := congrArg Subtype.val hc
    rw [hc',hST]
    exact ((hP ▸ mem_map_of_mem K.subtype y.property): (y:K).val ∈ (T:Subgroup H) ⊓ K).1
  have hctK : (c:H)*t*(c:H)⁻¹ ∈ K := K.mul_mem (K.mul_mem c.property htK) (K.inv_mem c.property)
  have hcg : (c:H)*g ∈ K := K.mul_mem c.property hg
  have hh := h.sylow_conjugates_commute S hB a hV ((c:H)*t*(c:H)⁻¹) ((c:H)*g) hct hctK hcg
  dsimp only at hh ⊢
  have he : ((c:H)*t*(c:H)⁻¹)*((c:H)*g)=(c:H)*(t*g) := by group
  rw [he] at hh
  apply (Subgroup.map_eq_bot_iff_of_injective (f := (MulAut.conj (c:H)).toMonoidHom) _ (MulAut.conj (c:H)).injective).mp
  rw [map_commutator,conj_map_mul,conj_map_mul]
  exact hh


theorem InLocalClass.two_subgroup_conjugate_span_elementary (h : InLocalClass S.subtype)
    (hB : IsBaumannFixed S) (a : MulAut S)
    (hV : automorphismImage S a (Campbell.V H) ≤ pCore 2 H)
    (P : Subgroup H) (hP : IsPGroup 2 P) (hPK : P ≤ Campbell.J (⊤ : Subgroup H))
    (g:H) (hg : g ∈ Campbell.J (⊤ : Subgroup H)) :
    IsElementaryAbelian 2 (conjugateSpanBy
      ((automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom) P) := by
  let A := (automorphismImage S a (Campbell.F H)).map (MulAut.conj g).toMonoidHom
  have hAC : A ≤ centralizer (conjugateSpanBy A P : Set H) := by
    apply le_centralizer_iff.mpr
    apply (closure_le _).mpr
    rintro z ⟨x,hx,y,hy,rfl⟩
    have hx2 : ∃ n, orderOf x=2^n := by
      obtain ⟨n,hn⟩ := hP.exists_orderOf_eq_pow (⟨x,hx⟩ : P)
      exact ⟨n,by simpa only [←Subgroup.orderOf_coe] using hn⟩
    have hc := h.two_element_conjugates_commute S hB a hV x g (hPK hx) hx2 hg
    dsimp only at hc
    rw [←conj_map_mul] at hc
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
      (mem_map_of_mem (MulAut.conj x).toMonoidHom hy)
  let : IsMulCommutative (conjugateSpanBy A P) := (conjugateSpanBy_commutative_iff A P).mpr hAC
  let : IsElementaryAbelian 2 (Campbell.F H) := omegaOneCenterAmbient_elementaryAbelian _
  obtain ⟨T,hT,_⟩ := h.sylow
  have hST : S=(T:Subgroup H) := (range_subtype S).symm.trans hT
  have hFS : Campbell.F H ≤ S := Campbell.F_le_pCore.trans (hST ▸ pCore_isPGroup.le_sylow_of_normal T)
  let : IsElementaryAbelian 2 ((Campbell.F H).subgroupOf S) := IsElementaryAbelian.subgroupOf hFS
  let : IsElementaryAbelian 2 (((Campbell.F H).subgroupOf S).map a.toMonoidHom) := IsElementaryAbelian.map a.toMonoidHom
  let : IsElementaryAbelian 2 (automorphismImage S a (Campbell.F H)) := IsElementaryAbelian.map S.subtype
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  exact conjugateSpanBy_elementary_of_commutative A P
end CFSG.Quasithin.ChapterC.GlaubermanNiles
