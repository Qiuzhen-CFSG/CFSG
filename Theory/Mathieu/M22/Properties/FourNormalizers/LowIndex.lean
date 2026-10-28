module



public import Theory.Mathieu.M22.Properties.FourNormalizers.LowIndexCertificate
import all Theory.Mathieu.M22.Properties.CubicInverters.Enumeration

/-!
# Low-index four-group commutation in the Mathieu 22 automorphism group

Eight actual Sylow conjugates rule out an involution outside the certified
rows whenever its centralizer has index at most six. A four-group with
normalizer index at most two has every involution in those rows. The checked
full automorphism Sylow permutes the rows while preserving their commutation
relations. Sylow transport gives the result for the literal subgroup of
inner automorphisms in any two-subgroup containing an inner Sylow.

Source: Aschbacher–Smith 2.4.32, printed p.547.
-/

public section
namespace Sporadic.Mathieu.M22SmallFour
open Subgroup Theory.GroupTheory
open M22FourNormalizers.FixedSylow
set_option maxRecDepth 100000

private theorem element_centralizer_index_le_six (V : Subgroup M22)
    (hi : (normalizer (V : Set M22)).relIndex (M22EvenGeometry.sylow : Subgroup M22) ≤ 2)
    (hc : Nat.card V = 4) (v : M22) (hv : v ∈ V) :
    (centralizer ({v} : Set M22)).relIndex (M22EvenGeometry.sylow : Subgroup M22) ≤ 6 := by
  by_cases h1 : v = 1
  · subst v
    have he : centralizer ({(1:M22)} : Set M22) = ⊤ := by
      ext x
      simp [mem_centralizer_singleton_iff]
    rw [he,relIndex_top_left]
    decide
  let P := (M22EvenGeometry.sylow : Subgroup M22)
  let N := P ⊓ normalizer (V : Set M22)
  let C := centralizer ({v} : Set M22)
  have hN : N.relIndex P ≤ 2 := by simpa only [N,inf_relIndex_left] using hi
  have hC : C.relIndex N ≤ 3 := by
    have hh := centralizer_relIndex_le_card_sub_one N V inf_le_right v hv h1
    simpa only [hc] using hh
  have ht := relIndex_mul_relIndex (C ⊓ N) N P inf_le_right inf_le_left
  rw [inf_relIndex_right] at ht
  exact (relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite).trans
    (ht ▸ (Nat.mul_le_mul hC hN))

private theorem row_good_of_small_centralizer (i : Fin 128)
    (hs : rowElement i ^ 2 = 1)
    (hi : (centralizer ({rowElement i} : Set M22)).relIndex
      (M22EvenGeometry.sylow : Subgroup M22) ≤ 6) : ∃ j, i = good j := by
  rcases row_cases i with hg | ⟨x,hx⟩ | hi8
  · exact hg
  · have he := congrArg (fun z : M22 => z.val x) hs
    change (rowElement i).val ((rowElement i).val x) = x at he
    simp only [rowElement_apply] at he
    exact (hx he).elim
  · let P := (M22EvenGeometry.sylow : Subgroup M22)
    let v : P := ⟨rowElement i,wordElement_mem _⟩
    let f : Fin 8 → P := fun j =>
      ⟨rowElement (conjugator i j)*rowElement i*(rowElement (conjugator i j))⁻¹,
        P.mul_mem (P.mul_mem (wordElement_mem _) (wordElement_mem _)) (P.inv_mem (wordElement_mem _))⟩
    have hkey (j : Fin 8) : key (f j).val.val = conjugateKey i j := by
      have hp : (f j).val.val = fun x => rowTable (conjugator i j)
          (rowTable i (rowInvTable (conjugator i j) x)) := by
        funext x
        change (rowElement (conjugator i j)).val ((rowElement i).val
          (((rowElement (conjugator i j))⁻¹).val x)) = _
        rw [rowElement_apply,rowElement_apply,rowElement_inv_apply]
      exact congrArg key hp
    have hinj : Function.Injective f := by
      intro j k he
      apply hi8
      rw [←hkey j,←hkey k,he]
    have hconj (j : Fin 8) : IsConj v (f j) := by
      apply isConj_iff.mpr
      exact ⟨⟨rowElement (conjugator i j),wordElement_mem _⟩,rfl⟩
    have hb := card_mul_le_of_injective_conjugates v f hinj hconj
    have he : centralizer ({v} : Set P) =
        (centralizer ({rowElement i} : Set M22)).subgroupOf P := by
      ext p
      simp only [mem_centralizer_singleton_iff,mem_subgroupOf]
      exact Subtype.ext_iff
    have hidx : (centralizer ({v} : Set P)).index ≤ 6 := by
      rw [he]
      exact hi
    have hmul := (centralizer ({v} : Set P)).card_mul_index
    have hp : 0 < Nat.card (centralizer ({v} : Set P)) := Nat.card_pos
    nlinarith

/-- The native inner Sylow calculation retains the literal outer actor. -/
theorem fixed_low_index_four_commutes (V : Subgroup M22)
    (hVP : V ≤ (M22EvenGeometry.sylow : Subgroup M22))
    (hi : (normalizer (V : Set M22)).relIndex (M22EvenGeometry.sylow : Subgroup M22) ≤ 2)
    (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 4)
    (t : m22DesignAut) (ht : t ∈ M22CubicInverters.standardSylow) :
    ∀ u ∈ V, ∀ v ∈ V, Commute u (m22DesignAutToAut t v) := by
  let := hV
  intro u hu v hv
  obtain ⟨i,hiu⟩ := rowSylow_surjective ⟨u,hVP hu⟩
  obtain ⟨j,hjv⟩ := rowSylow_surjective ⟨v,hVP hv⟩
  have heu : rowElement i = u := congrArg Subtype.val hiu
  have hev : rowElement j = v := congrArg Subtype.val hjv
  have hiV : rowElement i ∈ V := heu.symm ▸ hu
  have hjV : rowElement j ∈ V := hev.symm ▸ hv
  obtain ⟨a,ha⟩ := row_good_of_small_centralizer i
    (elemPow_eq_one_of_isElementaryAbelian (p:=2) _ hiV)
    (element_centralizer_index_le_six V hi hc _ hiV)
  obtain ⟨b,hb⟩ := row_good_of_small_centralizer j
    (elemPow_eq_one_of_isElementaryAbelian (p:=2) _ hjV)
    (element_centralizer_index_le_six V hi hc _ hjV)
  obtain ⟨k,hkt⟩ := M22CubicInverters.rowSylow_surjective ⟨t,ht⟩
  have het : M22CubicInverters.rowElement k = t := by
    simpa only [M22ConjugateGeneration.rowSylow_val] using congrArg Subtype.val hkt
  have hcomm : commutes a b = true := by
    apply (good_commute a b).mpr
    intro x
    have he := congrArg (fun z : M22 => z.val x) ((le_centralizer V hu) v hv)
    rw [←heu,←hev,ha,hb] at he
    simpa only [Subgroup.coe_mul,Equiv.Perm.coe_mul,Function.comp_apply,rowElement_apply] using he.symm
  have hact : m22DesignAutToAut t v = rowElement (good (conjugateGood k b)) := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rw [m22DesignAutToAut_apply_perm]
    change t.val (v.val (t.val⁻¹ x)) = _
    rw [←het,←hev,hb]
    simp only [M22CubicInverters.rowElement_apply,rowElement_apply]
    have hh := good_conjugation k b ((M22CubicInverters.rowElement k).val⁻¹ x)
    have hc : M22CubicInverters.rowTable k ((M22CubicInverters.rowElement k).val⁻¹ x) = x := by
      rw [←M22CubicInverters.rowElement_apply]
      exact Equiv.apply_symm_apply _ x
    rw [hc] at hh
    exact hh
  rw [hact,←heu,ha]
  change _ * _ = _ * _
  apply Subtype.ext
  apply Equiv.ext
  intro x
  simpa only [Subgroup.coe_mul,Equiv.Perm.coe_mul,Function.comp_apply,rowElement_apply] using
    (good_commute a (conjugateGood k b)).mp (commutes_conjugate a b k hcomm) x

end Sporadic.Mathieu.M22SmallFour

namespace Sporadic.Mathieu.M22SmallFour
open Subgroup M22ValueBound.Concrete
open scoped Pointwise

private theorem inclusion_action (a : m22DesignAut) (u : M22) :
    inclusion (m22DesignAutToAut a u) = a*inclusion u*a⁻¹ := by
  apply Subtype.ext
  exact m22DesignAutToAut_apply_perm a u

private theorem standard_comap :
    (M22CubicInverters.standardSylow : Subgroup m22DesignAut).comap inclusion =
      (M22EvenGeometry.sylow : Subgroup M22) := by
  change (outerFirst ⊓ outerSecond).comap inclusion = first ⊓ second
  rw [comap_inf,comap_outerFirst,comap_outerSecond]

/-- The low-index calculation for the literal inner subgroup of any
2-subgroup containing a full inner Sylow. -/
theorem low_index_four_commutes
    (Q : Subgroup m22DesignAut) (hQ : IsPGroup 2 Q)
    (P : Sylow 2 M22) (hPQ : (P : Subgroup M22).map inclusion ≤ Q)
    (V : Subgroup M22) (hVQ : V.map inclusion ≤ Q)
    (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 4)
    (hi : (normalizer (V.map inclusion : Set m22DesignAut)).relIndex Q ≤ 2)
    (t : m22DesignAut) (ht : t ∈ Q) :
    ∀ u ∈ V, ∀ v ∈ V, Commute u (m22DesignAutToAut t v) := by
  obtain ⟨S,hQS⟩ := hQ.exists_le_sylow
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq m22DesignAut S M22CubicInverters.standardSylow
  let e := MulAut.conj a
  let eI := m22DesignAutToAut a
  let Q' := Q.map e.toMonoidHom
  let W := V.map eI.toMonoidHom
  have hmap (B : Subgroup M22) : (B.map eI.toMonoidHom).map inclusion =
      (B.map inclusion).map e.toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro b
    exact inclusion_action a b
  have hS : (S : Subgroup m22DesignAut).map e.toMonoidHom =
      (M22CubicInverters.standardSylow : Subgroup m22DesignAut) :=
    congrArg Sylow.toSubgroup ha
  have hQ'S : Q' ≤ (M22CubicInverters.standardSylow : Subgroup m22DesignAut) :=
    hS ▸ map_mono hQS
  have hWP : W ≤ (M22EvenGeometry.sylow : Subgroup M22) := by
    rw [←standard_comap]
    apply map_le_iff_le_comap.mp
    rw [show W=V.map eI.toMonoidHom from rfl,hmap]
    exact (map_mono hVQ).trans hQ'S
  have hP' : (P : Subgroup M22).map eI.toMonoidHom =
      (M22EvenGeometry.sylow : Subgroup M22) := by
    have hp : (P : Subgroup M22).map eI.toMonoidHom ≤
        (M22EvenGeometry.sylow : Subgroup M22) := by
      rw [←standard_comap]
      apply map_le_iff_le_comap.mp
      rw [hmap]
      exact (map_mono hPQ).trans hQ'S
    exact ((P.mapSurjective (f:=eI.toMonoidHom) eI.surjective).is_maximal'
      M22EvenGeometry.sylow.isPGroup' hp).symm
  have hstdQ : (M22EvenGeometry.sylow : Subgroup M22).map inclusion ≤ Q' := by
    rw [←hP',hmap]
    exact map_mono hPQ
  have hi' : (normalizer (W : Set M22)).relIndex (M22EvenGeometry.sylow : Subgroup M22) ≤ 2 := by
    have hnorm : (normalizer (W.map inclusion : Set m22DesignAut)).comap inclusion =
        normalizer (W : Set M22) := by
      rw [comap_normalizer_eq_of_le_range (Subgroup.map_le_range (f := M22ValueBound.Concrete.inclusion) (H := W)),
        comap_map_eq_self_of_injective inclusion_injective]
    have hij := (relIndex_le_of_le_right (H := normalizer (W.map inclusion : Set m22DesignAut)) hstdQ index_ne_zero_of_finite)
    have hhi : (normalizer (W.map inclusion : Set m22DesignAut)).relIndex Q' ≤ 2 := by
      rw [show W=V.map eI.toMonoidHom from rfl,hmap,
        ←map_equiv_normalizer_eq,show Q'=Q.map e.toMonoidHom from rfl,
        relIndex_map_map_of_injective _ _ e.injective]
      exact hi
    have he := relIndex_comap (H := normalizer (W.map inclusion : Set m22DesignAut))
      M22ValueBound.Concrete.inclusion (M22EvenGeometry.sylow : Subgroup M22)
    rw [hnorm] at he
    exact he ▸ hij.trans hhi
  let := hV
  have hWE : IsElementaryAbelian 2 W := IsElementaryAbelian.map eI.toMonoidHom
  have hWc : Nat.card W = 4 := (card_map_of_injective eI.injective).trans hc
  intro u hu v hv
  have hh := fixed_low_index_four_commutes W hWP hi' hWE hWc (e t)
    (hQ'S (mem_map_of_mem e.toMonoidHom ht))
    (eI u) (mem_map_of_mem eI.toMonoidHom hu) (eI v) (mem_map_of_mem eI.toMonoidHom hv)
  apply eI.injective
  simp only [map_mul]
  have he : m22DesignAutToAut (e t) (eI v) = eI (m22DesignAutToAut t v) := by
    change (m22DesignAutToAut (a*t*a⁻¹)) (m22DesignAutToAut a v) = _
    rw [map_mul,map_mul,map_inv]
    simp only [MulAut.mul_apply,MulAut.inv_apply,MulEquiv.symm_apply_apply]
    rfl
  rw [he] at hh
  exact hh

end Sporadic.Mathieu.M22SmallFour
