module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Sylow
public import Theory.GroupTheory.DihedralSemidihedralSquares

/-!
# Local fusion and the normalizer-square obstruction

Conjugate a proposed order-four lift into the fixed Sylow subgroup inside
N_G(L). This preserves nonterminality of its square, so uniform 16.3.8 makes
the square's centralizer elementary. An automorphism square fixes an element
of order four in the characteristic rotations, a contradiction.

The normalizer condition for the two-group T_C also supplies an actual
conjugator taking t to tz: it moves t in its elementary four-centralizer
while fixing the original central involution z.

Source: Aschbacher–Smith, 16.3.9–11, printed pp.1180–1181. The uniform
shape premise is precisely the earlier 16.3.8 conclusion.
-/

public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter16.EnlargementSieve
variable {G : Type*} [Group G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- Conjugacy by the normalizer of L preserves the contrary component condition. -/
theorem counterexample_conjugate_normalizer (h : TerminalCounterexample T z L t)
    (g : G) (hg : g ∈ normalizer L)
    (hm : (MulAut.conj g) t ∈ commutingSylow T L) :
    TerminalCounterexample T z L ((MulAut.conj g) t) := by
  let e := MulAut.conj g
  refine ⟨h.localSetup, h.normal, (e.orderOf_eq t).trans h.involution, hm, ?_⟩
  intro hc
  have he : e.symm.toMonoidHom = (MulAut.conj g⁻¹).toMonoidHom := by
    ext x
    apply e.injective
    simp [e, MulAut.conj_apply, mul_assoc]
  have hback : L.map e.symm.toMonoidHom = L := by
    rw [he]
    exact mem_normalizer_iff_map_conj_eq.mp ((normalizer (L : Set G)).inv_mem hg)
  have hmap := (show Theory.GroupTheory.IsComponentIn L
    (involutionCentralizer (e t)) from hc).map e.symm
  rw [hback, involutionCentralizer, map_centralizer_equiv,
    Set.image_singleton, e.symm_apply_apply] at hmap
  exact h.not_component hmap

variable [Finite G]

/-- A square in the fixed Sylow subgroup would fix an element of order four
inside the elementary centralizer of t. -/
theorem no_square_in_sylow (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (u : G) (hu : u ∈ (T : Subgroup G)) (hsq : u ^ 2 = t) : False := by
  let S := commutingSylow T L
  have hun : u ∈ normalizer S := inf_normalizer_le_normalizer_inf
    ⟨(T : Subgroup G).le_normalizer hu,
      normalizer_le_normalizer_centralizer L (h.sylow_le_normalizer hu)⟩
  let α : MulAut S := S.normalizerMonoidHom ⟨u, hun⟩
  obtain ⟨R, hR, hcyc, hcard⟩ := DihedralSemidihedral.exists_characteristic_cyclic_rotation hs.model
  let := hR
  let := hcyc
  obtain ⟨x, hx, hfix⟩ := Subgroup.exists_order_four_fixed_by_automorphism_square R hcard α
  have hc : (x : G) ∈ involutionCentralizer t := by
    apply mem_centralizer_singleton_iff.mpr
    have he := congrArg Subtype.val hfix
    change u * (u * (x : G) * u⁻¹) * u⁻¹ = (x : G) at he
    have he' : (u ^ 2) * (x : G) * (u ^ 2)⁻¹ = (x : G) := by
      simpa only [pow_two, mul_inv_rev, mul_assoc] using he
    rw [hsq] at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  have hxE : (x : G) ∈ zpowers z ⊔ zpowers t := hs.centralizer_eq ▸ ⟨x.property, hc⟩
  let := (four_group h).1
  have hp := elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) hxE
  have hd := orderOf_dvd_of_pow_eq_one hp
  rw [orderOf_coe, hx] at hd
  norm_num at hd

/-- No element of order four normalizing L can square to a contrary involution.
Conjugate its cyclic subgroup into the fixed T inside N_G(L), then apply
16.3.8 to the transported contrary involution. -/
theorem not_normalizer_square (h : TerminalCounterexample T z L t)
    (hshape : ∀ a : G, TerminalCounterexample T z L a →
      NonterminalCentralizerShape T z L a) : ¬ NormalizerSquareWitness L t := by
  rintro ⟨u, hu4, huN, husq⟩
  let N := normalizer (L : Set G)
  let uN : N := ⟨u, huN⟩
  have hU : IsPGroup 2 (zpowers uN) := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers, ← orderOf_coe uN, hu4]; norm_num)
  obtain ⟨P, hUP⟩ := hU.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N P (T.subtype h.sylow_le_normalizer)
  let e := MulAut.conj (g : G)
  have hvT : e u ∈ (T : Subgroup G) := by
    have hh : (MulAut.conj g) uN ∈ (T.subtype h.sylow_le_normalizer : Subgroup N) := by
      rw [← hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hUP (mem_zpowers uN))
    exact hh
  have hsq : (e u) ^ 2 = e t := by rw [← map_pow, husq]
  have hm : e t ∈ commutingSylow T L := by
    refine ⟨hsq ▸ (T : Subgroup G).pow_mem hvT 2, ?_⟩
    exact (normalizer_le_normalizer_centralizer L g.property t).mp h.mem_commutingSylow.2
  have hc := counterexample_conjugate_normalizer h g g.property hm
  exact no_square_in_sylow hc (hshape (e t) hc) (e u) hvT hsq

end CFSG.Quasithin.Chapter16.EnlargementSieve

namespace CFSG.Quasithin.Chapter16.EnlargementSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-- The other two involutions in the elementary centralizer fuse inside T_C.
The normalizer condition supplies an element moving t while fixing z. -/
theorem local_conjugacy (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t) :
    ∃ g ∈ commutingSylow T L, (MulAut.conj g) t = t * z := by
  let S := commutingSylow T L
  let E := zpowers z ⊔ zpowers t
  have hES : E ≤ S := four_le_commutingSylow h
  let E' := E.subgroupOf S
  let : IsElementaryAbelian 2 E := (four_group h).1
  have hproper : E' ≠ ⊤ := by
    intro he
    obtain ⟨R, hR, hcyc, hcard⟩ := DihedralSemidihedral.exists_characteristic_cyclic_rotation hs.model
    let := hR
    let := hcyc
    obtain ⟨x, hx, -⟩ := Subgroup.exists_order_four_fixed_by_automorphism_square R hcard 1
    have hxE : (x : G) ∈ E := by
      have hh : x ∈ E' := he ▸ mem_top x
      exact hh
    have hd := orderOf_dvd_of_pow_eq_one
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (x : G) hxE)
    rw [orderOf_coe, hx] at hd
    norm_num at hd
  let : Group.IsNilpotent S := (T.isPGroup'.to_le inf_le_left).isNilpotent
  obtain ⟨g, hg, hgE⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent E' (lt_top_iff_ne_top.mpr hproper))
  have hgN : (g : G) ∈ normalizer E := by
    rw [← subgroupOf_normalizer_eq hES] at hg
    exact hg
  let e := MulAut.conj (g : G)
  have het : e t ∈ E := (hgN t).mp ((le_sup_right : zpowers t ≤ E) (mem_zpowers t))
  have hzfix : e z = z := mul_inv_eq_iff_eq_mul.mpr
    (mem_centralizer_singleton_iff.mp (h.localSetup.sylow_centralizes g.property.1))
  have htfix : e t ≠ t := by
    intro hf
    apply hgE
    change (g : G) ∈ zpowers z ⊔ zpowers t
    rw [← hs.centralizer_eq]
    exact ⟨g.property, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hf)⟩
  have ht1 : e t ≠ 1 := by
    intro he
    have ht : t = 1 := e.injective (he.trans (map_one e).symm)
    have hh := h.involution
    simp [ht] at hh
  have htz : e t ≠ z := fun he => h.ne_original (e.injective (he.trans hzfix.symm))
  have hzt : Commute z t :=
    (mem_centralizer_singleton_iff.mp
      (h.localSetup.sylow_centralizes h.mem_commutingSylow.1)).symm
  have hclosure : E = closure ({z, t} : Set G) := by
    change zpowers z ⊔ zpowers t = _
    rw [show ({z, t} : Set G) = {z} ∪ {t} by ext; simp [or_comm],
      Subgroup.closure_union, ← zpowers_eq_closure, ← zpowers_eq_closure]
  rw [hclosure] at het
  rcases (mem_closure_pair_iff z t
    (by simpa only [h.localSetup.involution, pow_two] using pow_orderOf_eq_one z)
    (by simpa only [h.involution, pow_two] using pow_orderOf_eq_one t) hzt (e t)).mp het
    with h1 | hz | ht | hprod
  · exact (ht1 h1).elim
  · exact (htz hz).elim
  · exact (htfix ht).elim
  · exact ⟨g, g.property, hprod.trans hzt.eq⟩

/-- Ambient fusion follows from the actual conjugator in T_C. -/
theorem isConj_mul_original (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t) : IsConj t (t * z) := by
  obtain ⟨g, -, hg⟩ := local_conjugacy h hs
  exact isConj_iff.mpr ⟨g, hg⟩

end CFSG.Quasithin.Chapter16.EnlargementSieve
