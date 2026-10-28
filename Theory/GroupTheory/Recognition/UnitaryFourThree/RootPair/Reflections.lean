module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.CenterStructure
public import Theory.GroupTheory.ElementaryFourShear
public import Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# The two genuine root-pair reflections

The root product has elementary central quotient. An actor in a core but
outside its involution centralizer therefore fixes exactly that factor
modulo E. The reverse inclusion uses the no-singular-shear lemma: an
ambient actor whose core displacement lies in E is inner on the core,
and its remaining centralizer belongs to the central line.

Source: Aschbacher, *Sporadic Groups* (1994), 8.15(6) and45.3, pp.29–30,243.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace RootPair
variable (P : RootPair z)

/-- A normalizer element inducing a singular shear on the actual core is already in the core. -/
theorem mem_core_of_commutator_le_E (h : IsType z) (r : G)
    (hr : r ∈ centralizer z) (hc : ∀ q ∈ core z, ⁅r,q⁆ ∈ P.E) : r ∈ core z := by
  let Q := core z
  let Z : Q := ⟨z,z_mem_core h⟩
  let U : Q := ⟨P.u,P.mem_core⟩
  let d := h.toCentralizerHypothesis.coreData
  let : IsExtraspecial 2 Q := h.toCentralizerHypothesis.core_extraspecial
  let α := Q.normalizerMonoidHom ⟨r,CentralizerHypothesis.centralizer_normalizes_core hr⟩
  have hzZ : Z ∈ center Q := mem_center_iff.mpr (fun q =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (core_le_centralizer q.property)))
  have huZ : U ∉ center Q := by
    intro hh
    apply P.not_mem_line
    rw [← h.toCentralizerHypothesis.core_center]
    exact mem_map_of_mem Q.subtype hh
  have hF : (closure ({Z,U} : Set Q)).map Q.subtype = P.E := by
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq,Set.image_singleton]
    change closure ({z,P.u} : Set G) = zpowers z ⊔ zpowers P.u
    rw [zpowers_eq_closure,zpowers_eq_closure,← Subgroup.closure_union]
    congr 1
  have hd := α.central_displacement_of_four_displacement Z U
    (Subtype.ext (h.involution ▸ pow_orderOf_eq_one z))
    (Subtype.ext (P.u_order h ▸ pow_orderOf_eq_one P.u)) hzZ huZ
    (fun q => d.fixes_center α ⟨q^2,d.square_mem_center q⟩) (by
      intro q
      have hq := hc q q.property
      rw [← hF] at hq
      obtain ⟨v,hv,he⟩ := hq
      have heq : v = α q*q⁻¹ := Subtype.ext he
      exact heq ▸ hv)
  obtain ⟨a,ha⟩ := IsExtraspecial.exists_conj_of_central_displacement (p:=2) α hd
  have hcent : (a:G)⁻¹*r ∈ Subgroup.centralizer (Q : Set G) := by
    intro q hq
    have he := congrArg (fun f : MulAut Q => (f ⟨q,hq⟩ : G)) ha
    change (a:G)*q*(a:G)⁻¹ = r*q*r⁻¹ at he
    have hh := congrArg (fun v : G => (a:G)⁻¹*v*r) he
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_inv_cancel,
      mul_one,one_mul] using hh
  have hmem : (a:G)⁻¹*r ∈ Q := h.toCentralizerHypothesis.line_le_core
    (h.toCentralizerHypothesis.centralizer_core ▸ hcent)
  simpa only [mul_inv_cancel_left] using Q.mul_mem a.property hmem

theorem centralizer_conjugateCore (h : IsType z) :
    Subgroup.centralizer (P.conjugateCore : Set G) = zpowers P.u := by
  let e := MulAut.conj P.g⁻¹
  have he : (Subgroup.centralizer (core z : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (P.conjugateCore : Set G) := by
    ext x
    rw [mem_map_equiv]
    constructor
    · intro hx a ha
      obtain ⟨b,hb,rfl⟩ := ha
      change e b*x=x*e b
      simpa only [map_mul,e.apply_symm_apply] using congrArg e (hx b hb)
    · intro hx a ha
      apply e.injective
      simpa only [map_mul,e.apply_symm_apply] using hx (e a) (mem_map_of_mem _ ha)
  rw [← he,h.toCentralizerHypothesis.centralizer_core,MonoidHom.map_zpowers]
  simp only [e,u,MulAut.conj_apply,inv_inv,MulEquiv.coe_toMonoidHom]

/-- The returning core satisfies the same no-singular-shear conclusion. -/
theorem mem_conjugateCore_of_commutator_le_E (h : IsType z) (r : G)
    (hr : r ∈ centralizer P.u) (hc : ∀ q ∈ P.conjugateCore, ⁅r,q⁆ ∈ P.E) :
    r ∈ P.conjugateCore := by
  let Q := P.conjugateCore
  let Z : Q := ⟨P.u,P.u_mem_conjugateCore h⟩
  let U : Q := ⟨z,P.z_mem_conjugateCore h⟩
  let d := h.toCentralizerHypothesis.coreData.map P.conjugateCoreEquiv
  let : IsExtraspecial 2 Q := P.conjugateCore_extraspecial h
  let α := Q.normalizerMonoidHom ⟨r,(P.normalizer_conjugateCore h).ge hr⟩
  have hzZ : Z ∈ center Q := mem_center_iff.mpr (fun q =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (P.conjugateCore_le q.property)))
  have huZ : U ∉ center Q := by
    intro hh
    have hm : z ∈ zpowers P.u := P.conjugateCore_center h ▸ mem_map_of_mem Q.subtype hh
    have hle : P.E ≤ zpowers P.u := sup_le (zpowers_le.mpr hm) le_rfl
    have he := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
    rw [P.E_card h,Nat.card_zpowers,P.u_order h] at he
    omega
  have hF : (closure ({Z,U} : Set Q)).map Q.subtype = P.E := by
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq,Set.image_singleton]
    change closure ({P.u,z} : Set G) = zpowers z ⊔ zpowers P.u
    rw [zpowers_eq_closure,zpowers_eq_closure,← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    exact or_comm
  have hd := α.central_displacement_of_four_displacement Z U
    (Subtype.ext (P.u_order h ▸ pow_orderOf_eq_one P.u))
    (Subtype.ext (h.involution ▸ pow_orderOf_eq_one z)) hzZ huZ
    (fun q => d.fixes_center α ⟨q^2,d.square_mem_center q⟩) (by
      intro q
      have hq := hc q q.property
      rw [← hF] at hq
      obtain ⟨v,hv,he⟩ := hq
      have heq : v = α q*q⁻¹ := Subtype.ext he
      exact heq ▸ hv)
  obtain ⟨a,ha⟩ := IsExtraspecial.exists_conj_of_central_displacement (p:=2) α hd
  have hcent : (a:G)⁻¹*r ∈ Subgroup.centralizer (Q : Set G) := by
    intro q hq
    have he := congrArg (fun f : MulAut Q => (f ⟨q,hq⟩ : G)) ha
    change (a:G)*q*(a:G)⁻¹ = r*q*r⁻¹ at he
    have hh := congrArg (fun v : G => (a:G)⁻¹*v*r) he
    simpa only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_inv_cancel,
      mul_one,one_mul] using hh
  have hmem : (a:G)⁻¹*r ∈ Q := (zpowers_le.mpr (P.u_mem_conjugateCore h))
    (P.centralizer_conjugateCore h ▸ hcent)
  simpa only [mul_inv_cancel_left] using Q.mul_mem a.property hmem

theorem R_quotient_elementary (h : IsType z) : IsElementaryAbelian 2 (P.R ⧸ center P.R) := by
  have hs (q : P.R ⧸ center P.R) : q^2=1 := by
    obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (center P.R) q
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    have he := P.R_square_mem_E h r r.property
    rw [← P.R_center h] at he
    obtain ⟨x,hx,hxv⟩ := he
    have hx' : x=r^2 := Subtype.ext hxv
    exact hx' ▸ hx
  let : IsMulCommutative (P.R ⧸ center P.R) :=
    ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun q => orderOf_dvd_of_pow_eq_one (hs q)) a b).eq⟩⟩
  exact ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs⟩


theorem R_commutator_le_E (h : IsType z) : ⁅P.R,P.R⁆ ≤ P.E := by
  rw [← P.R_center h,← map_subtype_commutator]
  exact map_mono (P.R_quotient_elementary h).commutator_le_center_of_central_quotient

omit [Finite G] in
theorem R_inf_core (_h : IsType z) : P.R ⊓ core z = P.leftCore := by
  apply le_antisymm
  · exact le_inf inf_le_right
      (inf_le_left.trans (P.R_le_double_centralizer.trans inf_le_right))
  · exact le_inf le_sup_left inf_le_left

/-- The reflection induced by the original core fixes exactly its own factor modulo E. -/
theorem reflection_fixed_coset_iff (h : IsType z) (s : G)
    (hs : s ∈ core z) (hsA : s ∉ P.leftCore) (r : G) (hr : r ∈ P.R) :
    ⁅s,r⁆ ∈ P.E ↔ r ∈ P.leftCore := by
  constructor
  · intro hsr
    have hrs : ⁅r,s⁆ ∈ P.E := by
      rw [← commutatorElement_inv]
      exact P.E.inv_mem hsr
    have hrQ : r ∈ core z := by
      apply P.mem_core_of_commutator_le_E h r (P.R_le_double_centralizer hr).1
      intro q hq
      let Q := core z
      let A := P.leftCore.subgroupOf Q
      let S : Q := ⟨s,hs⟩
      have hi : A.index=2 := by
        have he := A.card_mul_index
        change Nat.card (P.leftCore.subgroupOf (core z))*A.index = Nat.card (core z) at he
        rw [Nat.card_congr (subgroupOfEquivOfLe (show P.leftCore ≤ core z from inf_le_left)).toEquiv,
          P.leftCore_card h,h.toCentralizerHypothesis.core_card] at he
        omega
      by_cases hqa : q ∈ P.leftCore
      · exact P.R_commutator_le_E h (commutator_mem_commutator hr (mem_sup_left hqa))
      · have ha : q*s⁻¹ ∈ P.leftCore := by
          have hqa' : (⟨q,hq⟩:Q) ∉ A := hqa
          have hsA' : S ∉ A := hsA
          exact (show (⟨q,hq⟩:Q)*S⁻¹ ∈ A from (A.mul_mem_iff_of_index_two hi).mpr
            (by simpa only [inv_mem_iff] using iff_of_false hqa' hsA'))
        have hcomm := P.R_commutator_le_E h
          (commutator_mem_commutator hr (mem_sup_left ha))
        have he : q=(q*s⁻¹)*s := by simp
        rw [he,commutatorElement_mul_right_eq_mul_conj]
        have hn : q*s⁻¹ ∈ normalizer (P.E : Set G) := P.core_le_N h (Q.mul_mem hq (Q.inv_mem hs))
        simpa only [mul_assoc] using P.E.mul_mem hcomm ((mem_normalizer_iff.mp hn _).mp hrs)
    exact (P.R_inf_core h).le ⟨hr,hrQ⟩
  · intro hrA
    let : IsExtraspecial 2 (core z) := h.toCentralizerHypothesis.core_extraspecial
    have he : ⁅s,r⁆ ∈ zpowers z := h.toCentralizerHypothesis.core_center ▸
      mem_map_of_mem (core z).subtype
        ((IsExtraspecial.quotient_elementary_abelian 2 (core z)).commutator_le_center_of_central_quotient
          (commutator_mem_commutator (mem_top (⟨s,hs⟩:core z)) (mem_top (⟨r,hrA.1⟩:core z))))
    exact (le_sup_left : zpowers z ≤ P.E) he

omit [Finite G] in
theorem R_inf_conjugateCore (_h : IsType z) : P.R ⊓ P.conjugateCore = P.rightCore := by
  apply le_antisymm
  · exact le_inf inf_le_right
      (inf_le_left.trans (P.R_le_double_centralizer.trans inf_le_left))
  · exact le_inf le_sup_right inf_le_left

/-- The reflection induced by the returning core fixes exactly its own factor modulo E. -/
theorem returning_reflection_fixed_coset_iff (h : IsType z) (s : G)
    (hs : s ∈ P.conjugateCore) (hsA : s ∉ P.rightCore) (r : G) (hr : r ∈ P.R) :
    ⁅s,r⁆ ∈ P.E ↔ r ∈ P.rightCore := by
  constructor
  · intro hsr
    have hrs : ⁅r,s⁆ ∈ P.E := by
      rw [← commutatorElement_inv]
      exact P.E.inv_mem hsr
    have hrQ : r ∈ P.conjugateCore := by
      apply P.mem_conjugateCore_of_commutator_le_E h r (P.R_le_double_centralizer hr).2
      intro q hq
      let Q := P.conjugateCore
      let A := P.rightCore.subgroupOf Q
      let S : Q := ⟨s,hs⟩
      have hi : A.index=2 := by
        have he := A.card_mul_index
        change Nat.card (P.rightCore.subgroupOf (P.conjugateCore))*A.index = Nat.card (P.conjugateCore) at he
        rw [Nat.card_congr (subgroupOfEquivOfLe (show P.rightCore ≤ P.conjugateCore from inf_le_left)).toEquiv,
          P.rightCore_card h,P.conjugateCore_card h] at he
        omega
      by_cases hqa : q ∈ P.rightCore
      · exact P.R_commutator_le_E h (commutator_mem_commutator hr (mem_sup_right hqa))
      · have ha : q*s⁻¹ ∈ P.rightCore := by
          have hqa' : (⟨q,hq⟩:Q) ∉ A := hqa
          have hsA' : S ∉ A := hsA
          exact (show (⟨q,hq⟩:Q)*S⁻¹ ∈ A from (A.mul_mem_iff_of_index_two hi).mpr
            (by simpa only [inv_mem_iff] using iff_of_false hqa' hsA'))
        have hcomm := P.R_commutator_le_E h
          (commutator_mem_commutator hr (mem_sup_right ha))
        have he : q=(q*s⁻¹)*s := by simp
        rw [he,commutatorElement_mul_right_eq_mul_conj]
        have hn : q*s⁻¹ ∈ normalizer (P.E : Set G) := P.conjugateCore_le_N h (Q.mul_mem hq (Q.inv_mem hs))
        simpa only [mul_assoc] using P.E.mul_mem hcomm ((mem_normalizer_iff.mp hn _).mp hrs)
    exact (P.R_inf_conjugateCore h).le ⟨hr,hrQ⟩
  · intro hrA
    let : IsExtraspecial 2 (P.conjugateCore) := P.conjugateCore_extraspecial h
    have he : ⁅s,r⁆ ∈ zpowers P.u := P.conjugateCore_center h ▸
      mem_map_of_mem (P.conjugateCore).subtype
        ((IsExtraspecial.quotient_elementary_abelian 2 (P.conjugateCore)).commutator_le_center_of_central_quotient
          (commutator_mem_commutator (mem_top (⟨s,hs⟩:P.conjugateCore)) (mem_top (⟨r,hrA.1⟩:P.conjugateCore))))
    exact (le_sup_right : zpowers P.u ≤ P.E) he

end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
