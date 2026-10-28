module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.Centralizer
public import Theory.ElementaryAbelian.ExtraspecialNormalCommutator
public import Theory.GroupTheory.SpecificGroups.KleinFourFullAction
public import Theory.GroupTheory.SymmetricThreeGeneration

/-!
# The actual symmetric action on the root four

The two marked extraspecial cores normalize E and provide its two different
transpositions. Their actions do not commute, so generate all Aut(E)=S₃.
The kernel is exactly the already identified product R=C_G(E). Consequently
N_G(E) has order 384, equals the join of the two original cores, and its literal
quotient by R is S₃. The quotient equivalence retains the actual conjugation
action; no normalizer recognition premise is introduced.

Source: Aschbacher, *Sporadic Groups* (1994), Lemmas 8.15(1),(5) and 45.3(1),
printed pp. 29–30 and 242–243.
-/

@[expose] public section
open Subgroup
private theorem kleinFour_action_surjective_of_noncommuting
    {A V : Type*} [Group A] [Group V] [IsKleinFour V]
    (f : A →* MulAut V) (a b : A) (hab : f a * f b ≠ f b * f a) :
    Function.Surjective f := by
  let e := IsKleinFour.autEquivPermThree V
  let φ := e.toMonoidHom.comp f
  have hnc : ⁅φ.range,φ.range⁆ ≠ ⊥ := by
    intro hc
    have hle := commutator_eq_bot_iff_le_centralizer.mp hc
    have he := hle (show φ a ∈ φ.range from ⟨a,rfl⟩) (φ b) ⟨b,rfl⟩
    apply hab
    apply e.injective
    simpa only [map_mul,φ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom] using he.symm
  have ht := sup_eq_top_of_symmetricThree_commutator_ne_bot φ.range φ.range hnc
  rw [sup_idem] at ht
  have hf := MonoidHom.range_eq_top.mp ht
  intro k
  obtain ⟨a,ha⟩ := hf (e k)
  exact ⟨a,e.injective ha⟩

namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace RootPair
variable (P : RootPair z)

def N : Subgroup G := normalizer (P.E : Set G)

omit [Finite G] in
theorem E_kleinFour (h : IsType z) : IsKleinFour P.E := by
  have he : P.E = closure ({z,P.u} : Set G) := by
    rw [E,zpowers_eq_closure,zpowers_eq_closure,← Subgroup.closure_union]
    congr 1
  rw [he]
  exact isKleinFour_closure_pair_of_orderOf z P.u h.involution (P.u_order h)
    P.u_ne_z.symm P.commute

theorem core_le_N (h : IsType z) : core z ≤ P.N := by
  let : IsExtraspecial 2 (core z) := h.toCentralizerHypothesis.core_extraspecial
  apply extraspecial_le_normalizer_of_center_le (core z) P.E (P.E_le_core h)
  intro x hx
  have hxline : (x:G) ∈ zpowers z := h.toCentralizerHypothesis.core_center ▸
    mem_map_of_mem (core z).subtype hx
  exact (le_sup_left : zpowers z ≤ P.E) hxline

theorem conjugateCore_le_N (h : IsType z) : P.conjugateCore ≤ P.N := by
  let : IsExtraspecial 2 P.conjugateCore := P.conjugateCore_extraspecial h
  apply extraspecial_le_normalizer_of_center_le P.conjugateCore P.E (P.E_le_conjugateCore h)
  intro x hx
  have hxline : (x:G) ∈ zpowers P.u := P.conjugateCore_center h ▸
    mem_map_of_mem P.conjugateCore.subtype hx
  exact (le_sup_right : zpowers P.u ≤ P.E) hxline

/-- The two original cores induce distinct transpositions on the marked four. -/
theorem exists_center_transpositions (h : IsType z) :
    ∃ a ∈ core z, ∃ b ∈ P.conjugateCore,
      a*z*a⁻¹=z ∧ a*P.u*a⁻¹=z*P.u ∧
      b*z*b⁻¹=z*P.u ∧ b*P.u*b⁻¹=P.u := by
  let Q := core z
  let Z : Q := ⟨z,z_mem_core h⟩
  let U : Q := ⟨P.u,P.mem_core⟩
  let : IsExtraspecial 2 Q := h.toCentralizerHypothesis.core_extraspecial
  have hUZ : U ∉ center Q := by
    intro hh
    apply P.not_mem_line
    rw [← h.toCentralizerHypothesis.core_center]
    exact mem_map_of_mem Q.subtype hh
  have hZZ : Z ∈ center Q := mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (core_le_centralizer x.property)))
  have hc := IsExtraspecial.isConj_of_center_quotient_eq (x:=U) (y:=Z*U) hUZ
    (by rw [map_mul,(show QuotientGroup.mk' (center Q) Z = 1 from (QuotientGroup.eq_one_iff Z).mpr hZZ),one_mul])
  obtain ⟨a,ha⟩ := isConj_iff.mp hc
  let Q' := P.conjugateCore
  let Z' : Q' := ⟨z,P.z_mem_conjugateCore h⟩
  let U' : Q' := ⟨P.u,P.u_mem_conjugateCore h⟩
  let : IsExtraspecial 2 Q' := P.conjugateCore_extraspecial h
  have hZ' : Z' ∉ center Q' := by
    intro hh
    have hm : z ∈ zpowers P.u := P.conjugateCore_center h ▸ mem_map_of_mem Q'.subtype hh
    have hle : P.E ≤ zpowers P.u := sup_le (zpowers_le.mpr hm) le_rfl
    have he := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
    rw [P.E_card h,Nat.card_zpowers,P.u_order h] at he
    omega
  have hU' : U' ∈ center Q' := mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (P.conjugateCore_le x.property)))
  have hc' := IsExtraspecial.isConj_of_center_quotient_eq (x:=Z') (y:=U'*Z') hZ'
    (by rw [map_mul,(show QuotientGroup.mk' (center Q') U' = 1 from (QuotientGroup.eq_one_iff U').mpr hU'),one_mul])
  obtain ⟨b,hb⟩ := isConj_iff.mp hc'
  refine ⟨a,a.property,b,b.property,?_,congrArg Subtype.val ha,?_,?_⟩
  · rw [mem_centralizer_singleton_iff.mp (core_le_centralizer a.property),mul_inv_cancel_right]
  · exact (congrArg Subtype.val hb).trans P.commute.symm.eq
  · rw [mem_centralizer_singleton_iff.mp (P.conjugateCore_le b.property),mul_inv_cancel_right]

def centerAction : P.N →* MulAut P.E := P.E.normalizerMonoidHom

omit [Finite G] in
private theorem centerAction_apply (a : P.N) (v : P.E) :
    (P.centerAction a v : G) = (a:G)*v*(a:G)⁻¹ := rfl

/-- Noncommuting actors are supplied by the two original cores. -/
theorem exists_noncommuting_core_actors (h : IsType z) :
    ∃ A B : P.N, (A:G) ∈ core z ∧ (B:G) ∈ P.conjugateCore ∧
      P.centerAction A * P.centerAction B ≠ P.centerAction B * P.centerAction A := by
  obtain ⟨a,ha,b,hb,haz,hau,hbz,hbu⟩ := P.exists_center_transpositions h
  let A : P.N := ⟨a,P.core_le_N h ha⟩
  let B : P.N := ⟨b,P.conjugateCore_le_N h hb⟩
  have hab : P.centerAction A * P.centerAction B ≠ P.centerAction B * P.centerAction A := by
    intro he
    have hz := congrArg (fun k : MulAut P.E => (k ⟨z,P.z_mem_E⟩ : G)) he
    change a*(b*z*b⁻¹)*a⁻¹ = b*(a*z*a⁻¹)*b⁻¹ at hz
    rw [hbz,haz] at hz
    have hh : a*(z*P.u)*a⁻¹ = z*(z*P.u) := by
      change MulAut.conj a (z*P.u) = z*(z*P.u)
      rw [map_mul]
      exact congrArg₂ (· * ·) haz hau
    have hzsq : z^2=1 := h.involution ▸ pow_orderOf_eq_one z
    rw [hh,← mul_assoc,← pow_two,hzsq,one_mul,hbz] at hz
    have hz1 : z = 1 := mul_right_cancel (hz.symm.trans (one_mul P.u).symm)
    have hz2 := h.involution
    simp [hz1] at hz2
  exact ⟨A,B,ha,hb,hab⟩

/-- The actual conjugation action on the root four is the full S₃ action. -/
theorem centerAction_surjective (h : IsType z) : Function.Surjective P.centerAction := by
  let : IsKleinFour P.E := P.E_kleinFour h
  obtain ⟨a,b,_,_,hab⟩ := P.exists_noncommuting_core_actors h
  exact kleinFour_action_surjective_of_noncommuting P.centerAction a b hab

theorem centerAction_kernel (h : IsType z) : P.centerAction.ker = P.R.subgroupOf P.N := by
  change P.E.normalizerMonoidHom.ker = _
  rw [normalizerMonoidHom_ker,← P.R_eq_centralizer_E h]
  rfl

theorem N_card (h : IsType z) : Nat.card P.N = 384 := by
  let : IsKleinFour P.E := P.E_kleinFour h
  have hRN : P.R ≤ P.N := by
    change P.R ≤ normalizer (P.E : Set G)
    rw [P.R_eq_centralizer_E h]
    exact Subgroup.centralizer_le_normalizer (P.E : Set G)
  have hc := P.centerAction.ker.card_mul_index
  rw [index_ker,P.centerAction_kernel h,Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv,
    P.R_card h,MonoidHom.range_eq_top.mpr (P.centerAction_surjective h),
    Nat.card_congr (topEquiv : (⊤ : Subgroup (MulAut P.E)) ≃* MulAut P.E).toEquiv,
    IsKleinFour.card_mulAut] at hc
  exact hc.symm

/-- The whole four-group normalizer is generated by the two actual extraspecial cores. -/
theorem N_eq_core_join (h : IsType z) : P.N = core z ⊔ P.conjugateCore := by
  let J := core z ⊔ P.conjugateCore
  have hJN : J ≤ P.N := sup_le (P.core_le_N h) (P.conjugateCore_le_N h)
  let f := P.centerAction.comp (inclusion hJN)
  have hf : Function.Surjective f := by
    let : IsKleinFour P.E := P.E_kleinFour h
    obtain ⟨a,b,ha,hb,hab⟩ := P.exists_noncommuting_core_actors h
    let A : J := ⟨a,(le_sup_left : core z ≤ J) ha⟩
    let B : J := ⟨b,(le_sup_right : P.conjugateCore ≤ J) hb⟩
    apply kleinFour_action_surjective_of_noncommuting f A B
    exact hab
  apply le_antisymm ?_ hJN
  intro n hn
  obtain ⟨j,hj⟩ := hf (P.centerAction ⟨n,hn⟩)
  have hk : (⟨n,hn⟩:P.N) * (inclusion hJN j)⁻¹ ∈ P.centerAction.ker := by
    change P.centerAction _ = 1
    rw [map_mul,map_inv,← hj]
    exact mul_inv_cancel _
  rw [P.centerAction_kernel h] at hk
  have hRJ : P.R ≤ J := sup_le (inf_le_left.trans le_sup_left)
    (inf_le_left.trans le_sup_right)
  have hm := J.mul_mem (hRJ hk) j.property
  change (n*(j:G)⁻¹)*(j:G) ∈ J at hm
  simpa only [inv_mul_cancel_right] using hm

theorem R_normal_in_N (h : IsType z) : (P.R.subgroupOf P.N).Normal := by
  rw [← P.centerAction_kernel h]
  infer_instance

/-- The literal quotient by the source root product is S₃. -/
noncomputable def normalizerQuotientEquiv (h : IsType z) :
    letI := P.R_normal_in_N h
    (P.N ⧸ P.R.subgroupOf P.N) ≃* Equiv.Perm (Fin 3) := by
  letI := P.R_normal_in_N h
  letI := P.E_kleinFour h
  exact (QuotientGroup.quotientMulEquivOfEq (P.centerAction_kernel h).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective P.centerAction
      (P.centerAction_surjective h)).trans (IsKleinFour.autEquivPermThree P.E))

end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
