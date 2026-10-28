module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.Seed
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic.Group
import Mathlib.Tactic.IntervalCases

/-!
# The literal centralizer and involutory splitting at the marked J₂ vertex

Let X be the published order-three marking, C its full centralizer, and M
its full normalizer. The standard ATLAS involution a inverts the commutator
word defining X. Since an automorphism of X either fixes or inverts its
generator, every element of M has a unique form c or ca. This constructs
the actual semidirect product, retaining inclusions and conjugation.

The quotient maps use X.subgroupOf C and X.subgroupOf M. X is central
in C, and the explicit inverting involution proves that X is not central
in M. The only numerical hypothesis used below is the permitted |M|=2160.
Identifying the central quotient with A₆ and the full quotient with
PGL₂(9), and proving perfectness of C, are separate structural obligations.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3(1) and 47.10,
pp.261–267. The marking is the retained ATLAS degree-100 carrier.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension
open Subgroup GeneratorPair
open scoped Pointwise

/-- The full centralizer of the fixed vertex subgroup. -/
def C : Subgroup Carrier := centralizer (X : Set Carrier)

/-- The literal distinguished subgroups in the two numerators. -/
abbrev XC : Subgroup C := X.subgroupOf C
abbrev XM : Subgroup M := X.subgroupOf M
abbrev CM : Subgroup M := C.subgroupOf M

theorem C_le_M : C ≤ M := centralizer_le_normalizer _

theorem mem_C_iff (g : Carrier) : g ∈ C ↔ g * x = x * g := by
  constructor
  · intro hg
    exact (hg x (mem_zpowers x)).symm
  · intro hg y hy
    obtain ⟨n, rfl⟩ := hy
    exact ((show Commute g x from hg).zpow_right n).eq.symm

theorem X_le_C : X ≤ C := by
  apply zpowers_le.mpr
  exact (mem_C_iff x).mpr rfl

theorem XC_le_center : XC ≤ center C := by
  intro z hz
  apply mem_center_iff.mpr
  intro c
  exact Subtype.ext (c.property z hz).symm

instance XC_normal : XC.Normal :=
  (normal_subgroupOf_iff_le_normalizer X_le_C).mpr C_le_M

instance XM_normal : XM.Normal := inferInstanceAs (X.subgroupOf (normalizer (X : Set Carrier))).Normal

instance CM_normal : CM.Normal :=
  normal_subgroupOf_centralizer_normalizer (X : Set Carrier)

/-- The central and full vertex quotients use the actual marked subgroup. -/
abbrev CentralQuotient := C ⧸ XC
abbrev VertexQuotient := M ⧸ XM

def centralQuotientMap : C →* CentralQuotient := QuotientGroup.mk' XC

def vertexQuotientMap : M →* VertexQuotient := QuotientGroup.mk' XM

theorem centralQuotientMap_ker : centralQuotientMap.ker = XC := QuotientGroup.ker_mk' XC

theorem vertexQuotientMap_ker : vertexQuotientMap.ker = XM := QuotientGroup.ker_mk' XM

/-- The literal inclusion of the centralizer into the normalizer. -/
def centralInclusion : C →* M := Subgroup.inclusion C_le_M

/-- The compatible inclusion of the two quotients. -/
def quotientInclusion : CentralQuotient →* VertexQuotient :=
  QuotientGroup.quotientMapSubgroupOfOfLe (le_refl X) C_le_M

theorem quotientInclusion_mk (c : C) :
    quotientInclusion (centralQuotientMap c) = vertexQuotientMap (centralInclusion c) := rfl

theorem quotientInclusion_injective : Function.Injective quotientInclusion := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro q hq
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective XC q
  have h : centralInclusion c ∈ XM :=
    (QuotientGroup.eq_one_iff _).mp hq
  exact (QuotientGroup.eq_one_iff _).mpr h

/-- The marked involution is the first standard ATLAS generator itself. -/
def splitter : Carrier := a

theorem splitter_square : splitter ^ 2 = 1 := a_pow_two

theorem splitter_inv : splitter⁻¹ = splitter := by
  exact inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using splitter_square)

theorem splitter_inverts_x : splitter * x * splitter⁻¹ = x⁻¹ := by
  have ha : a⁻¹ = a := splitter_inv
  have ha2 : a * a = 1 := by simpa only [pow_two] using a_pow_two
  have hw : MulAut.conj a (a * b * a * b⁻¹) = (a * b * a * b⁻¹)⁻¹ := by
    change a * (a * b * a * b⁻¹) * a⁻¹ = _
    simp only [mul_inv_rev, inv_inv, ha]
    simp only [← mul_assoc, ha2, one_mul]
  change MulAut.conj a ((a * b * a * b⁻¹) ^ 4) = ((a * b * a * b⁻¹) ^ 4)⁻¹
  rw [map_pow, hw, inv_pow]

theorem x_square : x ^ 2 = x⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [← pow_succ] using x_cube

theorem x_inv_ne_x : x⁻¹ ≠ x := by
  intro h
  have h2 : x ^ 2 = 1 := by
    calc
      x ^ 2 = x * x := pow_two x
      _ = x * x⁻¹ := congrArg (x * ·) h.symm
      _ = 1 := mul_inv_cancel x
  have hd := orderOf_dvd_of_pow_eq_one h2
  rw [orderOf_x] at hd
  norm_num at hd

theorem mem_X_iff (g : Carrier) : g ∈ X ↔ g = 1 ∨ g = x ∨ g = x⁻¹ := by
  classical
  change g ∈ zpowers x ↔ _
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_x]
  constructor
  · rintro hg
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hg
    have hi' := Finset.mem_range.mp hi
    interval_cases i <;> simp [x_square]
  · rintro (rfl | rfl | rfl)
    · exact Finset.mem_image.mpr ⟨0, by decide, pow_zero x⟩
    · exact Finset.mem_image.mpr ⟨1, by decide, pow_one x⟩
    · exact Finset.mem_image.mpr ⟨2, by decide, x_square⟩

/-- Inverting the literal generator is sufficient for membership in M. -/
theorem mem_M_of_inverts (g : Carrier) (hg : g * x * g⁻¹ = x⁻¹) : g ∈ M := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (zpowers x).map (MulAut.conj g).toMonoidHom = zpowers x
  rw [MonoidHom.map_zpowers]
  change zpowers (g * x * g⁻¹) = zpowers x
  rw [hg, zpowers_inv]

theorem splitter_mem_M : splitter ∈ M := mem_M_of_inverts splitter splitter_inverts_x

theorem splitter_not_mem_C : splitter ∉ C := by
  intro h
  have hc := (mem_C_iff splitter).mp h
  apply x_inv_ne_x
  rw [← splitter_inverts_x, hc, mul_assoc, mul_inv_cancel, mul_one]

theorem splitter_ne_one : splitter ≠ 1 := by
  intro h
  exact splitter_not_mem_C (h ▸ C.one_mem)

theorem orderOf_splitter : orderOf splitter = 2 :=
  orderOf_eq_prime splitter_square splitter_ne_one

/-- The same explicit element viewed in the literal normalizer. -/
def splitterM : M := ⟨splitter, splitter_mem_M⟩

theorem orderOf_splitterM : orderOf splitterM = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact orderOf_splitter

/-- Every normalizer element centralizes or inverts the marked generator. -/
theorem normalizer_action_cases (m : M) :
    (m : Carrier) * x * (m : Carrier)⁻¹ = x ∨
      (m : Carrier) * x * (m : Carrier)⁻¹ = x⁻¹ := by
  have hm : (m : Carrier) * x * (m : Carrier)⁻¹ ∈ X :=
    (mem_normalizer_iff.mp m.property x).mp (mem_zpowers x)
  rcases (mem_X_iff _).mp hm with h | h | h
  · have h' : MulAut.conj (m : Carrier) x = MulAut.conj (m : Carrier) 1 := by simpa using h
    exact (x_ne_one ((MulAut.conj (m : Carrier)).injective h')).elim
  · exact Or.inl h
  · exact Or.inr h

/-- A concrete two-coset normal form, without an order hypothesis. -/
theorem normal_form (m : M) :
    ∃ c : C, (m : Carrier) = c ∨ (m : Carrier) = (c : Carrier) * splitter := by
  rcases normalizer_action_cases m with hc | hi
  · have hmc : (m : Carrier) ∈ C := (mem_C_iff _).mpr ((mul_inv_eq_iff_eq_mul).mp hc)
    exact ⟨⟨m, hmc⟩, Or.inl rfl⟩
  · have hcs : (m : Carrier) * splitter ∈ C := by
      apply (mem_C_iff _).mpr
      apply (mul_inv_eq_iff_eq_mul).mp
      calc
        ((m : Carrier) * splitter) * x * ((m : Carrier) * splitter)⁻¹ =
            (m : Carrier) * (splitter * x * splitter⁻¹) * (m : Carrier)⁻¹ := by group
        _ = (m : Carrier) * x⁻¹ * (m : Carrier)⁻¹ := by rw [splitter_inverts_x]
        _ = ((m : Carrier) * x * (m : Carrier)⁻¹)⁻¹ := by group
        _ = x := by rw [hi, inv_inv]
    refine ⟨⟨(m : Carrier) * splitter, hcs⟩, Or.inr ?_⟩
    change (m : Carrier) = ((m : Carrier) * splitter) * splitter
    rw [mul_assoc, ← pow_two, splitter_square, mul_one]

/-- The actual involutory subgroup inside M. -/
def S : Subgroup M := zpowers splitterM

theorem card_S : Nat.card S = 2 := by
  rw [S, Nat.card_zpowers, orderOf_splitterM]

theorem mem_S_iff (m : M) : m ∈ S ↔ m = 1 ∨ m = splitterM := by
  classical
  change m ∈ zpowers splitterM ↔ _
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_splitterM]
  constructor
  · intro hm
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hm
    have hi' := Finset.mem_range.mp hi
    interval_cases i <;> simp
  · rintro (rfl | rfl)
    · exact Finset.mem_image.mpr ⟨0, by decide, pow_zero splitterM⟩
    · exact Finset.mem_image.mpr ⟨1, by decide, pow_one splitterM⟩

/-- The splitting is an actual complement of the literal centralizer. -/
theorem complement : CM.IsComplement' S := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · apply disjoint_def.mpr
    intro m hm hs
    rcases (mem_S_iff m).mp hs with h | rfl
    · exact h
    · exact (splitter_not_mem_C hm).elim
  · apply Set.eq_univ_iff_forall.mpr
    intro m
    obtain ⟨c, hc | hc⟩ := normal_form m
    · refine ⟨centralInclusion c, c.property, 1, S.one_mem, ?_⟩
      apply Subtype.ext
      change (c : Carrier) * 1 = (m : Carrier)
      exact (mul_one _).trans hc.symm
    · exact ⟨centralInclusion c, c.property, splitterM, mem_zpowers _, Subtype.ext hc.symm⟩

theorem C_sup_splitter : C ⊔ zpowers splitter = M := by
  apply le_antisymm (sup_le C_le_M (zpowers_le.mpr splitter_mem_M))
  intro m hm
  obtain ⟨c, hc | hc⟩ := normal_form ⟨m, hm⟩
  · change m = (c : Carrier) at hc
    rw [hc]
    exact mem_sup_left c.property
  · change m = (c : Carrier) * splitter at hc
    rw [hc]
    exact mul_mem (mem_sup_left c.property) (mem_sup_right (mem_zpowers splitter))

/-- Relative normality is only asserted inside M. -/
theorem M_le_normalizer_C : M ≤ normalizer (C : Set Carrier) :=
  (normal_subgroupOf_iff_le_normalizer C_le_M).mp CM_normal

/-- Conjugation by the literal complement on the literal centralizer. -/
def splitAction : S →* MulAut C :=
  C.normalizerMonoidHom.comp ((Subgroup.inclusion M_le_normalizer_C).comp S.subtype)

theorem splitAction_apply (s : S) (c : C) :
    ((splitAction s c : C) : Carrier) =
      ((s : M) : Carrier) * (c : Carrier) * ((s : M) : Carrier)⁻¹ := rfl

/-- The semidirect-product isomorphism retains the actual inclusion of C. -/
noncomputable def splitting : C ⋊[splitAction] S ≃* M := by
  let eC : CM ≃* C := subgroupOfEquivOfLe C_le_M
  let α : S →* MulAut CM :=
    CM.normalizerMonoidHom.comp (Subgroup.inclusion (CM.normalizer_eq_top ▸ le_top))
  let e : CM ⋊[α] S ≃* C ⋊[splitAction] S :=
    SemidirectProduct.congr eC (MulEquiv.refl S) (by intro s; ext c; rfl)
  exact e.symm.trans (SemidirectProduct.mulEquivSubgroup complement)

theorem splitting_apply (g : C ⋊[splitAction] S) :
    ((splitting g : M) : Carrier) = (g.left : Carrier) * ((g.right : M) : Carrier) := rfl

theorem splitting_inl (c : C) :
    splitting (SemidirectProduct.inl c) = centralInclusion c := by
  apply Subtype.ext
  rw [splitting_apply]
  exact mul_one _

theorem splitting_inr (s : S) :
    splitting (SemidirectProduct.inr s) = s := by
  apply Subtype.ext
  rw [splitting_apply]
  exact one_mul _

/-- The named outer actor is explicitly induced by the ATLAS involution. -/
def splitterAction : MulAut C := splitAction ⟨splitterM, mem_zpowers splitterM⟩

theorem splitterAction_apply (c : C) :
    ((splitterAction c : C) : Carrier) = splitter * (c : Carrier) * splitter⁻¹ := rfl

theorem splitterAction_square : splitterAction ^ 2 = 1 := by
  change splitAction (⟨splitterM, mem_zpowers splitterM⟩ : S) ^ 2 = 1
  rw [← map_pow]
  have h : (⟨splitterM, mem_zpowers splitterM⟩ : S) ^ 2 = 1 :=
    Subtype.ext (Subtype.ext splitter_square)
  rw [h, map_one]

/-- X cannot be central in M: its marked generator is inverted by a. -/
theorem XM_not_le_center : ¬ XM ≤ center M := by
  intro h
  have hx : (⟨x, X.le_normalizer (mem_zpowers x)⟩ : M) ∈ XM := mem_zpowers x
  have hc := congrArg (fun m : M => (m : Carrier))
    (mem_center_iff.mp (h hx) splitterM)
  exact splitter_not_mem_C ((mem_C_iff _).mpr hc)

theorem centralizer_index : CM.index = 2 :=
  complement.symm.index_eq_card.trans card_S

theorem card_C (hM : Nat.card M = 2160) : Nat.card C = 1080 := by
  have hc : Nat.card CM = Nat.card C := Nat.card_congr (subgroupOfEquivOfLe C_le_M).toEquiv
  have h := complement.card_mul_card
  rw [hc, card_S, hM] at h
  omega

theorem card_XC : Nat.card XC = 3 :=
  (Nat.card_congr (subgroupOfEquivOfLe X_le_C).toEquiv).trans card_X

theorem card_XM : Nat.card XM = 3 :=
  (Nat.card_congr (subgroupOfEquivOfLe X.le_normalizer).toEquiv).trans card_X

theorem card_CentralQuotient (hM : Nat.card M = 2160) : Nat.card CentralQuotient = 360 := by
  have h := XC.card_eq_card_quotient_mul_card_subgroup
  rw [card_C hM, card_XC] at h
  change 1080 = Nat.card CentralQuotient * 3 at h
  omega

theorem card_VertexQuotient (hM : Nat.card M = 2160) : Nat.card VertexQuotient = 720 := by
  have h := XM.card_eq_card_quotient_mul_card_subgroup
  rw [hM, card_XM] at h
  change 2160 = Nat.card VertexQuotient * 3 at h
  omega

end Sporadic.LeechRelated.J2.RecognitionGeometry.VertexExtension
