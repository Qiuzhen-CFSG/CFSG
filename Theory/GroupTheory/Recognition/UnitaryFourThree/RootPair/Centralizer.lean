module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
public import Theory.GroupTheory.QuaternionCentralProductInvolutionCensus

/-!
# The full centralizer of the marked root four

The actual involution centralizer is transitive on the eighteen noncentral
involutions of its quaternion-product core. Orbit–stabilizer gives order 64
for the pointwise centralizer of the marked four. The already constructed
product R has this order and centralizes the four, hence equals its full
ambient centralizer. This is a literal application of the root-pair and
involution-census producers, with only the original IsType hypothesis.

Source: Aschbacher, *Sporadic Groups* (1994), Lemmas 45.2–45.3, pp. 242–243.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z : G}
namespace RootPair
variable (P : RootPair z)

private def coreInCentralizer : Subgroup (centralizer z) := (core z).subgroupOf (centralizer z)
private noncomputable def coreInCentralizerEquiv : coreInCentralizer (z:=z) ≃* core z :=
  subgroupOfEquivOfLe core_le_centralizer

omit [Finite G] in
private theorem coreInCentralizer_normal : (coreInCentralizer (z:=z)).Normal :=
  (normal_subgroupOf_iff_le_normalizer core_le_centralizer).mpr
    CentralizerHypothesis.centralizer_normalizes_core

private theorem coreInCentralizer_not_mem_line (h : IsType z)
    (x : coreInCentralizer (z:=z)) (hx : x ∉ center (coreInCentralizer (z:=z))) :
    ((x : centralizer z) : G) ∉ zpowers z := by
  intro hh
  rw [← h.toCentralizerHypothesis.core_center] at hh
  obtain ⟨w,hw,he⟩ := hh
  apply hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  apply Subtype.ext
  change ((y : centralizer z) : G) * ((x : centralizer z) : G) =
    ((x : centralizer z) : G) * ((y : centralizer z) : G)
  change (w:G) = ((x : centralizer z) : G) at he
  rw [← he]
  exact congrArg Subtype.val (mem_center_iff.mp hw ⟨y,y.property⟩)

/-- The pointwise centralizer of the marked four has the order predicted by its eighteen-point orbit. -/
theorem centralizer_E_card (h : IsType z) :
    Nat.card (Subgroup.centralizer (P.E : Set G)) = 64 := by
  let H := centralizer z
  let Q := coreInCentralizer (z:=z)
  let : Q.Normal := coreInCentralizer_normal
  let U : Q := ⟨⟨P.u,core_le_centralizer P.mem_core⟩,P.mem_core⟩
  let d := h.toCentralizerHypothesis.coreData.map (coreInCentralizerEquiv (z:=z)).symm
  have hu : orderOf U = 2 :=
    (orderOf_coe U).symm.trans ((orderOf_coe (U:H)).symm.trans (P.u_order h))
  have huZ : U ∉ center Q := by
    intro hh
    apply P.not_mem_line
    rw [← h.toCentralizerHypothesis.core_center]
    exact mem_map_of_mem (core z).subtype
      ((centerCongr (coreInCentralizerEquiv (z:=z)) ⟨U,hh⟩).property)
  have ht : ∀ x y : Q, orderOf x = 2 → x ∉ center Q →
      orderOf y = 2 → y ∉ center Q → IsConj (x:H) (y:H) := by
    intro x y hx hxZ hy hyZ
    obtain ⟨k,hk,he⟩ := h.toCentralizerHypothesis.core_involution_orbit
      ((x:H):G) ((y:H):G) x.property y.property
      ((orderOf_coe (x:H)).trans ((orderOf_coe x).trans hx))
      ((orderOf_coe (y:H)).trans ((orderOf_coe y).trans hy))
      (coreInCentralizer_not_mem_line h x hxZ) (coreInCentralizer_not_mem_line h y hyZ)
    exact isConj_iff.mpr ⟨⟨k,map_subtype_le _ hk⟩,Subtype.ext he⟩
  have he := QuaternionCentralProductData.card_centralizer_mul_eighteen_of_transitive
    Q d ht U hu huZ
  rw [h.centralizer_card] at he
  change Nat.card (Subgroup.centralizer ({(U:H)} : Set H)) * 18 = 1152 at he
  have hc : Nat.card (Subgroup.centralizer ({(U:H)} : Set H)) = 64 := by omega
  let f : Subgroup.centralizer (P.E : Set G) ≃
      Subgroup.centralizer ({(U:H)} : Set H) :=
    { toFun := fun x => ⟨⟨x,((P.centralizer_E_eq).le x.property).1⟩,
        mem_centralizer_singleton_iff.mpr (Subtype.ext
          (mem_centralizer_singleton_iff.mp ((P.centralizer_E_eq).le x.property).2))⟩
      invFun := fun x => ⟨x.val,(P.centralizer_E_eq).ge ⟨x.val.property,
        mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr f).trans hc

/-- The source product is the entire ambient centralizer of the marked four. -/
theorem R_eq_centralizer_E (h : IsType z) : P.R = Subgroup.centralizer (P.E : Set G) := by
  apply eq_of_le_of_card_ge
  · rw [P.centralizer_E_eq]
    exact P.R_le_double_centralizer
  · rw [P.R_card h,P.centralizer_E_card h]

end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
