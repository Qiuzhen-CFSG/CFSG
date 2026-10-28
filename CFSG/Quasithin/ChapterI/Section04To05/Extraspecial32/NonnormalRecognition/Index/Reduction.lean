module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Definitions

/-!
# Reduction of the A₈ overgroup index to marked centralizer calculations

Odd index puts every ambient involution into L up to conjugacy. The two
internal involution classes, once proved to stay distinct in G, therefore
control their ambient fusion. If both full centralizers lie in L, Thompson's
order formula forces L = G. Otherwise the marked second centralizer must be
identified with its A₉ counterpart. An explicit equivalence of mixed-pair
fibers transports its count, while the first count is already computed in L.
The model counts 156 and 555 and centralizer orders 192 and 480 then give
|G| = 181440 and |G:L| = 9.

The final theorems here are conditional reductions. Existence of
`Index.InvolutionData`, `Index.SecondCentralizerData` in the proper case, and
`Index.ModelCounts` remains to be proved from the source and actual models.
They do not yet establish the unconditional index alternative or I.4.6.

Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38. The pair-count argument replaces the strong-embedding exclusion;
the residual-centralizer recognition remains an explicit prerequisite.
-/

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index

open Subgroup Equiv Equiv.Perm
open Theory.GroupTheory.TwoInvolutionClassOrder

public theorem z8_order : orderOf z8 = 2 := orderOf_eq_prime (by decide) (by decide)
public theorem t8_order : orderOf t8 = 2 := orderOf_eq_prime (by decide) (by decide)
public theorem z9_order : orderOf z9 = 2 := orderOf_eq_prime (by decide) (by decide)
public theorem t9_order : orderOf t9 = 2 := orderOf_eq_prime (by decide) (by decide)

public theorem z9_not_conjugate_t9 : ¬ IsConj z9 t9 := by
  intro h
  have he := Equiv.Perm.isConj_iff_cycleType_eq.mp
    ((alternatingGroup (Fin 9)).subtype.map_isConj h)
  have hn : (z9 : Perm (Fin 9)).cycleType ≠ (t9 : Perm (Fin 9)).cycleType := by decide
  exact hn he

variable {G : Type*} [Group G]

private theorem isConj_order {a b : G} (h : IsConj a b) : orderOf a = orderOf b := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact ((MulAut.conj g).orderOf_eq a).symm

private theorem isConj_map_iff {H : Type*} [Group H] (e : G ≃* H) (a b : G) :
    IsConj (e a) (e b) ↔ IsConj a b := by
  constructor
  · intro h
    simpa only [MulEquiv.coe_toMonoidHom, e.symm_apply_apply] using e.symm.toMonoidHom.map_isConj h
  · exact e.toMonoidHom.map_isConj

private theorem kappa_eq_card_fiber (z v u : G) :
    kappa z v u = Nat.card (Fiber z v u) := by
  simp only [kappa_def, Fiber, halfOrder_def]

private theorem kappa_map {H : Type*} [Group H] (e : G ≃* H) (z v u : G) :
    kappa z v u = kappa (e z) (e v) (e u) := by
  rw [kappa_eq_card_fiber, kappa_eq_card_fiber]
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (Equiv.prodCongr e.toEquiv e.toEquiv)
  intro p
  change (_ ∧ _ ∧ _) ↔
    (IsConj (e z) (e p.1) ∧ IsConj (e v) (e p.2) ∧ halfOrder (e p.1) (e p.2) = e u)
  rw [isConj_map_iff, isConj_map_iff, halfOrder_map, e.injective.eq_iff]

/-- Odd index guarantees an actual conjugate of every involution in L. -/
private theorem exists_conjugate_mem_of_odd_index [Finite G]
    (L : Subgroup G) (hL : Odd L.index) (u : G) (hu : orderOf u = 2) :
    ∃ g : G, g * u * g⁻¹ ∈ L := by
  let P : Sylow 2 L := Classical.choice inferInstance
  let R : Subgroup G := (P : Subgroup L).map L.subtype
  have hR : IsPGroup 2 R := P.isPGroup'.map L.subtype
  have hi : ¬ 2 ∣ R.index := by
    rw [show R.index = (P : Subgroup L).index * L.index from index_map_subtype _]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index hL.not_two_dvd_nat
  let S : Sylow 2 G := hR.toSylow hi
  have hS : (S : Subgroup G) ≤ L := map_subtype_le _
  have huP : IsPGroup 2 (zpowers u) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨T, huT⟩ := huP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  refine ⟨g, hS ?_⟩
  rw [← hg]
  exact ⟨u, huT (mem_zpowers u), rfl⟩

/-- The local intersection theorem already supplies the needed odd index. -/
public theorem odd_index [Finite G] {z : G} (h : Hypotheses z)
    (local_intersections : ∀ g : G, g * z * g⁻¹ ∈ coreInG z → g * z * g⁻¹ ≠ z →
      IntersectionData z g)
    (L : Subgroup G) (hCL : Centralizer z ≤ L) : Odd L.index := by
  obtain ⟨g, hgQ, hg⟩ := h.fused
  have ho := (local_intersections g hgQ hg).centralizer_odd_index
  apply Nat.not_even_iff_odd.mp
  intro he
  exact ho.not_two_dvd_nat ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hCL))

namespace InvolutionData
variable {z : G} {L : Subgroup G} (d : InvolutionData z L)

public theorem t_order : orderOf d.t = 2 :=
  (d.equiv.symm.orderOf_eq t8).trans t8_order

public theorem t_ambient_order : orderOf (d.t : G) = 2 :=
  (Subgroup.orderOf_coe d.t).trans d.t_order

/-- The two internal classes and their ambient separation prove fusion control. -/
public theorem controls_z (hz : orderOf z = 2) (a : L) :
    IsConj (⟨z, d.z_mem⟩ : L) a ↔ IsConj z (a : G) := by
  constructor
  · exact L.subtype.map_isConj
  · intro ha
    have ha2 : orderOf a = 2 :=
      (Subgroup.orderOf_coe a).symm.trans ((isConj_order ha).symm.trans hz)
    rcases d.classes a ha2 with h | h
    · exact h
    · exact (d.not_conjugate (ha.trans (L.subtype.map_isConj h).symm)).elim

public theorem controls_t (a : L) : IsConj d.t a ↔ IsConj (d.t : G) (a : G) := by
  constructor
  · exact L.subtype.map_isConj
  · intro ha
    have ha2 : orderOf a = 2 := (Subgroup.orderOf_coe a).symm.trans
      ((isConj_order ha).symm.trans d.t_ambient_order)
    rcases d.classes a ha2 with h | h
    · exact (d.not_conjugate ((L.subtype.map_isConj h).trans ha.symm)).elim
    · exact h

/-- The internal classification covers all ambient involutions by odd index. -/
public theorem ambient_classes [Finite G] (hL : Odd L.index) (u : G) (hu : orderOf u = 2) :
    IsConj z u ∨ IsConj (d.t : G) u := by
  obtain ⟨g, hg⟩ := exists_conjugate_mem_of_odd_index L hL u hu
  let a : L := ⟨g * u * g⁻¹, hg⟩
  have hc : IsConj u (a : G) := isConj_iff.mpr ⟨g, rfl⟩
  have ha : orderOf a = 2 :=
    (Subgroup.orderOf_coe a).symm.trans ((isConj_order hc).symm.trans hu)
  rcases d.classes a ha with h | h
  · exact Or.inl ((L.subtype.map_isConj h).trans hc.symm)
  · exact Or.inr ((L.subtype.map_isConj h).trans hc.symm)

/-- Full containment of the second centralizer forces L = G by pair counting.
This replaces the source's strong-embedding exclusion at this step. -/
public theorem eq_top_of_second_centralizer_le [Finite G]
    (hz : orderOf z = 2) (hL : Odd L.index)
    (hCL : Centralizer z ≤ L) (hK : d.K ≤ L) : L = ⊤ :=
  eq_top_of_centralizers_le L z d.t hz d.t_ambient_order d.not_conjugate
    (d.ambient_classes hL) d.z_mem d.t.property hCL hK (d.controls_z hz) d.controls_t

public theorem second_centralizer_not_le [Finite G]
    (hz : orderOf z = 2) (hL : Odd L.index)
    (hCL : Centralizer z ≤ L) (hproper : L ≠ ⊤) : ¬ d.K ≤ L :=
  fun hK => hproper (d.eq_top_of_second_centralizer_le hz hL hCL hK)

/-- Restriction to L and its marked equivalence identify the first pair count. -/
public theorem first_count_eq [Finite G] (hz : orderOf z = 2)
    (hCL : Centralizer z ≤ L) : kappa z (d.t : G) z = kappa z8 t8 z8 := by
  rw [← kappa_subgroup_eq L (⟨z, d.z_mem⟩ : L) d.t (⟨z, d.z_mem⟩ : L)
    hz d.t_ambient_order d.not_conjugate hCL (d.controls_z hz) d.controls_t]
  have hm := kappa_map d.equiv (⟨z, d.z_mem⟩ : L) d.t (⟨z, d.z_mem⟩ : L)
  simpa only [d.z_image, t, d.equiv.apply_symm_apply] using hm

end InvolutionData

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index

namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index

open Subgroup
open Theory.GroupTheory.TwoInvolutionClassOrder

variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

private noncomputable def mapFiber {z v u : G} {z' v' u' : H}
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (e : Centralizer u ≃* Centralizer u')
    (he : e (distinguished u) = distinguished u')
    (hfz : ∀ a : Centralizer u, IsConj z (a : G) ↔ IsConj z' (e a : H))
    (hfv : ∀ a : Centralizer u, IsConj v (a : G) ↔ IsConj v' (e a : H))
    (p : Fiber z v u) : Fiber z' v' u' := by
  have hm := fiber_mem_centralizer hz hv hn p
  let a : Centralizer u := ⟨p.val.1, hm.1⟩
  let b : Centralizer u := ⟨p.val.2, hm.2⟩
  have hab : halfOrder a b = distinguished u :=
    Subtype.ext ((halfOrder_coe (Centralizer u) a b).trans p.property.2.2)
  refine ⟨((e a : H), (e b : H)), (hfz a).mp p.property.1,
    (hfv b).mp p.property.2.1, ?_⟩
  calc
    halfOrder (e a : H) (e b : H) = (↑(halfOrder (e a) (e b)) : H) :=
      (halfOrder_coe (Centralizer u') (e a) (e b)).symm
    _ = (e (halfOrder a b) : H) := congrArg Subtype.val (halfOrder_map e a b)
    _ = u' := by rw [hab, he]; rfl

private noncomputable def fiberCentralizerEquiv {z v u : G} {z' v' u' : H}
    (hz : orderOf z = 2) (hv : orderOf v = 2) (hn : ¬ IsConj z v)
    (hz' : orderOf z' = 2) (hv' : orderOf v' = 2) (hn' : ¬ IsConj z' v')
    (e : Centralizer u ≃* Centralizer u')
    (he : e (distinguished u) = distinguished u')
    (hfz : ∀ a : Centralizer u, IsConj z (a : G) ↔ IsConj z' (e a : H))
    (hfv : ∀ a : Centralizer u, IsConj v (a : G) ↔ IsConj v' (e a : H)) :
    Fiber z v u ≃ Fiber z' v' u' where
  toFun := mapFiber hz hv hn e he hfz hfv
  invFun := mapFiber hz' hv' hn' e.symm (e.symm_apply_eq.mpr he.symm)
    (fun a => by simpa only [e.apply_symm_apply] using (hfz (e.symm a)).symm)
    (fun a => by simpa only [e.apply_symm_apply] using (hfv (e.symm a)).symm)
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val (e.symm_apply_apply _))
      (congrArg Subtype.val (e.symm_apply_apply _))
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext (congrArg Subtype.val (e.apply_symm_apply _))
      (congrArg Subtype.val (e.apply_symm_apply _))

namespace SecondCentralizerData
variable {z : G} {L : Subgroup G} {d : InvolutionData z L} (c : SecondCentralizerData d)

/-- A comparison of the actual centralizers and ambient classes identifies
Thompson's fibers, including the half-order power equation. -/
public noncomputable def pairEquiv (hz : orderOf z = 2) :
    Fiber z (d.t : G) (d.t : G) ≃ Fiber z9 t9 t9 :=
  fiberCentralizerEquiv hz d.t_ambient_order d.not_conjugate
    z9_order t9_order z9_not_conjugate_t9 c.equiv c.involution_image c.z_fusion c.t_fusion

include c in
public theorem count_eq (hz : orderOf z = 2) :
    kappa z (d.t : G) (d.t : G) = kappa z9 t9 t9 := by
  rw [kappa_eq_card_fiber, kappa_eq_card_fiber]
  exact Nat.card_congr (c.pairEquiv hz)

omit [Finite G] in
include c in
public theorem centralizer_card_eq : Nat.card d.K = Nat.card (Centralizer t9) :=
  Nat.card_congr c.equiv.toEquiv

end SecondCentralizerData

/-- The literal centralizer comparisons determine the ambient order by
Thompson's formula. Every local and finite-model premise remains explicit. -/
public theorem card_of_centralizer_comparison {z : G} (h : Hypotheses z)
    {L : Subgroup G} (d : InvolutionData z L) (hL : Odd L.index)
    (hCL : Centralizer z ≤ L) (c : SecondCentralizerData d) (counts : ModelCounts) :
    Nat.card G = 181440 := by
  have hc := card_eq z (d.t : G) h.involution d.t_ambient_order d.not_conjugate
    (d.ambient_classes hL)
  rw [d.first_count_eq h.involution hCL, c.count_eq h.involution,
    show Nat.card (Centralizer (d.t : G)) = 480 from
      c.centralizer_card_eq.trans counts.nine_centralizer,
    h.centralizer_card, counts.eight_z, counts.nine_t] at hc
  exact hc

/-- The calculated ambient order gives index nine in the actual A₈ subgroup. -/
public theorem index_nine_of_centralizer_comparison {z : G} (h : Hypotheses z)
    {L : Subgroup G} (d : InvolutionData z L) (hL : Odd L.index)
    (hCL : Centralizer z ≤ L) (c : SecondCentralizerData d) (counts : ModelCounts) :
    L.index = 9 := by
  have hcard := card_of_centralizer_comparison h d hL hCL c counts
  have hLcard : Nat.card L = 20160 := by
    rw [Nat.card_congr d.equiv.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hm := L.card_mul_index
  rw [hLcard, hcard] at hm
  omega

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
