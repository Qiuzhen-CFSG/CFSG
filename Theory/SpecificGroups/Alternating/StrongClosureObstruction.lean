module

public import Theory.SpecificGroups.Alternating.MarkedInvolutionExtension.Sylow
public import Theory.SpecificGroups.SymmetricSix.StrongClosureObstruction
public import Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Alternating outer actions excluded by abelian strong closure

A subnormal A6 component with a Sylow-central transposition action, or an
A7 component with a Sylow-central triple-transposition action, cannot occur
in the presence of the marked abelian strongly closed subgroup. Construct
the actual symmetric extension from the given component equivalence and
original involution. Centralizer Sylow conjugacy places the fixed six-letter
fusion configuration in the original Sylow while keeping that involution.
The A7 case fixes the seventh letter and uses the same finite obstruction.

These are precisely the simple-component parts of the inspection of
Aschbacher--Smith, Lemma 1.1.5(3)(c),(d), in Proposition 2.2.2,
printed pp.519--520 (combined manuscript, 1 March 2004).
-/

public section
open Subgroup Equiv Equiv.Perm
open scoped IsMulCommutative
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels

namespace Theory.GroupTheory.AlternatingStrongClosure

section BorelCenter
local instance : Fintype S6 := fintypePerm
local instance : Fintype borel := Subtype.fintype _

private theorem borel_central (x : S6) (hx : x ∈ borel) :
    Commute x trans ∧ Commute x triple := by
  exact (by decide +kernel : ∀ x : borel,
    (x : S6) * trans = trans * x ∧ (x : S6) * triple = triple * x) ⟨x, hx⟩

end BorelCenter

private theorem borel_six_central_trans :
    (borelSylow : Subgroup S6) ≤ centralizer ({trans} : Set S6) := by
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (borel_central x hx).1.eq

private theorem borel_seven_card : Nat.card (borel.map liftSix) = 16 :=
  (card_map_of_injective liftSix_injective).trans borel_order

private noncomputable def sevenSylow : Sylow 2 S7 :=
  (borelSylow.isPGroup'.map liftSix).toSylow (by
    have h := (borel.map liftSix).card_mul_index
    have hcard : Nat.card S7 = 5040 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      decide
    rw [borel_seven_card, hcard] at h
    have hi : (borel.map liftSix).index = 315 := by omega
    change ¬2 ∣ (borel.map liftSix).index
    rw [hi]
    decide)

private theorem sevenSylow_coe : (sevenSylow : Subgroup S7) = borel.map liftSix := rfl

private theorem borel_seven_central_triple :
    (sevenSylow : Subgroup S7) ≤ centralizer ({liftSix triple} : Set S7) := by
  rintro _ ⟨x, hx, rfl⟩
  exact mem_centralizer_singleton_iff.mpr ((borel_central x hx).2.map liftSix).eq

private theorem false_of_configuration {G : Type*} [Group G] [Finite G]
    {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 G) (U L : Subgroup G)
    [IsMulCommutative U] (hU : IsStronglyClosedSet (U : Set G) (S : Subgroup G) ⊤)
    (hL : L.IsSubnormal) (e : L ≃* alternatingGroup (Fin n))
    (z : G) (hzU : z ∈ U) (hz2 : z ^ 2 = 1)
    (hzc : ∀ s ∈ (S : Subgroup G), Commute z s)
    (t : Perm (Fin n)) (ht : t.sign = -1) (ht2 : t ^ 2 = 1)
    (haction : ∀ a : alternatingGroup (Fin n),
      (e.symm (MulAut.conjNormal t a) : G) = z * (e.symm a : G) * z⁻¹)
    (i : S6 →* Perm (Fin n)) (hi : Function.Injective i)
    (m : S6) (hm : m = trans ∨ m = triple)
    (Q : Sylow 2 (Perm (Fin n))) (hQ : (Q : Subgroup _) = borel.map i)
    (hQc : (Q : Subgroup _) ≤ centralizer ({i m} : Set (Perm (Fin n))))
    (hclass : IsConj (i m) t) : False := by
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal L hL
  let j : alternatingGroup (Fin n) →* G := L.subtype.comp e.symm.toMonoidHom
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP'S : (P' : Subgroup _).map j ≤ (S : Subgroup G) := by
    rintro _ ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    change (e.symm (e x) : G) ∈ (S : Subgroup G)
    rw [e.symm_apply_apply]
    have hx' : x ∈ (S : Subgroup G).subgroupOf L := hP ▸ hx
    exact hx'
  obtain ⟨g, hg⟩ := isConj_iff.mp hclass
  let Q' := Q.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hQ'c : (Q' : Subgroup _) ≤ centralizer ({t} : Set (Perm (Fin n))) := by
    rintro _ ⟨x, hx, rfl⟩
    have hc : Commute x (i m) := mem_centralizer_singleton_iff.mp (hQc hx)
    have hh := hc.map (MulAut.conj g).toMonoidHom
    change Commute (g * x * g⁻¹) (g * i m * g⁻¹) at hh
    rw [hg] at hh
    exact mem_centralizer_singleton_iff.mpr hh.eq
  obtain ⟨F, hF, hFt, hFS⟩ := MarkedAlternatingExtension.exists_sylow_embedding hn
    (S : Subgroup G) S.isPGroup' j (L.subtype_injective.comp e.symm.injective)
    P' hP'S t ht ht2 z (hU.1 hzU) hz2 hzc haction Q' hQ'c
  let f := F.comp ((MulAut.conj g).toMonoidHom.comp i)
  have hf : Function.Injective f := hF.comp ((MulAut.conj g).injective.comp hi)
  have hB : borel.map f ≤ (S : Subgroup G) := by
    rintro _ ⟨x, hx, rfl⟩
    apply hFS
    apply mem_map_of_mem F
    apply mem_map_of_mem (MulAut.conj g).toMonoidHom
    rw [hQ]
    exact mem_map_of_mem i hx
  have hfm : f m ∈ U := by
    change F (g * i m * g⁻¹) ∈ U
    rw [hg, hFt]
    exact hzU
  rcases hm with rfl | rfl
  · exact false_of_transposition_embedding (S : Subgroup G) U hU f hf hB hfm
  · exact false_of_triple_embedding (S : Subgroup G) U hU f hf hB hfm

/-- The transposition row of a marked A6 component is incompatible with
the original abelian strongly closed subgroup and Sylow-central z. -/
theorem false_of_alternating_six_transposition {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (U L : Subgroup G) [IsMulCommutative U]
    (hU : IsStronglyClosedSet (U : Set G) (S : Subgroup G) ⊤)
    (hL : L.IsSubnormal) (e : L ≃* alternatingGroup (Fin 6))
    (z : G) (hzU : z ∈ U) (hz2 : z ^ 2 = 1)
    (hzc : ∀ s ∈ (S : Subgroup G), Commute z s)
    (t : S6) (ht : t.IsSwap)
    (haction : ∀ a : alternatingGroup (Fin 6),
      (e.symm (MulAut.conjNormal t a) : G) = z * (e.symm a : G) * z⁻¹) : False := by
  have htype : t.cycleType = {2} := isSwap_iff_cycleType.mp ht
  have hclass : IsConj trans t := isConj_iff_cycleType_eq.mpr
    ((by decide +kernel : trans.cycleType = {2}).trans htype.symm)
  have hsign : t.sign = -1 := ht.sign_eq
  have hpow : t ^ 2 = 1 := by
    rw [← ht.orderOf]
    exact pow_orderOf_eq_one t
  apply false_of_configuration (by decide) S U L hU hL e z hzU hz2 hzc
    t hsign hpow haction (MonoidHom.id S6) Function.injective_id
    trans (Or.inl rfl) borelSylow (by simp) borel_six_central_trans hclass

/-- The triple-transposition row of a marked A7 component has the same
six-letter obstruction, fixing the seventh point. -/
theorem false_of_alternating_seven_triple {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (U L : Subgroup G) [IsMulCommutative U]
    (hU : IsStronglyClosedSet (U : Set G) (S : Subgroup G) ⊤)
    (hL : L.IsSubnormal) (e : L ≃* alternatingGroup (Fin 7))
    (z : G) (hzU : z ∈ U) (hz2 : z ^ 2 = 1)
    (hzc : ∀ s ∈ (S : Subgroup G), Commute z s)
    (t : S7) (ht : t.cycleType = {2, 2, 2})
    (haction : ∀ a : alternatingGroup (Fin 7),
      (e.symm (MulAut.conjNormal t a) : G) = z * (e.symm a : G) * z⁻¹) : False := by
  have hclass : IsConj (liftSix triple) t := isConj_iff_cycleType_eq.mpr
    ((by decide +kernel : (liftSix triple).cycleType = {2, 2, 2}).trans ht.symm)
  have hsign : t.sign = -1 := by rw [sign_of_cycleType', ht]; norm_num
  have hpow : t ^ 2 = 1 := by
    obtain ⟨g, rfl⟩ := isConj_iff.mp hclass
    have hh := congrArg (MulAut.conj g) (show (liftSix triple) ^ 2 = 1 by decide +kernel)
    simpa only [map_pow, map_one, MulAut.conj_apply] using hh
  exact false_of_configuration (by decide) S U L hU hL e z hzU hz2 hzc
    t hsign hpow haction liftSix liftSix_injective
    triple (Or.inr rfl) sevenSylow sevenSylow_coe borel_seven_central_triple hclass

end Theory.GroupTheory.AlternatingStrongClosure
