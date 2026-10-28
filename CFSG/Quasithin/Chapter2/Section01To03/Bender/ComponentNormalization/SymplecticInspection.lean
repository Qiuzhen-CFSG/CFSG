module

public import Theory.GroupTheory.MarkedInnerStrongClosure.ReturningProducts
public import Theory.GroupTheory.MarkedInnerStrongClosure.ReturningConjugates
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.SpecificGroups.SymplecticFour.MarkedStrongClosure
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization

/-!
# Excluding the nonbinary symplectic row in the Bender inspection

The actual source Sylow restricts to the component. The original inner
implementer has a nontrivial central involution as its image in the concrete
Sp₄ model. The model supplies a direct returning pair or a returning ratio
with such a pair. In the second case the ratio belongs to U inside L, so
ordinary strong closure applies without centrality of the new marker.

The PSp₄ and derived-carrier adapters use the actual central quotient and
the proved nonbinary perfectness. Source row selection and the original
inner action remain the earlier 1.1.5 inputs.

Source: Aschbacher--Smith 1.1.5(3)(a), printed pp.501--503, and Proposition
2.2.2, pp.519--520 (combined 1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.BenderFusion
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

private theorem false_of_inner_sp4_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (F : Type*) [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (e : L ≃* Sp F)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : IsElementaryAbelian 2 w.U := w.elementary
  let : IsQuasisimple L := hL.quasisimple
  let S' : Subgroup G := (S : Subgroup H).map H.subtype
  have hU : IsStronglyClosedSet (w.U : Set G) S' ⊤ :=
    ⟨hUS, fun x hx g hg hgs => w.strongly_closed.2 x hx g hg (hST hgs)⟩
  obtain ⟨P0, hP0⟩ := S.exists_subgroupOf_eq_of_subnormal (L.subgroupOf H) hL.2.1
  let e0 := subgroupOfEquivOfLe hL.1
  let P := P0.mapSurjective (f := e0.toMonoidHom) e0.surjective
  have hPS : (P : Subgroup L).map L.subtype ≤ S' := by
    rintro _ ⟨a, ⟨x, hx, rfl⟩, rfl⟩
    have hxS : (x : H) ∈ (S : Subgroup H) := by
      change x ∈ (S : Subgroup H).subgroupOf (L.subgroupOf H)
      rw [← hP0]
      exact hx
    exact mem_map_of_mem H.subtype hxS
  have hlocal : pPrimeCore 2 (L.subgroupOf H) = ⊥ :=
    hL.2.1.pPrimeCore_eq_bot hcore (L.subgroupOf H)
  have hcoreL : pPrimeCore 2 L = ⊥ := by
    have he := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hL.1)
    simpa only [hlocal, Subgroup.map_bot] using he.symm
  have hcL : center L = ⊥ := by
    apply bot_unique
    intro x hx
    have hh := (centerCongr e ⟨x, hx⟩).property
    change e x ∈ center (Sp F) at hh
    rw [EvenProjective.center_eq_bot, mem_bot] at hh
    exact e.injective (hh.trans (map_one e).symm)
  have hk : e.toMonoidHom.ker = center L :=
    (e.toMonoidHom.ker_eq_bot e.injective).trans hcL.symm
  have hk2 : IsPGroup 2 e.toMonoidHom.ker := by
    rw [hk, IsQuasisimple.center_eq_pCore hcoreL]
    exact pCore_isPGroup
  obtain ⟨t, ht⟩ := hinner
  have htn : e t ≠ 1 := by
    intro he
    have ht1 : t = 1 := e.injective (he.trans (map_one e).symm)
    apply hLM
    intro x hx
    apply w.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have hh := ht ⟨x, hx⟩
    rw [ht1] at hh
    simp only [one_mul, inv_one, mul_one] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  obtain ⟨htP, ho, hc⟩ := MarkedInnerStrongClosure.central_two_quotient_marker
    S' L.subtype L.subtype_injective P hPS e.toMonoidHom e.surjective hk hk2
    w.z (w.z_order ▸ pow_orderOf_eq_one w.z)
    (fun s hs => w.z_central s (hST hs)) t htn ht
  let R : Sylow 2 (Sp F) := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmodel := MarkedStrongClosure.sylow_returning_product_obstruction hF
    (by omega : 1 ≤ n) R (e t) (mem_map_of_mem e.toMonoidHom htP) ho hc
  have hback := hmodel.map e.symm
  have hmap : (R : Subgroup (Sp F)).map e.symm.toMonoidHom = (P : Subgroup L) := by
    change ((P : Subgroup L).map e.toMonoidHom).map e.symm.toMonoidHom = _
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id L := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [Subgroup.map_map, he, Subgroup.map_id]
  have hcert : MarkedInnerStrongClosure.ReturningProductObstruction (P : Subgroup L) t := by
    simpa only [hmap, e.symm_apply_apply] using hback
  exact MarkedInnerStrongClosure.false_of_returning_product_obstruction S' w.U hU
    L.subtype L.subtype_injective (P : Subgroup L) hPS w.z w.z_mem t htP ht hcert

/-- The simple full-matrix symplectic alternative is excluded with the
original source Sylow, odd-core and marked-action hypotheses. -/
theorem LocalControlWitness.false_of_inner_sp4_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (e : L ≃* Sp F)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  exact false_of_inner_sp4_model w H S hUS hST hcore L hL hLM F hF hn e hinner

/-- The source PSp₄ model is transported through the actual central quotient. -/
theorem LocalControlWitness.false_of_inner_psp4_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n) (e : L ≃* ClassicalGroup.PSp 2 F)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  exact w.false_of_inner_sp4_component H S hUS hST hcore L hL hLM F hF hn
    (e.trans EvenProjective.equiv.symm) hinner

/-- The genuine source model predicate supplies the field and projective
equivalence, leaving no extra pair, fusion or class premise. -/
theorem LocalControlWitness.false_of_inner_psp4_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp L 2 (2 ^ n))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  exact w.false_of_inner_psp4_component H S hUS hST hcore L hL hLM F hF hn e hinner

/-- The derived projective carrier agrees with the projective group here
by the existing perfectness theorem, with the quotient taken first. -/
theorem LocalControlWitness.false_of_inner_psp4_derived_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (e : L ≃* commutator (ClassicalGroup.PSp 2 F))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 0 < 2) hn)
  let : Group.IsPerfect (Sp F) := perfect_of_card_gt_two hq
  let : Group.IsPerfect (ClassicalGroup.PSp 2 F) := inferInstance
  let j : commutator (ClassicalGroup.PSp 2 F) ≃* ClassicalGroup.PSp 2 F :=
    (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans Subgroup.topEquiv
  exact w.false_of_inner_psp4_component H S hUS hST hcore L hL hLM F hF hn
    (e.trans j) hinner

/-- Apply the source model exclusion to the literal bad-centralizer
component, keeping the original Sylow embeddings and distinguished z. -/
theorem LocalControlWitness.false_of_inner_psp4_centralizer_component
    (w : LocalControlWitness T M) (u : G)
    (S : Sylow 2 (centralizer ({u} : Set G)))
    (hUS : w.U ≤ (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype)
    (hST : (S : Subgroup (centralizer ({u} : Set G))).map
      (centralizer ({u} : Set G)).subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 (centralizer ({u} : Set G)) = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L (centralizer ({u} : Set G)))
    (hLM : ¬L ≤ M) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSp L 2 (2 ^ n))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False :=
  w.false_of_inner_psp4_model (centralizer ({u} : Set G)) S hUS hST hcore
    L hL hLM hn hm hinner

end CFSG.Quasithin.Chapter2.BenderFusion
