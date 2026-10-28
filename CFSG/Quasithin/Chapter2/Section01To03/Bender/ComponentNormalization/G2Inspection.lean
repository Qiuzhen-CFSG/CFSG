module

public import Theory.GroupTheory.MarkedInnerStrongClosure.ReturningConjugates
public import Theory.SpecificGroups.G2.MarkedStrongClosure
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# Excluding all central-two G₂(4) covers in the Bender inspection

The actual component Sylow is obtained by restricting the original Sylow of
H. The source O(H)=1 makes the component center equal O₂(L), so the literal
map from L/O₂(L) to G₂(4) has a central two-kernel. The marked inner
implementer has nonidentity image because L is not contained in M and
C_G(z) is contained in M. Its image is a central involution of the actual
quotient Sylow.

Two long-root conjugates returning to that Sylow do not commute. Their
conjugators lift to L, and the two-kernel makes both lifts return to the
original component Sylow. The abelian strong closure of U forces them to
commute, giving the contradiction. The order of the center is unrestricted.

Source: Aschbacher--Smith 1.1.5(3)(b), pp.501--502, and the inspection in
Proposition 2.2.2, pp.519--520 (combined 1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

private theorem false_of_inner_g2_quotient_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (q : L →* Atlas.G2.Model F) (hq : Function.Surjective q)
    (hker : q.ker = center L) (hker2 : IsPGroup 2 q.ker)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : IsElementaryAbelian 2 w.U := w.elementary
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
  obtain ⟨t, ht⟩ := hinner
  have htn : q t ≠ 1 := by
    intro he
    have htc : t ∈ center L := hker ▸ (show t ∈ q.ker from he)
    apply hLM
    intro x hx
    apply w.centralizer_le
    apply mem_centralizer_singleton_iff.mpr
    have htx : t * (⟨x, hx⟩ : L) * t⁻¹ = ⟨x, hx⟩ := by
      rw [← mem_center_iff.mp htc ⟨x, hx⟩]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    have hh := ht ⟨x, hx⟩
    rw [htx] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  apply MarkedInnerStrongClosure.false_of_central_two_quotient_returning_pair
    S' w.U hU L.subtype L.subtype_injective P hPS q hq hker hker2
    w.z w.z_mem (w.z_order ▸ pow_orderOf_eq_one w.z)
    (fun s hs => w.z_central s (hST hs)) t htn ht
  intro R v hv ho hc
  exact Atlas.G2.MarkedStrongClosure.sylow_noncommuting_conjugates v
    ⟨ho, R, hv, fun x hx => mem_centralizer_singleton_iff.mpr (hc x hx).symm.eq⟩ R

/-- The G₂(4) alternative of source 1.1.5(3)(b) is impossible for the
original Bender witness, for every central two-kernel permitted by the source. -/
theorem LocalControlWitness.false_of_inner_g2_four_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (F : Type*) [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : (L ⧸ pCore 2 L) ≃* Atlas.G2.Model F)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := 2) (by
    norm_num only [← Nat.card_eq_fintype_card, hF])
  let : IsQuasisimple L := hL.quasisimple
  have hlocal : pPrimeCore 2 (L.subgroupOf H) = ⊥ :=
    hL.2.1.pPrimeCore_eq_bot hcore (L.subgroupOf H)
  have hcoreL : pPrimeCore 2 L = ⊥ := by
    have he := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hL.1)
    simpa only [hlocal, Subgroup.map_bot] using he.symm
  have hZ : center L = pCore 2 L := IsQuasisimple.center_eq_pCore hcoreL
  let q : L →* Atlas.G2.Model F := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hk : q.ker = pCore 2 L := by
    dsimp only [q]
    exact (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (pCore 2 L))
      e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  exact false_of_inner_g2_quotient_model w H S hUS hST L hL hLM F
    q (e.surjective.comp (QuotientGroup.mk'_surjective _)) (hk.trans hZ.symm)
    (hk.symm ▸ pCore_isPGroup) hinner

/-- The source model predicate supplies precisely the literal quotient
equivalence consumed by the G₂(4) exclusion. -/
theorem LocalControlWitness.false_of_inner_g2_four_twoCore_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hm : ClassificationModels.IsG2At (L ⧸ pCore 2 L) 4)
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  exact w.false_of_inner_g2_four_twoCore_component H S hUS hST hcore L hL hLM F hF e hinner

end CFSG.Quasithin.Chapter2.BenderFusion
