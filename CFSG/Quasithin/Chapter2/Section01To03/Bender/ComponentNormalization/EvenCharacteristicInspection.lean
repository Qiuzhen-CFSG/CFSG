module

public import Theory.GroupTheory.MarkedInnerStrongClosure.CentralTwoQuotient
public import Theory.SpecificGroups.EvenCharacteristic.InvolutionFusion
public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentNormalization

/-!
# Excluding the even-field PSL₃ component families

Restrict the actual Sylow S of H to its subnormal component L. The source
O(H)=1 passes to L and identifies Z(L) with O₂(L), so the literal quotient
L/O₂(L) has a central two-kernel. The original z acts nontrivially on L:
otherwise L lies in C_G(z)≤M, contrary to source 1.1.5. Its quotient
implementer is therefore an involution, and its returning quotient conjugates
must commute by abelian strong closure of the original U.

The actual PSL₃(2^n) model has one involution class and noncommuting
involutions in every Sylow, for all n>0. This excludes the simple A2 family
in row (a), as well as every central-two PSL₃(4) cover in row (b), without
assuming an involution lift or making U a subgroup of L. The earlier source
owner still supplies the row equivalence, marked innerness, L not≤M,
O(H)=1, and the indicated Sylow placement.

Source: Aschbacher--Smith 1.1.5(3)(a),(b), pp.501--503, and the component
inspection in Proposition 2.2.2, printed pp.519--520 (1 March 2004 manuscript).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M : Subgroup G}

private theorem false_of_inner_psl3_quotient_model
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (q : L →* PSL(3,F)) (hq : Function.Surjective q)
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
  exact MarkedInnerStrongClosure.false_of_central_two_quotient_fusion
    S' w.U hU L.subtype L.subtype_injective P hPS q hq hker hker2
    w.z w.z_mem (w.z_order ▸ pow_orderOf_eq_one w.z)
    (fun s hs => w.z_central s (hST hs)) t htn ht
    (EvenCharacteristicInvolutionFusion.psl3_involutions_isConj F hn hF)
    (EvenCharacteristicInvolutionFusion.psl3_sylow_noncommuting_involutions F hn hF)

/-- The literal central-two quotient cannot be an even-field PSL₃. This
includes every nontrivial PSL₃(4) cover in source 1.1.5(3)(b). -/
theorem LocalControlWitness.false_of_inner_psl3_twoCore_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hcore : pPrimeCore 2 H = ⊥)
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* PSL(3,F))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : IsQuasisimple L := hL.quasisimple
  have hlocal : pPrimeCore 2 (L.subgroupOf H) = ⊥ :=
    hL.2.1.pPrimeCore_eq_bot hcore (L.subgroupOf H)
  have hcoreL : pPrimeCore 2 L = ⊥ := by
    have he := pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hL.1)
    simpa only [hlocal, Subgroup.map_bot] using he.symm
  have hZ : center L = pCore 2 L := IsQuasisimple.center_eq_pCore hcoreL
  let q : L →* PSL(3,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hk : q.ker = pCore 2 L := by
    dsimp only [q]
    exact (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (pCore 2 L))
      e.toMonoidHom e.injective).trans (QuotientGroup.ker_mk' _)
  exact false_of_inner_psl3_quotient_model w H S hUS hST L hL hLM F hn hF
    q (e.surjective.comp (QuotientGroup.mk'_surjective _)) (hk.trans hZ.symm)
    (hk.symm ▸ pCore_isPGroup) hinner

/-- The simple even-field PSL₃ alternative in source 1.1.5(3)(a) is impossible. -/
theorem LocalControlWitness.false_of_inner_even_psl3_component
    (w : LocalControlWitness T M) (H : Subgroup G) (S : Sylow 2 H)
    (hUS : w.U ≤ (S : Subgroup H).map H.subtype)
    (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (L : Subgroup G) (hL : IsComponentIn L H) (hLM : ¬L ≤ M)
    (hsimple : IsSimpleGroup L)
    (F : Type*) [Field F] [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) (e : L ≃* PSL(3,F))
    (hinner : ∃ t : L, ∀ x : L,
      ((t * x * t⁻¹ : L) : G) = w.z * (x : G) * w.z⁻¹) : False := by
  let : IsQuasisimple L := hL.quasisimple
  let : IsSimpleGroup L := hsimple
  have hc : center L = ⊥ := center_eq_bot_of_simple_perfect
  have hk : e.toMonoidHom.ker = ⊥ := e.toMonoidHom.ker_eq_bot e.injective
  exact false_of_inner_psl3_quotient_model w H S hUS hST L hL hLM F hn hF
    e.toMonoidHom e.surjective (hk.trans hc.symm) (hk.symm ▸ IsPGroup.of_bot) hinner

end CFSG.Quasithin.Chapter2.BenderFusion
