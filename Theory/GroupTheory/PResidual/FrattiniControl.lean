module

public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.Frattini.OmegaProducts
public import Theory.GroupTheory.PPerfectHom

/-!
# Frattini detection for p-perfect commutator actions

The Frattini automorphism kernel is a p-group, so a p-perfect actor cannot
act nontrivially through it. Passing to a quotient by a normal subgroup X
removes a Frattini factor from a bound [P,A]≤Φ(P)X. Idempotence then
identifies [P,A] with [X,A] whenever X≤P. This is the general group-theoretic
first branch of MS93 (3.6), and is independent of the natural-module field.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), p.870.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]

/-- A p-perfect actor acts faithfully enough on the Frattini quotient to
detect whether its whole commutator vanishes. -/
theorem commutator_eq_bot_of_le_frattini_of_isPPerfect
    (P A : Subgroup G) [Finite P]
    (hP : IsPGroup p P) (hA : IsPPerfect p A)
    (hn : A ≤ normalizer (P : Set G))
    (hc : ⁅P,A⁆ ≤ (frattini P).map P.subtype) : ⁅P,A⁆ = ⊥ := by
  let action : A →* MulAut P := P.normalizerMonoidHom.comp (inclusion hn)
  have hk (a : A) : action a ∈ (quotientAut (frattini P)).ker := by
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (frattini P) x
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (frattini P) (action a y) = QuotientGroup.mk' (frattini P) y
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hh : ⁅(a : G),(y : G)⁆ ∈ (frattini P).map P.subtype := by
      apply hc
      rw [commutator_comm]
      exact commutator_mem_commutator a.property y.property
    obtain ⟨z,hz,he⟩ := hh
    have he' : z = action a y / y := by
      apply Subtype.ext
      simpa [action, commutatorElement_def, div_eq_mul_inv] using he
    exact he' ▸ hz
  let action' : A →* (quotientAut (frattini P)).ker := action.codRestrict _ hk
  have htriv := hA.hom_eq_one_of_isPGroup (isPGroup_quotientAut_frattini_kernel hP) action'
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro x hx a ha
  have he := congrArg (fun f : A →* (quotientAut (frattini P)).ker =>
    (((f ⟨a,ha⟩ : MulAut P) ⟨x,hx⟩) : G)) htriv
  change a * x * a⁻¹ = x at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- The Frattini factor can be removed from a normal-subgroup bound. -/
theorem commutator_le_of_le_frattini_sup_of_isPPerfect
    (P A X : Subgroup G) [Finite P] [P.Normal] [X.Normal]
    (hP : IsPGroup p P) (hA : IsPPerfect p A)
    (hc : ⁅P,A⁆ ≤ (frattini P).map P.subtype ⊔ X) : ⁅P,A⁆ ≤ X := by
  let q := QuotientGroup.mk' X
  let P' := P.map q
  let A' := A.map q
  have hP' : IsPGroup p P' := hP.map q
  have hA' : IsPPerfect p A' := hA.of_surjective (q.subgroupMap A)
    (q.subgroupMap_surjective A)
  let : Finite P' := Finite.of_surjective (q.subgroupMap P) (q.subgroupMap_surjective P)
  let : P'.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective X)
  have hphi : ((frattini P).map P.subtype).map q ≤ (frattini P').map P'.subtype := by
    have h := frattini_le_comap_frattini_of_surjective (q.subgroupMap_surjective P)
    have hh := map_mono (f := P'.subtype) (map_le_iff_le_comap.mpr h)
    have he : P'.subtype.comp (q.subgroupMap P) = q.comp P.subtype := by
      ext x
      rfl
    simpa only [map_map,he] using hh
  have hcomm : ⁅P',A'⁆ ≤ (frattini P').map P'.subtype := by
    have h := map_mono (f := q) hc
    rw [map_commutator,Subgroup.map_sup,QuotientGroup.map_mk'_self,sup_bot_eq] at h
    exact h.trans hphi
  have hzero := commutator_eq_bot_of_le_frattini_of_isPPerfect P' A' hP' hA'
    le_normalizer_of_normal hcomm
  rw [← map_commutator,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at hzero
  exact hzero

/-- Full commutation turns Frattini containment into an exact identification
with the moving part of X. -/
theorem commutator_eq_of_le_frattini_sup_of_isPPerfect [Finite G]
    (P A X : Subgroup G) [P.Normal] [X.Normal]
    (hP : IsPGroup p P) (hA : IsPPerfect p A) (hXP : X ≤ P)
    (hc : ⁅P,A⁆ ≤ (frattini P).map P.subtype ⊔ X) : ⁅P,A⁆ = ⁅X,A⁆ := by
  apply le_antisymm
  · rw [← commutator_isPPerfect_idempotent A P hA hP le_normalizer_of_normal]
    exact commutator_mono
      (commutator_le_of_le_frattini_sup_of_isPPerfect P A X hP hA hc) le_rfl
  · exact commutator_mono hXP le_rfl

end Subgroup
