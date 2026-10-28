module

public import Theory.GroupAction.ThompsonAB
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.ReducedNormal.Basic
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Reduced witnesses detecting a normal subgroup's p-core

If K is normal and a normal elementary abelian p-subgroup U satisfies
C_K(U) = O_p(K), choose such a witness of minimal order inside U.
Its conjugation image K* has trivial p-core and, being normal, centralizes
the p-core of the whole conjugation image. The Thompson fixed-point kernel
bound makes K* faithful on the fixed subgroup of this latter p-core.
Thus the fixed subgroup retains the detecting centralizer. Minimality makes
it the whole witness, and faithfulness kills the ambient image's p-core.
The explicit conjugation-kernel isomorphism identifies this image with the
literal quotient G/C_G(U), proving reducedness in the published definition.

The stronger kernel form of Thompson A × B is used here. Its proof applies
the residual theorem to the restriction kernel's p-residual, so it requires
no p-residual hypothesis on K* itself. This avoids introducing F*(K*) while
retaining all the source hypotheses and the actual fixed subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.18–19, printed p.24, generalized from two to an arbitrary prime.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] {p : ℕ}

private theorem normal_commutator_pCore_eq_bot (A : Subgroup G) [A.Normal]
    (hA : pCore p A = ⊥) : ⁅A, pCore p G⁆ = ⊥ := by
  have hle : (pCore p G).subgroupOf A ≤ pCore p A :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  apply bot_unique
  intro x hx
  have hxI := commutator_le_inf A (pCore p G) hx
  have hh := hle (show (⟨x, hxI.1⟩ : A) ∈ (pCore p G).subgroupOf A from hxI.2)
  rw [hA] at hh
  exact congrArg Subtype.val (mem_bot.mp hh)

/-- Conjugation has exactly the centralizer as kernel. -/
private theorem conjNormal_ker (U : Subgroup G) [U.Normal] :
    (MulAut.conjNormal : G →* MulAut U).ker = centralizer (U : Set G) := by
  ext x
  change (MulAut.conjNormal x : MulAut U) = 1 ↔ _
  constructor
  · intro hx u hu
    have he := congrArg (fun a : MulAut U => (a ⟨u, hu⟩ : G)) hx
    change x * u * x⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx
    ext u
    change x * u.val * x⁻¹ = u.val
    rw [← hx u.val u.property, mul_inv_cancel_right]

variable [Finite G] [Fact p.Prime]

/-- The fixed subgroup of the action's p-core preserves the detecting centralizer. -/
private theorem fixed_core_preserves_centralizer
    (K U : Subgroup G) [K.Normal] [U.Normal] [IsElementaryAbelian p U]
    (hcentral : K ⊓ centralizer (U : Set G) = (pCore p K).map K.subtype) :
    ∃ W : Subgroup G, W ≤ U ∧ W.Normal ∧ IsElementaryAbelian p W ∧
      K ⊓ centralizer (W : Set G) = (pCore p K).map K.subtype ∧
      (W = U → IsPReduced p U) := by
  let f : G →* MulAut U := MulAut.conjNormal
  let H := f.range
  let r : G →* H := f.rangeRestrict
  let A := K.map r
  let B := pCore p H
  let Q := B.comap r
  let W := U ⊓ centralizer (Q : Set G)
  let : A.Normal := Normal.map inferInstance r f.rangeRestrict_surjective
  have hker : (r.subgroupMap K).ker = pCore p K := by
    rw [ker_subgroupMap, MonoidHom.ker_rangeRestrict, conjNormal_ker]
    apply le_antisymm
    · intro k hk
      obtain ⟨a, ha, he⟩ := hcentral.le ⟨k.property, hk⟩
      exact K.subtype_injective he ▸ ha
    · intro k hk
      exact (hcentral.ge (mem_map_of_mem K.subtype hk)).2
  have hAcore : pCore p A = ⊥ := by
    have hkerP : IsPGroup p (r.subgroupMap K).ker := by rw [hker]; exact pCore_isPGroup
    have hpre := (r.subgroupMap K).comap_pCore_of_ker_isPGroup
      (r.subgroupMap_surjective K) hkerP
    apply bot_unique
    intro a ha
    obtain ⟨k, rfl⟩ := r.subgroupMap_surjective K a
    have hk : k ∈ pCore p K := hpre.le ha
    exact hker.ge hk
  have hAB : ⁅A, B⁆ = ⊥ := normal_commutator_pCore_eq_bot A hAcore
  have hfixed : ∀ u : U, u ∈ FixedPoints.subgroup B U ↔ u.val ∈ W := by
    intro u
    constructor
    · intro hu
      refine ⟨u.property, ?_⟩
      intro g hg
      have he := congrArg Subtype.val (hu (⟨r g, hg⟩ : B))
      change g * u.val * g⁻¹ = u.val at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hu b
      obtain ⟨g, hg⟩ := f.rangeRestrict_surjective (b : H)
      change ((b : H) : MulAut U) u = u
      rw [← hg]
      apply Subtype.ext
      change g * u.val * g⁻¹ = u.val
      have hcomm := hu.2 g (show g ∈ Q from (show r g ∈ B by rw [hg]; exact b.property))
      rw [hcomm, mul_inv_cancel_right]
  have hWcentral : K ⊓ centralizer (W : Set G) = (pCore p K).map K.subtype := by
    apply le_antisymm
    · intro k hk
      let a : A := ⟨r k, mem_map_of_mem r hk.1⟩
      have hak : a ∈ fixingSubgroup A (FixedPoints.subgroup B U : Set U) := by
        rw [mem_fixingSubgroup_iff]
        intro u hu
        apply Subtype.ext
        change k * u.val * k⁻¹ = u.val
        rw [← hk.2 u.val ((hfixed u).mp hu), mul_inv_cancel_right]
      have ha := thompson_fixedPoints_kernel_le_pCore A B
        (IsElementaryAbelian.isPGroup p U) pCore_isPGroup hAB hak
      rw [hAcore] at ha
      have hf : f k = 1 := congrArg (fun x : A => ((x : H) : MulAut U)) (mem_bot.mp ha)
      exact hcentral.le ⟨hk.1, (conjNormal_ker U).le hf⟩
    · exact hcentral.ge.trans (inf_le_inf_left K (centralizer_le inf_le_left))
  refine ⟨W, inf_le_left, inferInstance, IsElementaryAbelian.of_le inf_le_left,
    hWcentral, ?_⟩
  intro hWU
  have hBbot : B = ⊥ := by
    apply bot_unique
    intro b hb
    apply Subtype.ext
    apply MulEquiv.ext
    intro u
    have hu : u ∈ FixedPoints.subgroup B U := (hfixed u).mpr (hWU.symm ▸ u.property)
    exact hu ⟨b, hb⟩
  refine ⟨inferInstance, inferInstance, ?_⟩
  let e : (G ⧸ centralizer (U : Set G)) ≃* H :=
    (QuotientGroup.quotientMulEquivOfEq (conjNormal_ker U).symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso p e]
  exact hBbot

/-- A normal elementary abelian witness detecting the p-core contains a
reduced witness with the same centralizer in K. -/
theorem exists_isPReduced_le_centralizer_eq_core
    (K U : Subgroup G) [K.Normal] [U.Normal] [IsElementaryAbelian p U]
    (hcentral : K ⊓ centralizer (U : Set G) = (pCore p K).map K.subtype) :
    ∃ V : Subgroup G, V ≤ U ∧ IsPReduced p V ∧
      K ⊓ centralizer (V : Set G) = (pCore p K).map K.subtype := by
  let s : Set (Subgroup G) := {V | V ≤ U ∧ V.Normal ∧ IsElementaryAbelian p V ∧
    K ⊓ centralizer (V : Set G) = (pCore p K).map K.subtype}
  have hs : s.Nonempty := ⟨U, le_rfl, inferInstance, inferInstance, hcentral⟩
  obtain ⟨V, hV, hmin⟩ := Set.exists_min_image s (fun V => Nat.card V) (Set.toFinite s) hs
  obtain ⟨hVU, hVn, hVe, hVc⟩ := hV
  let := hVn
  let := hVe
  obtain ⟨W, hWV, hWn, hWe, hWc, hred⟩ := fixed_core_preserves_centralizer K V hVc
  have hWVeq : W = V := eq_of_le_of_card_ge hWV
    (hmin W ⟨hWV.trans hVU, hWn, hWe, hWc⟩)
  exact ⟨V, hVU, hred hWVeq, hVc⟩

end Theory.GroupTheory
