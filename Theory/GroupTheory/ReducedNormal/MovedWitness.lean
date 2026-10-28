module

public import Theory.GroupTheory.ChiefFactorsAboveCore
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.ReducedNormal.Basic
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupAction.ThompsonAB
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Minimal moved modules contain reduced witnesses

Let X be a subnormal p-perfect subgroup. Suppose every p-chief factor above
O_p(X) is central. A normal elementary abelian p-subgroup U moved by X and
centralized by O_p(X) contains a normal elementary abelian reduced subgroup
still moved by X.

Choose V of minimum order among the normal subgroups of U moved by X.
In the genuine conjugation image on V, the chief-factor theorem makes the
core of the image of X central. The subnormal residual commutator theorem
(A.4.2(3) followed by coprime commutator idempotence) then makes that image
centralize the whole actor's p-core. Thompson's A × B theorem shows that
the fixed subgroup of this core is still moved. Minimality makes it V,
and faithfulness kills the actor's core. The first isomorphism theorem
identifies that actor with G/C_G(V), exactly as required by `IsPReduced`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.4.11(1) implies (2), printed pp.60–61. The argument works for every prime.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- The fixed subgroup of the core of the conjugation image is still moved.
If this fixed subgroup is the whole module, the module is reduced. -/
private theorem fixed_core_preserves_moved
    (X U : Subgroup G) (hsub : X.IsSubnormal) (hX : IsPPerfect p X)
    (hchief : HasCentralPChiefFactorsAbove p (pCore p X))
    [U.Normal] [IsElementaryAbelian p U]
    (hkill : (pCore p X).map X.subtype ≤ centralizer (U : Set G))
    (hmoved : ⁅U, X⁆ ≠ ⊥) :
    ∃ W : Subgroup G, W ≤ U ∧ W.Normal ∧ ⁅W, X⁆ ≠ ⊥ ∧
      (W = U → IsPReduced p U) := by
  let f : G →* MulAut U := MulAut.conjNormal
  let H := f.range
  let r : G →* H := f.rangeRestrict
  let A := X.map r
  let B := pCore p H
  let Q := B.comap r
  let W := U ⊓ centralizer (Q : Set G)
  have hrker : r.ker = centralizer (U : Set G) := by
    rw [MonoidHom.ker_rangeRestrict, MulAut.conjNormal_ker_eq_centralizer]
  have hA : IsPPerfect p A :=
    hX.of_surjective (r.subgroupMap X) (r.subgroupMap_surjective X)
  have hAcore : pCore p A ≤ center A := by
    apply pCore_image_le_center_of_chiefFactors hX hchief (r.subgroupMap X)
      (r.subgroupMap_surjective X)
    intro x hx
    apply Subtype.ext
    exact hrker.ge (hkill (mem_map_of_mem X.subtype hx))
  have hBA : ⁅B, A⁆ = ⊥ := by
    have hh := commutator_le_core_commutator_of_isSubnormal A B
      (hsub.map f.rangeRestrict_surjective) hA pCore_isPGroup le_normalizer_of_normal
    rw [commutator_top_right_eq_bot_iff_le_center.mpr hAcore, Subgroup.map_bot] at hh
    exact bot_unique hh
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
      have hcomm := hu.2 g (show g ∈ Q from
        (show r g ∈ B by rw [hg]; exact b.property))
      rw [hcomm, mul_inv_cancel_right]
  have hWmoved : ⁅W, X⁆ ≠ ⊥ := by
    intro htriv
    have hfix : A ≤ fixingSubgroup H (FixedPoints.subgroup B U : Set U) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [mem_fixingSubgroup_iff]
      intro u hu
      apply Subtype.ext
      change x * u.val * x⁻¹ = u.val
      have he := mem_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp htriv ((hfixed u).mp hu)) x hx
      rw [he, mul_inv_cancel_right]
    have htrivA := thompson_a_times_b_fixedPoints A B
      (IsElementaryAbelian.isPGroup p U) pCore_isPGroup
      ((pResidual_eq_top_iff p A).mpr hA) (by rwa [commutator_comm]) hfix
    apply hmoved
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro u hu
    rw [mem_centralizer_iff]
    intro x hx
    have he := (mem_fixingSubgroup_iff H).mp (htrivA (mem_map_of_mem r hx))
      (⟨u, hu⟩ : U) (Set.mem_univ _)
    have he' := congrArg Subtype.val he
    change x * u * x⁻¹ = u at he'
    exact mul_inv_eq_iff_eq_mul.mp he'
  refine ⟨W, inf_le_left, inferInstance, hWmoved, ?_⟩
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
    (QuotientGroup.quotientMulEquivOfEq (MulAut.conjNormal_ker_eq_centralizer U).symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  rw [pCore_map_iso p e]
  exact hBbot

/-- A subnormal p-perfect subgroup with central p-chief factors above its
core detects a reduced subgroup inside every elementary normal module that
it moves and on which its original core acts trivially. -/
theorem exists_isPReduced_le_of_moved
    (X U : Subgroup G) (hsub : X.IsSubnormal) (hX : IsPPerfect p X)
    (hchief : HasCentralPChiefFactorsAbove p (pCore p X))
    [U.Normal] [IsElementaryAbelian p U]
    (hkill : (pCore p X).map X.subtype ≤ centralizer (U : Set G))
    (hmoved : ⁅U, X⁆ ≠ ⊥) :
    ∃ V : Subgroup G, V ≤ U ∧ IsPReduced p V ∧ ⁅V, X⁆ ≠ ⊥ := by
  let s : Set (Subgroup G) := {V | V ≤ U ∧ V.Normal ∧ ⁅V, X⁆ ≠ ⊥}
  have hs : s.Nonempty := ⟨U, le_rfl, inferInstance, hmoved⟩
  obtain ⟨V, hV, hmin⟩ := Set.exists_min_image s (fun V => Nat.card V) (Set.toFinite s) hs
  obtain ⟨hVU, hVn, hVm⟩ := hV
  let := hVn
  let : IsElementaryAbelian p V := IsElementaryAbelian.of_le hVU
  obtain ⟨W, hWV, hWn, hWm, hred⟩ := fixed_core_preserves_moved X V hsub hX hchief
    (hkill.trans (centralizer_le hVU)) hVm
  have he : W = V := eq_of_le_of_card_ge hWV
    (hmin W ⟨hWV.trans hVU, hWn, hWm⟩)
  exact ⟨V, hVU, hred he, hVm⟩

/-- The maximal reduced subgroup is moved under the same source hypotheses. -/
theorem reducedPSubgroup_commutator_ne_bot_of_moved
    (X U : Subgroup G) (hsub : X.IsSubnormal) (hX : IsPPerfect p X)
    (hchief : HasCentralPChiefFactorsAbove p (pCore p X))
    [U.Normal] [IsElementaryAbelian p U]
    (hkill : (pCore p X).map X.subtype ≤ centralizer (U : Set G))
    (hmoved : ⁅U, X⁆ ≠ ⊥) : ⁅reducedPSubgroup p G, X⁆ ≠ ⊥ := by
  obtain ⟨V, _, hV, hm⟩ := exists_isPReduced_le_of_moved X U hsub hX hchief hkill hmoved
  intro he
  exact hm (bot_unique ((commutator_mono hV.le_reducedPSubgroup le_rfl).trans_eq he))
end Theory.GroupTheory
