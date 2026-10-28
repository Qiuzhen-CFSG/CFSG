module

public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceFourActors.Geometry
public import Theory.Representation.BinaryOffender.CommutatorRank
/-!
# The remaining source core identities on printed p.392

The three natural axes generate V₁ and each is fixed by a cyclic subgroup
of corank two in B₂. Thus the original restricted action has full core.
For an outer a, its fixed space is A₂-invariant and a acts trivially there.
The map B₂ → A₂/⟨a⟩ is surjective, and the literal diagonal equivalence
intertwines its action with the natural one. Actual quotient and actor
transport therefore give both displayed full-core identities on C_V(a).

Source: Aschbacher–Smith, proof of H.9.3(6), printed p.392.
-/

@[expose] public section
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits Theory.GroupTheory
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]
  (S : SourceSetup 4 M V) (T : Sylow 2 M)

local instance sourceA2Elementary : IsElementaryAbelian 2 (A2 S T) := actor_elementary S T 2

theorem natural_invariant (b : B2 S T) :
    S.natural ≤ S.natural.comap (S.representation b) := by
  intro u hu
  change S.representation b u ∈ S.natural
  rw [natural_action S T ⟨b.val,b.property.2⟩ ⟨u,hu⟩]
  exact Subtype.coe_prop _

/-- The actual restriction of the source representation to B₂ acting on V₁. -/
noncomputable def naturalB2Action : Representation (ZMod 2) (B2 S T) S.natural :=
  Representation.subrepresentation (S.representation.comp (B2 S T).subtype) S.natural
    (fun b => natural_invariant S T b)

theorem B2_card : Nat.card (B2 S T) = 8 := by
  rw [← Subgroup.card_map_of_injective (f := (group S T).toMonoidHom) (group S T).injective,
    B2_map]
  exact BinaryNaturalDual.FourActors.A2Module.card_B2

theorem A2_outer_order (a : M) (ha : a ∈ A2 S T) (haB : a ∉ B2 S T) : orderOf a = 2 := by
  let := actor_elementary S T 2
  apply orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha)
  intro h
  exact haB (h ▸ (B2 S T).one_mem)

/-- The first core identity on printed p.392, in the original natural summand. -/
theorem naturalB2_core : generatedCore (naturalB2Action S T) 2 = ⊤ := by
  let := S.finite_group
  let := actor_elementary S T 2
  have hp := A2_three_transvections S T
  have haxis (i : Fin 3) : naturalElementFixed S (axis S T i) ≤
      generatedCore (naturalB2Action S T) 2 := by
    let b : B2 S T := ⟨axis S T i, (hp.1 i).1⟩
    have hb2 : b ^ 2 = 1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (b : M) b.property.1
    have hb1 : b ≠ 1 := by
      intro h
      have hl : axis S T i = 1 := Subtype.ext (show (axis S T i : M) = 1 from congrArg (fun b : B2 S T => (b : M)) h)
      exact ((hp.1 i).2.1.ne_one) (by rw [hl, map_one])
    have hcard : Nat.card (Subgroup.zpowers b) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hb2 hb1]
    have hi : (Subgroup.zpowers b).index = 4 := by
      have hm := (Subgroup.zpowers b).index_mul_card
      rw [hcard, B2_card] at hm
      omega
    intro u hu
    apply fixedSpace_le_generatedCore (naturalB2Action S T)
      (X := Subgroup.zpowers b) (by rw [hi]; decide)
    rw [mem_fixedSpace_zpowers_iff]
    apply Subtype.ext
    exact (mem_elementFixed S _ _).mp hu
  apply top_unique
  rw [← A2_axes_span S T (i := 0) (j := 1) (by decide)]
  exact sup_le (haxis 0) (haxis 1)

theorem outer_fixed_invariant (a : M) (ha : a ∈ A2 S T) (b : A2 S T) :
    elementFixed S a ≤ (elementFixed S a).comap (S.representation b) := by
  let := actor_elementary S T 2
  intro v hv
  apply (mem_elementFixed S a _).mpr
  have hc : Commute (a : M) (b : M) :=
    congrArg Subtype.val (mul_comm' (⟨a,ha⟩ : A2 S T) b)
  change S.representation a (S.representation b v) = S.representation b v
  rw [← Module.End.mul_apply, (hc.map S.representation).eq, Module.End.mul_apply,
    (mem_elementFixed S a v).mp hv]

/-- The actual action of A₂ on the invariant subspace C_V(a). -/
noncomputable def outerFixedAction (a : M) (ha : a ∈ A2 S T) :
    Representation (ZMod 2) (A2 S T) (elementFixed S a) :=
  Representation.subrepresentation (S.representation.comp (A2 S T).subtype) (elementFixed S a)
    (fun b => outer_fixed_invariant S T a ha b)

/-- Both displayed cores on C_V(a), including the literal quotient by ⟨a⟩.
The quotient action is constructed and its pullback is the original action. -/
theorem outerFixed_cores (a : M) (ha : a ∈ A2 S T) (haB : a ∉ B2 S T) :
    generatedCore (outerFixedAction S T a ha) 2 = ⊤ ∧
    ∃ σ : Representation (ZMod 2)
        ((A2 S T) ⧸ Subgroup.zpowers (⟨a,ha⟩ : A2 S T)) (elementFixed S a),
      (∀ (b : A2 S T) v,
        σ (QuotientGroup.mk b) v = outerFixedAction S T a ha b v) ∧
      generatedCore σ 2 = ⊤ := by
  let := S.finite_group
  let := actor_elementary S T 2
  let a₀ : A2 S T := ⟨a,ha⟩
  let K := Subgroup.zpowers a₀
  let ρ := outerFixedAction S T a ha
  have hfix (v : elementFixed S a) : v ∈ fixedSpace ρ K := by
    rw [mem_fixedSpace_zpowers_iff]
    apply Subtype.ext
    exact (mem_elementFixed S a v).mp v.property
  let : Representation.IsTrivial (ρ.comp K.subtype) := ⟨fun b => by
    ext v
    exact congrArg Subtype.val (hfix v b)⟩
  let σ := ρ.ofQuotient K
  let f : B2 S T →* (A2 S T) ⧸ K :=
    (QuotientGroup.mk' K).comp (Subgroup.inclusion inf_le_left)
  have hqa : QuotientGroup.mk' K a₀ = 1 := (QuotientGroup.eq_one_iff a₀).mpr (Subgroup.mem_zpowers a₀)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨b,rfl⟩ := QuotientGroup.mk_surjective q
    by_cases hb : (b : M) ∈ componentLayer M
    · exact ⟨⟨b,⟨b.property,hb⟩⟩,rfl⟩
    · have haL : a ∉ componentLayer M := fun h => haB ⟨ha,h⟩
      have hi : (b : M) * a⁻¹ ∈ componentLayer M := by
        apply (group_inner_iff S T _).mp
        rw [map_mul, map_inv]
        apply (Subgroup.mul_mem_iff_of_index_two BinaryNaturalDual.FourActors.inner_index).mpr
        exact iff_of_false (fun h => hb ((group_inner_iff S T _).mp h))
          (fun h => haL ((group_inner_iff S T _).mp ((BinaryNaturalDual.FourActors.inner.inv_mem_iff).mp h)))
      refine ⟨⟨(b : M) * a⁻¹,⟨(A2 S T).mul_mem b.property ((A2 S T).inv_mem ha),hi⟩⟩,?_⟩
      change QuotientGroup.mk' K (b * a₀⁻¹) = QuotientGroup.mk' K b
      rw [map_mul, map_inv, hqa, inv_one, mul_one]
  let E := diagonalEquiv S T a (A2_outer_order S T a ha haB) (fun h => haB ⟨ha,h⟩)
  have hE (b : B2 S T) (u : S.natural) :
      E (naturalB2Action S T b u) = σ (f b) (E u) := by
    apply Subtype.ext
    change (E (naturalB2Action S T b u) : V) = S.representation b (E u : V)
    rw [diagonalEquiv_apply, diagonalEquiv_apply, map_add]
    change S.representation b u + S.representation a (S.representation b u) =
      S.representation b u + S.representation b (S.representation a u)
    congr 1
    have hc : Commute (a : M) (b : M) :=
      congrArg Subtype.val (mul_comm' (⟨a,ha⟩ : A2 S T) (⟨b,b.property.1⟩ : A2 S T))
    exact congrArg (fun t : Module.End (ZMod 2) V => t u) (hc.map S.representation).eq
  have hσ : generatedCore σ 2 = ⊤ := by
    rw [← generatedCore_map_surjective (naturalB2Action S T) σ f hf E hE,
      naturalB2_core]
    simp
  refine ⟨?_,σ,fun _ _ => rfl,hσ⟩
  have he := generatedCore_map_surjective ρ σ (QuotientGroup.mk' K)
    (QuotientGroup.mk'_surjective K) (LinearEquiv.refl (ZMod 2) (elementFixed S a))
    (fun _ _ => rfl) 2
  simpa only [LinearEquiv.refl_toLinearMap, Submodule.map_id, hσ] using he
end CFSG.Quasithin.ChapterH.NaturalDual.SourceFourActors
