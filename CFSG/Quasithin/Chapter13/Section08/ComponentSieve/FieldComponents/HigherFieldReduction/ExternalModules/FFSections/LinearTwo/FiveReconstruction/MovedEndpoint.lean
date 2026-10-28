module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction.MovedAction
public import Theory.Representation.SubrepresentationDisplacement
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryPermutation.FiveTensorSylow
public import Theory.Representation.BinaryPermutation.FiveTensorTransvections

/-!
# The exceptional contradiction on the actual moved module

Inclusion W → U injects displacement images. A rank-one displacement on U
would therefore have rank at most one on the faithful tensor module W,
forcing its actor to be the identity. This proves the no-transvection
antecedent of exactly 13.8.18(4) on the original source carrier U.

The actual H-conjugation γ → α preserves the rank lower bound and transports
the given quadraticity. Restricting that quadraticity to W bounds the actual
subgroup Vα* ≤ T₀* ≤ K* by two, using an actual Sylow subgroup of K*. Its
action injection is also proved explicitly from the pointwise K* marking.
This contradicts the earlier rank lower bound, without requiring W = U.

Source: Aschbacher–Smith, 13.8.8(2), 13.8.18(4), and the proof of 13.8.20,
printed pp.949, 953–954 (combined manuscript, 1 March 2004).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open BinaryPermutation.FiveTensorQuadratic
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction

namespace FullCoordinates
variable {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {K : Subgroup D} {s : Equiv.Perm (Fin 3) →* D}

/-- The full ambient action has no transvections even if W is proper in U. -/
theorem no_transvection_on_ambient [Module.Finite (ZMod 2) U]
    (W : Subrepresentation ρ) (c : FullCoordinates W.toRepresentation K s) (g : D) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1 := by
  intro hr
  have hle := (W.finrank_displacement_le g).trans hr.le
  have hg := BinaryPermutation.FiveTensorTransvections.eq_one_of_displacement_le_one
    c.groupEquiv W.toRepresentation c.moduleEquiv c.equivariant g hle
  rw [hg, map_one] at hr
  change Module.finrank (ZMod 2) (LinearMap.range (1 - 1 : U →ₗ[ZMod 2] U)) = 1 at hr
  rw [sub_self, LinearMap.range_zero, finrank_bot] at hr
  exact Nat.zero_ne_one hr

/-- Both the kernel assertion and the cardinal bound concern the literal actor
A, rather than just its action image. -/
theorem quadratic_actor_bound [Finite D] [K.Normal]
    (c : FullCoordinates ρ K s) (P : Sylow 2 K) (A : Subgroup D)
    (hAP : A ≤ (P : Subgroup K).map K.subtype) (hq : IsQuadratic ρ A) :
    Function.Injective (ρ.comp A.subtype) ∧ Nat.card A ≤ 2 := by
  have hAK : A ≤ K := by
    intro a ha
    obtain ⟨k, _, he⟩ := hAP ha
    exact he ▸ k.property
  refine ⟨c.actor_injective A hAK, ?_⟩
  let w : BinaryPermutation.core (Fin 3) :=
    BinaryPermutation.FiveTensorTransvections.Coordinates.coreVector 2 0
  have hw : w ≠ 0 := by
    intro hw
    have he := congrArg (fun v : BinaryPermutation.core (Fin 3) => v.val 0) hw
    exact one_ne_zero he
  exact tensor_card_le_two_in_sylow K c.groupEquiv c.map_component ρ
    (BinaryPermutation.coreRepresentation (Fin 3)) c.moduleEquiv c.equivariant
    w hw P A hAP hq
end FullCoordinates

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem starImage_conjugate (H V : Subgroup G) (hVH : V ≤ H) (y : H) :
    Source.starImage H (V.map (MulAut.conj (y : G)).toMonoidHom) =
      (Source.starImage H V).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 H) y)).toMonoidHom := by
  let q := QuotientGroup.mk' (pCore 2 H)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨v, hv, he⟩ := hx
    have hx : x = (MulAut.conj y) ⟨v, hVH hv⟩ := Subtype.ext he.symm
    subst x
    refine ⟨q ⟨v, hVH hv⟩, ⟨⟨v, hVH hv⟩, hv, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
    rfl
  · rintro _ ⟨v, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨(MulAut.conj y) x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]

/-- The adequate exceptional endpoint, retaining exactly the earlier
13.8.18(4) implication, the actual conjugating element and source placement.
Its no-transvection antecedent is discharged on U, and quadraticity is
restricted to the given invariant moved module W. -/
theorem tensor_branch_impossible_on_moved
    (H K L₁ V₃ V₁ Vγ Vα T₀ : Subgroup G) (T : Sylow 2 G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    [(Source.starImage H K).Normal]
    (s : Equiv.Perm (Fin 3) →* Source.Hstar H)
    (W : Subrepresentation ρ)
    (hρ : SeedAction.IsConjugation H V₃ V₁ ρ)
    (hH : H = K ⊔ L₁ ⊔ (T : Subgroup G))
    (c : FullCoordinates W.toRepresentation (Source.starImage H K) s)
    (earlier_13_8_18_4 : SeedAction.IsConjugation H V₃ V₁ ρ →
      H = K ⊔ L₁ ⊔ (T : Subgroup G) →
      (∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) →
      1 < rank (Source.starImage H Vγ))
    (hVγH : Vγ ≤ H) (h : H)
    (hconj : Vγ.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hplace : Source.starImage H Vα ≤ Source.starImage H T₀)
    (hcore : Source.starImage H T₀ =
      (Source.starImage H L₁ ⊔ Source.starImage H (T : Subgroup G)).pCoreIn 2)
    (hT₀K : Source.starImage H T₀ ≤ Source.starImage H K)
    (hquad : IsQuadratic ρ (Source.starImage H Vγ)) : False := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hno := c.no_transvection_on_ambient W
  have hrank := earlier_13_8_18_4 hρ hH hno
  have hc := starImage_conjugate H Vγ hVγH h
  rw [hconj] at hc
  have hqa := quadratic_subrepresentation ρ W
    (quadratic_map_conj hquad (QuotientGroup.mk' (pCore 2 H) h))
  rw [← hc] at hqa
  have hrankα : 1 < rank (Source.starImage H Vα) := by
    rw [hc, rank, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact hrank
  have hp : IsPGroup 2 (Source.starImage H T₀) := by
    rw [hcore]
    exact isPGroup_pCoreIn 2 _
  have hp' : IsPGroup 2 ((Source.starImage H T₀).subgroupOf (Source.starImage H K)) :=
    hp.of_equiv (subgroupOfEquivOfLe hT₀K).symm
  obtain ⟨P, hP⟩ := hp'.exists_le_sylow
  have hAP : Source.starImage H Vα ≤
      (P : Subgroup (Source.starImage H K)).map (Source.starImage H K).subtype := by
    intro x hx
    exact ⟨⟨x, hT₀K (hplace hx)⟩, hP (hplace hx), rfl⟩
  have hsmall := (c.quadratic_actor_bound P (Source.starImage H Vα) hAP hqa).2
  have hlarge : 4 ≤ Nat.card (Source.starImage H Vα) :=
    (Nat.le_log_iff_pow_le (by decide) Nat.card_pos.ne').mp hrankα
  omega

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction
end
