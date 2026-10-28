module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction
public import Theory.Representation.BinaryPermutation.FiveTensorSylow
public import Theory.Representation.BinaryPermutation.FiveTensorTransvections

/-!
# The conditional S₅ × S₃ tensor contradiction in 13.8.20

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.8(2), 13.8.18(4), and the proof of 13.8.20, printed pp.949, 953–954
(PDF pp.966, 970–971), especially the external-X alternative (a).

The classified coordinates identify the literal H/O₂(H) action on U_H/V₁
with the tensor product of the binary five- and three-point cores, marking
K* as A₅ × 1 and X* as 1 × A₃. The intrinsic tensor calculation excludes
transvections, discharging the antecedent of the explicit earlier
13.8.18(4) implication. The same actual H-conjugation from γ to α transports
both quadraticity and the resulting rank lower bound.

The source equality T₀* = O₂(L₁*T*) makes T₀* a two-group. Its containment
in K* places it in an actual Sylow subgroup of K*. Compatible coordinates
and Sylow conjugacy construct a four-group with both double-transposition
marks. The tensor obstruction gives |Vα*| ≤ 2, contradicting its rank bound.
No Sylow order, marks, no-transvection premise, or rank-one conclusion is assumed.

This is the conditional tensor-branch endpoint. The FF-section assembly
must construct the classified coordinates and discharge the earlier source
inputs; this module does not assert all of 13.8.20. Conjugation uses the
project's left-action convention, with the supplied h chosen accordingly.
-/

@[expose] public section
open Subgroup TensorProduct Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SymmetricFive
open BinaryPermutation.FiveTensorQuadratic
variable {G : Type*} [Group G] [Finite G]

/-- Genuine compatible group and module coordinates for the exceptional tensor branch.
The actor and module are the literal source quotient and additive carrier. -/
structure Coordinates (H K X V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁)) where
  groupEquiv : Source.Hstar H ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)
  moduleEquiv : SeedAction.Space H V₃ V₁ ≃ₗ[ZMod 2]
    BinaryPermutation.FiveTensorTransvections.Space
  equivariant : ∀ g v, moduleEquiv (ρ g v) =
    BinaryPermutation.FiveTensorTransvections.action (groupEquiv g) (moduleEquiv v)
  component_mark : (Source.starImage H K).map groupEquiv.toMonoidHom =
    (alternatingGroup (Fin 5)).prod ⊥
  cubic_mark : (Source.starImage H X).map groupEquiv.toMonoidHom =
    (⊥ : Subgroup (Equiv.Perm (Fin 5))).prod (alternatingGroup (Fin 3))

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

/-- Exclude the tensor branch using the source conjugate endpoint.
The earlier 13.8.18(4) implication retains its standing conjugation action and
H = KL₁T hypotheses; its no-transvection antecedent is proved here.
The α endpoint is the supplied actual conjugate of γ inside H. -/
theorem tensor_branch_impossible
    (H K L₁ X V₃ V₁ Vγ Vα T₀ : Subgroup G) (T : Sylow 2 G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (hρ : SeedAction.IsConjugation H V₃ V₁ ρ)
    (hH : H = K ⊔ L₁ ⊔ (T : Subgroup G))
    (c : Coordinates H K X V₃ V₁ ρ)
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
  have hno := BinaryPermutation.FiveTensorTransvections.no_transvection
    c.groupEquiv ρ c.moduleEquiv c.equivariant
  have hrank := earlier_13_8_18_4 hρ hH hno
  have hc := starImage_conjugate H Vγ hVγH h
  rw [hconj] at hc
  have hqa := quadratic_map_conj hquad (QuotientGroup.mk' (pCore 2 H) h)
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
  let w : BinaryPermutation.core (Fin 3) :=
    BinaryPermutation.FiveTensorTransvections.Coordinates.coreVector 2 0
  have hw : w ≠ 0 := by
    intro hw
    have he := congrArg (fun v : BinaryPermutation.core (Fin 3) => v.val 0) hw
    exact one_ne_zero he
  have hsmall := tensor_card_le_two_in_sylow (Source.starImage H K)
    c.groupEquiv c.component_mark ρ (BinaryPermutation.coreRepresentation (Fin 3))
    c.moduleEquiv c.equivariant w hw P (Source.starImage H Vα) hAP hqa
  have hlarge : 4 ≤ Nat.card (Source.starImage H Vα) :=
    (Nat.le_log_iff_pow_le (by decide) Nat.card_pos.ne').mp hrankα
  omega
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SymmetricFive

end
