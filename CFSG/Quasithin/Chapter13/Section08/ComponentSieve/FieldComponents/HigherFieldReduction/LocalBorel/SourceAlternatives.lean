module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.InnerCase
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.SourceAssembly

/-!
# The full-product dichotomy with a Sylow inverter

The ordinary and covered calculations use J = BL₁, keeping the marked
X equal to L₁ or L₁,+ respectively. For the original t in T ∩ L, the
outer branch uses the proved torus fixation and small commutator bound.
In the inner branch actual X-normality kills O₂(X) in H*. The correction
s⁻¹t* from `InnerCase.inner_correction` lies in T* ∩ C_H*(K*) and still
inverts every element of X*, since s belongs to K* and X* centralizes K*.

The strengthened alternative is separate from the unchanged public
`BorelAlternative`. It retains precisely the extra membership required
by the full-product external-centralization argument. Neither a trivial
action of O₂(H) on V nor C ≤ K is assumed.

These are conditional assemblies over `CentralizingCalculation.SourceContext`.
That context still contains the preceding Borel normalization and placement.
The completed local calculations do not discharge those two fields; in
particular the source theorem cannot be inferred merely from this assembly.
`SourceAssembly` supplies placement from normalization and the universal
13.8.13 input, leaving normalization as an explicit source obligation.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954/PDF p.971;
Notation 13.2.1 and the earlier covered factorization 13.2.2(3).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel
open Components.Fitting TorusModels.Assembly CentralizingCalculation
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- The source external alternative retains an inverter in the actual Sylow image. -/
def SylowExternalXAlternative (H K T X : Subgroup G) : Prop :=
  ExternalXAlternative H K X ∧
    ∃ c ∈ Source.starImage H T ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)),
      ∀ x ∈ Source.starImage H X, c * x * c⁻¹ = x⁻¹

/-- The source dichotomy with the Sylow membership needed for external centralization. -/
def SylowBorelAlternative (H K T X : Subgroup G) (t : Source.Hstar H) : Prop :=
  SylowExternalXAlternative H K T X ∨ ExceptionalOuterAlternative.{u,v} H K t

omit [Finite G] in
theorem SylowBorelAlternative.borelAlternative {H K T X : Subgroup G} {t : Source.Hstar H}
    (h : SylowBorelAlternative.{u,v} H K T X t) : BorelAlternative.{u,v} H K X t :=
  h.elim (fun h => Or.inl h.1) Or.inr

/-- After the inner branch has lifted actual X-normality, the prescribed
inversion passes to X*. Correction by T* ∩ K* preserves it. -/
theorem sylowExternal_of_inner_external (H K T X : Subgroup G)
    [(Source.starImage H K).Normal] (hT : Chapter1.IsSylowIn 2 T H)
    (hX : ExternalXAlternative H K X) (t : H) (ht : t.val ∈ T)
    (hinv : ∀ x ∈ X, t.val * x * t.val⁻¹ * x ∈ X.pCoreIn 2)
    (hi : markedActor H K T t ht ∈ MulAut.innerSubgroup (Source.starImage H K)) :
    SylowExternalXAlternative H K T X := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := X.subgroupOf H
  have hnA : A.Normal := hX.2.2.2.1
  have hkill : ∀ z ∈ X.pCoreIn 2, ∀ hzH : z ∈ H, q ⟨z, hzH⟩ = 1 := by
    intro z hz hzH
    have he : (A.pCoreIn 2).map H.subtype = X.pCoreIn 2 := by
      rw [map_pCoreIn_of_injective 2 A H.subtype H.subtype_injective,
        map_subgroupOf_eq_of_le hX.1]
    have hzA : (⟨z, hzH⟩ : H) ∈ A.pCoreIn 2 :=
      (mem_map_iff_mem H.subtype_injective).mp (he ▸ hz)
    exact (QuotientGroup.eq_one_iff _).mpr
      ((pCoreIn_le_of_subnormal 2 hnA.isSubnormal) hzA)
  have htinv : ∀ x ∈ Source.starImage H X, q t * x * (q t)⁻¹ = x⁻¹ := by
    rintro _ ⟨x, hx, rfl⟩
    have hh := hkill _ (hinv x.val hx) (H.mul_mem (H.mul_mem
      (H.mul_mem t.property x.property) (H.inv_mem t.property)) x.property)
    change q (t * x * t⁻¹ * x) = 1 at hh
    rw [map_mul, map_mul, map_mul, map_inv] at hh
    exact mul_eq_one_iff_eq_inv.mp hh
  obtain ⟨s, hs, hc⟩ := InnerCase.inner_correction H K T hT t ht hi
  refine ⟨hX, s⁻¹ * q t, hc, ?_⟩
  intro x hx
  have hcomm : s * x = x * s := (hX.2.2.1 hx) s hs.2
  calc
    _ = s⁻¹ * (q t * x * (q t)⁻¹) * s := by group
    _ = s⁻¹ * x⁻¹ * s := by rw [htinv x hx]
    _ = x⁻¹ := by
      have hh : s⁻¹ * x⁻¹ = x⁻¹ * s⁻¹ := (Commute.inv_left hcomm).inv_right
      rw [hh, mul_assoc, inv_mul_cancel, mul_one]

namespace CentralizingCalculation.SourceContext
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] [(K.subgroupOf H).Normal]
  {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
local notation "D" => one L (T : Subgroup G) V₁
local notation "X" => plus L (T : Subgroup G) V₁

/-- The actual marked inner branch, retaining the Sylow inverter. -/
theorem sylowExternal_of_inner (Y : Subgroup G) (hmark : Y = D ∨ Y = X)
    (hcard : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G)) (hinv : InvertsTwoCoreQuotient Y t.val)
    (hi : markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1 ∈
      MulAut.innerSubgroup (Source.starImage H K)) :
    SylowExternalXAlternative H K (T : Subgroup G) Y := by
  obtain ⟨hY, hp, hn⟩ := InnerCase.marked_inputs L D (T : Subgroup G) V₁ Y rfl
    d.standing.normalizes_L d.standing.line_stable hmark
  have hS := InnerCase.sylow_normalization_of_borel_core H K D (T : Subgroup G) Y
    d.component_le d.sylow_H hY d.borel_normalized
    (InnerCase.model_residual_twoCore d.model d.degree (sourceSylow H K (T : Subgroup G) d.sylow_H))
  have he := InnerCase.external_of_normalizes_sylow H K D (T : Subgroup G) Y
    d.component_le d.one_le_H hY (by simpa only [sup_assoc] using d.generated)
    d.sylow_H inferInstance hp hn hcard hS (d.actorElement t) t.property.1 hinv.2 hi
  exact sylowExternal_of_inner_external H K (T : Subgroup G) Y d.sylow_H he
    (d.actorElement t) t.property.1 hinv.2 hi

/-- Full-product ordinary dichotomy for the prescribed inverter. -/
theorem sylowBorelAlternative_ordinary (a : NaturalSetup L (T : Subgroup G) V V₁)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G)) (hinv : InvertsTwoCoreQuotient D t.val) :
    SylowBorelAlternative.{u,v} H K (T : Subgroup G) D
      (QuotientGroup.mk' (pCore 2 H) (d.actorElement t)) := by
  classical
  by_cases hi : markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1 ∈
      MulAut.innerSubgroup (Source.starImage H K)
  · exact Or.inl (d.sylowExternal_of_inner D (Or.inl rfl)
      (source_residual_quotient_card a D rfl) t hinv hi)
  · exact Or.inr (d.exceptionalOuter_of_ordinary a t hi)

/-- Full-product covered dichotomy, keeping X=L₁,+ and the same actor. -/
theorem sylowBorelAlternative_covered (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : D = X ⊔ zero L)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G)) (hinv : InvertsTwoCoreQuotient X t.val) :
    SylowBorelAlternative.{u,v} H K (T : Subgroup G) X
      (QuotientGroup.mk' (pCore 2 H) (d.actorElement t)) := by
  classical
  by_cases hi : markedActor H K (T : Subgroup G) (d.actorElement t) t.property.1 ∈
      MulAut.innerSubgroup (Source.starImage H K)
  · exact Or.inl (d.sylowExternal_of_inner X (Or.inr rfl) (a.plus_core_card hfactor) t hinv hi)
  · exact Or.inr (d.exceptionalOuter_of_covered a hfactor t hi)

/-- The ordinary natural action supplies the marked inverter. -/
theorem exists_sylowBorelAlternative_ordinary (a : NaturalSetup L (T : Subgroup G) V V₁) :
    ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G), InvertsTwoCoreQuotient D t.val ∧
      SylowBorelAlternative.{u,v} H K (T : Subgroup G) D
        (QuotientGroup.mk' (pCore 2 H) (d.actorElement t)) := by
  obtain ⟨t, hinv, _⟩ := d.exists_marked_calculation_ordinary a
  exact ⟨t, hinv, d.sylowBorelAlternative_ordinary a t hinv⟩

/-- The covered action supplies the original inverter and its zero-direction fixation. -/
theorem exists_sylowBorelAlternative_covered (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : D = X ⊔ zero L) :
    ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G), InvertsTwoCoreQuotient X t.val ∧
      coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property.2⟩ = 1 ∧
      SylowBorelAlternative.{u,v} H K (T : Subgroup G) X
        (QuotientGroup.mk' (pCore 2 H) (d.actorElement t)) := by
  obtain ⟨t, hinv, hzero, _⟩ := d.exists_marked_calculation_covered a hfactor
  exact ⟨t, hinv, hzero, d.sylowBorelAlternative_covered a hfactor t hinv⟩
end CentralizingCalculation.SourceContext
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel
