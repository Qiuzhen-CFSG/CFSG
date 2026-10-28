module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SpanProjection
public import Theory.SpecificGroups.PSL2.PrimePerfectCore

/-!
# Odd prime PSL₂ components are excluded by the source module

The actual perfect projection into an ordinary component has noncentral
two-core. Its image in an odd prime-field PSL₂ central quotient has trivial
two-core, so the original two-core lies in the central kernel. This
contradicts that projection. The field of order three is included through
the model theorem's nonsolvability argument.

This is the odd prime-field obstruction in Aschbacher–Smith C.3.3,
printed p.149, on the literal C.2.8 hypotheses and quotient map.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G]
variable {H M L R V : Subgroup G}

/-- Odd prime-field PSL₂ cannot be the central quotient of an ordinary
component in the genuine C.2.8 configuration. -/
theorem no_ordinary_component_prime_psl2_central_quotient
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p)
    (e : K ⧸ center K ≃* PSL(2,F)) : False := by
  apply h.no_ordinary_component_of_perfect_subgroup_core_central K hK
  intro P hPK hP
  let := hP
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hker : q.ker ≤ center K := by
    intro k hk
    change e (QuotientGroup.mk k) = 1 at hk
    exact (QuotientGroup.eq_one_iff k).mp (e.injective (by simpa only [map_one] using hk))
  have hcore := Theory.PSL2.prime_perfect_hom_twoCore_le_ker ho hF
    (q.comp (inclusion hPK))
  apply commutator_eq_bot_iff_le_centralizer.mpr
  rintro x ⟨u,hu,rfl⟩ y hy
  have hz : inclusion hPK u ∈ center K := hker (hcore hu)
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y,hPK hy⟩)

/-- The source's `IsPSL` marking supplies the same exclusion without any
additional lower bound on its odd prime parameter. -/
theorem no_ordinary_component_prime_psl2_model
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (K : Subgroup H) (hK : IsComponent H K)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL (K ⧸ center K) 2 p) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  exact h.no_ordinary_component_prime_psl2_central_quotient K hK ho hF e

end CFSG.Quasithin.ChapterC.HypothesisC28
