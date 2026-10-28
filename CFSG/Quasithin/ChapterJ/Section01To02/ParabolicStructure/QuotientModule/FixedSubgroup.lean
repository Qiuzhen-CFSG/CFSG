module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.Natural
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.QuotientModule.FixedPlane

/-!
# The fixed-subgroup equality in J.2.2(3)

The established trivial K-action on HC/U gives one inclusion. Conversely,
a K-fixed class in Q/U maps to a fixed vector in the marked natural Q/HC
module. The natural SL₂(4) action has zero fixed space, so the element lies
in HC. The result is stated as the exact ambient preimage of C_{Q/U}(K),
using commutators in U and the literal subgroup Q. The only earlier-source
premise is Q ≤ K from J.2.2(1).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(3), printed p.432 (PDF p.443).
-/

public section
open Subgroup Representation
open scoped commutatorElement
noncomputable section
namespace CFSG.Quasithin.ChapterJ
variable {G : Type*} [Group G] [Finite G]

/-- The exact ambient preimage specification of HC/U = C_{Q/U}(K). -/
theorem LocalSetup.mem_HC_iff_commutator_mem_U (d : LocalSetup G)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K) (q : G) :
    q ∈ d.toTypeRuSetup.HC ↔ q ∈ d.toTypeRuSetup.Q ∧
      ∀ k ∈ d.toTypeRuSetup.K, ⁅k, q⁆ ∈ d.toTypeRuSetup.U := by
  constructor
  · intro hq
    exact ⟨d.toTypeRuSetup.HC_le_Q hq,
      fun k hk => d.HC_commutator_K_mem_U ⟨q, hq⟩ ⟨k, hk⟩⟩
  · rintro ⟨hq, hfix⟩
    let n := d.naturalQuotientSection hQK
    let q₀ : d.toTypeRuSetup.Q := ⟨q, hq⟩
    have hcoord : (n.coordinates q₀).toAdd = 0 := by
      apply SL2FourNatural.natural_fixed_eq_zero
      intro g
      obtain ⟨k, rfl⟩ := d.toTypeRuSetup.naturalQuotientMap_surjective g
      let q' : d.toTypeRuSetup.Q := ⟨k * q * (k : G)⁻¹,
        (mem_normalizer_iff.mp (n.normalized k.property) q).mp hq⟩
      have he : n.coordinates (q' * q₀⁻¹) = 1 := by
        apply (n.coordinates_eq_one_iff _).mpr
        exact d.U_le_HC (hfix k k.property)
      rw [map_mul, map_inv, mul_inv_eq_one] at he
      have heq := n.equivariant k q₀
      exact heq.symm.trans (congrArg Multiplicative.toAdd he)
    exact (n.coordinates_eq_one_iff q₀).mp hcoord

end CFSG.Quasithin.ChapterJ
