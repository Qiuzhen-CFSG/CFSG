module
public import Theory.GroupTheory.FullAutomizerNormalizerControl
/-!
# Sylow promotion from a unique central involution

An ambient normalizer preserves the center and element orders. If a two-group
has exactly one central involution, its normalizer fixes that involution.
An odd relative index in the involution centralizer therefore makes the same
subgroup Sylow in the ambient group by the normalizer-index congruence.

Source: Aschbacher--Smith J.3.6, printed p.439; unlike the order-two-center
variant, this applies to the cyclic order-four center of C₄ wr C₂.
-/

public section
open Subgroup
namespace Subgroup

/-- The unique central involution forces the normalizer into its centralizer,
so a local odd index promotes the original two-subgroup to Sylow. -/
theorem exists_sylow_of_unique_central_involution
    {G : Type*} [Group G] [Finite G] (P : Subgroup G) (hP : IsPGroup 2 P)
    (z : P) (hz : orderOf z=2) (hzc : z∈center P)
    (hu : ∀ x:P, x∈center P → orderOf x=2 → x=z)
    (hi : ¬2∣P.relIndex (centralizer ({(z:G)} : Set G))) :
    ∃ S : Sylow 2 G, (S : Subgroup G)=P := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply exists_sylow_of_local_index P (centralizer ({(z:G)} : Set G)) hP hi
  intro g hg
  let a := P.normalizerMonoidHom ⟨g,hg⟩
  have hchar := characteristic_iff_map_le.mp (inferInstance : (center P).Characteristic) a
  have hza : a z∈center P := hchar (mem_map_of_mem a.toMonoidHom hzc)
  have he := hu (a z) hza ((a.orderOf_eq z).trans hz)
  have heG : g*(z:G)*g⁻¹=(z:G) := congrArg Subtype.val he
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp heG)

end Subgroup
