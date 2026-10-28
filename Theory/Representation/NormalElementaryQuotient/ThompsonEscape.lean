module
public import Theory.Representation.NormalElementaryQuotient.Thompson

/-!
# Failure of factorization from Thompson normalizer control

Let H escape a subgroup M of the ambient finite group, while the normalizer
of the embedded elementary Thompson subgroup J(S) lies in M. A normal
elementary subgroup of H with a two-group centralizer must be an FF-module
for its literal centralizer quotient. Otherwise Thompson heredity makes
J(S) normal in H, contradicting the escape.

Source: Aschbacher--Smith, B.2.5--7, printed p.76. The source small-Thompson
branch of 12.6.14, printed p.826, supplies the normalizer-control application.
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace Representation.NormalElementaryQuotient
variable {G : Type*} [Group G] [Finite G]

/-- Ambient Thompson normalizer control forces an FF action when the centralizer is a two-group. -/
theorem ff_of_thompson_normalizer_escape (H M : Subgroup G) (S : Sylow 2 H)
    (E : Subgroup H) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : IsPGroup 2 (centralizer (E : Set H)))
    (hHM : ¬ H ≤ M)
    (hN : normalizer ((elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype : Set G) ≤ M) :
    Representation.BinaryOffender.IsFFModule
      (representation E (QuotientGroup.mk' (centralizer (E : Set H)))
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)) := by
  by_contra hn
  let f := QuotientGroup.mk' (centralizer (E : Set H))
  have hker : IsPGroup 2 f.ker := by rwa [QuotientGroup.ker_mk']
  let : (elementaryAbelianMaxJ (S : Subgroup H)).Normal :=
    thompson_normal_of_nonFF S E f (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) hker
      ((IsElementaryAbelian.isPGroup 2 E).le_sylow_of_normal S) hn
  apply hHM
  apply le_trans _ hN
  simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
    (elementaryAbelianMaxJ (S : Subgroup H)).le_normalizer_map H.subtype
end Representation.NormalElementaryQuotient
