module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.Interface
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
public import Theory.GroupTheory.PerfectCentralCover

/-!
# The literal component cover in the surviving Mathieu cases

Source: Aschbacher–Smith 1.1.5(3)(f), printed p.502, and 2.3.9(7),
printed pp.525–526. Relative component quasisimplicity makes the actual
map `L → L/O₂(L) → K` a perfect central cover. Its kernel is literally
`O₂(L)`. Once that kernel is proved trivial, the resulting model equivalence
has the same pointwise map; no replacement quotient or action is chosen.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory PerfectCentralCovering
variable {G K : Type*} [Group G] [Group K]
variable {H L M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The cover determined by the original component and its two-core quotient. -/
def LocalSetup.componentQuotientCover (h : LocalSetup H L M S z)
    (e : (L ⧸ pCore 2 L) ≃* K) : Cover L K := by
  letI := h.finite
  letI := h.quasisimple
  refine { toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
           surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)
           isPerfect := inferInstance
           ker_le_center := ?_ }
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact IsQuasisimple.pCore_le_center 2

/-- Identification with the exact quotient map from 1.1.5(3)(f). -/
theorem LocalSetup.componentQuotientCover_hom (h : LocalSetup H L M S z)
    (e : (L ⧸ pCore 2 L) ≃* K) :
    (h.componentQuotientCover e).toMonoidHom =
      e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)) := rfl

/-- The kernel being eliminated is the original component's two-core. -/
theorem LocalSetup.componentQuotientCover_ker (h : LocalSetup H L M S z)
    (e : (L ⧸ pCore 2 L) ≃* K) :
    (h.componentQuotientCover e).toMonoidHom.ker = pCore 2 L := by
  rw [h.componentQuotientCover_hom,
    MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

/-- Upgrade the original quotient map to an equivalence after the two-core
has been eliminated. The Mathieu-specific proofs supply `hcore`. -/
noncomputable def twoCoreQuotientEquiv (e : (L ⧸ pCore 2 L) ≃* K)
    (hcore : pCore 2 L = ⊥) : L ≃* K :=
  MulEquiv.ofBijective (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
    ⟨by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk', hcore],
     e.surjective.comp (QuotientGroup.mk'_surjective _)⟩

/-- The actual model equivalence retains the prescribed pointwise map. -/
theorem twoCoreQuotientEquiv_apply (e : (L ⧸ pCore 2 L) ≃* K)
    (hcore : pCore 2 L = ⊥) (x : L) :
    twoCoreQuotientEquiv e hcore x = e (QuotientGroup.mk' (pCore 2 L) x) := rfl

end CFSG.Quasithin.Chapter2.ComponentRefinement
end
