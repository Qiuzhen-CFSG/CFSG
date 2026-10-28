module
public import Theory.GroupTheory.ReducedNormal.IrreducibleClosure
public import Theory.GroupTheory.PCoreSurjective
/-!
# Lifting an irreducible section's normal closure

A nonzero elementary section normalized by a Sylow overgroup has a reduced
normal closure in the quotient. Its full preimage control gives containment
of the original normal closure in the two-core, and its commutator with that
core lies in the original denominator. No part of the denominator is removed.

The proof uses the irreducible-closure theorem and lifts the quotient two-core
through the two-group kernel. The application is the central section in
Aschbacher–Smith 8.2.12, first paragraph, printed p.722, refs/quasithin.pdf.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The literal normal closure lies in the two-core and centralizes it modulo
the given normal denominator. Its quotient image is reduced elementary abelian. -/
theorem normalClosure_core_of_irreducible_section
    (Z W A : Subgroup G) [Z.Normal] (T : Sylow 2 G)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (he : IsElementaryAbelian 2 W) (hZW : Z < W)
    (hWT : W ≤ T) (hTA : (T : Subgroup G) ≤ A)
    (hAW : A ≤ normalizer (W : Set G))
    (hirr : ∀ U : Subgroup G, Z ≤ U → U ≤ W → A ≤ normalizer (U : Set G) →
      U = Z ∨ U = W) :
    IsPReduced 2 ((normalClosure (W : Set G)).map (QuotientGroup.mk' Z)) ∧
      normalClosure (W : Set G) ≤ pCore 2 G ∧
      ⁅normalClosure (W : Set G),pCore 2 G⁆ ≤ Z := by
  let q := QuotientGroup.mk' Z
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective Z
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    let := he
    exact (IsElementaryAbelian.isPGroup 2 W).to_le hZW.le
  have hred := isPReduced_normalClosure_image_of_irreducible q hq W A T hchar he
    (by simpa only [q,QuotientGroup.ker_mk'] using hZW.le)
    (by simpa only [q,QuotientGroup.ker_mk'] using hZW.ne)
    hWT hTA hAW (by simpa only [q,QuotientGroup.ker_mk'] using hirr)
  have hm : (normalClosure (W : Set G)).map q = normalClosure (W.map q : Set (G ⧸ Z)) :=
    map_normalClosure _ q hq
  rw [←hm] at hred
  refine ⟨hred,?_,?_⟩
  · have hh := map_le_iff_le_comap.mp hred.le_pCore
    rwa [q.comap_pCore_of_ker_isPGroup hq hk] at hh
  · have hcore : (pCore 2 G).map q ≤ pCore 2 (G ⧸ Z) :=
      le_sSup ⟨Normal.map inferInstance q hq,pCore_isPGroup.map q⟩
    have hh : (⁅normalClosure (W : Set G),pCore 2 G⁆).map q = ⊥ := by
      rw [map_commutator]
      exact commutator_eq_bot_iff_le_centralizer.mpr
        (hred.le_centralizer_pCore.trans (centralizer_le hcore))
    have hh := (Subgroup.map_eq_bot_iff _).mp hh
    simpa only [q,QuotientGroup.ker_mk'] using hh
end Theory.GroupTheory
