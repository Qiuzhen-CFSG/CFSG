module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.BorelSourceSemisimple
public import Theory.GroupTheory.NormalSubgroupCoreQuotient

/-!
# The actual Suzuki component in H/O₂(H)

A normal subgroup A≤H has O₂(A)=A∩O₂(H). Transporting the first isomorphism
theorem through the literal subgroup inclusion identifies A/O₂(A) with A*,
the original image in H*. Both the binary section representation and its
scalar extension agree exactly through this equivalence.

Consequently an elementary actor in H* can be used directly on A*: no
elementary lift to H is assumed. Any marking of A/O₂(A) gives the same
marked source representation when transported to A*.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), §13.6,
printed pp.934--935, and the source H* convention of Notation 13.5.8.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open Section08 Ratio BenderSuzuki.MatrixGroups Representation
variable {G : Type*} [Group G] {H A : Subgroup G}
  (hAH : A ≤ H) (hHA : H ≤ normalizer (A : Set G))

/-- The intrinsic component quotient is its literal image in the source H*. -/
def sourceComponentStarEquiv (hAH : A ≤ H) (hHA : H ≤ normalizer (A : Set G)) :
    (A ⧸ pCore 2 A) ≃* Source.starImage H A := by
  let : (A.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHA
  let e := subgroupOfEquivOfLe hAH
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans
    (coreQuotientEquivImage 2 (A.subgroupOf H))

/-- The component equivalence uses exactly the ambient quotient representative. -/
theorem sourceComponentStarEquiv_mk (a : A) :
    (sourceComponentStarEquiv hAH hHA (QuotientGroup.mk' (pCore 2 A) a) : Source.Hstar H) =
      QuotientGroup.mk' (pCore 2 H) (inclusion hAH a) := by
  let : (A.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHA
  let e := subgroupOfEquivOfLe hAH
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hq : q.symm (QuotientGroup.mk' (pCore 2 A) a) =
      QuotientGroup.mk' (pCore 2 (A.subgroupOf H)) (e.symm a) := by
    apply q.injective
    rw [q.apply_symm_apply]
    change QuotientGroup.mk' (pCore 2 A) a = QuotientGroup.mk' (pCore 2 A) (e (e.symm a))
    rw [e.apply_symm_apply]
  change ((coreQuotientEquivImage 2 (A.subgroupOf H))
    (q.symm (QuotientGroup.mk' (pCore 2 A) a)) : Source.Hstar H) = _
  rw [hq, coreQuotientEquivImage_apply_mk]
  rfl

include hHA in
/-- Source normalization descends to actual normality inside H*. -/
theorem sourceComponentStar_normal : (Source.starImage H A).Normal := by
  let : (A.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHA
  exact Subgroup.Normal.map inferInstance (QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective (pCore 2 H))

variable {V₁ V₃ : Subgroup G} [IsElementaryAbelian 2 (Source.UH H V₃)]
  (hn : H ≤ normalizer (V₁ : Set G))
  (hk : commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H)
local instance sourceStarSpanCommGroup : CommGroup (Source.UH H V₃) := inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The source star action restricts to the original component quotient action. -/
theorem sourceComponentStar_representation (x : A ⧸ pCore 2 A) :
    starRepresentation H V₃ V₁ hn hk (sourceComponentStarEquiv hAH hHA x) =
      componentQuotientRepresentation hn hk hAH hHA x := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 A) x
  rw [sourceComponentStarEquiv_mk, starRepresentation_mk, componentQuotientRepresentation_mk]

set_option backward.isDefEq.respectTransparency false in
/-- Any component marking preserves the literal scalar-extended source action
when transported from A/O₂(A) to A*. -/
theorem sourceComponentStar_marked_representation
    {m : ℕ} (K : Type*) [Field K] [Algebra (ZMod 2) K]
    (f : SuzukiMatrixGroup m ≃* (A ⧸ pCore 2 A)) :
    ((extendScalars (F := ZMod 2) (G := Source.Hstar H) (V := Space H V₃ V₁) K
      (starRepresentation H V₃ V₁ hn hk)).comp (Source.starImage H A).subtype).comp
      (f.trans (sourceComponentStarEquiv hAH hHA)).toMonoidHom =
        markedExtendedComponentRepresentation hn hk hAH hHA K f := by
  apply MonoidHom.ext
  intro d
  change extendScalars (F := ZMod 2) (G := Source.Hstar H) (V := Space H V₃ V₁) K
      (starRepresentation H V₃ V₁ hn hk) (sourceComponentStarEquiv hAH hHA (f d)) =
    extendScalars (F := ZMod 2) (G := A ⧸ pCore 2 A) (V := Space H V₃ V₁) K
      (componentQuotientRepresentation hn hk hAH hHA) (f d)
  rw [extendScalars_apply, extendScalars_apply, sourceComponentStar_representation]

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
