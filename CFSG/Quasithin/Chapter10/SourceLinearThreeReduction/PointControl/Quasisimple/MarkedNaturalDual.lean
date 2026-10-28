module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Quasisimple.CentralQuotient
public import Theory.Representation.BinaryConjugationSection.CentralKernelImage
public import Theory.Representation.BinaryConjugationSection.Restriction
public import Theory.Representation.PSL3Two.NaturalDualCentralizer

/-!
# The original natural-plus-dual section in a containing central quotient

Restriction to I and the actual projection through Z(I) preserve the exact
fixed kernel. The induced action uses the inverse of the already marked
isomorphism of two-core quotients, and agrees on every original representative.
Thus the model commutant calculation applies to this section, even for a
nonsplit extension with nonzero fixed vectors.

Source: Aschbacher--Smith 10.2.9, printed p.750. Other.JankoNaturalDual is
the point-component consumer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.PointControl.Quasisimple
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

theorem marked_natural_dual_section
    {I : Subgroup G} (hLI : L ≤ I) {H : Type*} [Group H] [Finite H]
    (eI : (I ⧸ center I) ≃* H)
    (dL : (L ⧸ pCore 2 L) ≃* SL(3,ZMod 2))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆
      (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
      (BinaryLinearThree.NaturalDual.action.comp
        (dL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    let q := eI.toMonoidHom.comp (QuotientGroup.mk' (center I))
    let B := (L.subgroupOf I).map q
    let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
    let π := dL.toMonoidHom.comp ((markedCoreQuotientEquiv D hLI eI).symm.toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 B)))
    Nonempty (BinaryConjugationSection B E (E ⊓ centralizer (B : Set H))
      (BinaryLinearThree.NaturalDual.action.comp π)) := by
  let q := eI.toMonoidHom.comp (QuotientGroup.mk' (center I))
  let B := (L.subgroupOf I).map q
  let E := ((⁅D.fullModule,L⁆).subgroupOf I).map q
  let π := dL.toMonoidHom.comp ((markedCoreQuotientEquiv D hLI eI).symm.toMonoidHom.comp
    (QuotientGroup.mk' (pCore 2 B)))
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect (L.subgroupOf I) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLI).symm.toMonoidHom)
    (subgroupOfEquivOfLe hLI).symm.surjective
  have hk : ((⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G)).subgroupOf I) =
      ((⁅D.fullModule,L⁆).subgroupOf I) ⊓ centralizer (L.subgroupOf I : Set I) := by
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun l hl => Subtype.ext (hc l hl)⟩
    · rintro ⟨hx,hc⟩
      exact ⟨hx,fun l hl => congrArg I.subtype (hc ⟨l,hLI hl⟩ hl)⟩
  let d0 := (d.subgroupOf I hLI).replaceKernel _ hk
  apply d0.exists_map_of_central_kernel q
  · intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    exact eI.injective (hx.trans (map_one eI).symm)
  · intro b
    change BinaryLinearThree.NaturalDual.action (π (q.subgroupMap (L.subgroupOf I) b)) =
      BinaryLinearThree.NaturalDual.action
        (dL (QuotientGroup.mk' (pCore 2 L) ((subgroupOfEquivOfLe hLI) b)))
    congr 1
    change dL ((markedCoreQuotientEquiv D hLI eI).symm
      (QuotientGroup.mk' (pCore 2 B) (markedLocalHom hLI eI
        ((subgroupOfEquivOfLe hLI) b)))) = _
    rw [←markedCoreQuotientEquiv_mk, MulEquiv.symm_apply_apply]
end CFSG.Quasithin.Chapter10.PointControl.Quasisimple
