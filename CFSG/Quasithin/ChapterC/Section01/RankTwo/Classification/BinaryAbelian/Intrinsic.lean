module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic

/-!
# Intrinsic natural quotients of abelian binary MS cores

The actual ambient commutator core is identified with the intrinsic block
commutator through its inclusion. The source natural quotient then descends
to the exact quotient by the component's fixed subgroup, retaining its
conjugation formula and the common quotient marking. The proved MS recognition
and fixed-kernel bounds give multiplicity one or two without a splitting.

Source: Aschbacher–Smith C.1.34(1),(2),(5), printed pp.136–137.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)

noncomputable def Input.intrinsicCoreEquiv : blockU L ≃* commutatorCore L :=
  ((blockU L).equivMapOfInjective L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr h.commutatorCore_eq_internal.symm)

@[simp] theorem Input.intrinsicCoreEquiv_val (x : blockU L) :
    (h.intrinsicCoreEquiv x : J) = ((x : L) : J) := rfl

theorem Input.intrinsicCoreEquiv_conjugate (l : L) (x : blockU L) :
    h.intrinsicCoreEquiv (blockConjugate L l x) =
      h.coreConjugate l (h.intrinsicCoreEquiv x) := by
  apply Subtype.ext
  rw [h.intrinsicCoreEquiv_val, h.coreConjugate_val, h.intrinsicCoreEquiv_val]
  rfl

namespace AbelianCore.NaturalQuotient
variable {h} {m : ℕ} (q : AbelianCore.NaturalQuotient h m)

noncomputable def intrinsicProjection : blockU L →* Multiplicative (Fin m → Fin 3 → ZMod 2) :=
  q.projection.comp h.intrinsicCoreEquiv.toMonoidHom

theorem intrinsicProjection_surjective : Function.Surjective q.intrinsicProjection :=
  q.surjective.comp h.intrinsicCoreEquiv.surjective

theorem intrinsicProjection_kernel : q.intrinsicProjection.ker = blockFixed L := by
  ext x
  change q.projection (h.intrinsicCoreEquiv x) = 1 ↔ (x : L) ∈ center L
  change h.intrinsicCoreEquiv x ∈ q.projection.ker ↔ _
  rw [q.kernel]
  constructor
  · intro hx
    apply mem_center_iff.mpr
    intro l
    exact Subtype.ext ((mem_centralizer_iff.mp hx) l l.property)
  · intro hx
    apply mem_centralizer_iff.mpr
    intro l hl
    exact congrArg Subtype.val ((mem_center_iff.mp hx) ⟨l,hl⟩)

theorem intrinsicProjection_conjugate (l : L) (x : blockU L) (i : Fin m) :
    (q.intrinsicProjection (blockConjugate L l x)).toAdd i =
      Representation.specialLinearNatural 3
        (q.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l))
        ((q.intrinsicProjection x).toAdd i) := by
  change (q.projection (h.intrinsicCoreEquiv (blockConjugate L l x))).toAdd i = _
  rw [h.intrinsicCoreEquiv_conjugate]
  exact q.equivariant l _ i

noncomputable def intrinsicModuleEquiv : BlockModule L ≃*
    Multiplicative (Fin m → Fin 3 → ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq q.intrinsicProjection_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q.intrinsicProjection
      q.intrinsicProjection_surjective)

@[simp] theorem intrinsicModuleEquiv_mk (x : blockU L) :
    q.intrinsicModuleEquiv (QuotientGroup.mk' (blockFixed L) x) =
      q.intrinsicProjection x := rfl

end AbelianCore.NaturalQuotient

include h in
/-- Source coordinates on the original intrinsic core; no ambient splitting is used. -/
theorem Input.abelian_intrinsic_natural_quotient
    (hc : IsMulCommutative (commutatorCore L)) :
    ∃ (m : ℕ) (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
      (f : blockU L →* Multiplicative (Fin m → Fin 3 → ZMod 2)),
      (m = 1 ∨ m = 2) ∧ Function.Surjective f ∧ f.ker = blockFixed L ∧
      (∀ l x i, (f (blockConjugate L l x)).toAdd i =
        Representation.specialLinearNatural 3 (e (QuotientGroup.mk' (pCore 2 L) l))
          ((f x).toAdd i)) ∧
      Nat.card (blockFixed L) ≤ 2 ∧ (m = 2 → Nat.card (blockFixed L) = 1) := by
  obtain ⟨m, hm, ⟨q⟩⟩ := AbelianCore.QuotientRecognition.Input.exists_abelianCore_naturalQuotient
    (h := h) hc
  have hk := h.abelianCore_fixedKernel_bounds hc hm q
  have he : (coreFixed L).comap h.intrinsicCoreEquiv.toMonoidHom = blockFixed L := by
    rw [← q.kernel]
    exact q.intrinsicProjection_kernel
  have hcK : Nat.card (blockFixed L) = Nat.card (coreFixed L) := by
    rw [← he]
    rw [Subgroup.comap_equiv_eq_map_symm']
    exact (Nat.card_congr (h.intrinsicCoreEquiv.symm.subgroupMap (coreFixed L)).toEquiv).symm
  exact ⟨m, q.quotientEquiv, q.intrinsicProjection, hm, q.intrinsicProjection_surjective,
    q.intrinsicProjection_kernel, q.intrinsicProjection_conjugate,
    hcK.symm ▸ hk.1, fun h2 => hcK.trans (hk.2 h2)⟩

end CFSG.Quasithin.ChapterC.BinaryMS
