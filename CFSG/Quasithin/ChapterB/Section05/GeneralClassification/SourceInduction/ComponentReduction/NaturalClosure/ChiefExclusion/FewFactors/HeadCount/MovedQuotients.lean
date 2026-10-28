module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.MovedHead
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.HeadCount.DualMultiplicity

/-!
# Central quotients of the moved module

For a perfect L, every invariant linear map from W = [V,L] to a trivial
module vanishes. For each v, applying that map to l·v-v gives a homomorphism
from L to an additive abelian group, hence zero. Those displacements span W.
Consequently every simple quotient of W is noncentral. The argument uses
neither the second component's cross action nor any semisimplicity of W.
Semisimplicity of the literal head then excludes central submodules of that
head, by splitting off its fixed space and pulling the projection back to W.

Source: Aschbacher–Smith, B.5.9, printed p.108, the c = 2 centralizer
argument (1 March 2004 manuscript).
-/

@[expose] public section

open Representation Representation.BinaryOffender Subgroup
open scoped MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors.HeadCount
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false
variable {G V S : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup S] [Module (ZMod 2) S]
  (ρ : Representation (ZMod 2) G V)

/-- Perfectness kills every invariant linear map from the actual moved space. -/
theorem moved_map_to_trivial_eq_zero (L : Subgroup G) [Group.IsPerfect L]
    (a : moved ρ L →ₗ[ZMod 2] S)
    (hc : ∀ (l : L) w, a (componentAction ρ L l w) = a w) : a = 0 := by
  let δ (v : V) (l : L) : moved ρ L :=
    ⟨ρ l v - v, Submodule.subset_span ⟨l, l.property, v, Submodule.mem_top, rfl⟩⟩
  have hd (v : V) (x y : L) :
      δ v (x * y) = componentAction ρ L x (δ v y) + δ v x := by
    apply Subtype.ext
    change ρ (x * y : G) v - v = ρ x (ρ y v - v) + (ρ x v - v)
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel
  have hz (v : V) (l : L) : a (δ v l) = 0 := by
    let t : L →* Multiplicative S := {
      toFun l := Multiplicative.ofAdd (a (δ v l))
      map_one' := by
        change a (δ v 1) = 0
        have he : δ v 1 = 0 := by
          apply Subtype.ext
          change ρ (1 : G) v - v = 0
          simp
        rw [he, map_zero]
      map_mul' x y := by
        change a (δ v (x * y)) = a (δ v x) + a (δ v y)
        rw [hd, map_add, hc, add_comm] }
    let : Group.IsPerfect t.range := Group.IsPerfect.range t
    exact congrArg (fun x : t.range => Multiplicative.toAdd x.val)
      (Subsingleton.elim (⟨t l, l, rfl⟩ : t.range) 1)
  have hzero (v : V) (hv : v ∈ moved ρ L) : a ⟨v, hv⟩ = 0 := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, hl, w, _, rfl⟩ := hv
      exact hz w ⟨l, hl⟩
    | zero => exact map_zero a
    | add x y hx hy ihx ihy =>
      change a (⟨x, hx⟩ + ⟨y, hy⟩) = 0
      rw [map_add, ihx, ihy, add_zero]
    | smul c x hx ih =>
      change a (c • ⟨x, hx⟩) = 0
      rw [map_smul, ih, smul_zero]
  exact LinearMap.ext fun w => hzero w w.property

/-- A maximal quotient of the moved module is noncentral. -/
theorem moved_coatom_quotient_ne_one {L : Subgroup G}
    (hL : Theory.GroupTheory.IsComponent G L)
    (N : Subrepresentation (componentAction ρ L)) (hN : IsCoatom N) :
    N.quotientRepresentation ≠ 1 := by
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  intro ht
  have hzero := moved_map_to_trivial_eq_zero ρ L N.toSubmodule.mkQ (by
    intro l w
    exact DFunLike.congr_fun (DFunLike.congr_fun ht l) (N.toSubmodule.mkQ w))
  have hall : N.toSubmodule = ⊤ := by
    apply top_unique
    intro w _
    apply (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp
    exact DFunLike.congr_fun hzero w
  exact hN.1 (Subrepresentation.toSubmodule_injective hall)

/-- The semisimple head has no central constituents: its fixed space is zero. -/
theorem head_fixedSpace_eq_bot [Module.Finite (ZMod 2) V] {L : Subgroup G}
    (hL : Theory.GroupTheory.IsComponent G L) :
    fixedSpace (Head.representation (componentAction ρ L)) ⊤ = ⊥ := by
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  let τ := componentAction ρ L
  let η := Head.representation τ
  let : IsSemisimpleModule (ZMod 2)[L] η.asModule := head_semisimple τ
  let Z : Subrepresentation η := {
    toSubmodule := fixedSpace η ⊤
    apply_mem_toSubmodule l v hv := by
      have he : η l v = v := hv ⟨l, mem_top _⟩
      rwa [he] }
  let Zm := Z.asSubmodule
  obtain ⟨r, hr⟩ := IsSemisimpleModule.extension_property (R := (ZMod 2)[L])
    (M := η.asModule) (N := Zm) (P := Zm) Zm.subtype Zm.subtype_injective
    (LinearMap.id : Zm →ₗ[(ZMod 2)[L]] Zm)
  let a : moved ρ L →ₗ[ZMod 2] Zm := (r.comp (headMap τ)).restrictScalars (ZMod 2)
  have ha : a = 0 := moved_map_to_trivial_eq_zero ρ L a (by
    intro l w
    have he := (r.comp (headMap τ)).map_smul
      (MonoidAlgebra.single l (1 : ZMod 2)) (τ.asModuleEquiv.symm w)
    simp only [Representation.single_smul, one_smul] at he
    change a (componentAction ρ L l w) = a w
    rw [show a (componentAction ρ L l w) =
      (MonoidAlgebra.single l (1 : ZMod 2)) • a w from he]
    apply Subtype.ext
    change (MonoidAlgebra.single l (1 : ZMod 2)) • (a w).val = (a w).val
    rw [Representation.single_smul, one_smul]
    exact (a w).property ⟨l, mem_top _⟩)
  have hrzero : r = 0 := by
    ext w
    obtain ⟨v, rfl⟩ := headMap_surjective τ w
    exact congrArg Subtype.val (DFunLike.congr_fun ha v)
  apply le_bot_iff.mp
  intro v hv
  have he := DFunLike.congr_fun hr (⟨v, hv⟩ : Zm)
  rw [hrzero] at he
  exact congrArg Subtype.val he.symm


end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors.HeadCount
