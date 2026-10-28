module
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.NormalComponentConstituents

/-!
# Best offenders inside a normal actor

Conjugation preserves best offenders, including those contained in a fixed
normal subgroup. Thus its offender subgroup has normal image in the full
acting group. In a faithful irreducible representation, a nontrivial such
image has zero fixed space. The conclusion keeps the literal restricted
action and its invariants, so subsequent fixed-space quotients have a proved
zero kernel.

Source: Aschbacher–Smith B.1.7, pp.70–71, and the quiet branch of 10.1.1.
The application is the actual Suzuki orbit centralizer in Chapter 10.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem normal_restriction_offender_image
    (ρ : Representation (ZMod 2) G V) (C : Subgroup G) [C.Normal] :
    ((offenderSubgroup (ρ.comp C.subtype)).map C.subtype).Normal := by
  let N := offenderSubgroup (ρ.comp C.subtype)
  refine ⟨fun n hn g => ?_⟩
  have hle : (N.map C.subtype).map (MulAut.conj g).toMonoidHom ≤ N.map C.subtype := by
    dsimp only [N,offenderSubgroup,generatedBy]
    rw [Subgroup.map_iSup,Subgroup.map_iSup]
    apply iSup_le
    intro A
    rw [Subgroup.map_iSup,Subgroup.map_iSup]
    apply iSup_le
    intro hA
    let B := (A.map C.subtype).map (MulAut.conj g).toMonoidHom
    have hB : IsBestOffender ρ B := (hA.1.map_subtype ρ).map_conj ρ g
    have hBC : B ≤ C := by
      rintro x ⟨a,⟨y,hy,rfl⟩,rfl⟩
      exact (inferInstance : C.Normal).conj_mem y y.property g
    have hBN := (hB.subgroupOf ρ hBC).le_offenderSubgroup (ρ.comp C.subtype)
    have hh := map_mono (f := C.subtype) hBN
    rw [map_subgroupOf_eq_of_le hBC] at hh
    simpa only [N,offenderSubgroup,generatedBy,Subgroup.map_iSup] using hh
  exact hle (mem_map_of_mem _ hn)

theorem normal_restriction_offender_fixed_eq_bot
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (hi : ρ.IsIrreducible) (C : Subgroup G) [C.Normal]
    (hne : offenderSubgroup (ρ.comp C.subtype) ≠ ⊥) :
    Representation.invariants (ρ.comp (C.subtype.comp (offenderSubgroup (ρ.comp C.subtype)).subtype)) = ⊥ := by
  let N := offenderSubgroup (ρ.comp C.subtype)
  let H := N.map C.subtype
  let : H.Normal := normal_restriction_offender_image ρ C
  have hH : H ≠ ⊥ := by
    intro h
    exact hne ((map_eq_bot_iff_of_injective _ C.subtype_injective).mp h)
  have hz := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi H hH
  change fixedSpace (ρ.comp C.subtype) N = ⊥
  rw [fixedSpace_comp_map]
  exact hz
end Representation.BinaryOffender
