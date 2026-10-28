module
public import Theory.Representation.BinaryOffender.SectionLinear
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RepresentationTheory.Irreducible

/-!
# A chief section exhausting the whole commutator

Intersect the numerator of a nontrivial irreducible section with the original
commutator. Its quotient map is nonzero, hence surjective. If the commutator's
dimension is bounded by the section's dimension, equality forces the entire
commutator into that numerator and makes the literal quotient map bijective.
This identifies the commutator without splitting the ambient representation
or discarding fixed layers. Normality retains the action of the full group.

Source application: Aschbacher–Smith, proof of 12.6.26, printed p.832.
-/
public section
set_option backward.isDefEq.respectTransparency false
namespace Representation.BinaryOffender
open Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- If a nontrivial irreducible section exhausts the dimension of the whole
commutator, its literal quotient map identifies that commutator with the section. -/
theorem coinvariants_section_bijective_of_finrank_le
    (ρ : Representation (ZMod 2) G V) (B : Subgroup G) [B.Normal]
    (U N : Subrepresentation ρ)
    [IsIrreducible ((sectionRepresentation ρ U N).comp B.subtype)]
    (hn : (sectionRepresentation ρ U N).comp B.subtype ≠ 1)
    (hd : Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp B.subtype)) ≤
      Module.finrank (ZMod 2) (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule)) :
    ∃ hle : Coinvariants.ker (ρ.comp B.subtype) ≤ N.toSubmodule,
      Function.Bijective ((sectionLower ρ U N).toSubmodule.mkQ.comp
        (Submodule.inclusion hle)) := by
  let M := Coinvariants.ker (ρ.comp B.subtype)
  let Q := N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule
  let τ := sectionRepresentation ρ U N
  let I : Subrepresentation N.toRepresentation := {
    toSubmodule := M.comap N.toSubmodule.subtype
    apply_mem_toSubmodule g v hv := Coinvariants.le_comap_ker ρ B g hv }
  let f : IntertwiningMap (I.toRepresentation.comp B.subtype) (τ.comp B.subtype) := {
    toLinearMap := (sectionLower ρ U N).toSubmodule.mkQ.comp I.toSubmodule.subtype
    isIntertwining' _ := rfl }
  have hf : f ≠ 0 := by
    intro hz
    apply hn
    apply MonoidHom.ext
    intro b
    apply LinearMap.ext
    intro w
    obtain ⟨n,rfl⟩ := (sectionLower ρ U N).toSubmodule.mkQ_surjective w
    let d : I := ⟨N.toRepresentation b n - n, Coinvariants.sub_mem_ker b n.val⟩
    have he : f d = 0 := congrArg (fun a : IntertwiningMap (I.toRepresentation.comp B.subtype)
      (τ.comp B.subtype) => a d) hz
    change (sectionLower ρ U N).toSubmodule.mkQ (N.toRepresentation b n - n) = 0 at he
    rw [map_sub] at he
    exact sub_eq_zero.mp he
  have hfs : Function.Surjective f := (IsIrreducible.surjective_or_eq_zero f).resolve_right hf
  let i : I.toSubmodule →ₗ[ZMod 2] M :=
    (N.toSubmodule.subtype.comp I.toSubmodule.subtype).codRestrict M (fun v => v.property)
  have hi : Function.Injective i := by
    intro v w he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : M => x.val) he
  change Module.finrank (ZMod 2) M ≤ Module.finrank (ZMod 2) Q at hd
  have hdim₁ := LinearMap.finrank_le_finrank_of_injective hi
  have hdim₂ := LinearMap.finrank_le_finrank_of_surjective hfs
  change Module.finrank (ZMod 2) Q ≤ Module.finrank (ZMod 2) I.toSubmodule at hdim₂
  have hdim : Module.finrank (ZMod 2) I.toSubmodule = Module.finrank (ZMod 2) M := by omega
  have his : Function.Surjective i :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
  have hle : M ≤ N.toSubmodule := by
    intro v hv
    obtain ⟨w,hw⟩ := his ⟨v,hv⟩
    have he : (w.val : V) = v := congrArg (fun x : M => x.val) hw
    exact he ▸ w.val.property
  let q := (sectionLower ρ U N).toSubmodule.mkQ.comp (Submodule.inclusion hle)
  have hqs : Function.Surjective q := by
    intro w
    obtain ⟨v,hv⟩ := hfs w
    exact ⟨i v,hv⟩
  have heq : Module.finrank (ZMod 2) M = Module.finrank (ZMod 2) Q := by omega
  exact ⟨hle,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hqs,hqs⟩

/-- The identification intertwines the full actor, through the original
numerator inclusion followed by the original chief quotient map. -/
theorem coinvariants_section_equiv_of_finrank_le
    (ρ : Representation (ZMod 2) G V) (B : Subgroup G) [B.Normal]
    (U N : Subrepresentation ρ)
    [IsIrreducible ((sectionRepresentation ρ U N).comp B.subtype)]
    (hn : (sectionRepresentation ρ U N).comp B.subtype ≠ 1)
    (hd : Module.finrank (ZMod 2) (Coinvariants.ker (ρ.comp B.subtype)) ≤
      Module.finrank (ZMod 2) (N.toSubmodule ⧸ (sectionLower ρ U N).toSubmodule)) :
    ∃ hle : Coinvariants.ker (ρ.comp B.subtype) ≤ N.toSubmodule,
      ∃ e : Equiv (toCoinvariantsKer ρ B) (sectionRepresentation ρ U N),
        ∀ v, e v = (sectionLower ρ U N).toSubmodule.mkQ (Submodule.inclusion hle v) := by
  obtain ⟨hle,hq⟩ := coinvariants_section_bijective_of_finrank_le ρ B U N hn hd
  let f : IntertwiningMap (toCoinvariantsKer ρ B) (sectionRepresentation ρ U N) := {
    toLinearMap := (sectionLower ρ U N).toSubmodule.mkQ.comp (Submodule.inclusion hle)
    isIntertwining' _ := rfl }
  exact ⟨hle, f.ofBijective hq, fun _ => rfl⟩
end Representation.BinaryOffender
