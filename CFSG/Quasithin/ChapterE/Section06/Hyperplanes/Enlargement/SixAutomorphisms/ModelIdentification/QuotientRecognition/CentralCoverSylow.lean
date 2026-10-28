module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.SourceSylow
public import Theory.GroupAction.CentralKernelFixedCommutator
/-!
# Derived fixed groups under the original enlargement quotient

The source Sylow witness has ambient image Q ∩ Y, so every original V-actor
fixes it. Under an equivariant central quotient, its image is Sylow in the
image of the first fixed group and lies in every second fixed group. The
derived fixed group downstairs lifts into that first image. Consequently
its Sylow order divides the order of every second fixed group.

The model wrapper constructs the literal map Y → Y/Z(Y) → D and both
induced automorphisms internally. No quotient-fixed Sylow is lifted to Y.
Source: Aschbacher–Smith E.6.23, p.254 (PDF p.265).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
variable {G : Type*} [Group G] [Finite G] {M V U A L X Y : Subgroup G} {g : G}

/-- The actual common Sylow supplies the comparison for an equivariant central image. -/
theorem source_fixed_derived_sylow_dvd [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V) (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    {D : Type*} [Group D] [Finite D] (f : Y →* D)
    (hf : Function.Surjective f) (hk : f.ker ≤ center Y)
    (a a₀ : MulAut Y) (ha : a ∈ actionImage V Y) (ha1 : a ≠ 1)
    (ha₀ : a₀ ∈ actionImage V Y) (b c : MulAut D)
    (hab : ∀ x, f (a x) = b (f x)) (hac : ∀ x, f (a₀ x) = c (f x))
    (Q : Sylow 2 (commutator b.fixedSubgroup)) : Nat.card Q ∣ Nat.card c.fixedSubgroup := by
  obtain ⟨P, hP⟩ := actor_fixed_sylow h h15 d hY ha ha1
  apply MulAut.fixed_derived_sylow_card_dvd a b c f hf hk hab P _ Q
  rintro _ ⟨u, ⟨x, hx, rfl⟩, rfl⟩
  have hxu : (x.val : G) ∈ sylowCentralizer (T : Subgroup G) V ⊓ Y :=
    hP ▸ mem_map_of_mem Y.subtype (mem_map_of_mem a.fixedSubgroup.subtype hx)
  have hfix : x.val ∈ FixedPoints.subgroup (actionImage V Y) Y := by
    rw [fixed_subgroup_eq V Y (hY.normalized_by_V d.subspace_mem.1)]
    exact hxu.1.2
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  rw [← hac]
  exact congrArg f (hfix ⟨a₀, ha₀⟩)

/-- The literal central quotient and supplied model identify both original actors. -/
theorem quotient_actor_derived_sylow_dvd [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V) (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y)
    {D : Type*} [Group D] [Finite D] (e : (Y ⧸ center Y) ≃* D)
    (a c : MulAut Y) (ha : a ∈ actionImage V Y) (ha1 : a ≠ 1)
    (hc : c ∈ actionImage V Y)
    (Q : Sylow 2 (commutator ((MulAut.congr e) (quotientAut (center Y) a)).fixedSubgroup)) :
    Nat.card Q ∣ Nat.card ((MulAut.congr e) (quotientAut (center Y) c)).fixedSubgroup := by
  let q := QuotientGroup.mk' (center Y)
  let f := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker ≤ center Y := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have heq (b : MulAut Y) (x : Y) :
      f (b x) = (MulAut.congr e (quotientAut (center Y) b)) (f x) := by
    change e (q (b x)) = e (quotientAut (center Y) b (e.symm (e (q x))))
    rw [e.symm_apply_apply, quotientAut_apply_mk]
  exact source_fixed_derived_sylow_dvd h h15 d hY f hf hk a c ha ha1 hc _ _
    (heq a) (heq c) Q
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
