module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeSection
public import Theory.LinearAlgebra.RegularLinearAction
public import Theory.Representation.ElementaryAbelianAction
/-!
# The faithful five-dimensional A5 action in the M22-code pair

The actual alternating subgroup of the native five-part S5 quotient contains
the natural actor. Its action on the quintet kernel is nontrivial on the
inner four-space, hence faithful by simplicity of A5. The inner four-space
is irreducible under the full normalizer and has trivial one-dimensional
quotient. The A5 displacement span is invariant under that normalizer;
it is nonzero and consequently equals the inner four-space.

Surjective actor markings transport these dimensions to literal group
quotients with their specified automorphism action. The Chapter12 application
uses the unchanged B/U, original residual and exact two-core kernel.
This establishes the dimension and kernel facts used in 8.2.8; it does not
assert the later two-copy action or selection of the pair's S3 quotient.

Source: Aschbacher--Smith H.14.3(2), H.16.3(3), and 8.2.8(3--5), printed
pp.397,403,718--719, refs/quasithin.pdf. The native natural-actor constructions
retain the licensed ATLAS coordinates; see LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.M22Quintet MathieuCode.M22Quintet.CocodeTransfer
open scoped IsMulCommutative
namespace MathieuCode.NormalizedShadowRows.M22CodeSection
open M22ChapterH.Quintet

/-- The actual inner five-part image, retaining the native quotient. -/
theorem naturalFivePart_eq : naturalFivePartGroup = alternatingGroup (Fin 5) := by
  have hc : Nat.card naturalFivePartGroup = 60 := by
    rw [Nat.card_congr naturalFivePartModelEquiv.toEquiv,
      ←Nat.card_congr Hexacode.ZeroNatural.modelEquiv.toEquiv]
    exact Atlas.Codes.hexPointKernel_card _
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have hh := naturalFivePartGroup.card_mul_index
  rw [hc,Nat.card_perm,Nat.card_fin] at hh
  norm_num at hh
  omega

@[expose] def fiveAction : Representation (ZMod 2) (alternatingGroup (Fin 5)) (Additive M22Quintet.K) :=
  kernelS5Conjugation.comp (alternatingGroup (Fin 5)).subtype

private theorem fiveAction_ne_one : fiveAction ≠ 1 := by
  intro he
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨a,ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
  have hm : a.val ∈ naturalFivePartGroup := naturalFivePart_eq.symm ▸ a.property
  obtain ⟨g,hg⟩ := hm
  have hgact : kernelConjugation g.val = 1 := by
    rw [←kernelS5Conjugation_q,show NaturalQuotient.q g.val = a.val from hg]
    exact congrArg (fun ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) (Additive M22Quintet.K) => ρ a) he
  have hin : innerTranslationConjugation g.val = 1 := by
    ext v : 1
    apply innerTranslationInclusion_injective
    rw [innerTranslationInclusion.isIntertwining]
    let w := coreTranslationEquiv.symm (innerTranslationInclusion v)
    have hh := LinearMap.congr_fun (coreTranslationRepresentationEquiv.isIntertwining' g.val) w
    rw [hgact] at hh
    change coreTranslationEquiv w = outerTranslationConjugation g.val (coreTranslationEquiv w) at hh
    rw [coreTranslationEquiv.apply_symm_apply] at hh
    exact hh.symm
  have hmem : g ∈ naturalActorTranslations := innerTranslation_actor_kernel ▸ hin
  have hq : NaturalQuotient.q g.val = 1 :=
    show g ∈ (NaturalQuotient.q.comp naturalActor.subtype).ker from
      naturalActor_fivePart_kernel.symm ▸ hmem
  exact ha (Subtype.ext (hg.symm.trans hq))

/-- Faithfulness is for the literal alternating subgroup of the original S5 quotient. -/
theorem fiveAction_faithful : Function.Injective fiveAction := by
  apply (MonoidHom.ker_eq_bot_iff fiveAction).mp
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top
      (by simp : 5 ≤ Nat.card (Fin 5)) (N := fiveAction.ker) with h | h
  · exact h
  · exact (fiveAction_ne_one (MonoidHom.ker_eq_top_iff.mp h)).elim

private def innerSpace : Subrepresentation kernelS5Conjugation where
  toSubmodule := innerInclusion.range
  apply_mem_toSubmodule g v hv := by
    obtain ⟨g,rfl⟩ := q_surjective g
    obtain ⟨w,rfl⟩ := hv
    rw [kernelS5Conjugation_q,←innerInclusion_equivariant M22ChapterH.Quintet.innerInputs]
    exact ⟨_,rfl⟩

private theorem inner_dim : Module.finrank (ZMod 2) innerSpace.toSubmodule = 4 := by
  change Module.finrank (ZMod 2) innerInclusion.range = 4
  rw [LinearMap.finrank_range_of_inj innerInclusion_injective,innerIntersection_finrank]

private theorem inner_quotient_dim : Module.finrank (ZMod 2)
    ((Additive M22Quintet.K) ⧸ innerSpace.toSubmodule) = 1 := by
  have hh := innerSpace.toSubmodule.finrank_quotient_add_finrank
  rw [inner_dim,kernel_finrank] at hh
  omega

private def moved : Subrepresentation kernelS5Conjugation where
  toSubmodule := Coinvariants.ker fiveAction
  apply_mem_toSubmodule g v hv := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨a,w⟩,rfl⟩ := hv
      have ha : g * a.val * g⁻¹ ∈ alternatingGroup (Fin 5) :=
        (inferInstance : (alternatingGroup (Fin 5)).Normal).conj_mem a a.property g
      have hm := Coinvariants.sub_mem_ker (ρ := fiveAction) ⟨g*a.val*g⁻¹,ha⟩ (kernelS5Conjugation g w)
      simpa only [fiveAction,MonoidHom.comp_apply,Subgroup.coe_subtype,map_sub,map_mul,
        Module.End.mul_apply,inv_self_apply] using hm
    | zero => simpa only [map_zero] using (Submodule.zero_mem (Coinvariants.ker fiveAction))
    | add x y _ _ hx hy => simpa only [map_add] using (Submodule.add_mem _ hx hy)
    | smul c x _ hx => simpa only [map_smul] using (Submodule.smul_mem _ c hx)

private theorem moved_le_inner : moved ≤ innerSpace := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,v⟩,rfl⟩
  apply (Submodule.Quotient.eq innerSpace.toSubmodule).mp
  have he := LinearGroup.eq_one_of_binary_finrank_le_one inner_quotient_dim.le
    (LinearMap.GeneralLinearGroup.toLinearEquiv (innerSpace.quotientRepresentation.asGroupHom g.val))
  exact LinearEquiv.congr_fun he (innerSpace.toSubmodule.mkQ v)

/-- The same five-dimensional module has commutator rank four, hence a trivial one-dimensional quotient. -/
theorem fiveAction_moved_dim : Module.finrank (ZMod 2) (Coinvariants.ker fiveAction) = 4 := by
  let W : Subrepresentation (innerConjugation M22ChapterH.Quintet.innerInputs) := {
    toSubmodule := moved.toSubmodule.comap innerInclusion
    apply_mem_toSubmodule g v hv := by
      change innerInclusion (innerConjugation M22ChapterH.Quintet.innerInputs g v) ∈ moved
      rw [innerInclusion_equivariant]
      rw [←kernelS5Conjugation_q]
      exact moved.apply_mem_toSubmodule _ hv }
  have hirr := M22ChapterH.Quintet.innerConjugation_isIrreducible
  have he : moved = innerSpace := by
    rcases hirr.eq_bot_or_eq_top W with hz | ht
    · exfalso
      apply fiveAction_ne_one
      ext g v : 2
      have hm := Coinvariants.sub_mem_ker (ρ := fiveAction) g v
      obtain ⟨w,hw⟩ := moved_le_inner hm
      have hwW : w ∈ W := show innerInclusion w ∈ moved from hw.symm ▸ hm
      rw [hz] at hwW
      have hw0 : w = 0 := hwW
      rw [hw0,map_zero] at hw
      exact sub_eq_zero.mp hw.symm
    · apply le_antisymm moved_le_inner
      rintro v ⟨w,rfl⟩
      have hw : w ∈ W := ht.symm ▸ Submodule.mem_top
      exact hw
  change Module.finrank (ZMod 2) moved.toSubmodule = 4
  rw [he,inner_dim]

/-- A surjective actor marking transports the displacement dimension to the
literal source representation. -/
theorem moved_dim_of_marking {R W : Type*} [Group R] [AddCommGroup W]
    [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) R W) (r : R →* alternatingGroup (Fin 5))
    (hr : Function.Surjective r) (e : W ≃ₗ[ZMod 2] Additive M22Quintet.K)
    (he : ∀ x v, e (ρ x v) = fiveAction (r x) (e v)) :
    Module.finrank (ZMod 2) W = 5 ∧
      Module.finrank (ZMod 2) (Coinvariants.ker ρ) = 4 ∧
      Module.finrank (ZMod 2) (Coinvariants ρ) = 1 := by
  have hmap : (Coinvariants.ker ρ).map e.toLinearMap = Coinvariants.ker fiveAction := by
    apply le_antisymm
    · apply Submodule.map_le_iff_le_comap.mpr
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨x,v⟩,rfl⟩
      change e (ρ x v - v) ∈ Coinvariants.ker fiveAction
      rw [map_sub,he]
      exact Coinvariants.sub_mem_ker _ _
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨x,v⟩,rfl⟩
      obtain ⟨x,rfl⟩ := hr x
      obtain ⟨v,rfl⟩ := e.surjective v
      exact ⟨ρ x v-v,Coinvariants.sub_mem_ker _ _,by simp only [LinearEquiv.coe_coe,map_sub,he]⟩
  have hd : Module.finrank (ZMod 2) W = 5 := e.finrank_eq.trans kernel_finrank
  have hm : Module.finrank (ZMod 2) (Coinvariants.ker ρ) = 4 := by
    rw [←LinearEquiv.finrank_map_eq e,hmap,fiveAction_moved_dim]
  refine ⟨hd,hm,?_⟩
  have hq := (Coinvariants.ker ρ).finrank_quotient_add_finrank
  change Module.finrank (ZMod 2) (Coinvariants ρ) + _ = _ at hq
  omega

/-- The actual automorphism action on a marked elementary group has the
same five, four, and one dimensional section and coinvariants. -/
theorem dimensions_of_group_marking {R W : Type*} [Group R] [Group W] [Finite W]
    (f : R →* MulAut W) (r : R →* alternatingGroup (Fin 5)) (hr : Function.Surjective r)
    (e : W ≃* M22Quintet.K)
    (he : ∀ x v, Additive.ofMul (e (f x v)) = fiveAction (r x) (Additive.ofMul (e v))) :
    ∃ hEl : IsElementaryAbelian 2 W, letI := hEl
      ∃ ρ : Representation (ZMod 2) R (Additive W),
        (∀ x v, ρ x (Additive.ofMul v) = Additive.ofMul (f x v)) ∧
        Module.finrank (ZMod 2) (Additive W) = 5 ∧
        Module.finrank (ZMod 2) (Coinvariants.ker ρ) = 4 ∧
        Module.finrank (ZMod 2) (Coinvariants ρ) = 1 := by
  let hEl : IsElementaryAbelian 2 W := IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  let := hEl
  let : MulDistribMulAction R W := MulDistribMulAction.compHom W f
  let ρ := ofElementaryAbelianAction (A := R) (G := W) (p := 2)
  let E : Additive W ≃ₗ[ZMod 2] Additive M22Quintet.K :=
    LinearEquiv.ofBijective (e.toAdditive.toAddMonoidHom.toZModLinearMap 2) e.bijective
  exact ⟨hEl,ρ,fun _ _ => rfl,moved_dim_of_marking ρ r hr E he⟩

end MathieuCode.NormalizedShadowRows.M22CodeSection
