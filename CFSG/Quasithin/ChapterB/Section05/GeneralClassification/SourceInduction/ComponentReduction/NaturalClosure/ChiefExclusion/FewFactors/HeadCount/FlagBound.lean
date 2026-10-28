module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FewFactors.HeadCount.MovedQuotients
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.Flags

/-!
# Dual multiplicities bounded by the original chief flag

Intersect the literal L-chief flag with a subrepresentation U. Restricting
maps to each earlier intersection gives a linear map over End_L(S). Its
kernel comes from maps out of the original chief section: the image of the
intersection in that simple section is a direct summand, so a map on this
image extends to the section. Schur's lemma bounds the contribution by one.
A central section contributes zero when S is noncentral. Telescoping counts
exactly the original `noncentralFactors` filter, including the empty case.

Applying this to U = W = [V,L] bounds the literal dual multiplicity space.
Perfectness makes every maximal quotient of W noncentral, giving the
`hbound` premise of `secondHead_eq_one_of_flag_multiplicity_bound`. The
parent head-count argument retains the final assembly with count at most
two. No flag for a second actor or semisimplicity of W is required.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, the c = 2 centralizer argument.
-/

@[expose] public section

open Representation Representation.BinaryOffender
open scoped MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors.HeadCount
set_option backward.isDefEq.respectTransparency false
section Algebra
variable {R M N Q S : Type*} [Ring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup Q] [Module R Q] [AddCommGroup S] [Module R S]

private def pullHom (r : N →ₗ[R] M) :
    (M →ₗ[R] S) →ₗ[Module.End R S] (N →ₗ[R] S) where
  toFun a := a.comp r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem simple_hom_finrank_le_one [IsSimpleModule R Q] [IsSimpleModule R S] :
    Module.finrank (Module.End R S) (Q →ₗ[R] S) ≤ 1 := by
  classical
  by_cases hz : ∀ a : Q →ₗ[R] S, a = 0
  · exact finrank_le_one (0 : Q →ₗ[R] S) (fun a => ⟨0, by simp [hz a]⟩)
  · obtain ⟨a, ha⟩ := not_forall.mp hz
    let e := LinearEquiv.ofBijective a (LinearMap.bijective_of_ne_zero ha)
    apply finrank_le_one a
    intro b
    refine ⟨b.comp e.symm.toLinearMap, ?_⟩
    ext x
    exact congrArg b (e.symm_apply_apply x)

private theorem hom_step [IsSimpleModule R Q] [IsSimpleModule R S]
    [Module.Finite (Module.End R S) (M →ₗ[R] S)]
    [Module.Finite (Module.End R S) (N →ₗ[R] S)]
    [Module.Finite (Module.End R S) (Q →ₗ[R] S)]
    (r : N →ₗ[R] M) (q : M →ₗ[R] Q) (hexact : q.ker ≤ r.range) :
    Module.finrank (Module.End R S) (M →ₗ[R] S) ≤
      Module.finrank (Module.End R S) (N →ₗ[R] S) +
      Module.finrank (Module.End R S) (Q →ₗ[R] S) := by
  classical
  let a := pullHom (S := S) r
  let b := pullHom (S := S) q
  have hker : a.ker ≤ b.range := by
    intro t ht
    have hk : q.ker ≤ t.ker := by
      intro x hx
      obtain ⟨y, rfl⟩ := hexact hx
      exact DFunLike.congr_fun ht y
    let t' : q.range →ₗ[R] S :=
      (q.ker.liftQ t hk).comp q.quotKerEquivRange.symm.toLinearMap
    obtain ⟨s, hs⟩ := IsSemisimpleModule.extension_property
      q.range.subtype q.range.subtype_injective t'
    refine ⟨s, ?_⟩
    ext x
    change s (q x) = t x
    have he := DFunLike.congr_fun hs (q.quotKerEquivRange (Submodule.Quotient.mk x))
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.quotKerEquivRange_apply_mk, t', LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, Submodule.liftQ_apply] using he
  have hd := a.finrank_range_add_finrank_ker
  have hk := (Submodule.finrank_mono hker).trans b.finrank_range_le
  have hr : Module.finrank (Module.End R S) a.range ≤
      Module.finrank (Module.End R S) (N →ₗ[R] S) := Submodule.finrank_le _
  omega
end Algebra

section Representation
variable {P V S T : Type*} [Group P]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup S] [Module (ZMod 2) S] [Module.Finite (ZMod 2) S]
  [AddCommGroup T] [Module (ZMod 2) T]
  (π : Representation (ZMod 2) P S) [IsIrreducible π]

private theorem central_hom_finrank_eq_zero (τ : Representation (ZMod 2) P T)
    (hπ : π ≠ 1) (ht : ∀ g x, τ g x = x) :
    Module.finrank (Module.End (ZMod 2)[P] π.asModule) (DualMultiplicity τ π) = 0 := by
  classical
  let : IsSimpleModule (ZMod 2)[P] π.asModule :=
    (irreducible_iff_isSimpleModule_asModule π).mp inferInstance
  have hz (a : DualMultiplicity τ π) : a = 0 := by
    by_contra hn
    have hs := LinearMap.surjective_of_ne_zero hn
    apply hπ
    ext g v
    obtain ⟨x, hx⟩ := hs (π.asModuleEquiv.symm v)
    let ai := (IntertwiningMap.equivLinearMapAsModule τ π).symm a
    have he := IntertwiningMap.isIntertwining τ π ai g (τ.asModuleEquiv x)
    rw [ht] at he
    have hv : ai (τ.asModuleEquiv x) = v := hx
    change π g v = v
    simpa only [hv] using he.symm
  let : Subsingleton (DualMultiplicity τ π) := ⟨fun a b => (hz a).trans (hz b).symm⟩
  exact Module.finrank_eq_zero_of_subsingleton _ _

variable [Module.Finite (ZMod 2) V]
private theorem intersection_step (τ : Representation (ZMod 2) P V)
    (U E B : Subrepresentation τ) (hEB : E ≤ B)
    [IsIrreducible (sectionRepresentation τ E B)] :
    Module.finrank (Module.End (ZMod 2)[P] π.asModule)
      (DualMultiplicity (U ⊓ B).toRepresentation π) ≤
    Module.finrank (Module.End (ZMod 2)[P] π.asModule)
      (DualMultiplicity (U ⊓ E).toRepresentation π) +
    Module.finrank (Module.End (ZMod 2)[P] π.asModule)
      (DualMultiplicity (sectionRepresentation τ E B) π) := by
  let : IsSimpleModule (ZMod 2)[P] π.asModule :=
    (irreducible_iff_isSimpleModule_asModule π).mp inferInstance
  let : IsSimpleModule (ZMod 2)[P] (sectionRepresentation τ E B).asModule :=
    (irreducible_iff_isSimpleModule_asModule _).mp inferInstance
  let ri : (U ⊓ E).toRepresentation.IntertwiningMap (U ⊓ B).toRepresentation := {
    toLinearMap := Submodule.inclusion (inf_le_inf_left U.toSubmodule hEB)
    isIntertwining' _ := rfl }
  let qi : (U ⊓ B).toRepresentation.IntertwiningMap (sectionRepresentation τ E B) := {
    toLinearMap := (sectionLower τ E B).toSubmodule.mkQ.comp
      (Submodule.inclusion (show (U ⊓ B).toSubmodule ≤ B.toSubmodule from inf_le_right))
    isIntertwining' _ := rfl }
  let r := IntertwiningMap.equivLinearMapAsModule _ _ ri
  let q := IntertwiningMap.equivLinearMapAsModule _ _ qi
  apply hom_step r q
  intro x hx
  have hxE : x.val ∈ E.toSubmodule :=
    (Submodule.Quotient.mk_eq_zero (sectionLower τ E B).toSubmodule).mp hx
  exact ⟨⟨x.val, x.property.1, hxE⟩, rfl⟩
end Representation

universe uG uV uS
variable {G : Type uG} {V : Type uV} {S : Type uS} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
  [AddCommGroup S] [Module (ZMod 2) S] [Module.Finite (ZMod 2) S]
  (ρ : Representation (ZMod 2) G V)

private theorem subrepresentation_flag_bound {A L : Subgroup G}
    (f : InvariantChiefFlag ρ A L ⊤)
    (π : Representation (ZMod 2) L S) [IsIrreducible π] (hπ : π ≠ 1)
    (U : Subrepresentation (ρ.comp L.subtype)) :
    Module.finrank (Module.End (ZMod 2)[L] π.asModule)
      (DualMultiplicity U.toRepresentation π) ≤ f.noncentral.card := by
  classical
  let τ := ρ.comp L.subtype
  let D := Module.End (ZMod 2)[L] π.asModule
  let c (i : ℕ) := Module.finrank D (DualMultiplicity (U ⊓ f.term i).toRepresentation π)
  let d (i : ℕ) := Module.finrank D
    (DualMultiplicity (sectionRepresentation τ (f.term i) (f.term (i + 1))) π)
  have hc0 : c 0 = 0 := by
    have hx (x : (U ⊓ f.term 0).toRepresentation.asModule) : x = 0 := by
      apply Subtype.ext
      exact f.start.le x.property.2
    let : Subsingleton (DualMultiplicity (U ⊓ f.term 0).toRepresentation π) :=
      ⟨fun a b => LinearMap.ext fun x => by rw [hx x, map_zero, map_zero]⟩
    exact Module.finrank_eq_zero_of_subsingleton _ _
  have hsum (n : ℕ) (hn : n ≤ f.length) : c n ≤ ∑ i ∈ Finset.range n, d i := by
    induction n with
    | zero => simp [hc0]
    | succ n ih =>
      let : IsIrreducible (sectionRepresentation τ (f.term n) (f.term (n + 1))) :=
        f.chief n (by omega)
      have hs := intersection_step π τ U (f.term n) (f.term (n + 1))
        (f.monotone (Nat.le_succ n))
      have hi := ih (by omega)
      change c (n + 1) ≤ c n + d n at hs
      rw [Finset.sum_range_succ]
      omega
  have hfactor (i : ℕ) (hi : i ∈ Finset.range f.length) :
      d i ≤ if i ∈ f.noncentral then 1 else 0 := by
    let : IsIrreducible (sectionRepresentation τ (f.term i) (f.term (i + 1))) :=
      f.chief i (Finset.mem_range.mp hi)
    let : IsSimpleModule (ZMod 2)[L] π.asModule :=
      (irreducible_iff_isSimpleModule_asModule π).mp inferInstance
    let : IsSimpleModule (ZMod 2)[L]
        (sectionRepresentation τ (f.term i) (f.term (i + 1))).asModule :=
      (irreducible_iff_isSimpleModule_asModule _).mp inferInstance
    by_cases hm : i ∈ f.noncentral
    · simpa only [if_pos hm] using
        (simple_hom_finrank_le_one (R := (ZMod 2)[L])
          (Q := (sectionRepresentation τ (f.term i) (f.term (i + 1))).asModule)
          (S := π.asModule))
    · have ht : ∀ l v, sectionRepresentation τ (f.term i) (f.term (i + 1)) l v = v := by
        by_contra ht
        exact hm (f.noncentral_mem.mpr ⟨Finset.mem_range.mp hi, ht⟩)
      have hz := central_hom_finrank_eq_zero π
        (sectionRepresentation τ (f.term i) (f.term (i + 1))) hπ ht
      change d i = 0 at hz
      rw [if_neg hm, hz]
  have hcard : (∑ i ∈ Finset.range f.length, if i ∈ f.noncentral then 1 else 0) =
      f.noncentral.card := by
    rw [← Finset.sum_filter]
    have he : (Finset.range f.length).filter (fun i => i ∈ f.noncentral) = f.noncentral := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
      exact fun hi => (f.noncentral_mem.mp hi).1
    rw [he]
    simp
  have hbound : c f.length ≤ f.noncentral.card :=
    (hsum _ le_rfl).trans ((Finset.sum_le_sum hfactor).trans_eq hcard)
  let ri : (U ⊓ f.term f.length).toRepresentation.IntertwiningMap U.toRepresentation := {
    toLinearMap := Submodule.inclusion (show (U ⊓ f.term f.length).toSubmodule ≤
      U.toSubmodule from inf_le_left)
    isIntertwining' _ := rfl }
  let r := IntertwiningMap.equivLinearMapAsModule _ _ ri
  have hr : Function.Surjective r := by
    intro x
    refine ⟨⟨x.val, x.property, ?_⟩, rfl⟩
    change x.val ∈ (f.term f.length).toSubmodule
    rw [f.stop]
    trivial
  have hinj : Function.Injective (pullHom (S := π.asModule) r) := by
    intro a b hab
    ext x
    obtain ⟨y, rfl⟩ := hr x
    exact DFunLike.congr_fun hab y
  exact (LinearMap.finrank_le_finrank_of_injective hinj).trans hbound

/-- The literal noncentral chief-factor count bounds every noncentral simple dual multiplicity of W. -/
theorem dualMultiplicity_finrank_le_noncentral [Finite G] {A L : Subgroup G}
    (f : InvariantChiefFlag ρ A L ⊤)
    (π : Representation (ZMod 2) L S) [IsIrreducible π] (hπ : π ≠ 1) :
    Module.finrank (Module.End (ZMod 2)[L] π.asModule)
      (DualMultiplicity (componentAction ρ L) π) ≤ f.noncentral.card :=
  subrepresentation_flag_bound ρ f π hπ (componentMoved ρ L)

/-- The flag supplies precisely the multiplicity premise for the actual maximal quotients of W. -/
theorem moved_coatom_dualMultiplicity_finrank_le_noncentral [Finite G] {A L : Subgroup G}
    (f : InvariantChiefFlag ρ A L ⊤) (hL : Theory.GroupTheory.IsComponent G L)
    (N : Subrepresentation (componentAction ρ L)) (hN : IsCoatom N) :
    Module.finrank (Module.End (ZMod 2)[L] N.quotientRepresentation.asModule)
      (DualMultiplicity (componentAction ρ L) N.quotientRepresentation) ≤ f.noncentral.card := by
  let : IsIrreducible N.quotientRepresentation :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom N hN
  exact dualMultiplicity_finrank_le_noncentral ρ f N.quotientRepresentation
    (moved_coatom_quotient_ne_one ρ hL N hN)
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure.FewFactors.HeadCount
