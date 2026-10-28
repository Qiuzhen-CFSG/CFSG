module
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryPermutation.EightTransvectionActors
public import Theory.Representation.BinaryOffender.NormalizerExtension
public import Theory.SpecificGroups.SymmetricEight.InvolutionActions

/-!
# The full permutation action on the binary eight-letter core

Three internal three-cycles and the triangle relation force a commuting
operator to fix a pair word. The invariant-subspace theorem then makes
it the identity on the augmentation core. Conjugation on A₈ and
Aut(A₈)=S₈ identify every linear normalizer with a unique permutation.
An ambient action extending a marked normal A₈ action consequently has
permutation coordinates on the same seven-dimensional module, retaining
both its original restriction and its exact kernel.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
B.3.1 and the opening of Section 12.6, printed pp.83 and 822.
-/

public section

open Representation BinaryPermutation Equiv
namespace BinaryPermutation.EightCoreAction
private abbrev Ω := Fin 8
private def a : Perm Ω := swap 2 3 * swap 3 4
private def b : Perm Ω := swap 4 5 * swap 5 6
private def d : Perm Ω := swap 5 6 * swap 6 7
private def c : Perm Ω := swap 0 1 * swap 1 2
private def p : core Ω := ⟨![1,1,0,0,0,0,0,0], by rw [mem_core]; decide⟩
private theorem even : a ∈ alternatingGroup Ω ∧ b ∈ alternatingGroup Ω ∧
    c ∈ alternatingGroup Ω ∧ d ∈ alternatingGroup Ω := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide
private theorem pair_ne : p ≠ 0 := by
  intro h
  have hh := congrArg (fun w : core Ω => w.val 0) h
  exact one_ne_zero hh
private theorem pair_fixed : coreRepresentation Ω a p = p ∧
    coreRepresentation Ω b p = p ∧ coreRepresentation Ω d p = p := by
  refine ⟨?_,?_,?_⟩ <;> apply Subtype.ext <;> decide
private theorem pair_relation :
    p + coreRepresentation Ω c p + coreRepresentation Ω (c*c) p = 0 := by
  apply Subtype.ext
  decide
private theorem fixed_relation (w : core Ω)
    (ha : coreRepresentation Ω a w = w)
    (hb : coreRepresentation Ω b w = w)
    (hd : coreRepresentation Ω d w = w)
    (hc : w + coreRepresentation Ω c w + coreRepresentation Ω (c*c) w = 0) :
    w = 0 ∨ w = p := by
  have h23 := congrArg (fun w : core Ω => w.val 3) ha
  have h34 := congrArg (fun w : core Ω => w.val 4) ha
  have h45 := congrArg (fun w : core Ω => w.val 5) hb
  have h56 := congrArg (fun w : core Ω => w.val 6) hb
  have h67 := congrArg (fun w : core Ω => w.val 7) hd
  change w.val 2 = w.val 3 at h23
  change w.val 3 = w.val 4 at h34
  change w.val 4 = w.val 5 at h45
  change w.val 5 = w.val 6 at h56
  change w.val 6 = w.val 7 at h67
  have h3 := congrArg (fun w : core Ω => w.val 3) hc
  change w.val 3 + w.val 3 + w.val 3 = 0 at h3
  have h3z : w.val 3 = 0 := by simpa only [CharTwo.add_self_eq_zero, zero_add] using h3
  have h2z := h23.trans h3z
  have h4z := h34.symm.trans h3z
  have h5z := h45.symm.trans h4z
  have h6z := h56.symm.trans h5z
  have h7z := h67.symm.trans h6z
  have hsum := w.property
  change ∑ i : Fin 8, w.val i = 0 at hsum
  simp only [Fin.sum_univ_succ] at hsum
  change w.val 0 + (w.val 1 + (w.val 2 + (w.val 3 + (w.val 4 +
    (w.val 5 + (w.val 6 + (w.val 7 + 0))))))) = 0 at hsum
  rw [h2z,h3z,h4z,h5z,h6z,h7z] at hsum
  have h01 : w.val 0 = w.val 1 := by
    simpa only [add_zero, CharTwo.add_eq_zero] using hsum
  have hcases : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  rcases hcases (w.val 0) with hz | ho
  · left; apply Subtype.ext; funext i; fin_cases i <;> simp_all
  · right; apply Subtype.ext; funext i; fin_cases i <;> simp_all [p]

/-- Every invertible operator commuting with the A₈ augmentation action is the identity. -/
theorem commuting_eq_refl (f : core (Fin 8) ≃ₗ[ZMod 2] core (Fin 8))
    (hf : ∀ g : alternatingGroup (Fin 8), ∀ x,
      f (coreRepresentation (Fin 8) g.val x) =
        coreRepresentation (Fin 8) g.val (f x)) : f = LinearEquiv.refl _ _ := by
  have hp : f p = p := by
    apply (fixed_relation (f p) ?_ ?_ ?_ ?_).resolve_left
    · exact fun h => pair_ne (f.injective (h.trans f.map_zero.symm))
    · exact (hf ⟨a,even.1⟩ p).symm.trans (congrArg f pair_fixed.1)
    · exact (hf ⟨b,even.2.1⟩ p).symm.trans (congrArg f pair_fixed.2.1)
    · exact (hf ⟨d,even.2.2.2⟩ p).symm.trans (congrArg f pair_fixed.2.2)
    · have h := congrArg f pair_relation
      rw [map_add,map_add,hf ⟨c,even.2.2.1⟩,hf ⟨c*c,mul_mem even.2.2.1 even.2.2.1⟩,map_zero] at h
      exact h
  let P : Submodule (ZMod 2) (core Ω) := LinearMap.ker (f.toLinearMap - LinearMap.id)
  let W := P.map (core Ω).subtype
  have hW : ∀ g : alternatingGroup Ω, ∀ w ∈ W, representation Ω g.val w ∈ W := by
    rintro g _ ⟨w,hw,rfl⟩
    refine ⟨coreRepresentation Ω g.val w,?_,rfl⟩
    change f w - w = 0 at hw
    change f (coreRepresentation Ω g.val w) - coreRepresentation Ω g.val w = 0
    rw [hf,sub_eq_zero.mp hw,sub_self]
  have hPW : p.val ∈ W := ⟨p,sub_eq_zero.mpr hp,rfl⟩
  have hcore : core Ω ≤ W :=
    (invariant_le_constants_or_core_le (by decide : 5 ≤ Fintype.card Ω) W hW).resolve_left (by
      intro h
      obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp (h hPW)
      exact one_ne_zero ((congrFun ht.symm 0).trans (congrFun ht 2)))
  apply LinearEquiv.ext
  intro w
  obtain ⟨x,hx,he⟩ := hcore w.property
  have hxe : x = w := Subtype.ext he
  subst x
  exact sub_eq_zero.mp hx
end BinaryPermutation.EightCoreAction

public noncomputable section
namespace BinaryPermutation.EightCoreAction
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricEight.Involutions

abbrev Space := core (Fin 8)
abbrev Actor := alternatingGroup (Fin 8)
abbrev Full := Equiv.Perm (Fin 8)
abbrev action := alternatingCoreRepresentation (Ω := Fin 8)

private theorem faithful : Function.Injective action := by
  intro g h he
  apply Subtype.ext
  exact EightTransvectionActors.core_faithful he

private def automorphism : linearNormalizer action →* MulAut Actor :=
  let hf : Function.Injective action.asGroupHom := fun _ _ h => faithful (congrArg Units.val h)
  let e : Actor ≃* actionImage action := MonoidHom.ofInjective hf
  (MulAut.congr e.symm).toMonoidHom.comp (actionImage action).normalizerMonoidHom

private theorem intertwines (t : linearNormalizer action) (g : Actor) (v : Space) :
    t.val.val (action g v) = action (automorphism t g) (t.val.val v) := by
  let hf : Function.Injective action.asGroupHom := fun _ _ h => faithful (congrArg Units.val h)
  let e : Actor ≃* actionImage action := MonoidHom.ofInjective hf
  have he : action.asGroupHom (automorphism t g) = t.val * action.asGroupHom g * t.val⁻¹ := by
    change (e (e.symm ((actionImage action).normalizerMonoidHom t (e g)))).val = _
    rw [e.apply_symm_apply]
    rfl
  have hh := congrArg (fun u : (Module.End (ZMod 2) Space)ˣ => u.val (t.val.val v)) he
  have hinv : (t.val⁻¹).val (t.val.val v) = v := by
    change (t.val⁻¹ * t.val).val v = v
    rw [inv_mul_cancel]
    rfl
  change action (automorphism t g) (t.val.val v) =
    t.val.val (action g ((t.val⁻¹).val (t.val.val v))) at hh
  rw [hinv] at hh
  exact hh.symm

/-- Every normalizing operator is an actual permutation operator. -/
theorem exists_permutation (t : linearNormalizer action) :
    ∃ g : Full, ∀ v : Space, t.val.val v = coreRepresentation (Fin 8) g v := by
  let τ := coreRepresentation (Fin 8)
  obtain ⟨g,hg⟩ := permutationAutEquiv.surjective (automorphism t)
  let F := (LinearMap.GeneralLinearGroup.toLinearEquiv t.val).trans
    (LinearEquiv.ofBijective (τ g⁻¹) (τ.apply_bijective g⁻¹))
  have hF : ∀ k : Actor, ∀ v,
      F (τ k.val v) = τ k.val (F v) := by
    intro k v
    change τ g⁻¹ (t.val.val (action k v)) = _
    rw [intertwines, ← hg]
    change τ g⁻¹ (τ (g * k.val * g⁻¹) (t.val.val v)) =
      τ k.val (τ g⁻¹ (t.val.val v))
    have he : g⁻¹ * (g * k.val * g⁻¹) = k.val * g⁻¹ := by group
    calc
      _ = τ (g⁻¹ * (g * k.val * g⁻¹)) (t.val.val v) :=
        (LinearMap.congr_fun (map_mul τ _ _) _).symm
      _ = τ (k.val * g⁻¹) (t.val.val v) := by rw [he]
      _ = _ := LinearMap.congr_fun (map_mul τ _ _) _
  have he := commuting_eq_refl F hF
  refine ⟨g, fun v => ?_⟩
  have hv := congrArg (fun f : Space ≃ₗ[ZMod 2] Space => f v) he
  change τ g⁻¹ (t.val.val v) = v at hv
  have hh := congrArg (τ g) hv
  have hc (w : Space) : τ g (τ g⁻¹ w) = w := by
    change (τ g * τ g⁻¹) w = w
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  exact (hc _).symm.trans hh

/-- Permutation operators normalize the actual alternating image. -/
def embedding : Full →* linearNormalizer action :=
  (coreRepresentation (Fin 8)).asGroupHom.codRestrict _ (fun g =>
    actionImage_le_linearNormalizer (coreRepresentation (Fin 8)) Actor ⟨g,rfl⟩)

theorem embedding_bijective : Function.Bijective embedding := by
  constructor
  · intro g h he
    exact EightTransvectionActors.core_faithful
      (congrArg (fun t : linearNormalizer action => t.val.val) he)
  · intro t
    obtain ⟨g,hg⟩ := exists_permutation t
    exact ⟨g, Subtype.ext (Units.ext (LinearMap.ext (fun v => (hg v).symm)))⟩

/-- The full linear normalizer is S₈, with its literal natural action. -/
def equiv : Full ≃* linearNormalizer action :=
  MulEquiv.ofBijective embedding embedding_bijective

/-- An ambient action extending a marked normal A₈ action has a canonical
permutation realization. No faithfulness hypothesis is needed to construct it. -/
theorem exists_ambient_hom {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
    (H : Subgroup G) [H.Normal] (e : H →* Actor) (he : Function.Surjective e)
    (E : W ≃ₗ[ZMod 2] Space)
    (hE : ∀ (h : H) v, E (ρ h v) = action (e h) (E v)) :
    ∃ f : G →* Full,
      (∀ h : H, f h = (e h).val) ∧
      (∀ g v, E (ρ g v) = coreRepresentation (Fin 8) (f g) (E v)) ∧
      f.ker = ρ.ker := by
  let τ : Representation (ZMod 2) G Space := E.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (h : H) : τ h = action (e h) := by
    apply LinearMap.ext
    intro v
    change E (ρ h (E.symm v)) = action (e h) v
    rw [hE, E.apply_symm_apply]
  have hi : actionImage (τ.comp H.subtype) = actionImage action := by
    apply le_antisymm
    · rintro _ ⟨h,rfl⟩
      refine ⟨e h, Units.ext (hτ h).symm⟩
    · rintro _ ⟨h,rfl⟩
      obtain ⟨h,rfl⟩ := he h
      refine ⟨h, ?_⟩
      apply Units.ext
      exact hτ h
  let k : G →* linearNormalizer action := τ.asGroupHom.codRestrict _ (fun g => by
    change τ.asGroupHom g ∈ normalizer (actionImage action : Set _)
    rw [← hi]
    exact actionImage_le_linearNormalizer τ H ⟨g,rfl⟩)
  let f := equiv.symm.toMonoidHom.comp k
  have hf (g : G) : equiv (f g) = k g := equiv.apply_symm_apply (k g)
  have heq (g : G) (v : W) :
      E (ρ g v) = coreRepresentation (Fin 8) (f g) (E v) := by
    have hh := congrArg (fun t : linearNormalizer action => t.val.val (E v)) (hf g)
    change coreRepresentation (Fin 8) (f g) (E v) = E (ρ g (E.symm (E v))) at hh
    simpa only [E.symm_apply_apply] using hh.symm
  refine ⟨f, ?_, heq, ?_⟩
  · intro h
    apply EightTransvectionActors.core_faithful
    apply LinearMap.ext
    intro v
    obtain ⟨v,rfl⟩ := E.surjective v
    exact (heq h v).symm.trans (hE h v)
  · ext g
    change f g = 1 ↔ ρ g = 1
    constructor
    · intro hg
      apply LinearMap.ext
      intro v
      apply E.injective
      rw [heq, hg, map_one]
      rfl
    · intro hg
      apply EightTransvectionActors.core_faithful
      apply LinearMap.ext
      intro v
      obtain ⟨v,rfl⟩ := E.surjective v
      rw [← heq, hg, map_one]
      rfl

end BinaryPermutation.EightCoreAction
