module

public import Theory.Representation.BinaryPermutationSixCover.Universal
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Marked six-letter perfect central covers

An augmentation-core surjection is first constructed for the alternating
component. The difference of two lifts lands in the central kernel, so
commutator generation makes the surjection equivariant for the whole actor.
The alternating invariant-subspace classification then leaves precisely the
natural quotient and the augmentation core, with the original actor marking.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.3.1–3,
printed pp.83–84, and I.1.5–6, printed p.408.
-/

@[expose] public section
open Representation Representation.OneCohomology Representation.BinaryOffender
namespace BinaryPermutation.SixCover
variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

omit [FiniteDimensional (ZMod 2) U] in
private lemma core_map_equivariant
    (ρ : Representation (ZMod 2) H U) (eH : H →* Equiv.Perm (Fin 6)) (hinj : Function.Injective eH) (K : Subgroup H)
    (a : alternatingGroup (Fin 6) →* H)
    (ha : ∀ k, a k ∈ K) (hae : ∀ k, eH (a k) = k.val)
    (p : U →ₗ[ZMod 2] natural (Fin 6))
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 6) (eH g) (p u))
    (hker : p.ker ≤ fixedSpace ρ K)
    (f : core (Fin 6) →ₗ[ZMod 2] U)
    (hpf : ∀ v, p (f v) = coreToNatural (Fin 6) v)
    (hfa : ∀ g : alternatingGroup (Fin 6), ∀ v,
      f (coreRepresentation (Fin 6) g.val v) = ρ (a g) (f v))
    (g : H) (v : core (Fin 6)) :
    f (coreRepresentation (Fin 6) (eH g) v) = ρ g (f v) := by
  let d : core (Fin 6) →ₗ[ZMod 2] U :=
    f.comp (coreRepresentation (Fin 6) (eH g)) - (ρ g).comp f
  have hdker (v : core (Fin 6)) : d v ∈ p.ker := by
    change p (f (coreRepresentation (Fin 6) (eH g) v) - ρ g (f v)) = 0
    rw [map_sub, hpf, hp, hpf, coreToNatural_equivariant, sub_self]
  have hd (k : alternatingGroup (Fin 6)) (v : core (Fin 6)) :
      d (alternatingCoreRepresentation (Fin 6) k v) = d v := by
    let l : alternatingGroup (Fin 6) := ⟨eH g * k.val * (eH g)⁻¹,
      (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem _ k.property _⟩
    have hal : a l = g * a k * g⁻¹ := by
      apply hinj
      simp only [map_mul, map_inv, hae]
      rfl
    have he : coreRepresentation (Fin 6) (eH g) (coreRepresentation (Fin 6) k.val v) =
        coreRepresentation (Fin 6) l.val (coreRepresentation (Fin 6) (eH g) v) := by
      simp [l, ← Module.End.mul_apply, ← map_mul]
    change f (coreRepresentation (Fin 6) (eH g) (coreRepresentation (Fin 6) k.val v)) -
      ρ g (f (coreRepresentation (Fin 6) k.val v)) = d v
    rw [he, hfa, hfa]
    have hh : ρ (a l) (ρ g (f v)) = ρ g (ρ (a k) (f v)) := by
      rw [hal]
      simp [← Module.End.mul_apply, ← map_mul]
    rw [← hh, ← map_sub]
    exact hker (hdker v) ⟨a l, ha l⟩
  have hz : Coinvariants.ker (alternatingCoreRepresentation (Fin 6)) ≤ d.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, v⟩, rfl⟩
    change d (_ - _) = 0
    rw [map_sub, hd, sub_self]
  rw [alternatingSix_core_generated] at hz
  exact sub_eq_zero.mp (hz (Submodule.mem_top : v ∈ ⊤))

private lemma core_surjection_of_cover
    (ρ : Representation (ZMod 2) H U)
    (e : H →* Equiv.Perm (Fin 6)) (hinj : Function.Injective e) (K : Subgroup H)
    (a : alternatingGroup (Fin 6) →* H)
    (ha : ∀ k, a k ∈ K) (hae : ∀ k, e (a k) = k.val)
    (hag : ∀ k ∈ K, ∃ g, a g = k)
    (p : U →ₗ[ZMod 2] natural (Fin 6))
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 6) (e g) (p u))
    (hsur : Function.Surjective p)
    (hker : p.ker ≤ fixedSpace ρ K)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤) :
    ∃ f : core (Fin 6) →ₗ[ZMod 2] U, Function.Surjective f ∧
      (∀ g v, f (coreRepresentation (Fin 6) (e g) v) = ρ g (f v)) ∧
      ∀ v, p (f v) = coreToNatural (Fin 6) v := by
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) U := ρ.comp a
  let P : σ.IntertwiningMap (alternatingNaturalRepresentation (Fin 6)) :=
    p.intertwiningMap_of_isIntertwiningMap _ _ (fun g u => by
      change p (ρ (a g) u) = naturalRepresentation (Fin 6) g.val (p u)
      rw [hp, hae])
  have hcoin : Coinvariants.ker σ = subspaceCommutator ρ ⊤ K := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨⟨g, u⟩, rfl⟩
      exact Submodule.subset_span ⟨a g, ha g, u, Submodule.mem_top, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, u, _, rfl⟩
      obtain ⟨g, rfl⟩ := hag k hk
      exact Coinvariants.sub_mem_ker g u
  have hP : IsCover P := ⟨hsur, fun u hu g => hker hu ⟨a g, ha g⟩, hcoin.trans hgen⟩
  obtain ⟨f, hf, hfa, hpf⟩ := core_quotient_of_alternating_cover σ P hP
  exact ⟨f, hf, core_map_equivariant ρ e hinj K a ha hae p hp hker f hpf hfa, hpf⟩

omit [FiniteDimensional (ZMod 2) U] in
private theorem core_kernel_alternatives (ρ : Representation (ZMod 2) H U)
    (e : H →* Equiv.Perm (Fin 6))
    (hlift : ∀ k : alternatingGroup (Fin 6), ∃ g, e g = k.val)
    (f : core (Fin 6) →ₗ[ZMod 2] U)
    (heq : ∀ g v, f (coreRepresentation (Fin 6) (e g) v) = ρ g (f v))
    (hne : f ≠ 0) :
    f.ker = ⊥ ∨ f.ker = (coreToNatural (Fin 6)).ker := by
  let P := f.ker.map (core (Fin 6)).subtype
  have hP : ∀ g : alternatingGroup (Fin 6), ∀ v ∈ P,
      representation (Fin 6) g.val v ∈ P := by
    rintro g v ⟨u, hu, rfl⟩
    refine ⟨coreRepresentation (Fin 6) g.val u, ?_, rfl⟩
    obtain ⟨k, hk⟩ := hlift g
    change f (coreRepresentation (Fin 6) g.val u) = 0
    rw [← hk, heq, show f u = 0 from hu, map_zero]
  have hproper : ¬ core (Fin 6) ≤ P := by
    intro h
    apply hne
    ext v
    obtain ⟨w, hw, hwv⟩ := h v.property
    have he : w = v := Subtype.ext hwv
    subst w
    exact hw
  rcases invariant_submodule_classification (by decide : 5 ≤ Fintype.card (Fin 6)) P hP with
      hz | hc | ht | ht
  · left
    apply le_antisymm _ bot_le
    intro v hv
    have hv' : v.val ∈ P := ⟨v, hv, rfl⟩
    rw [hz] at hv'
    exact Subtype.ext hv'
  · right
    ext v
    have hv : v ∈ f.ker ↔ v.val ∈ P := by
      constructor
      · exact fun h => ⟨v, h, rfl⟩
      · rintro ⟨w, hw, he⟩
        exact (Subtype.ext he : w = v) ▸ hw
    rw [hv, hc]
    change v.val ∈ constants (Fin 6) ↔ coreToNatural (Fin 6) v = 0
    rw [← Subtype.val_inj]
    exact (Submodule.Quotient.mk_eq_zero (constants (Fin 6))).symm
  · exact (hproper ht.ge).elim
  · exact (hproper (by rw [ht]; exact le_top)).elim

/-- Natural-or-core coordinates retaining the specified six-letter marking. -/
def IsNaturalOrCore (ρ : Representation (ZMod 2) H U)
    (e : H →* Equiv.Perm (Fin 6)) : Prop :=
  (∃ E : U ≃ₗ[ZMod 2] natural (Fin 6),
    ∀ g u, E (ρ g u) = naturalRepresentation (Fin 6) (e g) (E u)) ∨
  (∃ E : U ≃ₗ[ZMod 2] core (Fin 6),
    ∀ g u, E (ρ g u) = coreRepresentation (Fin 6) (e g) (E u))

omit [FiniteDimensional (ZMod 2) U] in
private theorem naturalOrCore_of_core_surjection (ρ : Representation (ZMod 2) H U)
    (e : H →* Equiv.Perm (Fin 6))
    (hlift : ∀ k : alternatingGroup (Fin 6), ∃ g, e g = k.val)
    (f : core (Fin 6) →ₗ[ZMod 2] U)
    (heq : ∀ g v, f (coreRepresentation (Fin 6) (e g) v) = ρ g (f v))
    (hf : Function.Surjective f) (hne : f ≠ 0) : IsNaturalOrCore ρ e := by
  rcases core_kernel_alternatives ρ e hlift f heq hne with hk | hk
  · let E : core (Fin 6) ≃ₗ[ZMod 2] U :=
      LinearEquiv.ofBijective f ⟨LinearMap.ker_eq_bot.mp hk, hf⟩
    refine Or.inr ⟨E.symm, ?_⟩
    intro g u
    apply E.injective
    simp only [E.apply_symm_apply]
    exact (congrArg (ρ g) (E.apply_symm_apply u)).symm.trans (heq g (E.symm u)).symm
  · let q := coreToNatural (Fin 6)
    let eqn := q.quotKerEquivOfSurjective coreToNatural_surjective
    let E : U ≃ₗ[ZMod 2] natural (Fin 6) :=
      (f.quotKerEquivOfSurjective hf).symm.trans
        ((Submodule.quotEquivOfEq _ _ hk).trans eqn)
    have hE (v : core (Fin 6)) : E (f v) = q v := by
      simp only [E, LinearEquiv.trans_apply, LinearMap.quotKerEquivOfSurjective_symm_apply,
        Submodule.quotEquivOfEq_mk, eqn, LinearMap.quotKerEquivOfSurjective_apply_mk]
    refine Or.inl ⟨E, ?_⟩
    intro g u
    obtain ⟨v, rfl⟩ := hf u
    rw [← heq, hE, hE]
    exact coreToNatural_equivariant _ _

private lemma naturalOrCore_of_cover
    (ρ : Representation (ZMod 2) H U)
    (e : H →* Equiv.Perm (Fin 6)) (hinj : Function.Injective e) (K : Subgroup H)
    (a : alternatingGroup (Fin 6) →* H)
    (ha : ∀ k, a k ∈ K) (hae : ∀ k, e (a k) = k.val)
    (hag : ∀ k ∈ K, ∃ g, a g = k)
    (p : U →ₗ[ZMod 2] natural (Fin 6))
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 6) (e g) (p u))
    (hsur : Function.Surjective p)
    (hker : p.ker ≤ fixedSpace ρ K)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤) : IsNaturalOrCore ρ e := by
  obtain ⟨f, hf, heq, hpf⟩ := core_surjection_of_cover ρ e hinj K a ha hae hag
    p hp hsur hker hgen
  apply naturalOrCore_of_core_surjection ρ e (fun k => ⟨a k, hae k⟩) f heq hf
  intro hz
  have hzero : ∀ v : natural (Fin 6), v = 0 := by
    intro v
    obtain ⟨w, rfl⟩ := coreToNatural_surjective v
    rw [← hpf]
    simp [hz]
  have : Subsingleton (natural (Fin 6)) := ⟨fun x y => (hzero x).trans (hzero y).symm⟩
  have hd := finrank_natural_even (Fin 6) (by decide)
  rw [Module.finrank_zero_of_subsingleton] at hd
  norm_num at hd

/-- Recognition for the alternating actor, under its original marking. -/
theorem naturalOrCore_alternating (ρ : Representation (ZMod 2) H U)
    (e : H ≃* alternatingGroup (Fin 6)) (K : Subgroup H) (hK : K = ⊤)
    (p : U →ₗ[ZMod 2] natural (Fin 6))
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 6) (e g).val (p u))
    (hsur : Function.Surjective p)
    (hker : p.ker ≤ fixedSpace ρ K)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤) :
    IsNaturalOrCore ρ ((alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom) := by
  let b : H →* Equiv.Perm (Fin 6) :=
    (alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom
  have hinj : Function.Injective b :=
    (alternatingGroup (Fin 6)).subtype_injective.comp e.injective
  have ha (k : alternatingGroup (Fin 6)) : e.symm k ∈ K := by
    rw [hK]
    exact Subgroup.mem_top _
  have hae (k : alternatingGroup (Fin 6)) : b (e.symm k) = k.val :=
    congrArg Subtype.val (e.apply_symm_apply k)
  have hag (k : H) (_ : k ∈ K) : ∃ g, e.symm g = k :=
    ⟨e k, e.symm_apply_apply k⟩
  exact naturalOrCore_of_cover ρ b hinj K e.symm.toMonoidHom ha hae hag p hp hsur hker hgen

/-- Recognition for the symmetric actor, with its actual alternating component. -/
theorem naturalOrCore_symmetric (ρ : Representation (ZMod 2) H U)
    (e : H ≃* Equiv.Perm (Fin 6)) (K : Subgroup H)
    (hK : K.map e.toMonoidHom = alternatingGroup (Fin 6))
    (p : U →ₗ[ZMod 2] natural (Fin 6))
    (hp : ∀ g u, p (ρ g u) = naturalRepresentation (Fin 6) (e g) (p u))
    (hsur : Function.Surjective p)
    (hker : p.ker ≤ fixedSpace ρ K)
    (hgen : subspaceCommutator ρ ⊤ K = ⊤) : IsNaturalOrCore ρ e.toMonoidHom := by
  let a : alternatingGroup (Fin 6) →* H :=
    e.symm.toMonoidHom.comp (alternatingGroup (Fin 6)).subtype
  have ha (g : alternatingGroup (Fin 6)) : a g ∈ K := by
    have : g.val ∈ K.map e.toMonoidHom := hK.symm ▸ g.property
    obtain ⟨k, hk, he⟩ := this
    have he' : k = a g := e.injective (he.trans (e.apply_symm_apply _).symm)
    exact he' ▸ hk
  have hag (k : H) (hk : k ∈ K) : ∃ g, a g = k := by
    let g : alternatingGroup (Fin 6) := ⟨e k, hK ▸ Subgroup.mem_map_of_mem _ hk⟩
    exact ⟨g, e.symm_apply_apply k⟩
  exact naturalOrCore_of_cover ρ e.toMonoidHom e.injective K a ha
    (fun k => e.apply_symm_apply k.val) hag p hp hsur hker hgen

end BinaryPermutation.SixCover
