module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Extensions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer

/-!
# Faithful extension of the marked six-letter augmentation action

A faithful binary action extending the prescribed alternating action on the
five-dimensional even-weight core embeds in the literal symmetric group on the
same six letters. Both the component marking and the original linear coordinates
are retained. The map to the four-dimensional natural module is the actual
`coreToNatural`, and the resulting quotient action is proved faithful.

Normality gives intertwining operators for the alternating component. Its
invariant-subspace classification forces them to preserve the constant line.
An operator acting trivially on the natural quotient then centralizes the
component, by faithfulness of its natural action. The difference from the
identity has image of dimension at most one and an invariant kernel of dimension
at least four; the same subspace classification forces it to vanish. Thus the
quotient action is faithful. Its known natural extension lifts uniquely back to
the core by this rigidity argument.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, §B.3, printed
pp.83–85; 13.7.6(3) and its proof, pp.938–939; and the first paragraph of the
proof of 13.8.6, p.948. This is an intrinsic conditional extension theorem.
Source applicability and the remaining book-theorem clauses belong to the
compatible-flags and parabolic-marking assembly owners.
-/

public section

open BinaryPermutation Module
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.CompatibleFlags.AugmentationExtension
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2
private abbrev F := ZMod 2
private abbrev C := core (Fin 6)
private abbrev N := natural (Fin 6)
private abbrev Alt := alternatingGroup (Fin 6)
private abbrev q : C →ₗ[F] N := coreToNatural (Fin 6)
private abbrev act (k : Alt) : Module.End F C := coreRepresentation (Fin 6) k.val

private theorem mem_kernel (v : C) : v ∈ q.ker ↔ v.val ∈ constants (Fin 6) := by
  change q v = 0 ↔ _
  rw [← Subtype.val_inj]
  exact Submodule.Quotient.mk_eq_zero _

private theorem kernel_finrank : finrank F q.ker = 1 := by
  have h := q.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr coreToNatural_surjective, finrank_top,
    NaturalSix.natural_finrank, NaturalSix.augmentation_finrank] at h
  omega

private theorem invariant_le_kernel_or_eq_top (W : Submodule F C)
    (hW : ∀ k : Alt, ∀ v ∈ W, act k v ∈ W) : W ≤ q.ker ∨ W = ⊤ := by
  let W' := W.map (core (Fin 6)).subtype
  have hinv : ∀ k : Alt, ∀ v ∈ W', representation (Fin 6) k.val v ∈ W' := by
    rintro k _ ⟨v, hv, rfl⟩
    exact ⟨act k v, hW k v hv, rfl⟩
  rcases invariant_le_constants_or_core_le (by decide : 5 ≤ Fintype.card (Fin 6))
      W' hinv with h | h
  · exact Or.inl (fun v hv => (mem_kernel v).mpr (h ⟨v, hv, rfl⟩))
  · right
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := h v.property
    exact (Subtype.ext he : w = v) ▸ hw

private theorem kernel_action (k : Alt) {v : C} (hv : v ∈ q.ker) : act k v ∈ q.ker := by
  change q (act k v) = 0
  rw [coreToNatural_equivariant]
  change naturalRepresentation (Fin 6) k.val (q v) = 0
  rw [show q v = 0 from hv, map_zero]

/-- A backward intertwining relation with the literal alternating image. -/
private def Twists (t : Module.End F C) : Prop :=
  ∀ k : Alt, ∃ l : Alt, ∀ v, act k (t v) = t (act l v)

private theorem twists_mul {t s : Module.End F C} (ht : Twists t) (hs : Twists s) :
    Twists (t * s) := by
  intro k
  obtain ⟨l, hl⟩ := ht k
  obtain ⟨m, hm⟩ := hs l
  exact ⟨m, fun v => (hl (s v)).trans (congrArg t (hm v))⟩

private theorem twists_core (g : Equiv.Perm (Fin 6)) :
    Twists (coreRepresentation (Fin 6) g) := by
  intro k
  let l : Alt := ⟨g⁻¹ * k.val * g, by
    simpa using (inferInstance : (alternatingGroup (Fin 6)).Normal).conj_mem
      k.val k.property g⁻¹⟩
  refine ⟨l, fun v => ?_⟩
  change (coreRepresentation (Fin 6) k.val * coreRepresentation (Fin 6) g) v =
    (coreRepresentation (Fin 6) g * coreRepresentation (Fin 6) l.val) v
  rw [← map_mul, ← map_mul]
  congr 2
  simp [l, mul_assoc]

private theorem preserves_kernel {t : Module.End F C} (ht : Twists t) :
    q.ker ≤ q.ker.comap t := by
  let W := q.ker.map t
  have hinv : ∀ k : Alt, ∀ v ∈ W, act k v ∈ W := by
    rintro k _ ⟨v, hv, rfl⟩
    obtain ⟨l, hl⟩ := ht k
    exact ⟨act l v, kernel_action l hv, (hl v).symm⟩
  have hd : finrank F W ≤ 1 := (Submodule.finrank_map_le t q.ker).trans_eq kernel_finrank
  rcases invariant_le_kernel_or_eq_top W hinv with h | h
  · exact fun v hv => h ⟨v, hv, rfl⟩
  · rw [h, finrank_top, NaturalSix.augmentation_finrank] at hd
    omega

private theorem quotient_trivial_eq_one (t : Module.End F C) (ht : Twists t)
    (hq : ∀ v, q (t v) = q v) : t = 1 := by
  have hc (k : Alt) (v : C) : act k (t v) = t (act k v) := by
    obtain ⟨l, hl⟩ := ht k
    have he : k = l := by
      apply Subtype.ext
      apply NaturalSix.symmetricAction_injective
      apply LinearMap.ext
      intro w
      obtain ⟨u, rfl⟩ := coreToNatural_surjective w
      have hh := congrArg q (hl u)
      simpa only [coreToNatural_equivariant, hq] using hh
    simpa only [he] using hl v
  let d : Module.End F C := t - 1
  have hr : d.range ≤ q.ker := by
    rintro _ ⟨v, rfl⟩
    change q (t v - v) = 0
    rw [map_sub, hq, sub_self]
  have hk : ∀ k : Alt, ∀ v ∈ d.ker, act k v ∈ d.ker := by
    intro k v hv
    change t (act k v) - act k v = 0
    have hv' : t v = v := sub_eq_zero.mp hv
    rw [← hc, hv']
    exact sub_self _
  have hd := d.finrank_range_add_finrank_ker
  rw [NaturalSix.augmentation_finrank] at hd
  rcases invariant_le_kernel_or_eq_top d.ker hk with h | h
  · have h₁ := (Submodule.finrank_mono hr).trans_eq kernel_finrank
    have h₂ := (Submodule.finrank_mono h).trans_eq kernel_finrank
    omega
  · exact sub_eq_zero.mp (LinearMap.ker_eq_top.mp h)

private noncomputable def descend (t : Module.End F C) (ht : Twists t) : Module.End F N :=
  (q.ker.liftQ (q.comp t) (preserves_kernel ht)).comp
    (q.quotKerEquivOfSurjective coreToNatural_surjective).symm.toLinearMap

private theorem descend_apply (t : Module.End F C) (ht : Twists t) (v : C) :
    descend t ht (q v) = q (t v) := by
  simp only [descend, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

private theorem twists_rep {A : Type*} [Group A] (K : Subgroup A) [K.Normal]
    (γ : Representation F A C) (eK : K ≃* Alt)
    (he : ∀ k : K, γ k = act (eK k)) (a : A) : Twists (γ a) := by
  intro k
  let j := eK.symm k
  let l : K := ⟨a⁻¹ * j.val * a, by
    simpa using (inferInstance : K.Normal).conj_mem j.val j.property a⁻¹⟩
  refine ⟨eK l, fun v => ?_⟩
  have hj : act k = γ j := by simpa [j] using (he j).symm
  rw [hj, ← he l]
  change (γ j.val * γ a) v = (γ a * γ l.val) v
  rw [← map_mul, ← map_mul]
  congr 2
  simp [l, mul_assoc]

private theorem literal_extension {A : Type*} [Group A] (K : Subgroup A) [K.Normal]
    (γ : Representation F A C) (hγ : Function.Injective γ) (eK : K ≃* Alt)
    (he : ∀ k : K, γ k = act (eK k)) :
    ∃ f : A →* Equiv.Perm (Fin 6), Function.Injective f ∧
      (∀ k : K, f k = (eK k).val) ∧
      (∀ a v, γ a v = coreRepresentation (Fin 6) (f a) v) := by
  let ht := twists_rep K γ eK he
  let δ : Representation F A N := {
    toFun := fun a => descend (γ a) (ht a)
    map_one' := by
      apply LinearMap.ext
      intro w
      obtain ⟨v, rfl⟩ := coreToNatural_surjective w
      rw [descend_apply, map_one]
      rfl
    map_mul' := by
      intro a b
      apply LinearMap.ext
      intro w
      obtain ⟨v, rfl⟩ := coreToNatural_surjective w
      change descend (γ (a * b)) (ht (a * b)) (q v) =
        descend (γ a) (ht a) (descend (γ b) (ht b) (q v))
      rw [descend_apply, descend_apply, descend_apply, map_mul]
      rfl }
  have hδq (a : A) (v : C) : δ a (q v) = q (γ a v) := descend_apply (γ a) (ht a) v
  have hδ : Function.Injective δ := by
    apply (injective_iff_map_eq_one δ).mpr
    intro a ha
    apply hγ
    rw [map_one]
    apply quotient_trivial_eq_one _ (ht a)
    intro v
    rw [← hδq, ha]
    rfl
  have hδK (k : K) : δ k = NaturalSix.alternatingAction (eK k) := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := coreToNatural_surjective w
    rw [hδq, he]
    exact coreToNatural_equivariant _ _
  obtain ⟨f, hf, hfK, hfδ, _⟩ := NaturalSix.faithful_extension_of_normalizer
    NaturalSix.normalizer_alternatingImage K δ hδ eK (LinearEquiv.refl F N)
    (fun k v => LinearMap.congr_fun (hδK k) v)
  refine ⟨f, hf, hfK, fun a v => ?_⟩
  have hfδ' (a : A) (w : N) : δ a w = naturalRepresentation (Fin 6) (f a) w := hfδ a w
  have hi : coreRepresentation (Fin 6) (f a)⁻¹ * γ a = 1 := by
    apply quotient_trivial_eq_one _ (twists_mul (twists_core _) (ht a))
    intro u
    change q (coreRepresentation (Fin 6) (f a)⁻¹ (γ a u)) = q u
    rw [coreToNatural_equivariant, ← hδq, hfδ']
    exact Representation.inv_self_apply _ _ _
  have hv := LinearMap.congr_fun hi v
  have hh := congrArg (coreRepresentation (Fin 6) (f a)) hv
  change coreRepresentation (Fin 6) (f a)
    (coreRepresentation (Fin 6) (f a)⁻¹ (γ a v)) = coreRepresentation (Fin 6) (f a) v at hh
  simpa only [Representation.self_inv_apply] using hh

/-- Every faithful extension of the marked alternating augmentation action is the
literal coordinate action of a faithful permutation extension. The actual natural
quotient intertwines this extension and remains faithful. -/
theorem faithful_extension
    {A U : Type*} [Group A] [AddCommGroup U] [Module (ZMod 2) U]
    (K : Subgroup A) [K.Normal]
    (ρ : Representation (ZMod 2) A U) (hρ : Function.Injective ρ)
    (eK : K ≃* alternatingGroup (Fin 6)) (E : U ≃ₗ[ZMod 2] core (Fin 6))
    (he : ∀ k : K, ∀ u, E (ρ k u) = coreRepresentation (Fin 6) (eK k).val (E u)) :
    ∃ φ : A →* Equiv.Perm (Fin 6), Function.Injective φ ∧
      (∀ k : K, φ k = (eK k).val) ∧
      (∀ a u, E (ρ a u) = coreRepresentation (Fin 6) (φ a) (E u)) ∧
      alternatingGroup (Fin 6) ≤ φ.range ∧
      (∀ a u, coreToNatural (Fin 6) (E (ρ a u)) =
        naturalRepresentation (Fin 6) (φ a) (coreToNatural (Fin 6) (E u))) ∧
      Function.Injective ((naturalRepresentation (Fin 6)).comp φ) := by
  let γ : Representation F A C := E.conjRingEquiv.toMonoidHom.comp ρ
  have hγ : Function.Injective γ := E.conjRingEquiv.injective.comp hρ
  have hγK (k : K) : γ k = act (eK k) := by
    apply LinearMap.ext
    intro v
    change E (ρ k (E.symm v)) = coreRepresentation (Fin 6) (eK k).val v
    simpa using he k (E.symm v)
  obtain ⟨φ, hφ, hφK, hφγ⟩ := literal_extension K γ hγ eK hγK
  have hact (a : A) (u : U) : E (ρ a u) = coreRepresentation (Fin 6) (φ a) (E u) := by
    have hh := hφγ a (E u)
    change E (ρ a (E.symm (E u))) = coreRepresentation (Fin 6) (φ a) (E u) at hh
    simpa using hh
  refine ⟨φ, hφ, hφK, hact, ?_, ?_, NaturalSix.symmetricAction_injective.comp hφ⟩
  · intro k hk
    obtain ⟨j, hj⟩ := eK.surjective ⟨k, hk⟩
    exact ⟨j.val, by rw [hφK, hj]⟩
  · intro a u
    rw [hact, coreToNatural_equivariant]

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.Marking.CompatibleFlags.AugmentationExtension
