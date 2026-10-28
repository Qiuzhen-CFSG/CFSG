module

public import Theory.Representation.G2NaturalFaithfulness
public import Theory.Representation.FirstCohomologyG2Natural.Commutant
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.Representation.BinaryOffender.InnerNormalizerActors
public import Theory.Representation.G2NaturalBinary

/-!
# The full binary normalizer of the derived G₂(2) natural module

Conjugation identifies every automorphism of G₂(2)′ with an actual element
of G₂(2). The additive scalar commutant is F₂, whose only invertible scalar
is one. Hence the full binary linear normalizer consists exactly of the
natural G₂(2) operators. The final theorem extends a literal marked normal
derived action to a faithful embedding of its original ambient group,
retaining the same module coordinates and component inclusion.

Source: Aschbacher–Smith B.4.2(4), B.4.6(1), and I.2.3.
-/

public noncomputable section
namespace Atlas.G2.Natural.BinaryNormalizer
open Representation Representation.BinaryOffender Subgroup LieAutomorphismExtensions
abbrev Full := Model (ZMod 2)
abbrev Derived := commutator Full
abbrev N := Natural.Space (ZMod 2)
abbrev σ := Natural.derivedAction (ZMod 2)

theorem faithful : Function.Injective σ := by
  intro g h he
  apply Subtype.ext
  exact Natural.action_injective (ZMod 2) he

def automorphism : linearNormalizer σ →* MulAut Derived :=
  let hf : Function.Injective σ.asGroupHom := fun _ _ h => faithful (congrArg Units.val h)
  let e : Derived ≃* actionImage σ := MonoidHom.ofInjective hf
  (MulAut.congr e.symm).toMonoidHom.comp (actionImage σ).normalizerMonoidHom

theorem intertwines (t : linearNormalizer σ) (g : Derived) (v : N) :
    t.val.val (σ g v) = σ (automorphism t g) (t.val.val v) := by
  let hf : Function.Injective σ.asGroupHom := fun _ _ h => faithful (congrArg Units.val h)
  let e : Derived ≃* actionImage σ := MonoidHom.ofInjective hf
  have he : σ.asGroupHom (automorphism t g) = t.val * σ.asGroupHom g * t.val⁻¹ := by
    change (e (e.symm ((actionImage σ).normalizerMonoidHom t (e g)))).val = _
    rw [e.apply_symm_apply]
    rfl
  have hh := congrArg (fun u : (Module.End (ZMod 2) N)ˣ => u.val (t.val.val v)) he
  have hinv : (t.val⁻¹).val (t.val.val v) = v := by
    change (t.val⁻¹ * t.val).val v = v
    rw [inv_mul_cancel]
    rfl
  change σ (automorphism t g) (t.val.val v) = t.val.val (σ g ((t.val⁻¹).val (t.val.val v))) at hh
  rw [hinv] at hh
  exact hh.symm

theorem exists_natural_actor (t : linearNormalizer σ) :
    ∃ g : Full, ∀ v : N, t.val.val v = Natural.action (ZMod 2) g v := by
  obtain ⟨g,hg⟩ := binaryConjugation_surjective (automorphism t)
  let f : N →+ N := (Natural.action (ZMod 2) g⁻¹).toAddMonoidHom.comp t.val.val.toAddMonoidHom
  have hf : ∀ (h : Derived) v, f (σ h v) = σ h (f v) := by
    intro h v
    change Natural.action (ZMod 2) g⁻¹ (t.val.val (σ h v)) = _
    rw [intertwines, ← hg]
    change Natural.action (ZMod 2) g⁻¹ (Natural.action (ZMod 2) (g*h*g⁻¹) (t.val.val v)) =
      Natural.action (ZMod 2) h (Natural.action (ZMod 2) g⁻¹ (t.val.val v))
    have he : g⁻¹ * (g * (h : Full) * g⁻¹) = (h : Full) * g⁻¹ := by group
    calc
      _ = Natural.action (ZMod 2) (g⁻¹ * (g * h * g⁻¹)) (t.val.val v) :=
        (LinearMap.congr_fun (map_mul (Natural.action (ZMod 2)) _ _) _).symm
      _ = Natural.action (ZMod 2) ((h : Full) * g⁻¹) (t.val.val v) := by rw [he]
      _ = _ := LinearMap.congr_fun (map_mul (Natural.action (ZMod 2)) _ _) _
  obtain ⟨c,hc⟩ := exists_scalar_of_additive_commutes_derived f hf
  have ht (v : N) : t.val.val v = c • Natural.action (ZMod 2) g v := by
    have he := congrArg (Natural.action (ZMod 2) g) (hc v)
    change Natural.action (ZMod 2) g (Natural.action (ZMod 2) g⁻¹ (t.val.val v)) = _ at he
    have hcancel (w : N) : Natural.action (ZMod 2) g (Natural.action (ZMod 2) g⁻¹ w) = w := by
      change (Natural.action (ZMod 2) g * Natural.action (ZMod 2) g⁻¹) w = w
      rw [← map_mul, mul_inv_cancel, map_one]
      rfl
    simpa only [hcancel, map_smul] using he
  have hc1 : c = 1 := by
    have hc0 : c ≠ 0 := by
      intro hz
      have he : t.val.val = 0 := LinearMap.ext (fun v => by simp [ht, hz])
      have hone : (1 : Module.End (ZMod 2) N) = 0 := by
        have hh := t.val.inv_mul
        rw [he, mul_zero] at hh
        exact hh.symm
      have hd : Module.finrank (ZMod 2) N = 6 := Natural.finrank_space (ZMod 2)
      let : Nontrivial N := Module.nontrivial_of_finrank_pos (show 0 < Module.finrank (ZMod 2) N by rw [hd]; decide)
      exact one_ne_zero hone
    fin_cases c
    · exact (hc0 rfl).elim
    · rfl
  exact ⟨g,fun v => by simpa only [hc1,one_smul] using ht v⟩
def fullEmbedding : Full →* linearNormalizer σ :=
  (Natural.action (ZMod 2)).asGroupHom.codRestrict _ (fun g =>
    actionImage_le_linearNormalizer (Natural.action (ZMod 2)) Derived ⟨g,rfl⟩)

theorem fullEmbedding_bijective : Function.Bijective fullEmbedding := by
  constructor
  · intro g h he
    exact Natural.action_injective (ZMod 2)
      (congrArg (fun t : linearNormalizer σ => t.val.val) he)
  · intro t
    obtain ⟨g,hg⟩ := exists_natural_actor t
    exact ⟨g, Subtype.ext (Units.ext (LinearMap.ext (fun v => (hg v).symm)))⟩

def fullEquiv : Full ≃* linearNormalizer σ :=
  MulEquiv.ofBijective fullEmbedding fullEmbedding_bijective
theorem ambient_embedding {G W : Type*} [Group G] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
    (H : Subgroup G) [H.Normal] (e : H ≃* Derived) (E : W ≃ₗ[ZMod 2] N)
    (hE : ∀ (h : H) v, E (ρ h v) = σ (e h) (E v))
    (hf : Function.Injective ρ) :
    ∃ f : G →* Full, Function.Injective f ∧
      (∀ (h : H), f h = (e h : Full)) ∧
      ∀ g v, E (ρ g v) = Natural.action (ZMod 2) (f g) (E v) := by
  let τ : Representation (ZMod 2) G N := E.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (g : G) (v : W) : E (ρ g v) = τ g (E v) := by
    change E (ρ g v) = E (ρ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hnat (h : H) : τ.asGroupHom h = σ.asGroupHom (e h) := by
    apply Units.ext
    apply LinearMap.ext
    intro v
    change E (ρ h (E.symm v)) = σ (e h) v
    rw [hE, E.apply_symm_apply]
  have himage : actionImage (τ.comp H.subtype) = actionImage σ := by
    ext a
    constructor
    · rintro ⟨h,rfl⟩
      exact ⟨e h, Units.ext (congrArg Units.val (hnat h).symm)⟩
    · rintro ⟨g,rfl⟩
      refine ⟨e.symm g, Units.ext ?_⟩
      simpa only [e.apply_symm_apply, Representation.asGroupHom_apply,
        MonoidHom.comp_apply, Subgroup.coe_subtype] using congrArg Units.val (hnat (e.symm g))
  let k : G →* linearNormalizer σ := τ.asGroupHom.codRestrict _ (fun g => by
    change τ.asGroupHom g ∈ normalizer (actionImage σ : Set _)
    rw [← himage]
    exact actionImage_le_linearNormalizer τ H ⟨g,rfl⟩)
  have hk : Function.Injective k := by
    intro a b hab
    apply hf
    apply E.conjRingEquiv.injective
    exact congrArg (fun x : linearNormalizer σ => x.val.val) hab
  let f := fullEquiv.symm.toMonoidHom.comp k
  refine ⟨f, fullEquiv.symm.injective.comp hk, ?_, ?_⟩
  · intro h
    apply fullEquiv.injective
    change fullEquiv (fullEquiv.symm (k h)) = fullEmbedding (e h)
    rw [fullEquiv.apply_symm_apply]
    exact Subtype.ext (Units.ext (congrArg Units.val (hnat h)))
  · intro g v
    have he := congrArg (fun x : linearNormalizer σ => x.val.val (E v))
      (fullEquiv.apply_symm_apply (k g))
    exact (hτ g v).trans he.symm
end Atlas.G2.Natural.BinaryNormalizer
