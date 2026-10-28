module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.GroupTheory.PGroup.OmegaCenterDetection

/-!
# The reselected point is fixed by the other triangle residual

The first flag preimage is a nontrivial T-invariant subgroup of the chosen
elementary module. It meets the Sylow omega-center nontrivially. Once the
chosen fixed space vanishes, such a central vector has nonzero image in the
one-dimensional field point. Every element of the component that centralizes
the omega-center fixes this vector, hence the entire field point. Perfectness
places any such subgroup in the literal first normalizer residual.

The triangle application uses the actual K₀ ≤ K ∩ I and source [Z,K] = 1.
It constructs the first residual containment in either orientation. Equality
with K₀, placement of K itself, and the common second residual remain required.
The printed formula U₁ = [Z ∩ U₁, X_K] cannot supply this step: X_K ≤ K and
[Z,K] = 1 make its right side trivial. The proof below instead uses the
actual field-linear action of K₀; it does not infer that all of K fixes U₁.
Source: Aschbacher--Smith, proof of 11.1.2(3), printed p.764.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {I U : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T I U) (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)

/-- Centralizing the actual Sylow omega-center forces a component subgroup
to fix the entire new field point, including its original ambient preimage. -/
theorem centralizes_point_of_centralizes_omega
    (hfix : U ⊓ centralizer (I : Set G) = ⊥)
    (A : Subgroup G) (hAI : A ≤ I)
    (hAZ : A ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G)) :
    A ≤ centralizer (f.Vi 0 : Set G) := by
  let Z := omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype)
  have hPU : f.Vi 0 ≤ U := D.centralQuotientPreimage_le _
  have hne : Z ⊓ f.Vi 0 ≠ ⊥ := by
    intro he
    exact f.V_ne_bot 0 (eq_bot_of_normalized_of_omega_center_disjoint
      (T : Subgroup G) (f.Vi 0) T.isPGroup' (hPU.trans D.le_sylow) (f.invariant 0) he)
  obtain ⟨v, hv, hv1⟩ : ∃ v : G, v ∈ Z ⊓ f.Vi 0 ∧ v ≠ 1 := by
    classical
    by_contra hn
    apply hne
    apply le_bot_iff.mp
    intro v hv
    apply mem_bot.mpr
    by_contra hv1
    exact hn ⟨v, hv, hv1⟩
  let vU : U := ⟨v, hPU hv.2⟩
  let x : c.Space := (c.projection vU).toAdd
  have hinj : Function.Injective c.projection :=
    c.linearEquiv.toAddEquiv.toMultiplicative.injective.comp (centralQuotient_injective D hfix)
  have hx : x ∈ f.space 0 := (c.mem_preimage _ vU).mp hv.2
  have hx0 : x ≠ 0 := by
    intro he
    have hp : c.projection vU = c.projection 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective he
    exact hv1 (congrArg Subtype.val (hinj hp))
  have hspan : f.space 0 = Submodule.span S.field.Carrier {x} :=
    eq_span_singleton_of_mem_of_finrank_eq_one (f.dimension 0) hx hx0
  intro a ha u hu
  let aI : I := ⟨a, hAI ha⟩
  have hav : a * v = v * a := (hAZ ha v hv.1).symm
  have hcv : U.normalizerMonoidHom (inclusion D.normalizes aI) vU = vU := by
    apply Subtype.ext
    change a * v * a⁻¹ = v
    rw [hav]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hcx : c.modelAction (c.quotientMap aI) x = x :=
    (c.projection_component_conjugation aI vU).symm.trans
      (congrArg (fun w : U => (c.projection w).toAdd) hcv)
  let uU : U := ⟨u, hPU hu⟩
  have hy : (c.projection uU).toAdd ∈ Submodule.span S.field.Carrier {x} :=
    hspan ▸ (c.mem_preimage _ uU).mp hu
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hy
  have hcy : c.modelAction (c.quotientMap aI) (c.projection uU).toAdd =
      (c.projection uU).toAdd := by
    rw [← hr, map_smul, hcx]
  have hcu : U.normalizerMonoidHom (inclusion D.normalizes aI) uU = uU := by
    apply hinj
    apply Multiplicative.toAdd.injective
    exact (c.projection_component_conjugation aI uU).trans hcy
  have he : a * u * a⁻¹ = u := congrArg Subtype.val hcu
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Perfectness upgrades the constructed point fixation to containment in
the actual N_I(U₁)^∞, with the source residual convention unchanged. -/
theorem le_firstResidual_of_centralizes_omega
    (hfix : U ⊓ centralizer (I : Set G) = ⊥)
    (A : Subgroup G) [Group.IsPerfect A] (hAI : A ≤ I)
    (hAZ : A ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G)) :
    A ≤ f.Li 0 := by
  apply le_map_solvableResidual_of_isPerfect A (I ⊓ normalizer (f.Vi 0 : Set G))
  exact le_inf hAI ((centralizes_point_of_centralizes_omega D S f hfix A hAI hAZ).trans
    (Subgroup.centralizer_le_normalizer _))

/-- Source application to the literal other residual K₀ in I = K₀ ∨ L₂.
The earlier [Z,K] = 1 supplies its point fixation; no point-stabilizer or
first-residual containment is assumed. -/
theorem triangle_other_le_firstResidual
    {L₂ K K₀ : Subgroup G}
    (hI : I = K₀ ⊔ L₂) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ ≤ K)
    (hKZ : K ≤ centralizer
      (omegaOneAmbient ((center (T : Subgroup G)).map (T : Subgroup G).subtype) : Set G))
    (hfix : U ⊓ centralizer (I : Set G) = ⊥) :
    K₀ ≤ centralizer (f.Vi 0 : Set G) ∧ K₀ ≤ f.Li 0 := by
  let : Group.IsPerfect K₀ := Chapter1.mem_L_isPerfect hK₀
  have hK₀I : K₀ ≤ I := by rw [hI]; exact le_sup_left
  exact ⟨centralizes_point_of_centralizes_omega D S f hfix K₀ hK₀I (hK₀K.trans hKZ),
    le_firstResidual_of_centralizes_omega D S f hfix K₀ hK₀I (hK₀K.trans hKZ)⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
