module

public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction.Graph
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction.Transport
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.GroupTheory.SubgroupCenterImageBound

/-!
# The kernel of the action on a symplectic Sylow center

The actual two-root center detects both characters of the Borel: the weights
are a² and c, and squaring is injective in characteristic two. An automorphism
fixing this center therefore induces the identity on the Borel torus. The
proved graph-power description of the torus kernel, with its semilinear
classification premise discharged, makes the automorphism inner. The same
central-root calculation puts its Borel conjugator in the unipotent Sylow.
Sylow conjugacy retains that witness inside any specified Sylow subgroup.

This treats arbitrary automorphisms preserving the Sylow, including all
two-power orders. It uses no Thompson placement or Baumann decomposition.
Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 (PDF p.944), and the
standard two-root central plane of Sp₄ in characteristic two.
-/

public noncomputable section
open Subgroup
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.CenterAction
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem unipotent_conj_parameter (u : unipotent (F := F)) (s t : F) :
    (u : Sp F) * parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t) *
      (u : Sp F)⁻¹ = parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  exact congrArg Subtype.val (mem_center_iff.mp (theta_mem_center s t) u)

/-- The Borel characters act with weights a² and c on the two central roots. -/
theorem borel_conj_parameter (b : borel (F := F)) (s t : F) :
    (b : Sp F) * parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t) *
        (b : Sp F)⁻¹ =
      parameter (Multiplicative.ofAdd (((borelCharacters b).1 : F)^2*s),
        Multiplicative.ofAdd (((borelCharacters b).2 : F)*t)) := by
  let d := torusSection (borelCharacters b)
  let u := b * d⁻¹
  have hu : (u : Sp F) ∈ unipotent := by
    apply (borelCharacters_eq_one u).mp
    simp [u, d]
  have hd : (d : Sp F) * parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t) *
      (d : Sp F)⁻¹ = parameter
        (Multiplicative.ofAdd (((borelCharacters b).1 : F)^2*s),
        Multiplicative.ofAdd (((borelCharacters b).2 : F)*t)) := by
    have h := diagonalTorus_weights
      ((borelCharacters b).1, (borelCharacters b).1⁻¹ * (borelCharacters b).2) s t
    simpa [d, torusSection, diagonalTorusHom_apply, mul_assoc] using h
  have hb : (b : Sp F) = (u : Sp F) * (d : Sp F) := by simp [u]
  rw [hb, mul_inv_rev]
  calc
    _ = (u : Sp F) * ((d : Sp F) * parameter
        (Multiplicative.ofAdd s, Multiplicative.ofAdd t) * (d : Sp F)⁻¹) *
        (u : Sp F)⁻¹ := by simp only [mul_assoc]
    _ = _ := by rw [hd]; exact unipotent_conj_parameter (⟨(u : Sp F), hu⟩ : unipotent (F := F)) _ _

/-- The action on the actual central root plane detects both Borel characters. -/
theorem characters_eq_of_center_action (b c : borel (F := F))
    (h : ∀ s t : F,
      (b : Sp F) * parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t) *
        (b : Sp F)⁻¹ =
      (c : Sp F) * parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t) *
        (c : Sp F)⁻¹) : borelCharacters b = borelCharacters c := by
  have h1 := h 1 0
  have h2 := h 0 1
  rw [borel_conj_parameter, borel_conj_parameter] at h1 h2
  have he1 := congrArg (fun x : Multiplicative F × Multiplicative F => x.1.toAdd)
    (parameter_injective h1)
  have he2 := congrArg (fun x : Multiplicative F × Multiplicative F => x.2.toAdd)
    (parameter_injective h2)
  apply Prod.ext
  · apply Units.ext
    apply frobenius_inj F 2
    simpa [frobenius_def] using he1
  · exact Units.ext (by simpa using he2)

/-- Fixing the central root plane pointwise forces trivial action on the Borel torus. -/
theorem torusAction_eq_one_of_center_fixed {n : ℕ} (hF : Nat.card F = 2^n)
    (a : ActorReduction.stabilizer (F := F))
    (hfix : ∀ s t : F, a.val (parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t)) =
      parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t)) :
    torusAction hF a = 1 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨b, rfl⟩ := characters_surjective x
  rw [torusAction_characters]
  change borelCharacters (borelAction a b) = borelCharacters b
  apply characters_eq_of_center_action
  intro s t
  have h := congrArg a.val (borel_conj_parameter b s t)
  rw [map_mul, map_mul, map_inv, hfix, hfix] at h
  exact h.trans (borel_conj_parameter b s t).symm

private theorem aut_center_fixed_unipotent_inner {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (a : ActorReduction.stabilizer (F := F))
    (hfix : ∀ s t : F, a.val (parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t)) =
      parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t)) :
    ∃ g ∈ unipotent (F := F), a.val = MulAut.conj g := by
  obtain ⟨g, hg⟩ := (torusAction_eq_one_iff_inner hF hn
    DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram a).mp
      (torusAction_eq_one_of_center_fixed hF a hfix)
  have hgb : g ∈ borel (F := F) := by
    rw [borel_eq_normalizer_unipotent]
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hg]
    exact a.property
  refine ⟨g, ?_, hg.symm⟩
  apply (borelCharacters_eq_one ⟨g, hgb⟩).mp
  have he := characters_eq_of_center_action (⟨g, hgb⟩ : borel (F := F)) 1 (by
    intro s t
    have h := hfix s t
    rw [← hg] at h
    simpa only [Subgroup.coe_one, one_mul, inv_one, mul_one, MulAut.conj_apply] using h)
  exact he.trans (map_one _)

/-- A Sylow-preserving automorphism fixing its center pointwise is conjugation
by an element of that Sylow. No restriction on the automorphism order is needed. -/
theorem aut_fixing_sylow_center_inner {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n)
    (S : Sylow 2 (Sp F)) (a : MulAut (Sp F))
    (hS : (S : Subgroup (Sp F)).map a.toMonoidHom = S)
    (hfix : ∀ z ∈ (center S).map (S : Subgroup (Sp F)).subtype, a z = z) :
    ∃ g ∈ (S : Subgroup (Sp F)), a = MulAut.conj g := by
  let e := alignment hF hn.le S
  let b := alignActorHom hF hn.le S ⟨a, hS⟩
  have hUS : unipotent.map e.toMonoidHom = (S : Subgroup (Sp F)) :=
    alignment_unipotent hF hn.le S
  have hZ := map_subgroup_center_eq e.toMonoidHom e.injective
    (unipotent (F := F))
  rw [hUS] at hZ
  have hb (s t : F) :
      b.val (parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t)) =
        parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t) := by
    have hz : parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t) ∈
        (center (unipotent (F := F))).map unipotent.subtype :=
      ⟨theta s t, theta_mem_center s t, rfl⟩
    have hez := hZ.le (mem_map_of_mem e.toMonoidHom hz)
    change e.symm (a (e (parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t)))) = _
    exact (congrArg e.symm (hfix _ hez)).trans (e.symm_apply_apply _)
  obtain ⟨g, hg, he⟩ := aut_center_fixed_unipotent_inner hF hn b hb
  refine ⟨e g, hUS.le (mem_map_of_mem e.toMonoidHom hg), ?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨z, rfl⟩ := e.surjective y
  have hz := congrArg (fun c : MulAut (Sp F) => e (c z)) he
  change e (e.symm (a (e z))) = e (g * z * g⁻¹) at hz
  simpa only [e.apply_symm_apply, map_mul, map_inv, MulAut.conj_apply] using hz


end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.CenterAction
