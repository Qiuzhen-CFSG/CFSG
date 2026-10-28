module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank.Basic
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.CenterAction
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.OuterReduction
public import Theory.FieldTheory.ScalarTwistedFixedPoints.Triangular

/-!
# Fixed centers of swapping symplectic automorphisms

A Sylow-normalizing automorphism that interchanges the two parabolic classes
is Borel conjugation times an odd power of the exceptional graph map. On the
actual two-root center its fixed equations are
`s = c * σ(t)^2` and `t = d * σ(s)`, where σ is a Frobenius power.
Projection to s is injective and satisfies a scalar-twisted equation for an
odd power of Frobenius. Scalar twisting cannot increase the fixed-field order.
In even field degree this odd power is nonidentity, so the square of the
fixed-center order is at most the field order. An actual inner Sylow alignment
transports the estimates to every Sylow subgroup.

There is no restriction on the actor's order, and no placement of noncentral
fixed involutions is assumed. These are the center counts used in the
symplectic branch of Aschbacher--Smith E.1.14(1), printed p.214, with the
literal tau convention of E.1.1--2, printed pp.209--210. The graph and Borel
formulas use the explicit root matrices of GLS3 §2.5.
-/

public section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms DiagramAutomorphisms.ExceptionalGraph
open CentralRootGeometry EvenBorelTorus EvenBorelTorus.ActorReduction
noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
omit [Finite F] in
private theorem field_parameter (σ : F ≃+* F) (s t : F) :
    fieldAutomorphism σ (parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t)) =
      parameter (Multiplicative.ofAdd (σ s), Multiplicative.ofAdd (σ t)) := by
  simp only [parameter_apply, map_mul, fieldAutomorphism_root,
    toAdd_ofAdd]

private theorem graph_parameter (s t : F) :
    graphAut (parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t)) =
      parameter (Multiplicative.ofAdd (t^2), Multiplicative.ofAdd s) := by
  have hc := (Commute.all
    (Multiplicative.ofAdd (0 : F), Multiplicative.ofAdd s)
    (Multiplicative.ofAdd (t^2), Multiplicative.ofAdd (0 : F))).map
      (parameter (F := F))
  simp only [parameter_apply, toAdd_ofAdd,
    RootSubgroup.element_zero, one_mul, mul_one] at hc
  simpa [parameter_apply, graphAut_apply, graphEnd_root, rootPermutation,
    rootParameter] using hc.eq

private theorem graph_odd_parameter (m : ℕ) (s t : F) :
    (graphAut ^ (2*m+1)) (parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t)) =
      parameter (Multiplicative.ofAdd (((frobeniusEquiv F 2)^m) t ^ 2),
        Multiplicative.ofAdd (((frobeniusEquiv F 2)^m) s)) := by
  have hp : graphAut (F := F) ^ (2*m+1) =
      fieldAutomorphism (frobeniusEquiv F 2 ^ m) * graphAut := by
    rw [pow_add, pow_mul, graphAut_square, pow_one]
    exact congrArg (· * graphAut) (fieldAutomorphismHom.map_pow _ _).symm
  rw [hp, MulAut.mul_apply, graph_parameter, field_parameter, map_pow]

private theorem odd_decomposition (hq : 2 < Nat.card F)
    (a : ActorReduction.stabilizer (F := F)) (ha : ¬ PreservesDiagram a.val) :
    ∃ (m : ℕ) (c₀ d₀ : F), ∀ s t : F,
      a.val (parameter (Multiplicative.ofAdd s, Multiplicative.ofAdd t)) =
        parameter (Multiplicative.ofAdd (c₀ * ((frobeniusEquiv F 2)^m) t ^ 2),
          Multiplicative.ofAdd (d₀ * ((frobeniusEquiv F 2)^m) s)) := by
  obtain ⟨g, k, hk⟩ := exists_inner_graph_power hq
    SemilinearClassification.inner_field_of_preservesDiagram a
  have he : a.val = MulAut.conj g.val * graphAut ^ k := congrArg Subtype.val hk
  have ho : Odd k := by
    rcases Nat.even_or_odd k with h | h
    · obtain ⟨m, rfl⟩ := even_iff_two_dvd.mp h
      apply False.elim
      apply ha
      rw [he, pow_mul, graphAut_square]
      have hi : MulAut.conj g.val ∈ (parabolicClassAction hq).ker :=
        (mem_parabolicClassAction_ker_iff hq _).mpr (inner_preservesDiagram _)
      have hf : fieldAutomorphism (frobeniusEquiv F 2) ∈ (parabolicClassAction hq).ker :=
        (mem_parabolicClassAction_ker_iff hq _).mpr (field_preservesDiagram _)
      exact (mem_parabolicClassAction_ker_iff hq _).mp
        ((parabolicClassAction hq).ker.mul_mem hi ((parabolicClassAction hq).ker.pow_mem hf m))
    · exact h
  obtain ⟨m, rfl⟩ := ho
  refine ⟨m, ((borelCharacters g).1 : F)^2, ((borelCharacters g).2 : F), ?_⟩
  intro s t
  rw [he, MulAut.mul_apply, graph_odd_parameter]
  exact CenterAction.borel_conj_parameter g _ _

private theorem frobenius_double (m : ℕ) (x : F) :
    ((frobeniusEquiv F 2)^m) (((frobeniusEquiv F 2)^m) x) ^ 2 =
      ((frobeniusEquiv F 2)^(2*m+1)) x := by
  rw [pow_succ' (frobeniusEquiv F 2)]
  change _ = (((frobeniusEquiv F 2)^(2*m)) x)^2
  rw [show 2*m = m+m by omega, pow_add]
  rfl

private theorem coordinate_count {f : ℕ} (hF : Nat.card F = 2^f)
    (m : ℕ) (c₀ d₀ : F) :
    let X := {p : F × F // c₀ * ((frobeniusEquiv F 2)^m) p.2 ^ 2 = p.1 ∧
      d₀ * ((frobeniusEquiv F 2)^m) p.1 = p.2}
    Nat.card X ≤ Nat.card F ∧ (Even f → Nat.card X ^ 2 ≤ Nat.card F) := by
  let σ := (frobeniusEquiv F 2)^m
  let τ := (frobeniusEquiv F 2)^(2*m+1)
  let X := {p : F × F // c₀ * σ p.2 ^ 2 = p.1 ∧ d₀ * σ p.1 = p.2}
  let j : X → {x : F // (c₀ * (σ d₀)^2) * τ x = x} := fun p => ⟨p.val.1, by
    have h := p.property.1
    rw [← p.property.2, map_mul, mul_pow, ← mul_assoc] at h
    rw [frobenius_double] at h
    exact h⟩
  have hj : Function.Injective j := by
    intro p q h
    have hs : p.val.1 = q.val.1 := congrArg Subtype.val h
    apply Subtype.ext
    exact Prod.ext hs (p.property.2.symm.trans ((congrArg (fun x => d₀ * σ x) hs).trans q.property.2))
  have hb : Nat.card X ≤ Nat.card (FixedBy.subfield F τ) :=
    (Nat.card_le_card_of_injective j hj).trans (FiniteField.card_scalar_fixed_le τ _)
  refine ⟨hb.trans (Nat.card_le_card_of_injective Subtype.val Subtype.val_injective), ?_⟩
  intro hf
  have ht : τ ≠ 1 := by
    intro ht
    have hd : f ∣ 2*m+1 := by
      rw [← InvolutionNormalForms.frobenius_order hF]
      exact orderOf_dvd_of_pow_eq_one ht
    have he := even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hf).trans hd)
    exact (Nat.not_even_iff_odd.mpr ⟨m, rfl⟩) he
  exact (Nat.pow_le_pow_left hb 2).trans (FiniteField.card_fixed_sq_le τ ht)

private theorem standard_count {f : ℕ} (hF : Nat.card F = 2^f)
    (hq : 2 < Nat.card F) (a : ActorReduction.stabilizer (F := F))
    (ha : ¬ PreservesDiagram a.val) :
    let Z := (center (unipotent (F := F))).map unipotent.subtype ⊓ a.val.fixedSubgroup
    Nat.card Z ≤ Nat.card F ∧ (Even f → Nat.card Z ^ 2 ≤ Nat.card F) := by
  classical
  obtain ⟨m, c₀, d₀, hact⟩ := odd_decomposition hq a ha
  let Z := (center (unipotent (F := F))).map unipotent.subtype ⊓ a.val.fixedSubgroup
  let X := {p : F × F // c₀ * ((frobeniusEquiv F 2)^m) p.2 ^ 2 = p.1 ∧
    d₀ * ((frobeniusEquiv F 2)^m) p.1 = p.2}
  have hex (z : Z) : ∃ p, parameter p = z.val :=
    (parameter_range (F := F)).ge z.property.1
  let c (z : Z) := Classical.choose (hex z)
  have hc (z : Z) : parameter (c z) = z.val := Classical.choose_spec (hex z)
  let j : Z → X := fun z => ⟨((c z).1.toAdd, (c z).2.toAdd), by
    have hz : a.val (parameter (c z)) = parameter (c z) := by
      rw [hc]
      exact (MulAut.mem_fixedSubgroup _ _).mp z.property.2
    change a.val (parameter (Multiplicative.ofAdd (c z).1.toAdd,
      Multiplicative.ofAdd (c z).2.toAdd)) = _ at hz
    rw [hact] at hz
    have hp := parameter_injective hz
    exact ⟨congrArg (fun p : Multiplicative F × Multiplicative F => p.1.toAdd) hp,
      congrArg (fun p : Multiplicative F × Multiplicative F => p.2.toAdd) hp⟩⟩
  have hj : Function.Injective j := by
    intro z w h
    have hp : c z = c w := Prod.ext
      (congrArg (fun p : X => Multiplicative.ofAdd p.val.1) h)
      (congrArg (fun p : X => Multiplicative.ofAdd p.val.2) h)
    apply Subtype.ext
    exact (hc z).symm.trans ((congrArg parameter hp).trans (hc w))
  have hle : Nat.card Z ≤ Nat.card X := Nat.card_le_card_of_injective j hj
  obtain ⟨hsmall, heven⟩ := coordinate_count hF m c₀ d₀
  exact ⟨hle.trans hsmall, fun hf => (Nat.pow_le_pow_left hle 2).trans (heven hf)⟩

/-- Every swapping Sylow-normalizing automorphism has at most |F| fixed central
points; in even degree their number squared is at most |F|. -/
theorem fixedCenter_card_bounds {f : ℕ} (hF : Nat.card F = 2^f) (hf : 1 < f)
    (S : Sylow 2 (Sp F)) (a : MulAut (Sp F))
    (hS : (S : Subgroup (Sp F)).map a.toMonoidHom = S)
    (ha : ¬ PreservesDiagram a) :
    Nat.card (fixedCenter S a) ≤ Nat.card F ∧
      (Even f → Nat.card (fixedCenter S a)^2 ≤ Nat.card F) := by
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^f from Nat.pow_lt_pow_right (by decide) hf)
  let e := alignment hF hf.le S
  let b := alignActorHom hF hf.le S ⟨a, hS⟩
  have he : e ∈ (parabolicClassAction hq).ker :=
    (mem_parabolicClassAction_ker_iff hq _).mpr (inner_preservesDiagram _)
  have hb_eq : b.val = e⁻¹ * a * e := by
    ext x
    rfl
  have hb : ¬ PreservesDiagram b.val := by
    intro hb
    apply ha
    have hab : a = e * b.val * e⁻¹ := by rw [hb_eq]; group
    rw [hab]
    exact (mem_parabolicClassAction_ker_iff hq _).mp
      ((parabolicClassAction hq).ker.mul_mem
        ((parabolicClassAction hq).ker.mul_mem he
          ((mem_parabolicClassAction_ker_iff hq _).mpr hb))
        ((parabolicClassAction hq).ker.inv_mem he))
  have hUS : unipotent.map e.toMonoidHom = (S : Subgroup (Sp F)) :=
    alignment_unipotent hF hf.le S
  have hZ := map_subgroup_center_eq e.toMonoidHom e.injective (unipotent (F := F))
  rw [hUS] at hZ
  let Z := (center (unipotent (F := F))).map unipotent.subtype ⊓ b.val.fixedSubgroup
  let j : fixedCenter S a → Z := fun z => ⟨e.symm z.val, by
    constructor
    · apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
      rw [hZ]
      change e (e.symm z.val) ∈ (center S).map (S : Subgroup (Sp F)).subtype
      rw [e.apply_symm_apply]
      exact z.property.1
    · apply (MulAut.mem_fixedSubgroup _ _).mpr
      change e.symm (a (e (e.symm z.val))) = e.symm z.val
      rw [e.apply_symm_apply]
      exact congrArg e.symm ((mem_fixedCenter S a _).mp z.property).2⟩
  have hj : Function.Injective j := fun _ _ h =>
    Subtype.ext (e.symm.injective (congrArg Subtype.val h))
  have hle : Nat.card (fixedCenter S a) ≤ Nat.card Z := Nat.card_le_card_of_injective j hj
  obtain ⟨hsmall, heven⟩ := standard_count hF hq b hb
  exact ⟨hle.trans hsmall, fun hf => (Nat.pow_le_pow_left hle 2).trans (heven hf)⟩
end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SwappingFixedRank
