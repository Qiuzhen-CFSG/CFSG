module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.Induction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors.Basic
public import Theory.Representation.QuadraticDuality
public import Mathlib.GroupTheory.Sylow

/-!
# The two-factor splitting input and the geometry of its four-group

The input below is precisely the GL₄(2) instance of B.4.9(1): a faithful
extension with natural kernel and natural-or-dual quotient splits when an
order-four subgroup is quadratic on the extension and has a common
transvection axis on the quotient. It is quantified over actual group
identifications, so a later change to the dual natural coordinates must be
justified by an equivariant equivalence.

We extract an actual four-subgroup from a noncyclic elementary actor,
pass quadratic action to sections and duals, and turn pointwise fixation of
a hyperplane into the literal common-axis condition. These are preparation
for the two exclusions in 13.8.25; neither exclusion is assumed here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, B.4.9(1), printed p.92, and 13.8.25,
printed p.961 (PDF p.978).
-/

@[expose] public section

universe u v

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions

open Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors

variable {H U V : Type*} [Group H]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Pointwise fixation of one codimension-one subspace. -/
def FixesHyperplane (ρ : Representation (ZMod 2) H U) (A : Subgroup H) : Prop :=
  ∃ P : Submodule (ZMod 2) U, Module.finrank (ZMod 2) (U ⧸ P) = 1 ∧
    ∀ g ∈ A, ∀ v ∈ P, ρ g v = v

/-- Every nonidentity element has the same hyperplane as its fixed space.
For an elementary two-group these are exactly transvections with fixed axis. -/
def HasCommonAxis (ρ : Representation (ZMod 2) H U) (A : Subgroup H) : Prop :=
  ∃ P : Submodule (ZMod 2) U, Module.finrank (ZMod 2) (U ⧸ P) = 1 ∧
    ∀ g ∈ A, g ≠ 1 → (ρ g - 1).ker = P

/-- Every nonidentity element has the same one-dimensional displacement space.
For an elementary two-group these are transvections with fixed center. -/
def HasCommonCenter (ρ : Representation (ZMod 2) H U) (A : Subgroup H) : Prop :=
  ∃ L : Submodule (ZMod 2) U, Module.finrank (ZMod 2) L = 1 ∧
    ∀ g ∈ A, g ≠ 1 → LinearMap.range (ρ g - 1) = L

/-- Only the two-factor GL₄(2) case of B.4.9(1), with an actual invariant
complement as conclusion. The actor identification is universally quantified
because either of the two natural orientations may occur as kernel. -/
def TwoFactorSplitting (H : Type u) [Group H] : Prop :=
  ∀ (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) H V)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (K : Subrepresentation σ),
    Function.Injective σ → IsNatural K.toRepresentation eH →
    IsNaturalOrDual K.quotientRepresentation eH →
    ∀ E : Subgroup H, Nat.card E = 4 → IsQuadratic σ E →
      HasCommonAxis K.quotientRepresentation E →
      ∃ C : Subrepresentation σ, K ⊓ C = ⊥ ∧ K ⊔ C = ⊤

/-- Equivariance transfers faithfulness from a quotient or another target. -/
theorem faithful_of_equivariant_surjection
    (ρ : Representation (ZMod 2) H U) (σ : Representation (ZMod 2) H V)
    (f : U →ₗ[ZMod 2] V) (hf : Function.Surjective f)
    (he : ∀ g v, f (ρ g v) = σ g (f v)) (hσ : Function.Injective σ) :
    Function.Injective ρ := by
  intro g h hgh
  apply hσ
  ext v
  obtain ⟨u, rfl⟩ := hf v
  rw [← he, ← he, hgh]

/-- A submodule with faithful action makes the whole action faithful. -/
theorem faithful_of_faithful_subrepresentation
    (ρ : Representation (ZMod 2) H U) (K : Subrepresentation ρ)
    (hK : Function.Injective K.toRepresentation) : Function.Injective ρ := by
  intro g h hgh
  apply hK
  ext v
  exact LinearMap.congr_fun hgh v

/-- An actual noncyclic elementary actor contains a subgroup of order four. -/
theorem exists_four_subgroup (A : Subgroup H) [Finite A]
    [IsElementaryAbelian 2 A] (hn : ¬ IsCyclic A) :
    ∃ E ≤ A, Nat.card E = 4 := by
  have hA := IsElementaryAbelian.isPGroup 2 A
  obtain ⟨n, hncard⟩ := hA.exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra! h
    have hdiv : Nat.card A ∣ 2 := by
      rw [hncard]
      interval_cases n <;> norm_num
    exact hn (isCyclic_of_card_dvd_prime hdiv)
  have h4 : 2 ^ 2 ≤ Nat.card A := by
    rw [hncard]
    exact Nat.pow_le_pow_right (by decide) hn2
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card Nat.prime_two hA h4
  refine ⟨E.map A.subtype, Subgroup.map_subtype_le E, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact hE

/-- The extracted subgroup retains the elementary-abelian structure in the
original actor, rather than in a separately tagged group. -/
theorem exists_elementary_four_subgroup (A : Subgroup H) [Finite A]
    [IsElementaryAbelian 2 A] (hn : ¬ IsCyclic A) :
    ∃ E ≤ A, IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  obtain ⟨E, hEA, hE⟩ := exists_four_subgroup A hn
  have hA0 : A ≠ ⊥ := by
    intro h
    subst A
    exact hn inferInstance
  have hE0 : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE
    omega
  exact ⟨E, hEA, (IsElementaryTwo.of_le ⟨hA0, inferInstance⟩ hEA hE0).2, hE⟩

theorem quadratic_of_le (ρ : Representation (ZMod 2) H U)
    {A B : Subgroup H} (hq : IsQuadratic ρ A) (hBA : B ≤ A) : IsQuadratic ρ B :=
  fun a ha b hb v => hq a (hBA ha) b (hBA hb) v

theorem quadratic_subrepresentation (ρ : Representation (ZMod 2) H U)
    (A : Subgroup H) (hq : IsQuadratic ρ A) (W : Subrepresentation ρ) :
    IsQuadratic W.toRepresentation A := by
  intro a ha b hb v
  apply Subtype.ext
  exact hq a ha b hb v

theorem quadratic_quotient (ρ : Representation (ZMod 2) H U)
    (A : Subgroup H) (hq : IsQuadratic ρ A) (W : Subrepresentation ρ) :
    IsQuadratic W.quotientRepresentation A := by
  intro a ha b hb v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change W.quotientRepresentation a
      (W.toSubmodule.mkQ (ρ b v) - W.toSubmodule.mkQ v) =
        W.toSubmodule.mkQ (ρ b v) - W.toSubmodule.mkQ v
    rw [← map_sub, Subrepresentation.quotientRepresentation_mk, hq a ha b hb v]

theorem quadratic_section (ρ : Representation (ZMod 2) H U)
    (A : Subgroup H) (hq : IsQuadratic ρ A) (Y X : Subrepresentation ρ) :
    IsQuadratic (sectionRepresentation ρ Y X) A :=
  quadratic_quotient X.toRepresentation A (quadratic_subrepresentation ρ A hq X)
    (sectionLower ρ Y X)

theorem quadratic_dual [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (A : Subgroup H) (hq : IsQuadratic ρ A) :
    IsQuadratic ρ.dual A := by
  have h := (commutator_le_invariants_iff (ρ.comp A.subtype)).mpr
    (fun a b v => hq a a.property b b.property v)
  have hd := (commutator_le_invariants_iff_dual (ρ.comp A.subtype)).mp h
  have hp := (commutator_le_invariants_iff (Representation.dual (ρ.comp A.subtype))).mp hd
  exact fun a ha b hb v => hp ⟨a, ha⟩ ⟨b, hb⟩ v

theorem FixesHyperplane.of_le {ρ : Representation (ZMod 2) H U}
    {A B : Subgroup H} (h : FixesHyperplane ρ A) (hBA : B ≤ A) :
    FixesHyperplane ρ B := by
  obtain ⟨P, hP, hfix⟩ := h
  exact ⟨P, hP, fun g hg v hv => hfix g (hBA hg) v hv⟩

theorem HasCommonAxis.of_le {ρ : Representation (ZMod 2) H U}
    {A B : Subgroup H} (h : HasCommonAxis ρ A) (hBA : B ≤ A) :
    HasCommonAxis ρ B := by
  obtain ⟨P, hP, hfix⟩ := h
  exact ⟨P, hP, fun g hg hne => hfix g (hBA hg) hne⟩

/-- Faithfulness excludes the identity transformation, so a fixed hyperplane
is the entire fixed space of every nonidentity group element. -/
theorem commonAxis_of_fixesHyperplane [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (A : Subgroup H) (h : FixesHyperplane ρ A) : HasCommonAxis ρ A := by
  obtain ⟨P, hP, hfix⟩ := h
  refine ⟨P, hP, ?_⟩
  intro g hg hne
  have hle : P ≤ (ρ g - 1).ker := by
    intro v hv
    change ρ g v - v = 0
    exact sub_eq_zero.mpr (hfix g hg v hv)
  have hproper : (ρ g - 1).ker ≠ ⊤ := by
    intro he
    have he' : ρ g = 1 := sub_eq_zero.mp (LinearMap.ker_eq_top.mp he)
    exact hne (hρ (he'.trans (map_one ρ).symm))
  have hrank := P.finrank_quotient_add_finrank
  have hstrict := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hproper)
  have hmono := Submodule.finrank_mono hle
  have hdim : Module.finrank (ZMod 2) P = Module.finrank (ZMod 2) (ρ g - 1).ker := by
    simp only [finrank_top] at hstrict
    omega
  exact (Submodule.eq_of_le_of_finrank_eq hle hdim).symm

/-- The fixed space in the contragredient is the annihilator of the original
displacement space, with the inverse required by the action convention. -/
theorem dual_displacement_ker (ρ : Representation (ZMod 2) H U) (g : H) :
    (ρ.dual g - 1).ker = (LinearMap.range (ρ g⁻¹ - 1)).dualAnnihilator := by
  have he : ρ.dual g - 1 = (ρ g⁻¹ - 1).dualMap := by
    ext f v
    simp [Module.Dual.transpose_apply]
  rw [he, LinearMap.ker_dualMap_eq_dualAnnihilator_range]

/-- A common transvection center on the chosen module becomes a common
hyperplane axis on its dual, not on an unrelated head of the ambient module. -/
theorem HasCommonCenter.dual {ρ : Representation (ZMod 2) H U}
    {A : Subgroup H} (h : HasCommonCenter ρ A) : HasCommonAxis ρ.dual A := by
  obtain ⟨L, hL, hcenter⟩ := h
  refine ⟨L.dualAnnihilator, ?_, ?_⟩
  · rw [(Subspace.quotAnnihilatorEquiv L).finrank_eq, Subspace.dual_finrank_eq]
    exact hL
  · intro g hg hne
    rw [dual_displacement_ker, hcenter g⁻¹ (A.inv_mem hg) (inv_ne_one.mpr hne)]

/-- The actual dual of an intertwining equivalence is intertwining for the
contragredient actions. -/
theorem equivariant_dual
    (ρ : Representation (ZMod 2) H U) (σ : Representation (ZMod 2) H V)
    (e : U ≃ₗ[ZMod 2] V) (he : ∀ g u, e (ρ g u) = σ g (e u)) :
    ∀ g f, e.symm.dualMap (ρ.dual g f) = σ.dual g (e.symm.dualMap f) := by
  intro g f
  ext v
  change f (ρ g⁻¹ (e.symm v)) = f (e.symm (σ g⁻¹ v))
  congr 1
  apply e.injective
  rw [he, e.apply_symm_apply, e.apply_symm_apply]

/-- Evaluation is the equivariant identification with the double dual. -/
theorem equivariant_eval [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (g : H) (v : U) :
    Module.evalEquiv (ZMod 2) U (ρ g v) =
      ρ.dual.dual g (Module.evalEquiv (ZMod 2) U v) := by
  ext f
  change f (ρ g v) = f (ρ (g⁻¹)⁻¹ v)
  rw [inv_inv]

/-- Natural-or-dual identifications are closed under duality, through the
specified actor equivalence and an explicit double-dual identification. -/
theorem naturalOrDual_dual (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (h : IsNaturalOrDual ρ eH) :
    IsNaturalOrDual ρ.dual eH := by
  rcases h with ⟨e, he⟩ | ⟨e, he⟩
  · exact Or.inr ⟨e.symm.dualMap, equivariant_dual ρ (naturalAction eH) e he⟩
  · let d := Module.evalEquiv (ZMod 2) NaturalSpace
    refine Or.inl ⟨e.symm.dualMap.trans d.symm, ?_⟩
    intro g f
    apply d.injective
    change d (d.symm (e.symm.dualMap (ρ.dual g f))) =
      d (eH g (d.symm (e.symm.dualMap f)))
    rw [d.apply_symm_apply]
    change _ = d ((naturalAction eH) g (d.symm (e.symm.dualMap f)))
    rw [equivariant_eval, d.apply_symm_apply]
    exact equivariant_dual ρ (naturalAction eH).dual e he g f

/-- An equivariant natural identification is faithful. -/
theorem natural_faithful (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (h : IsNatural ρ eH) :
    Function.Injective ρ := by
  obtain ⟨e, he⟩ := h
  intro g k hgk
  apply eH.injective
  ext v
  obtain ⟨u, rfl⟩ := e.surjective v
  rw [← he, ← he, hgk]

/-- Faithfulness is reflected from the contragredient to the original action. -/
theorem faithful_of_dual_faithful (ρ : Representation (ZMod 2) H U)
    (h : Function.Injective ρ.dual) : Function.Injective ρ := by
  intro g k hgk
  apply inv_injective
  apply h
  ext f v
  change f (ρ (g⁻¹)⁻¹ v) = f (ρ (k⁻¹)⁻¹ v)
  simp only [inv_inv, hgk]

theorem naturalOrDual_faithful (ρ : Representation (ZMod 2) H U)
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (h : IsNaturalOrDual ρ eH) :
    Function.Injective ρ := by
  rcases h with h | ⟨e, he⟩
  · exact natural_faithful ρ eH h
  · apply faithful_of_dual_faithful ρ
    let d := Module.evalEquiv (ZMod 2) NaturalSpace
    apply natural_faithful ρ.dual eH
    refine ⟨e.symm.dualMap.trans d.symm, ?_⟩
    intro g f
    apply d.injective
    change d (d.symm (e.symm.dualMap (ρ.dual g f))) =
      d (eH g (d.symm (e.symm.dualMap f)))
    rw [d.apply_symm_apply]
    change _ = d ((naturalAction eH) g (d.symm (e.symm.dualMap f)))
    rw [equivariant_eval, d.apply_symm_apply]
    exact equivariant_dual ρ (naturalAction eH).dual e he g f

/-- Transfer the actual natural-or-dual identification through an
intertwining linear equivalence. -/
theorem naturalOrDual_of_equivariant
    (ρ : Representation (ZMod 2) H U) (σ : Representation (ZMod 2) H V)
    (e : U ≃ₗ[ZMod 2] V) (he : ∀ g u, e (ρ g u) = σ g (e u))
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (h : IsNaturalOrDual σ eH) :
    IsNaturalOrDual ρ eH := by
  rcases h with ⟨d, hd⟩ | ⟨d, hd⟩
  · exact Or.inl ⟨e.trans d, fun g u => by simpa only [LinearEquiv.trans_apply, he] using hd g (e u)⟩
  · exact Or.inr ⟨e.trans d, fun g u => by simpa only [LinearEquiv.trans_apply, he] using hd g (e u)⟩

/-- Common axes are transported by the actual module equivalence. -/
theorem commonAxis_of_equivariant [FiniteDimensional (ZMod 2) U]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H U) (σ : Representation (ZMod 2) H V)
    (e : U ≃ₗ[ZMod 2] V) (he : ∀ g u, e (ρ g u) = σ g (e u))
    (A : Subgroup H) (h : HasCommonAxis σ A) : HasCommonAxis ρ A := by
  obtain ⟨P, hP, hker⟩ := h
  let Q := P.comap e.toLinearMap
  have hmap : Q.map e.toLinearMap = P := by
    exact Submodule.map_comap_eq_of_surjective e.surjective P
  have hdim : Module.finrank (ZMod 2) Q = Module.finrank (ZMod 2) P := by
    rw [← hmap]
    exact (e.submoduleMap Q).finrank_eq
  refine ⟨Q, ?_, ?_⟩
  · have hq := Q.finrank_quotient_add_finrank
    have hp := P.finrank_quotient_add_finrank
    have hu := e.finrank_eq
    omega
  · intro g hg hne
    ext u
    change (ρ g - 1) u = 0 ↔ e u ∈ P
    rw [← hker g hg hne]
    change ρ g u - u = 0 ↔ σ g (e u) - e u = 0
    rw [sub_eq_zero, sub_eq_zero, ← he, e.injective.eq_iff]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions
