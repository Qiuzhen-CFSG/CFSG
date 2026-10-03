module

public import Glauberman.SuzukiCharacterization.NormalizerFrobenius
public import Glauberman.SuzukiCharacterization.CommutatorSupport
public import Theory.Character.InertiaCentralizers
public import Theory.Character.Transport
public import Theory.Character.IrreducibleDegrees

/-!
# The normalizer action on nonprincipal Sylow characters

The stabilizer of each nonprincipal irreducible character of P is exactly PK,
where K is the normalizer's odd core. The forward inclusion follows from Brauer
permutation and the normalizer centralizer theorem. Conversely, P acts by inner
automorphisms and K centralizes P. Thus N/PK acts freely. Choosing a section of
the finite orbit quotient, with a prescribed first value, gives the ordinary
character representatives used in the restriction-degree argument.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Lemma 3.3 and equation (3.6), pp. 84–85, saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

@[expose] public section
open Subgroup
noncomputable section
attribute [local instance] Fintype.ofFinite

namespace Glauberman.SuzukiCharacterization
variable {G : Type*} [Group G] [Finite G]

theorem Hypotheses.mem_normalizerSylowCore_of_character_fixed
    (P : Sylow 2 G) (h : Hypotheses P) {χ : ClassFunction P}
    (hχ : IsIrreducibleCharacter χ) (hne : χ ≠ 1)
    (n : normalizer (P : Set G))
    (hfix : ∀ x : P, χ ((P : Subgroup G).normalizerMonoidHom n x) = χ x) :
    n ∈ normalizerSylowCore P := by
  let D := normalizer (P : Set G)
  let S := (P : Subgroup G).subgroupOf D
  have : S.Normal := normal_in_normalizer
  let e : S ≃* P := subgroupOfEquivOfLe (P : Subgroup G).le_normalizer
  apply inertia_le_of_centralizers_le S (normalizerSylowCore P) le_sup_left
    (fun x hx => h.normalizer_centralizer_le P x x.property
      (fun he => hx (Subtype.ext he)))
    (isIrreducibleCharacter_comp_mulEquiv e hχ)
    (fun he => hne (by
      funext x
      have hh := congrFun he (e.symm x)
      simpa using hh)) n
  intro x
  exact hfix (e x)

theorem character_fixed_of_mem_normalizerSylowCore
    (P : Sylow 2 G) {χ : ClassFunction P} (hχ : IsClassFunction χ)
    (n : normalizer (P : Set G)) (hn : n ∈ normalizerSylowCore P) :
    ∀ x : P, χ ((P : Subgroup G).normalizerMonoidHom n x) = χ x := by
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.mp hn
  have hbC := normalizerOddCore_le_centralizer P (mem_map_of_mem _ hb)
  intro x
  have hbx : (b : G) * (x : G) * (b : G)⁻¹ = x :=
    mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp hbC x x.property).symm
  have he : (P : Subgroup G).normalizerMonoidHom n x =
      (⟨(a : G), ha⟩ : P) * x * (⟨(a : G), ha⟩ : P)⁻¹ := by
    apply Subtype.ext
    change (n : G) * (x : G) * (n : G)⁻¹ = (a : G) * (x : G) * (a : G)⁻¹
    have habG := congrArg Subtype.val hab
    change (a : G) * (b : G) = (n : G) at habG
    rw [← habG, mul_inv_rev]
    simpa only [mul_assoc] using congrArg (fun z : G => (a : G) * z * (a : G)⁻¹) hbx
  rw [he]
  exact hχ x ⟨(a : G), ha⟩
end Glauberman.SuzukiCharacterization

namespace Glauberman.SuzukiCharacterization
variable {G : Type*} [Group G] [Finite G]

theorem Hypotheses.character_fixed_iff
    (P : Sylow 2 G) (h : Hypotheses P) {χ : ClassFunction P}
    (hχ : IsIrreducibleCharacter χ) (hne : χ ≠ 1)
    (n : normalizer (P : Set G)) :
    (fun x : P => χ ((P : Subgroup G).normalizerMonoidHom n x)) = χ ↔
      n ∈ normalizerSylowCore P := by
  constructor
  · intro he
    exact h.mem_normalizerSylowCore_of_character_fixed P hχ hne n (congrFun he)
  · intro hn
    apply funext
    apply character_fixed_of_mem_normalizerSylowCore P _ n hn
    obtain ⟨d, ρ, _, rfl⟩ := hχ
    exact Representation.char_conj ρ

/-- The actual nonprincipal irreducible characters of the Sylow subgroup. -/
abbrev NonprincipalCharacter (P : Sylow 2 G) :=
  {χ : ClassFunction P // IsIrreducibleCharacter χ ∧ χ ≠ 1}

instance normalizerCharacterAction (P : Sylow 2 G) :
    MulAction (normalizer (P : Set G)) (NonprincipalCharacter P) where
  smul n χ := ⟨fun x => χ.val ((P : Subgroup G).normalizerMonoidHom n⁻¹ x),
    isIrreducibleCharacter_comp_mulEquiv _ χ.property.1, by
      intro he
      apply χ.property.2
      funext x
      obtain ⟨y, rfl⟩ := ((P : Subgroup G).normalizerMonoidHom n⁻¹).surjective x
      exact congrFun he y⟩
  one_smul χ := by
    apply Subtype.ext
    funext x
    change χ.val ((P : Subgroup G).normalizerMonoidHom (1 : normalizer (P : Set G))⁻¹ x) = χ.val x
    simp
  mul_smul m n χ := by
    apply Subtype.ext
    funext x
    change χ.val ((P : Subgroup G).normalizerMonoidHom (m * n)⁻¹ x) =
      χ.val ((P : Subgroup G).normalizerMonoidHom n⁻¹ ((P : Subgroup G).normalizerMonoidHom m⁻¹ x))
    simp [mul_inv_rev]

theorem Hypotheses.character_stabilizer_eq
    (P : Sylow 2 G) (h : Hypotheses P) (χ : NonprincipalCharacter P) :
    MulAction.stabilizer (normalizer (P : Set G)) χ = normalizerSylowCore P := by
  ext n
  change ((n • χ : NonprincipalCharacter P) = χ) ↔ _
  rw [Subtype.ext_iff]
  change (fun x : P => χ.val ((P : Subgroup G).normalizerMonoidHom n⁻¹ x)) = χ.val ↔ _
  rw [h.character_fixed_iff P χ.property.1 χ.property.2, inv_mem_iff]

instance normalizerSylowCore_normal (P : Sylow 2 G) :
    (normalizerSylowCore P).Normal := by
  have : ((P : Subgroup G).subgroupOf (normalizer (P : Set G))).Normal := normal_in_normalizer
  unfold normalizerSylowCore
  infer_instance

theorem normalizerSylowCore_le_characterAction_ker (P : Sylow 2 G) :
    normalizerSylowCore P ≤
      (MulAction.toPermHom (normalizer (P : Set G)) (NonprincipalCharacter P)).ker := by
  intro n hn
  apply Equiv.ext
  intro χ
  apply Subtype.ext
  apply funext
  apply character_fixed_of_mem_normalizerSylowCore P _ n⁻¹
    ((normalizerSylowCore P).inv_mem hn)
  obtain ⟨d, ρ, _, hρ⟩ := χ.property.1
  intro x g
  exact (congrFun hρ _).trans ((Representation.char_conj ρ x g).trans (congrFun hρ _).symm)

instance normalizerQuotientCharacterAction (P : Sylow 2 G) :
    MulAction ((normalizer (P : Set G)) ⧸ normalizerSylowCore P) (NonprincipalCharacter P) :=
  MulAction.compHom _ (QuotientGroup.lift (normalizerSylowCore P)
    (MulAction.toPermHom (normalizer (P : Set G)) (NonprincipalCharacter P))
    (normalizerSylowCore_le_characterAction_ker P))

theorem normalizerQuotient_mk_smul (P : Sylow 2 G)
    (n : normalizer (P : Set G)) (χ : NonprincipalCharacter P) :
    (QuotientGroup.mk' (normalizerSylowCore P) n) • χ = n • χ := rfl

theorem Hypotheses.normalizerQuotient_character_free (P : Sylow 2 G) (h : Hypotheses P) :
    IsCancelSMul ((normalizer (P : Set G)) ⧸ normalizerSylowCore P) (NonprincipalCharacter P) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro n χ hn
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (normalizerSylowCore P) n
  rw [normalizerQuotient_mk_smul] at hn
  apply (QuotientGroup.eq_one_iff (N := normalizerSylowCore P) m).mpr
  rw [← h.character_stabilizer_eq P χ]
  exact hn
end Glauberman.SuzukiCharacterization

namespace Glauberman.SuzukiCharacterization
variable {G : Type*} [Group G] [Finite G]

theorem normalizerCharacter_smul_apply (P : Sylow 2 G)
    (n : normalizer (P : Set G)) (χ : NonprincipalCharacter P) (x : P) :
    (n • χ : NonprincipalCharacter P).val x =
      χ.val ((P : Subgroup G).normalizerMonoidHom n⁻¹ x) := rfl

theorem normalizerCharacter_smul_one (P : Sylow 2 G)
    (n : normalizer (P : Set G)) (χ : NonprincipalCharacter P) :
    (n • χ : NonprincipalCharacter P).val 1 = χ.val 1 := by
  rw [normalizerCharacter_smul_apply, map_one]

theorem Hypotheses.card_character_orbit (P : Sylow 2 G) (h : Hypotheses P)
    (χ : NonprincipalCharacter P) :
    Nat.card (MulAction.orbit (normalizer (P : Set G)) χ) =
      (normalizerSylowCore P).index := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (normalizer (P : Set G)) χ)]
  change (MulAction.stabilizer (normalizer (P : Set G)) χ).index = _
  rw [h.character_stabilizer_eq]
end Glauberman.SuzukiCharacterization

namespace Glauberman.SuzukiCharacterization
variable {G : Type*} [Group G] [Finite G]

instance finite_nonprincipalCharacter (P : Sylow 2 G) : Finite (NonprincipalCharacter P) := by
  have : Finite {χ : ClassFunction P // IsIrreducibleCharacter χ} :=
    Nat.finite_of_card_ne_zero (by
      rw [Theory.Character.card_irreducibleCharacters]
      exact Nat.card_pos.ne')
  exact Finite.of_injective
    (fun χ : NonprincipalCharacter P =>
      (⟨χ.val, χ.property.1⟩ : {χ : ClassFunction P // IsIrreducibleCharacter χ}))
    (by
      intro a b he
      apply Subtype.ext
      exact congrArg (fun χ : {χ : ClassFunction P // IsIrreducibleCharacter χ} => χ.val) he)

/-- A pointed complete set of normalizer-orbit representatives. -/
structure NormalizerCharacterOrbitData (P : Sylow 2 G) (s : CommutatorSupportData P) where
  r : ℕ
  pos : 0 < r
  rep : Fin r → NonprincipalCharacter P
  first : (rep ⟨0, pos⟩).val = s.theta
  orbit_bijective : Function.Bijective
    (fun p : Fin r × ((normalizer (P : Set G)) ⧸ normalizerSylowCore P) =>
      p.2 • rep p.1)

/-- Lemma 3.3 with the specified linear character as the first representative. -/
theorem Hypotheses.exists_normalizerCharacterOrbitData
    (P : Sylow 2 G) (h : Hypotheses P) (s : CommutatorSupportData P) :
    Nonempty (NormalizerCharacterOrbitData P s) := by
  classical
  let A := (normalizer (P : Set G)) ⧸ normalizerSylowCore P
  let X := NonprincipalCharacter P
  let R := MulAction.orbitRel A X
  let Q := Quotient R
  let x₀ : X := ⟨s.theta, s.linear.1, s.theta_ne_one⟩
  let q₀ : Q := Quotient.mk R x₀
  let rep (q : Q) : X := if q = q₀ then x₀ else q.out
  have hrep (q : Q) : Quotient.mk R (rep q) = q := by
    dsimp [rep]
    split_ifs with he
    · exact he.symm
    · exact q.out_eq
  have hr : 0 < Fintype.card Q := Fintype.card_pos_iff.mpr ⟨q₀⟩
  let E : Q ≃ Fin (Fintype.card Q) :=
    (Fintype.equivFin Q).trans (Equiv.swap ((Fintype.equivFin Q) q₀) ⟨0, hr⟩)
  have he : E q₀ = ⟨0, hr⟩ := by simp [E]
  let ψ (i : Fin (Fintype.card Q)) := rep (E.symm i)
  let F : Fin (Fintype.card Q) × A → X := fun p => p.2 • ψ p.1
  have hFq (i) (a : A) : Quotient.mk R (F (i, a)) = E.symm i := by
    exact (MulAction.orbitRel.Quotient.quotient_smul_eq).trans (hrep _)
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, a⟩ ⟨j, b⟩ hab
      have hij : i = j := E.symm.injective
        ((hFq i a).symm.trans ((congrArg (Quotient.mk R) hab).trans (hFq j b)))
      subst j
      have : IsCancelSMul A X := h.normalizerQuotient_character_free P
      have hab' : a = b := IsCancelSMul.right_cancel a b (ψ i) hab
      exact Prod.ext rfl hab'
    · intro χ
      let q : Q := Quotient.mk R χ
      have hrel : R (rep q) χ := Quotient.exact (hrep q)
      obtain ⟨a, ha⟩ := hrel
      refine ⟨(E q, a⁻¹), ?_⟩
      change a⁻¹ • rep (E.symm (E q)) = χ
      rw [E.symm_apply_apply, ← ha, inv_smul_smul]
  refine ⟨⟨Fintype.card Q, hr, ψ, ?_, hF⟩⟩
  change (rep (E.symm ⟨0, hr⟩)).val = s.theta
  rw [← he, E.symm_apply_apply]
  simp [rep, x₀]

namespace NormalizerCharacterOrbitData
variable {P : Sylow 2 G} {s : CommutatorSupportData P}
variable (o : NormalizerCharacterOrbitData P s)

abbrev firstIndex : Fin o.r := ⟨0, o.pos⟩
def psi (j : Fin o.r) : ClassFunction P := (o.rep j).val
def degree (j : Fin o.r) : ℕ := (o.rep j).property.1.degree

theorem psi_irreducible (j : Fin o.r) : IsIrreducibleCharacter (o.psi j) :=
  (o.rep j).property.1

theorem psi_ne_one (j : Fin o.r) : o.psi j ≠ 1 := (o.rep j).property.2

theorem psi_first : o.psi o.firstIndex = s.theta := o.first

theorem psi_one (j : Fin o.r) : o.psi j 1 = (o.degree j : ℂ) :=
  (o.rep j).property.1.degree_eq

theorem degree_pos (j : Fin o.r) : 0 < o.degree j := (o.rep j).property.1.degree_pos

theorem degree_first : o.degree o.firstIndex = 1 := by
  have he := o.psi_one o.firstIndex
  rw [o.psi_first, s.linear.2] at he
  exact_mod_cast he.symm

theorem orbit_disjoint (i j : Fin o.r) (n : normalizer (P : Set G))
    (he : n • o.rep i = o.rep j) : i = j := by
  have he' : (QuotientGroup.mk' (normalizerSylowCore P) n) • o.rep i =
      (1 : ((normalizer (P : Set G)) ⧸ normalizerSylowCore P)) • o.rep j := by
    simpa only [normalizerQuotient_mk_smul, one_smul] using he
  exact congrArg Prod.fst (o.orbit_bijective.1
    (a₁ := (i, QuotientGroup.mk' (normalizerSylowCore P) n)) (a₂ := (j, 1)) he')

theorem orbit_cover (χ : NonprincipalCharacter P) :
    ∃ (j : Fin o.r) (n : normalizer (P : Set G)), n • o.rep j = χ := by
  obtain ⟨⟨j, a⟩, ha⟩ := o.orbit_bijective.2 χ
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (normalizerSylowCore P) a
  exact ⟨j, n, ha⟩

end NormalizerCharacterOrbitData
end Glauberman.SuzukiCharacterization

namespace Glauberman.SuzukiCharacterization.NormalizerCharacterOrbitData
variable {G : Type*} [Group G] [Finite G]
variable {P : Sylow 2 G} {s : CommutatorSupportData P}

/-- Conjugates of representatives coincide precisely on the same orbit and in PK. -/
theorem psi_conjugate_eq_iff (o : NormalizerCharacterOrbitData P s) (h : Hypotheses P)
    (i j : Fin o.r) (n : normalizer (P : Set G)) :
    (fun x : P => o.psi i ((P : Subgroup G).normalizerMonoidHom n x)) = o.psi j ↔
      i = j ∧ n ∈ normalizerSylowCore P := by
  constructor
  · intro he
    have hij : i = j := by
      apply o.orbit_disjoint i j n⁻¹
      apply Subtype.ext
      funext x
      rw [normalizerCharacter_smul_apply, inv_inv]
      exact congrFun he x
    subst j
    exact ⟨rfl, (h.character_fixed_iff P (o.psi_irreducible i) (o.psi_ne_one i) n).mp he⟩
  · rintro ⟨rfl, hn⟩
    exact (h.character_fixed_iff P (o.psi_irreducible i) (o.psi_ne_one i) n).mpr hn

end Glauberman.SuzukiCharacterization.NormalizerCharacterOrbitData
