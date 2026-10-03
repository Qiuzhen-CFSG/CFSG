module

public import Theory.GroupAction.Order512FiveInvolutionCosets
public import Theory.GroupTheory.CentralSquareAutomorphisms
public import Theory.SpecificGroups.ReeTwo.CoreFrame

/-!
# Intrinsic input and symmetry normalization for a Ree extension

The data consist of the order-512 residual in its order-1024 extension, the
native five-action, a generating involution, and an automorphism squaring the
five-action and preserving or inverting the prescribed root. They include no
frame equations, model recognition, or order assumption on that automorphism.

The involutory-coset census lets us multiply the symmetry by a five-actor so
that it fixes the generating seed modulo the residual derived subgroup.
It then doubles orbit indices on that quotient. Its action on the actual
root displacement is equivariant even when the root is inverted.

The four explicit orbit words still require an intrinsic calculation of their
quotient squares and commutators and of their central pairing. Those facts are
not part of the data and are not asserted here.

Sources: Thompson VI, pp.629–630; Parrott (1972), pp.672–674, especially the
five involutory cosets; Shinoda (1975), pp.81–82, for the intended root order.
-/

@[expose] public section
namespace ReeTwo
open Subgroup
variable {K A : Type*} [Group K] [Group A]

/-- Intrinsic input for the semilinear normalization of the residual extension.
No coordinate, presentation, or order condition on the squaring lift is included. -/
structure SemilinearExtensionData (ρ : A →* MulAut K) (R : Subgroup K)
    (t z : K) (b : R) (σ : MulAut K) : Prop where
  actor_card : Nat.card A = 5
  core_card : Nat.card K = 1024
  residual_card : Nat.card R = 512
  residual_normal : R.Normal
  residual_class : Group.nilpotencyClass R = 3
  invariant : ∀ a x, ρ a x ∈ R ↔ x ∈ R
  center_card : Nat.card ((center R).map R.subtype) = 2
  derived_card : Nat.card ((commutator R).map R.subtype) = 32
  derived_elementary : IsElementaryAbelian 2 ((commutator R).map R.subtype)
  derived_eq : (commutator R).map R.subtype = commutator K
  derived_commutator : ⁅(commutator R).map R.subtype, (⊤ : Subgroup K)⁆ =
    (center R).map R.subtype
  center_eq : center K = (center R).map R.subtype
  residual_derived_centralizer : R ⊓ centralizer ((commutator R).map R.subtype : Set K) =
    (commutator R).map R.subtype
  residual_centralizer : centralizer (R : Set K) = (center R).map R.subtype
  fixed_central : ∀ x : R, (∀ a, ρ a x = x) → x ∈ center R
  root_outside : t ∉ R
  central_mem : z ∈ (center R).map R.subtype
  central_order : orderOf z = 2
  root_square : t ^ 2 = z
  root_fixed : ∀ a, ρ a t = t
  root_centralizes : t ∈ centralizer ((commutator R).map R.subtype : Set K)
  root_generates : R ⊔ zpowers t = ⊤
  root_centralizer : R ⊓ centralizer ({t} : Set K) = (commutator R).map R.subtype
  root_commutator : ⁅R, zpowers t⁆ = (commutator R).map R.subtype
  seed_square : b ^ 2 = 1
  seed_outside : b ∉ commutator R
  seed_generates : closure (Set.range (fun a : A => ρ a (b : K))) = R
  symmetry_invariant : ∀ x, σ x ∈ R ↔ x ∈ R
  symmetry_squares : ∀ a, σ * ρ a * σ⁻¹ = ρ (a ^ 2)
  symmetry_root : σ t = t ∨ σ t = t⁻¹

/-- The four candidate words, before removing their central errors. -/
def orbitFrame (ρ : A →* MulAut K) (b : K) (g : A) (t : K) : Fin 4 → K :=
  ![b, ρ (g ^ 2) b * ρ (g ^ 3) b * t,
    ρ g b * ρ (g ^ 2) b * t, b * ρ g b * ρ (g ^ 2) b * ρ (g ^ 3) b]

/-- The actual root displacement is equivariant even if the symmetry inverts
rather than fixes the root. This is an equality before taking a quotient. -/
theorem map_root_rightComm (σ : MulAut K) (t : K)
    (ht : t ^ 2 ∈ center K) (hσ : σ t = t ∨ σ t = t⁻¹) (x : K) :
    σ (rightComm x t) = rightComm (σ x) t := by
  have hinv := MulAut.conj_inv_eq_of_square_central t ht
  have hc := MulAut.commute_conj_of_preserves_root σ t ht hσ
  have he := congrArg (fun f : MulAut K => f x) hc.eq
  change σ (MulAut.conj t x) = MulAut.conj t (σ x) at he
  calc
    σ (rightComm x t) = (σ x)⁻¹ * σ (MulAut.conj (t⁻¹) x) := by
      change σ (x⁻¹ * t⁻¹ * x * t) = (σ x)⁻¹ * σ (t⁻¹ * x * (t⁻¹)⁻¹)
      simp only [inv_inv, map_mul, map_inv, mul_assoc]
    _ = (σ x)⁻¹ * MulAut.conj (t⁻¹) (σ x) := by rw [hinv, he]
    _ = rightComm (σ x) t := by
      change (σ x)⁻¹ * (t⁻¹ * σ x * (t⁻¹)⁻¹) = (σ x)⁻¹ * t⁻¹ * σ x * t
      simp only [inv_inv, mul_assoc]

private def restrictAut (R : Subgroup K) (σ : MulAut K)
    (hσ : ∀ x, σ x ∈ R ↔ x ∈ R) : MulAut R where
  toFun x := ⟨σ x, (hσ x).mpr x.property⟩
  invFun x := ⟨σ⁻¹ x, (hσ (σ⁻¹ x)).mp (by simp)⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x)
  right_inv x := Subtype.ext (σ.apply_symm_apply x)
  map_mul' x y := Subtype.ext (map_mul σ (x : K) (y : K))

/-- Twist the given symmetry by an actor so that it fixes the seed modulo the
residual derived subgroup. The twist retains every original input, including
the permitted inversion of the prescribed root. -/
theorem exists_seed_normalized_symmetry [Finite A] [Finite K]
    (ρ : A →* MulAut K) (R : Subgroup K) (t z : K) (b : R) (σ : MulAut K)
    (h : SemilinearExtensionData ρ R t z b σ) :
    ∃ c : A, SemilinearExtensionData ρ R t z b (ρ c * σ) ∧
      (ρ c (σ b)) / (b : K) ∈ (commutator R).map R.subtype := by
  let _ : MulDistribMulAction A K := MulDistribMulAction.compHom K ρ
  let _ : IsInvariant A K R := ⟨fun a x => (h.invariant a x).symm⟩
  let σR := restrictAut R σ h.symmetry_invariant
  have hb2 : σR b ^ 2 = 1 := by rw [← map_pow, h.seed_square, map_one]
  have hbD : σR b ∉ commutator R := by
    intro hh
    have hi := characteristic_iff_le_comap.mp
      (inferInstance : (commutator R).Characteristic) σR.symm hh
    exact h.seed_outside (by simpa using hi)
  have hfixed : FixedPoints.subgroup A R ≤ center R := by
    intro x hx
    exact h.fixed_central x (fun a => congrArg Subtype.val (hx a))
  obtain ⟨_, horbit⟩ := Theory.GroupAction.parrott_involutory_derived_coset_census
    (IsPGroup.of_card (p := 2) (n := 9) h.residual_card) h.residual_card
    h.residual_class.ge h.actor_card hfixed b h.seed_square h.seed_outside
  obtain ⟨c, hc⟩ := horbit (σR b) hb2 hbD
  have hcoset : (ρ c (σ b)) / (b : K) ∈ (commutator R).map R.subtype := by
    have hm : (c • σR b) / b ∈ commutator R := QuotientGroup.eq_iff_div_mem.mp hc
    exact mem_map_of_mem R.subtype hm
  let _ : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let _ : IsCyclic A := isCyclic_of_prime_card h.actor_card
  have hac (a : A) : Commute (ρ c) (ρ (a ^ 2)) := by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm' c]
  refine ⟨c, { h with
    symmetry_invariant := ?_, symmetry_squares := ?_, symmetry_root := ?_ }, hcoset⟩
  · intro x
    change ρ c (σ x) ∈ R ↔ x ∈ R
    exact (h.invariant c (σ x)).trans (h.symmetry_invariant x)
  · intro a
    calc
      (ρ c * σ) * ρ a * (ρ c * σ)⁻¹ =
          ρ c * (σ * ρ a * σ⁻¹) * (ρ c)⁻¹ := by group
      _ = ρ (a ^ 2) := by rw [h.symmetry_squares, (hac a).eq, mul_inv_cancel_right]
  · change ρ c (σ t) = t ∨ ρ c (σ t) = t⁻¹
    rcases h.symmetry_root with ht | ht
    · exact Or.inl (by rw [ht, h.root_fixed])
    · exact Or.inr (by rw [ht, map_inv, h.root_fixed])

/-- The given central involution generates the whole center. -/
theorem SemilinearExtensionData.center_eq_zpowers [Finite K]
    {ρ : A →* MulAut K} {R : Subgroup K} {t z : K} {b : R} {σ : MulAut K}
    (h : SemilinearExtensionData ρ R t z b σ) : center K = zpowers z := by
  have hz : z ∈ center K := h.center_eq.symm ▸ h.central_mem
  apply (eq_of_le_of_card_ge (zpowers_le.mpr hz) ?_).symm
  rw [h.center_eq, h.center_card, Nat.card_zpowers, h.central_order]

/-- Equivariance of the actual displacement follows from the supplied input;
no quotient identification is needed for this step. -/
theorem SemilinearExtensionData.root_displacement_equivariant
    {ρ : A →* MulAut K} {R : Subgroup K} {t z : K} {b : R} {σ : MulAut K}
    (h : SemilinearExtensionData ρ R t z b σ) (x : K) :
    σ (rightComm x t) = rightComm (σ x) t := by
  apply map_root_rightComm σ t _ h.symmetry_root x
  rw [h.root_square, h.center_eq]
  exact h.central_mem

/-- After seed normalization, the symmetry doubles every orbit index modulo
D. This is the intrinsic source of its matrix in a five-orbit basis. -/
theorem SemilinearExtensionData.symmetry_orbit_coset
    {ρ : A →* MulAut K} {R : Subgroup K} {t z : K} {b : R} {σ : MulAut K}
    (h : SemilinearExtensionData ρ R t z b σ)
    (hseed : σ b / (b : K) ∈ (commutator R).map R.subtype) (a : A) :
    σ (ρ a b) / ρ (a ^ 2) b ∈ (commutator R).map R.subtype := by
  have he : σ * ρ a = ρ (a ^ 2) * σ :=
    mul_inv_eq_iff_eq_mul.mp (h.symmetry_squares a)
  have hev := congrArg (fun f : MulAut K => f (b : K)) he
  change σ (ρ a b) = ρ (a ^ 2) (σ b) at hev
  rw [h.derived_eq] at hseed ⊢
  have hm := characteristic_iff_le_comap.mp
    (inferInstance : (commutator K).Characteristic) (ρ (a ^ 2)) hseed
  change ρ (a ^ 2) (σ b / (b : K)) ∈ commutator K at hm
  simpa only [map_div, hev] using hm

end ReeTwo
