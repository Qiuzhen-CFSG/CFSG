module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.QuaternionCentralProductSylowIndex
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Sylow

/-!
# The marked exceptional geometry in §5.3.7

This file is the interface for the exceptional `L₃(4)` branch.  The two
maximal 2-locals and their rank-two subgroups are kept as *marked* subgroups
of one ambient group.  In particular, the quotient assertions below are
genuine quotient isomorphisms; an order calculation by itself is not used as
a replacement for the amalgam.

The recognition and even-characteristic results from §5.3 are inputs to the
certificate.  The lemmas in this file package the local consequences in the
form used by the centralizer argument.  This separation is useful because the
centralizer argument must not import its own conclusion back into the marked
geometry.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
§5.3.7, printed pp. 660--661 (PDF pp. 677--678).
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter5.Section03ExceptionalGeometry

universe u

variable {G : Type u} [Group G] [Finite G]

/- The span of the conjugates of a marked subgroup.  Its codomain is the
ambient group, so it can be used directly in centralizer and normalizer
statements. -/
public noncomputable def conjugateSpan (H V : Subgroup G) : Subgroup G :=
  ⨆ g : H, V.map (MulAut.conj (g : G)).toMonoidHom

/-- The marked `L₃(4)` amalgam.  The two quotient maps are represented by
actual isomorphisms from `Mᵢ/Vᵢ`; the fields `intersection` and `generation`
    record the marked amalgam rather than merely its order. -/
public structure MarkedL3FourAmalgam (G : Type u) [Group G] [Finite G] where
  T : Sylow 2 G
  M₁ : Subgroup G
  M₂ : Subgroup G
  V₁ : Subgroup G
  V₂ : Subgroup G
  S : Subgroup G
  Z : Subgroup G
  z : G
  z_in_center : z ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype
  S_le_T : S ≤ (T : Subgroup G)
  Z_eq_center : (center S).map S.subtype = Z
  V₁_le_M₁ : V₁ ≤ M₁
  V₂_le_M₂ : V₂ ≤ M₂
  normal_V₁ : (V₁.subgroupOf M₁).Normal
  normal_V₂ : (V₂.subgroupOf M₂).Normal
  quotient₁ : ∃ f : M₁ →* Equiv.Perm (Fin 5), Function.Surjective f ∧
    f.ker = V₁.subgroupOf M₁
  quotient₂ : ∃ f : M₂ →* Equiv.Perm (Fin 5), Function.Surjective f ∧
    f.ker = V₂.subgroupOf M₂
  intersection : M₁ ⊓ M₂ = (T : Subgroup G)
  generation : M₁ ⊔ M₂ = ⊤
  q : ℕ
  q_eq_four : q = 4
  even_characteristic : IsEvenCharacteristicAt T
  unique_marked_overgroup : ∀ M : Subgroup G, IsMaximalTwoLocal M →
    (T : Subgroup G) ≤ M → M = M₁ ∨ M = M₂

namespace MarkedL3FourAmalgam

variable (A : MarkedL3FourAmalgam G)

public theorem parameter_eq_four : A.q = 4 := A.q_eq_four

public theorem marked_intersection : A.M₁ ⊓ A.M₂ = (A.T : Subgroup G) :=
  A.intersection

public theorem marked_generation : A.M₁ ⊔ A.M₂ = ⊤ := A.generation

public theorem both_quotients_are_symmetric_five :
    (∃ f : A.M₁ →* Equiv.Perm (Fin 5), Function.Surjective f ∧
      f.ker = A.V₁.subgroupOf A.M₁) ∧
      (∃ f : A.M₂ →* Equiv.Perm (Fin 5), Function.Surjective f ∧
        f.ker = A.V₂.subgroupOf A.M₂) :=
  ⟨A.quotient₁, A.quotient₂⟩

end MarkedL3FourAmalgam

/- The local certificate obtained after writing `H = C_G(z)` and
`W = ⟨Zᴴ⟩`.  The fields are the source's local recognition statements.  They
are deliberately explicit: an application has to provide the even-
characteristic and uniqueness proofs at the marked amalgam, and cannot obtain
an ambient centralizer equality from a finite abstract model alone. -/
public structure LocalGeometry (A : MarkedL3FourAmalgam G) where
  H : Subgroup G
  Q : Subgroup G
  W : Subgroup G
  H_eq_centralizer : H = centralizer ({A.z} : Set G)
  W_eq_conjugateSpan : W = conjugateSpan H A.Z
  Q_le_H : Q ≤ H
  Q_normal_in_H : (Q.subgroupOf H).Normal
  Q_selfCentralizing_in_H :
    centralizer (Q.subgroupOf H : Set H) ≤ Q.subgroupOf H
  Q_card : Nat.card Q = 32
  B : Subgroup Q
  C : Subgroup Q
  B_quaternion : Nonempty (B ≃* QuaternionGroup 2)
  C_quaternion : Nonempty (C ≃* QuaternionGroup 2)
  BC_intersection : Nat.card (B ⊓ C : Subgroup Q) = 2
  BC_commute : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b
  BC_generate : B ⊔ C = ⊤
  Q_center_card : Nat.card (center Q) = 2
  z_in_Q : A.z ∈ Q
  quotient_center : Subgroup Q
  quotient_center_normal : quotient_center.Normal
  quotient_center_card : Nat.card quotient_center = 2
  quotient_center_is_z : quotient_center =
    closure ({⟨A.z, z_in_Q⟩} : Set Q)
  quotient_is_E16 : ∃ (E : Type u) (_ : Group E) (f : Q →* E),
    Function.Surjective f ∧ f.ker = quotient_center ∧ Nat.card E = 16
  centralizer_Q_le_H : centralizer (Q : Set G) ≤ H
  C_T_Q_le_Q : centralizer (Q : Set G) ⊓ (A.T : Subgroup G) ≤ Q
  orbit_lower_bound : 4 ≤ H.index
  W_normalized : H ≤ normalizer (W : Set G)
  abelian_W_in_V : IsMulCommutative W → W ≤ A.V₁ ∨ W ≤ A.V₂
  abelian_W_alternative : IsMulCommutative W →
    (W = A.Z ∨ centralizer (W : Set G) = A.V₁ ∨
      centralizer (W : Set G) = A.V₂)
  nonabelian_W_in_S : ¬ IsMulCommutative W → W ≤ A.S →
    (center W).map W.subtype = A.Z
  nonabelian_W_eq_Q : ¬ IsMulCommutative W → ¬ W ≤ A.S → W = Q
  Vi_inter_Q_card : Nat.card (A.V₁ ⊓ Q : Subgroup G) = 8 ∧
    Nat.card (A.V₂ ⊓ Q : Subgroup G) = 8
  Vi_card : Nat.card (A.V₁ : Subgroup G) = 16 ∧ Nat.card (A.V₂ : Subgroup G) = 16
  Vi_elementary : IsElementaryAbelian 2 (↥A.V₁) ∧ IsElementaryAbelian 2 (↥A.V₂)
  local_two_group_bound :
    IsPGroup 2 (H ⊓ A.M₁ : Subgroup G) ∧
      IsPGroup 2 (H ⊓ A.M₂ : Subgroup G)

namespace LocalGeometry

variable {A : MarkedL3FourAmalgam G} (L : LocalGeometry A)

public theorem centralizer_identification : L.H = centralizer ({A.z} : Set G) :=
  L.H_eq_centralizer

public theorem conjugate_span_identification : L.W = conjugateSpan L.H A.Z :=
  L.W_eq_conjugateSpan

public theorem quaternion_core_card : Nat.card L.Q = 32 := L.Q_card

public theorem quaternion_core_quotient_order : Nat.card L.quotient_center = 2 :=
  L.quotient_center_card

public theorem quaternion_core_quotient_E16 :
    ∃ (E : Type u) (_ : Group E) (f : L.Q →* E),
      Function.Surjective f ∧ f.ker = L.quotient_center ∧ Nat.card E = 16 :=
  L.quotient_is_E16

public theorem quaternion_core_factors :
    Nonempty (L.B ≃* QuaternionGroup 2) ∧
      Nonempty (L.C ≃* QuaternionGroup 2) ∧
      Nat.card (L.B ⊓ L.C : Subgroup L.Q) = 2 ∧
      (∀ b ∈ L.B, ∀ c ∈ L.C, b * c = c * b) ∧ L.B ⊔ L.C = ⊤ :=
  ⟨L.B_quaternion, L.C_quaternion, L.BC_intersection,
    L.BC_commute, L.BC_generate⟩

public theorem quaternion_factor_orders :
    Nat.card L.B = 8 ∧ Nat.card L.C = 8 := by
  constructor
  · obtain ⟨e⟩ := L.B_quaternion
    rw [Nat.card_congr e.toEquiv]
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  · obtain ⟨e⟩ := L.C_quaternion
    rw [Nat.card_congr e.toEquiv]
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

public theorem nonabelian_W_alternatives (hncomm : ¬ IsMulCommutative L.W) :
    (L.W ≤ A.S → (center L.W).map L.W.subtype = A.Z) ∧
      (¬ L.W ≤ A.S → L.W = L.Q) :=
  ⟨L.nonabelian_W_in_S hncomm, L.nonabelian_W_eq_Q hncomm⟩

public theorem abelian_W_alternatives (hcomm : IsMulCommutative L.W) :
    (L.W ≤ A.V₁ ∨ L.W ≤ A.V₂) ∧
      (L.W = A.Z ∨ centralizer (L.W : Set G) = A.V₁ ∨
        centralizer (L.W : Set G) = A.V₂) :=
  ⟨L.abelian_W_in_V hcomm, L.abelian_W_alternative hcomm⟩

public theorem marked_Vi_geometry :
    (Nat.card (A.V₁ ⊓ L.Q : Subgroup G) = 8 ∧
      Nat.card (A.V₂ ⊓ L.Q : Subgroup G) = 8) ∧
      (Nat.card (A.V₁ : Subgroup G) = 16 ∧ Nat.card (A.V₂ : Subgroup G) = 16) ∧
      (IsElementaryAbelian 2 (↥A.V₁) ∧ IsElementaryAbelian 2 (↥A.V₂)) :=
  ⟨L.Vi_inter_Q_card, L.Vi_card, L.Vi_elementary⟩

public theorem local_two_group_bounds :
    IsPGroup 2 (L.H ⊓ A.M₁ : Subgroup G) ∧
      IsPGroup 2 (L.H ⊓ A.M₂ : Subgroup G) :=
  L.local_two_group_bound

end LocalGeometry

/- The arithmetic part of the exceptional branch is independent of the
marked model.  It is stated here so that a consumer can use the actual two
quaternion factors from `LocalGeometry` without importing the terminal
centralizer file. -/
public theorem index_eq_nine_of_quaternion_core
    {H : Type*} [Group H] [Finite H]
    (Q : Subgroup H) [Q.Normal]
    (hCQ : centralizer (Q : Set H) ≤ Q)
    (hZQ : Nat.card (center Q) = 2)
    (B C : Subgroup Q)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hBC : Nat.card (B ⊓ C : Subgroup Q) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (hjoin : B ⊔ C = ⊤)
    (T : Sylow 2 H) (hT : Nat.card T = 128)
    (hlower : 4 ≤ (T : Subgroup H).index) :
    (T : Subgroup H).index = 9 := by
  have hd := card_dvd_of_selfCentralizing_quaternion_factors
    Q hCQ hZQ B C hB hC hBC hcomm hjoin
  have hcount := (T : Subgroup H).card_mul_index
  rw [hT] at hcount
  rw [← hcount] at hd
  have hi : (T : Subgroup H).index ∣ 18 :=
    Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 128) hd
  have hn := T.not_dvd_index
  obtain ⟨k, hk⟩ := hi
  have hkbound : k ≤ 4 := by
    have hm := Nat.mul_le_mul_right k hlower
    omega
  simp only [Nat.dvd_iff_mod_eq_zero] at hn
  interval_cases k <;> omega

end CFSG.Quasithin.Chapter5.Section03ExceptionalGeometry
