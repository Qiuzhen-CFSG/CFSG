module

public import CFSG.Quasithin.Chapter1.Defs
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.PResidual.Defs
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Concrete data for the two choices of each local factor

This is the geometric input to Aschbacher–Smith 15.4.21–23, from 15.4.12,
15.4.14 and 15.4.17–20 (printed pp.1160–1165). Both factors of `X` and `Y`
are retained in one ambient group. Changing `i` to `!i` constructs the alternate
amalgam using the same `T₀`, modules and ambient subgroups.

The modules are actual subgroup commutators. Their actions below are restrictions
of conjugation, with a proved ambient-value formula. Normality is relative to
the indicated overgroup. No A₄, A₆, S₆ or D₈ identification is an input.

This interface records earlier structural inputs, not their construction from
Hypothesis 15.4.1 and not the later classification. SQTK/known-simple-group
hypotheses required by the classification must also be supplied when the
F.6 and B.5 results are applied.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.Source

open Subgroup

variable {G : Type*} [Group G]

/-- The shared ambient subgroups before imposing the earlier local lemmas. -/
structure Geometry (G : Type*) [Group G] where
  T : Sylow 2 G
  X : Bool → Subgroup G
  Y : Bool → Subgroup G
  J : Subgroup G
  Z : Subgroup G
  VM₁ : Subgroup G
  VM₂ : Subgroup G

namespace Geometry

variable (d : Geometry G)

def wholeX : Subgroup G := d.X false ⊔ d.X true
def wholeY : Subgroup G := d.Y false ⊔ d.Y true
def M₁ : Subgroup G := normalizer (d.wholeX : Set G)
def M₂ : Subgroup G := normalizer (d.wholeY : Set G)
def T₀ : Subgroup G :=
  (d.T : Subgroup G) ⊓ normalizer (d.X false : Set G) ⊓ normalizer (d.Y false : Set G)
def G₁ (i : Bool) : Subgroup G := d.X i ⊔ d.T₀
def G₂ (j : Bool) : Subgroup G := d.Y j ⊔ d.T₀
def I (i j : Bool) : Subgroup G := d.G₁ i ⊔ d.G₂ j
def V₁ (i : Bool) : Subgroup G := ⁅d.VM₁, d.X i⁆
def V₂ (j : Bool) : Subgroup G := ⁅d.VM₂, d.Y j⁆

/-- The alternate amalgam in 15.4.23; `!i` exchanges the two X-factors. -/
def alternateI (i j : Bool) : Subgroup G := d.I (!i) j

theorem alternateI_alternate (i j : Bool) : d.alternateI (!i) j = d.I i j := by
  simp [alternateI]

theorem T₀_le_T : d.T₀ ≤ (d.T : Subgroup G) := inf_le_left.trans inf_le_left

theorem T₀_le_I (i j : Bool) : d.T₀ ≤ d.I i j := le_sup_right.trans le_sup_left

theorem X_le_I (i j : Bool) : d.X i ≤ d.I i j := le_sup_left.trans le_sup_left

theorem Y_le_I (i j : Bool) : d.Y j ≤ d.I i j := le_sup_left.trans le_sup_right

/-- Generation holds before either Fitting branch. Normality is the substantive
additional assertion in 15.4.21. -/
theorem I_eq_join (i j : Bool) : d.I i j = (d.X i ⊔ d.Y j) ⊔ d.T₀ := by
  change (d.X i ⊔ d.T₀) ⊔ (d.Y j ⊔ d.T₀) = _
  rw [sup_sup_sup_comm, sup_idem]

end Geometry

/-- Earlier structural inputs, simultaneously for all four pairs of factors.
The Sylow and symmetric-three quotients are the Goldschmidt-triple inputs,
not the later recognition conclusions. The 1.1.5 hypotheses come from 15.4.17.
The final rank bound is the part of the ambient SQTK hypothesis used by the
independent rank obstruction. -/
structure LocalData (d : Geometry G) where
  J_le : d.J ≤ d.T₀
  Z_le : d.Z ≤ d.T₀
  Z_elementary : IsElementaryAbelian 2 d.Z
  Z_card : Nat.card d.Z = 4
  centralizer_Z : centralizer (d.Z : Set G) = (d.T : Subgroup G)
  VM₁_elementary : IsElementaryAbelian 2 d.VM₁
  VM₂_elementary : IsElementaryAbelian 2 d.VM₂
  VM₁_le : d.VM₁ ≤ d.M₁
  VM₂_le : d.VM₂ ≤ d.M₂
  VM₁_normalized : d.M₁ ≤ normalizer (d.VM₁ : Set G)
  VM₂_normalized : d.M₂ ≤ normalizer (d.VM₂ : Set G)
  T_normalizes_X : (d.T : Subgroup G) ≤ normalizer (d.wholeX : Set G)
  T_normalizes_Y : (d.T : Subgroup G) ≤ normalizer (d.wholeY : Set G)
  X_normalized : ∀ i, d.T₀ ≤ normalizer (d.X i : Set G)
  Y_normalized : ∀ j, d.T₀ ≤ normalizer (d.Y j : Set G)
  normalizer_X_eq : ∀ i,
    (d.T : Subgroup G) ⊓ normalizer (d.X i : Set G) =
      (d.T : Subgroup G) ⊓ normalizer (d.X false : Set G)
  normalizer_Y_eq : ∀ j,
    (d.T : Subgroup G) ⊓ normalizer (d.Y j : Set G) =
      (d.T : Subgroup G) ⊓ normalizer (d.Y false : Set G)
  X_commutator : ∀ i, ⁅d.X i, d.J⁆ = d.X i
  Y_commutator : ∀ j, ⁅d.Y j, d.J⁆ = d.Y j
  X_perfect : ∀ i, IsPPerfect 2 (d.X i)
  Y_perfect : ∀ j, IsPPerfect 2 (d.Y j)
  wholeX_quotient_elementary : IsElementaryAbelian 3 (d.wholeX ⧸ pCore 2 d.wholeX)
  wholeY_quotient_elementary : IsElementaryAbelian 3 (d.wholeY ⧸ pCore 2 d.wholeY)
  wholeX_quotient_card : Nat.card (d.wholeX ⧸ pCore 2 d.wholeX) = 9
  wholeY_quotient_card : Nat.card (d.wholeY ⧸ pCore 2 d.wholeY) = 9
  X_quotient_card : ∀ i, Nat.card (d.X i ⧸ pCore 2 (d.X i)) = 3
  Y_quotient_card : ∀ j, Nat.card (d.Y j ⧸ pCore 2 (d.Y j)) = 3
  V₁_le : ∀ i, d.V₁ i ≤ d.X i
  V₂_le : ∀ j, d.V₂ j ≤ d.Y j
  V₁_elementary : ∀ i, IsElementaryAbelian 2 (d.V₁ i)
  V₂_elementary : ∀ j, IsElementaryAbelian 2 (d.V₂ j)
  V₁_card : ∀ i, Nat.card (d.V₁ i) = 4
  V₂_card : ∀ j, Nat.card (d.V₂ j) = 4
  V₁_normalized : ∀ i, d.G₁ i ≤ normalizer (d.V₁ i : Set G)
  V₂_normalized : ∀ j, d.G₂ j ≤ normalizer (d.V₂ j : Set G)
  V₁_disjoint : Disjoint (d.V₁ false) (d.V₁ true)
  V₂_disjoint : Disjoint (d.V₂ false) (d.V₂ true)
  V₁_full_commutator : ∀ i, ⁅d.V₁ i, d.X i⁆ = d.V₁ i
  V₂_full_commutator : ∀ j, ⁅d.V₂ j, d.Y j⁆ = d.V₂ j
  siblings_X : ∀ i, ⁅d.X (!i), d.X i⁆ ≤ (d.X i).pCoreIn 2
  siblings_Y : ∀ j, ⁅d.Y (!j), d.Y j⁆ ≤ (d.Y j).pCoreIn 2
  X_outside : ∀ i, ¬ d.X i ≤ d.M₂
  Y_outside : ∀ j, ¬ d.Y j ≤ d.M₁
  intersection : ∀ i j, d.G₁ i ⊓ d.G₂ j = d.T₀
  sylow : ∀ i j, Sylow 2 (d.I i j)
  sylow_image : ∀ i j, ((sylow i j : Subgroup (d.I i j)).map (d.I i j).subtype) = d.T₀
  sylow_core_normalizer : ∀ i j,
    ∃ S : Sylow 2 (normalizer ((d.I i j).pCoreIn 2 : Set G)),
      (S : Subgroup (normalizer ((d.I i j).pCoreIn 2 : Set G))).map
        (normalizer ((d.I i j).pCoreIn 2 : Set G)).subtype = d.T₀
  quotient₁ : ∀ i, Nonempty ((d.G₁ i ⧸ pCore 2 (d.G₁ i)) ≃* Equiv.Perm (Fin 3))
  quotient₂ : ∀ j, Nonempty ((d.G₂ j ⧸ pCore 2 (d.G₂ j)) ≃* Equiv.Perm (Fin 3))
  local115 : ∀ i j z, z ∈ d.Z → z ≠ 1 → ∃ M : Subgroup G,
    Chapter1.Lemma115Hypotheses (d.I i j) (sylow i j) M z
  fitting_of_Z_meets_core : ∀ i j,
    d.Z ⊓ (d.I i j).pCoreIn 2 ≠ ⊥ →
      Theory.GroupTheory.generalizedFitting (d.I i j) = pCore 2 (d.I i j)
  central_intersection : ∀ i j,
    d.Z ⊓ ((center (d.I i j)).map (d.I i j).subtype ⊔ d.V₁ i) ≠ ⊥
  normalizer_rank : ∀ i, primeRank 3 (normalizer ((d.X i).pCoreIn 2 : Set G)) ≤ 2

namespace LocalData

variable {d : Geometry G} (h : LocalData d)

/-- The first local action is ambient conjugation on the commutator module. -/
def action₁ (i : Bool) : d.G₁ i →* MulAut (d.V₁ i) :=
  (d.V₁ i).normalizerMonoidHom.comp (inclusion (h.V₁_normalized i))

/-- The second action uses the same ambient multiplication and conjugation. -/
def action₂ (j : Bool) : d.G₂ j →* MulAut (d.V₂ j) :=
  (d.V₂ j).normalizerMonoidHom.comp (inclusion (h.V₂_normalized j))

theorem action₁_coe (i : Bool) (g : d.G₁ i) (v : d.V₁ i) :
    (h.action₁ i g v : G) = (g : G) * (v : G) * (g : G)⁻¹ := rfl

theorem action₂_coe (j : Bool) (g : d.G₂ j) (v : d.V₂ j) :
    (h.action₂ j g v : G) = (g : G) * (v : G) * (g : G)⁻¹ := rfl

end LocalData
end CFSG.Quasithin.Chapter15.Section04.Source
