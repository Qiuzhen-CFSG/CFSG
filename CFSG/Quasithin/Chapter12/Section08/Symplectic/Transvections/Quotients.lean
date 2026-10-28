module

public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Intersection
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Normality
public import CFSG.Quasithin.Chapter12.Section08.Actions
public import Theory.ElementaryAbelian.Quotient

/-!
# The literal images used by the transvection calculation

The maps to U/Z(U) and H/ker(ρ) are restricted to the actual marked
subgroups. Their kernels retain the original center and action kernel.
The elementary quotient WX/E of 12.8.9(2) implies that Xdot is elementary
abelian, since E lies in U and inner conjugation is trivial on U/Z(U).
The image of the conjugate center is a subgroup of this actual actor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the proof of
Lemma 12.8.11(3–5), printed p.854 / PDF p.871. Earlier §12.8 clauses remain
explicit. This module does not yet assert the transvection or rank conclusions.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The literal projection of an ambient subgroup into the faithful action quotient. -/
def dotMap (F : InvariantFlag T V n) (ρ : F.H →* MulAut F.Uhat)
    (A : Subgroup G) (hA : A ≤ F.H) : A →* dotImage F ρ A :=
  ((QuotientGroup.mk' ρ.ker).comp (inclusion hA)).codRestrict _
    (fun a => ⟨⟨a, hA a.property⟩, a.property, rfl⟩)

@[simp] theorem dotMap_coe (F : InvariantFlag T V n) (ρ : F.H →* MulAut F.Uhat)
    (A : Subgroup G) (hA : A ≤ F.H) (a : A) :
    (dotMap F ρ A hA a : Hdot F ρ) = QuotientGroup.mk' ρ.ker ⟨a, hA a.property⟩ := rfl

theorem dotMap_surjective (F : InvariantFlag T V n) (ρ : F.H →* MulAut F.Uhat)
    (A : Subgroup G) (hA : A ≤ F.H) : Function.Surjective (dotMap F ρ A hA) := by
  intro a
  obtain ⟨h, hh, he⟩ := a.property
  exact ⟨⟨h, hh⟩, Subtype.ext he⟩

/-- Its kernel is precisely the restriction of the original action kernel. -/
theorem dotMap_ker (F : InvariantFlag T V n) (ρ : F.H →* MulAut F.Uhat)
    (A : Subgroup G) (hA : A ≤ F.H) :
    (dotMap F ρ A hA).ker = (ρ.comp (inclusion hA)).ker := by
  ext a
  change dotMap F ρ A hA a = 1 ↔ ρ (inclusion hA a) = 1
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

/-- The literal map from an ambient subgroup of U to its central-quotient image. -/
def hatMap (F : InvariantFlag T V n) (A : Subgroup G) (hA : A ≤ F.U) :
    A →* hatImage F A :=
  ((QuotientGroup.mk' (center F.U)).comp (inclusion hA)).codRestrict _
    (fun a => ⟨⟨a, hA a.property⟩, a.property, rfl⟩)

theorem hatMap_surjective (F : InvariantFlag T V n) (A : Subgroup G)
    (hA : A ≤ F.U) : Function.Surjective (hatMap F A hA) := by
  intro a
  obtain ⟨u, hu, he⟩ := a.property
  exact ⟨⟨u, hu⟩, Subtype.ext he⟩

/-- The hat kernel is the actual intersection with the embedded center. -/
theorem hatMap_ker (F : InvariantFlag T V n) (A : Subgroup G) (hA : A ≤ F.U) :
    (hatMap F A hA).ker = F.ZU.subgroupOf A := by
  ext a
  change hatMap F A hA a = 1 ↔ (a : G) ∈ F.ZU
  rw [Subtype.ext_iff]
  change QuotientGroup.mk' (center F.U) ⟨a, hA a.property⟩ = 1 ↔ _
  change ((⟨a, hA a.property⟩ : F.U) : F.Uhat) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro ha
    exact ⟨⟨a, hA a.property⟩, ha, rfl⟩
  · rintro ⟨u, hu, he⟩
    have heu : u = ⟨a, hA a.property⟩ := Subtype.ext he
    exact heu ▸ hu

/-- The conjugate center has its genuine containment in the acting image. -/
theorem conjugate_center_dot_le (F : InvariantFlag T V n)
    (ρ : F.H →* MulAut F.Uhat) (g : G) :
    dotImage F ρ (conjugate F.ZU g) ≤ dotImage F ρ (F.X g) :=
  map_mono (comap_mono (F.conjugate_ZU_le_X g))

/-- A homomorphic image is elementary abelian if an elementary quotient already
kills fewer elements. -/
private theorem elementary_of_kernel {A B C : Type*} [Group A] [Group B] [Group C]
    [IsElementaryAbelian 2 B] (f : A →* B) (q : A →* C)
    (hq : Function.Surjective q) (hker : f.ker ≤ q.ker) : IsElementaryAbelian 2 C := by
  have htransfer {a b : A} (h : f a = f b) : q a = q b := by
    apply div_eq_one.mp
    rw [← map_div]
    apply hker
    change f (a / b) = 1
    simp only [map_div, h, div_self']
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro a b
    obtain ⟨a, rfl⟩ := hq a
    obtain ⟨b, rfl⟩ := hq b
    rw [← map_mul, ← map_mul]
    apply htransfer
    simp only [map_mul, mul_comm]
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro a
    obtain ⟨a, rfl⟩ := hq a
    rw [← map_pow, ← q.map_one]
    apply htransfer
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 B) _

/-- The quotient module in 12.8.9(2) and the genuine conjugation equation
imply elementary abelianness of Xdot; it is not an extra input. -/
theorem Xdot_elementary (F : InvariantFlag T V n) [IsMulCommutative V]
    [IsMulCommutative F.Uhat] (g : G) (hg : g ∈ F.Gi 2)
    [((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal]
    [IsElementaryAbelian 2 ((F.W ⊔ F.X g : Subgroup G) ⧸
      (F.E g).subgroupOf (F.W ⊔ F.X g))]
    (ρ : F.H →* MulAut F.Uhat)
    (hρ : ∀ (h : F.H) (u : F.U),
      ρ h (QuotientGroup.mk' (center F.U) u) =
        QuotientGroup.mk' (center F.U)
          (F.U.normalizerMonoidHom
            ⟨h, le_normalizer_conjugateSpanBy V F.H h.property⟩ u)) :
    IsElementaryAbelian 2 (dotImage F ρ (F.X g)) := by
  have hXH : F.X g ≤ F.H := (F.X_le_plane_centralizer g hg).trans
    ((centralizer_le (F.monotone (by omega : 1 ≤ 2))).trans (centralizer_le_normalizer _))
  let f := (QuotientGroup.mk' ((F.E g).subgroupOf (F.W ⊔ F.X g))).comp
    (inclusion (le_sup_right : F.X g ≤ F.W ⊔ F.X g))
  apply elementary_of_kernel f (dotMap F ρ (F.X g) hXH) (dotMap_surjective _ _ _ _)
  intro x hx
  have hxE : (x : G) ∈ F.E g := by
    exact (QuotientGroup.eq_one_iff (N := (F.E g).subgroupOf (F.W ⊔ F.X g))
      (⟨x, (le_sup_right : F.X g ≤ F.W ⊔ F.X g) x.property⟩ : (F.W ⊔ F.X g : Subgroup G))).mp hx
  rw [dotMap_ker]
  exact U_le_action_kernel F ρ hρ (show (⟨x, hXH x.property⟩ : F.H) ∈ F.U.subgroupOf F.H from
    (inf_le_left.trans inf_le_left : F.E g ≤ F.U) hxE)

/-- Specialization to the action constructed by the preliminary source owner. -/
theorem Xdot_uhatAction_elementary (F : InvariantFlag T V n) [IsMulCommutative V]
    [IsMulCommutative F.Uhat] (g : G) (hg : g ∈ F.Gi 2)
    [((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal]
    [IsElementaryAbelian 2 ((F.W ⊔ F.X g : Subgroup G) ⧸
      (F.E g).subgroupOf (F.W ⊔ F.X g))] :
    IsElementaryAbelian 2 (dotImage F F.uhatAction (F.X g)) :=
  Xdot_elementary F g hg F.uhatAction F.uhatAction_apply_mk

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
