module

public import Mathlib.RepresentationTheory.Subrepresentation
public import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic.Abel

/-!
# First cohomology and universal dual coverings

For a linear group action, first cohomology is the quotient of crossed
homomorphisms by principal crossed homomorphisms. This elementary model avoids
requiring the categorical cochain complex in clients doing explicit calculations.

The connecting map for a subrepresentation with trivial quotient has kernel
`V + C_W(G)`. Consequently a fixed-point-free extension embeds modulo `V` into
first cohomology. The crossed homomorphisms themselves carry a canonical action;
if the original module is fixed-point-free, this constructs its universal dual
cover. Every dual cover embeds equivariantly in it via displacement cocycles.

Reference: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), Remark I.1.5, printed p.408. The construction
and kernel formula hold over any commutative ring, without finiteness hypotheses.
-/

@[expose] public section

namespace Representation
namespace OneCohomology
variable {k G W : Type*} [CommRing k] [Group G] [AddCommGroup W] [Module k W]
variable (ρ : Representation k G W)

/-- The vectors fixed by every group element. -/
def fixed : Submodule k W where
  carrier := {w | ∀ g, ρ g w = w}
  zero_mem' g := by simp
  add_mem' hx hy g := by simp [map_add, hx g, hy g]
  smul_mem' r x hx g := by simp [map_smul, hx g]

/-- Crossed homomorphisms with values in a representation. -/
def cocycles : Submodule k (G → W) where
  carrier := {f | ∀ g t, f (g * t) = ρ g (f t) + f g}
  zero_mem' g t := by simp
  add_mem' hx hy g t := by
    simp only [Pi.add_apply, hx g t, hy g t, map_add]
    abel
  smul_mem' r x hx g t := by
    simp only [Pi.smul_apply, hx g t, map_smul, smul_add]

/-- A vector determines a principal crossed homomorphism. -/
def principal : W →ₗ[k] cocycles ρ where
  toFun w := ⟨fun g => ρ g w - w, by
    intro g t
    dsimp
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel⟩
  map_add' x y := by
    apply Subtype.ext
    funext g
    change ρ g (x + y) - (x + y) = (ρ g x - x) + (ρ g y - y)
    rw [map_add]
    abel
  map_smul' r x := by
    apply Subtype.ext
    funext g
    change ρ g (r • x) - r • x = r • (ρ g x - x)
    rw [map_smul, smul_sub]

/-- The first cohomology module, as crossed homomorphisms modulo principal ones. -/
abbrev H1 := cocycles ρ ⧸ (principal ρ).range

/-- The cohomology class of a crossed homomorphism. -/
def classMap : cocycles ρ →ₗ[k] H1 ρ := (principal ρ).range.mkQ

lemma classMap_eq_zero_iff (f : cocycles ρ) :
    classMap ρ f = 0 ↔ ∃ w, principal ρ w = f :=
  Submodule.Quotient.mk_eq_zero _

lemma ker_principal : (principal ρ).ker = fixed ρ := by
  ext w
  change (principal ρ w = 0) ↔ ∀ g, ρ g w = w
  constructor
  · intro h g
    have he := congrArg (fun f : cocycles ρ => f.val g) h
    exact sub_eq_zero.mp he
  · intro h
    apply Subtype.ext
    funext g
    exact sub_eq_zero.mpr (h g)

/-- Evaluation of a crossed homomorphism. -/
def evaluation (g : G) : cocycles ρ →ₗ[k] W where
  toFun f := f.val g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical action on crossed homomorphisms.  Its quotient by the
principal crossed homomorphisms is trivial. -/
def universalAction : Representation k G (cocycles ρ) where
  toFun g := LinearMap.id + (principal ρ).comp (evaluation ρ g)
  map_one' := by
    ext f t
    change f.val t + (ρ t (f.val 1) - f.val 1) = f.val t
    have h := f.property 1 1
    have hzero : f.val 1 = 0 := by
      simpa using h.symm
    simp [hzero]
  map_mul' g t := by
    ext f x
    change f.val x + (ρ x (f.val (g * t)) - f.val (g * t)) =
      (f.val x + (ρ x (f.val t) - f.val t)) +
        (ρ x (f.val g + (ρ g (f.val t) - f.val t)) -
          (f.val g + (ρ g (f.val t) - f.val t)))
    rw [f.property g t]
    simp only [map_add, map_sub]
    abel

lemma universalAction_principal (g : G) (w : W) :
    universalAction ρ g (principal ρ w) = principal ρ (ρ g w) := by
  apply Subtype.ext
  funext t
  change (ρ t w - w) + (ρ t (ρ g w - w) - (ρ g w - w)) = ρ t (ρ g w) - ρ g w
  rw [map_sub]
  abel

lemma fixed_universalAction (hfixed : fixed ρ = ⊥) :
    fixed (universalAction ρ) = ⊥ := by
  apply bot_unique
  intro f hf
  change f = 0
  apply Subtype.ext
  funext g
  have hp : principal ρ (f.val g) = 0 := by
    have he := hf g
    change f + principal ρ (f.val g) = f at he
    exact add_eq_left.mp he
  have hm : f.val g ∈ (principal ρ).ker := hp
  rw [ker_principal, hfixed] at hm
  exact hm

/-- The original module inside the universal dual cover, represented by its
principal crossed homomorphisms. -/
def principalSubrepresentation : Subrepresentation (universalAction ρ) where
  toSubmodule := (principal ρ).range
  apply_mem_toSubmodule g := by
    rintro _ ⟨w, rfl⟩
    exact ⟨ρ g w, (universalAction_principal ρ g w).symm⟩

variable {ρ} (V : Subrepresentation ρ)

/-- The action on the quotient by `V` is trivial. -/
def HasTrivialQuotient : Prop := ∀ (g : G) (w : W), ρ g w - w ∈ V

/-- A dual covering in the sense of Aschbacher--Smith, I.1.5. -/
def IsDualCover : Prop := HasTrivialQuotient V ∧ fixed ρ = ⊥

variable (h : HasTrivialQuotient V)

/-- The connecting crossed homomorphism associated to a vector of an extension
with trivial quotient action. -/
def displacementCocycle : W →ₗ[k] cocycles V.toRepresentation where
  toFun w := ⟨fun g => ⟨ρ g w - w, h g w⟩, by
    intro g t
    apply Subtype.ext
    change ρ (g * t) w - w = ρ g (ρ t w - w) + (ρ g w - w)
    rw [map_mul, Module.End.mul_apply, map_sub]
    abel⟩
  map_add' x y := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    change ρ g (x + y) - (x + y) = (ρ g x - x) + (ρ g y - y)
    rw [map_add]
    abel
  map_smul' r x := by
    apply Subtype.ext
    funext g
    apply Subtype.ext
    change ρ g (r • x) - r • x = r • (ρ g x - x)
    rw [map_smul, smul_sub]

/-- The connecting cohomology class. -/
def extensionClass : W →ₗ[k] H1 V.toRepresentation :=
  (classMap _).comp (displacementCocycle V h)

lemma extensionClass_eq_zero_iff (w : W) :
    extensionClass V h w = 0 ↔ w ∈ V.toSubmodule ⊔ fixed ρ := by
  change classMap V.toRepresentation (displacementCocycle V h w) = 0 ↔ _
  rw [classMap_eq_zero_iff]
  constructor
  · rintro ⟨v, hv⟩
    have hfixed : w - (v : W) ∈ fixed ρ := by
      intro g
      have he := congrArg (fun f : cocycles V.toRepresentation => (f.val g : W)) hv
      change ρ g (v : W) - (v : W) = ρ g w - w at he
      rw [map_sub]
      calc
        ρ g w - ρ g (v : W) =
            (ρ g w - w) - (ρ g (v : W) - (v : W)) + (w - (v : W)) := by abel
        _ = w - (v : W) := by rw [← he]; abel
    exact Submodule.mem_sup.mpr ⟨v, v.property, w - (v : W), hfixed, by abel⟩
  · intro hw
    obtain ⟨v, hv, z, hz, rfl⟩ := Submodule.mem_sup.mp hw
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    funext g
    apply Subtype.ext
    change ρ g v - v = ρ g (v + z) - (v + z)
    rw [map_add, hz g]
    abel

lemma ker_extensionClass :
    (extensionClass V h).ker = V.toSubmodule ⊔ fixed ρ := by
  ext w
  exact extensionClass_eq_zero_iff V h w

include h in
lemma dualCover_eq_top_of_H1_subsingleton
    (hfixed : fixed ρ = ⊥) [Subsingleton (H1 V.toRepresentation)] :
    V.toSubmodule = ⊤ := by
  apply top_unique
  intro w _
  have hw := (extensionClass_eq_zero_iff V h w).mp (Subsingleton.elim _ _)
  simpa [hfixed] using hw

/-- The connecting map descends to the quotient by the original module. -/
def quotientToH1 : (W ⧸ V.toSubmodule) →ₗ[k] H1 V.toRepresentation :=
  V.toSubmodule.liftQ (extensionClass V h) (by
    rw [ker_extensionClass]
    exact le_sup_left)

lemma quotientToH1_injective (hfixed : fixed ρ = ⊥) :
    Function.Injective (quotientToH1 V h) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  rw [ker_extensionClass, hfixed, sup_bot_eq]

lemma displacementCocycle_injective (hfixed : fixed ρ = ⊥) :
    Function.Injective (displacementCocycle V h) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro w hw
  have hf : w ∈ fixed ρ := by
    intro g
    have he := congrArg (fun f : cocycles V.toRepresentation => (f.val g : W)) hw
    exact sub_eq_zero.mp he
  simpa [hfixed] using hf

lemma displacementCocycle_equivariant (g : G) (w : W) :
    displacementCocycle V h (ρ g w) =
      universalAction V.toRepresentation g (displacementCocycle V h w) := by
  apply Subtype.ext
  funext t
  apply Subtype.ext
  change ρ t (ρ g w) - ρ g w =
    (ρ t w - w) + (ρ t (ρ g w - w) - (ρ g w - w))
  rw [map_sub]
  abel

lemma displacementCocycle_on_submodule (v : V.toSubmodule) :
    displacementCocycle V h v = principal V.toRepresentation v := rfl

lemma principal_injective (hfixed : fixed ρ = ⊥) :
    Function.Injective (principal ρ) := by
  apply LinearMap.ker_eq_bot.mp
  rw [ker_principal, hfixed]

lemma principalSubrepresentation_isDualCover (hfixed : fixed ρ = ⊥) :
    IsDualCover (principalSubrepresentation ρ) := by
  refine ⟨?_, fixed_universalAction ρ hfixed⟩
  intro g f
  exact ⟨f.val g, by
    change principal ρ (f.val g) = f + principal ρ (f.val g) - f
    abel⟩

end OneCohomology
end Representation
