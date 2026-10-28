module

public import Theory.Representation.SL3FourNaturalDual.Actors

/-!
# Displacements and quadratic flags on the SL₃(4) module

On the natural summand, quadraticity makes every product of displacement
maps zero. Their combined image is consequently contained in their common
kernel. Nontriviality and the three-dimensional F₄-space force either a
common image line or a common fixed hyperplane, the two root-plane
orientations. The direct-sum representation is faithful. Testing the natural
summand also shows that a graph swap fixes all displacements of a matrix
actor only when that actor is the identity.

These are matrix inputs to the actor classification in Aschbacher--Smith,
proof of 13.8.20, printed p.955 (1 March 2004 manuscript). They do not assume
root coordinates or assert the still-needed arbitrary-normalizer reduction.
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors
open BinaryOffender

/-- Displacement on the three-dimensional module, retaining F₄-linearity. -/
def naturalDisplacement (g : SL) : W →ₗ[F] W := specialLinearNatural 3 g - 1

lemma naturalDisplacement_eq_zero_iff (g : SL) : naturalDisplacement g = 0 ↔ g = 1 := by
  constructor
  · intro h
    apply Matrix.SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    have he := LinearMap.congr_fun (sub_eq_zero.mp h) v
    change (Matrix.SpecialLinearGroup.toLin' g) v = v at he
    rw [map_one]
    exact he
  · rintro rfl
    simp [naturalDisplacement]

lemma representation_injective : Function.Injective representation := by
  intro g h he
  apply Matrix.SpecialLinearGroup.toLin'_injective
  apply LinearEquiv.ext
  intro v
  exact congrArg Prod.fst (LinearMap.congr_fun he (v, 0))

/-- Quadraticity of the direct sum forces every product of natural
coordinate displacements to vanish. -/
lemma naturalDisplacement_comp_eq_zero (A : Subgroup SL)
    (hq : IsQuadratic representation A) (a b : A) :
    (naturalDisplacement a).comp (naturalDisplacement b) = 0 := by
  apply LinearMap.ext
  intro v
  have h := congrArg Prod.fst (hq a a.property b b.property (v, 0))
  change naturalDisplacement a (naturalDisplacement b v) = 0
  apply sub_eq_zero.mpr
  exact h

/-- The F₄-space spanned by the images of the natural displacements. -/
def naturalMoved (A : Subgroup SL) : Submodule F W :=
  ⨆ a : A, (naturalDisplacement a).range

/-- The common kernel of the natural displacements. -/
def naturalFixed (A : Subgroup SL) : Submodule F W :=
  ⨅ a : A, (naturalDisplacement a).ker

lemma range_le_naturalMoved (A : Subgroup SL) (a : A) :
    (naturalDisplacement a).range ≤ naturalMoved A := by
  unfold naturalMoved
  exact le_iSup (fun b : A => (naturalDisplacement b).range) a

lemma naturalFixed_le_ker (A : Subgroup SL) (a : A) :
    naturalFixed A ≤ (naturalDisplacement a).ker := iInf_le _ a

lemma naturalMoved_ne_bot (A : Subgroup SL) (hA : A ≠ ⊥) : naturalMoved A ≠ ⊥ := by
  intro hm
  apply hA
  apply le_bot_iff.mp
  intro a ha
  have hr : (naturalDisplacement a).range = ⊥ :=
    le_bot_iff.mp (hm ▸ range_le_naturalMoved A ⟨a, ha⟩)
  exact (naturalDisplacement_eq_zero_iff a).mp (LinearMap.range_eq_bot.mp hr)

lemma naturalFixed_ne_top (A : Subgroup SL) (hA : A ≠ ⊥) : naturalFixed A ≠ ⊤ := by
  intro hc
  apply hA
  apply le_bot_iff.mp
  intro a ha
  have hk : (naturalDisplacement a).ker = ⊤ :=
    top_le_iff.mp (hc ▸ naturalFixed_le_ker A ⟨a, ha⟩)
  exact (naturalDisplacement_eq_zero_iff a).mp (LinearMap.ker_eq_top.mp hk)

lemma naturalMoved_le_naturalFixed (A : Subgroup SL)
    (hq : IsQuadratic representation A) : naturalMoved A ≤ naturalFixed A := by
  apply iSup_le
  intro b
  apply le_iInf
  intro a
  rintro _ ⟨v, rfl⟩
  exact LinearMap.congr_fun (naturalDisplacement_comp_eq_zero A hq a b) v

/-- A nontrivial quadratic actor has either a common image line or a common
fixed hyperplane on the natural F₄-module. These are the two root-plane
orientations; no choice of coordinates or output marking is assumed. -/
theorem natural_flag_dichotomy (A : Subgroup SL) (hA : A ≠ ⊥)
    (hq : IsQuadratic representation A) :
    Module.finrank F (naturalMoved A) = 1 ∨
      Module.finrank F (W ⧸ naturalFixed A) = 1 := by
  have hmn := naturalMoved_ne_bot A hA
  have hcn := naturalFixed_ne_top A hA
  have hm : 0 < Module.finrank F (naturalMoved A) := Submodule.one_le_finrank_iff.mpr hmn
  have hc := Submodule.finrank_lt hcn
  have hmc := Submodule.finrank_mono (naturalMoved_le_naturalFixed A hq)
  have hd : Module.finrank F W = 3 := by simp [W]
  have hquot := (naturalFixed A).finrank_quotient_add_finrank
  by_cases h : Module.finrank F (naturalMoved A) = 1
  · exact Or.inl h
  · right
    omega

/-- A graph swap cannot be quadratic together with a nonidentity matrix
actor: test the displacement on the natural summand alone. -/
lemma eq_one_of_swap_fixes_displacement (g : SL)
    (h : ∀ v : V, graphSwap (representation g v - v) = representation g v - v) :
    g = 1 := by
  apply (naturalDisplacement_eq_zero_iff g).mp
  apply LinearMap.ext
  intro w
  have he := congrArg Prod.fst (h (w, 0))
  change naturalDisplacement g w = 0
  have hzero : (representation g (w, 0)).2 = 0 := by
    change dualCoordinates g 0 = 0
    exact map_zero _
  change (representation g (w, 0)).2 - 0 =
    (representation g (w, 0)).1 - w at he
  rw [hzero, sub_zero] at he
  exact he.symm

end Representation.SL3FourNaturalDual.QuadraticActors
