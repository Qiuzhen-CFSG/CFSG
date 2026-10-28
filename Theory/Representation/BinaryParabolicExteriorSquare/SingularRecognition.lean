module
public import Theory.Representation.BinaryParabolicExteriorSquare.SingularOrbit

/-!
# Recognizing the exterior module from one local line

Point-stabilizer invariance makes the source orbit map well defined on
nonzero singular bivectors. The checked transitivity on ordered lines
transports a single local line relation to every singular line. The
singular presentation then constructs a nonzero injective intertwiner.
Neither a module dimension nor a prior exterior embedding is assumed.

This is the local-to-global step of B.4.13 used in Aschbacher--Smith,
The Classification of Quasithin Groups, 13.8.29(5), printed p.964.
The original natural quotient map is used throughout. Its exterior model
retains the attribution and license of the imported ATLAS construction.
-/

public noncomputable section
open Atlas.Order20160A8.Bivectors
open scoped MatrixGroups
namespace Representation.BinaryParabolicExteriorSquare.SingularPresentation
open Representation.BinaryParabolicExteriorSquare
variable {J W : Type*} [Group J] [AddCommGroup W] [Module Bit W]

/-- One source line relation and its point stabilizer construct the whole
exterior embedding, retaining the supplied natural marking. -/
theorem exists_intertwiner_of_one_line
    (π : J →* SL(4,Bit)) (hπ : Function.Surjective π)
    (ρ : Representation Bit J W) (v : W) (hv : v ≠ 0)
    (hfix : ∀ g, exteriorMap (π g).val (Pi.single 0 1) = (Pi.single 0 1 : Six) → ρ g v = v)
    (a b : J)
    (ha : exteriorMap (π a).val (Pi.single 0 1) = (Pi.single 1 1 : Six))
    (hb : exteriorMap (π b).val (Pi.single 0 1) = (Pi.single 0 1 + Pi.single 1 1 : Six))
    (hline : v + ρ a v = ρ b v) :
    ∃ F : (action π).IntertwiningMap ρ, Function.Injective F ∧ F (Pi.single 0 1) = v := by
  classical
  let e : Six := Pi.single 0 1
  let τ := action π
  have he0 : e ≠ 0 := by intro he; have hh := congrFun he 0; simp [e] at hh
  have heS : pfaffian e = 0 := by simp [e]
  have horbit (x : Six) (hx : pfaffian x = 0 ∧ x ≠ 0) : ∃ g : J, τ g e = x := by
    obtain ⟨m,hm⟩ := singular_orbit x hx.1 hx.2
    obtain ⟨g,hg⟩ := hπ m
    exact ⟨g,by change exteriorMap (π g).val e = x; rw [hg]; exact hm⟩
  have same (g h : J) (heq : τ g e = τ h e) : ρ g v = ρ h v := by
    have hs : τ (h⁻¹*g) e = e := by
      rw [map_mul,Module.End.mul_apply,heq,Representation.inv_self_apply]
    have hh := congrArg (ρ h) (hfix (h⁻¹*g) hs)
    simpa only [map_mul,Module.End.mul_apply,Representation.self_inv_apply] using hh
  let f : Six → W := fun x => if hx : pfaffian x = 0 ∧ x ≠ 0 then
    ρ (horbit x hx).choose v else 0
  have hf0 : f 0 = 0 := by simp [f]
  have hfg (g : J) : f (τ g e) = ρ g v := by
    have hs : pfaffian (τ g e) = 0 ∧ τ g e ≠ 0 := by
      constructor
      · change pfaffian (exteriorMap (π g).val e) = 0
        rw [pfaffian_exteriorMap,heS,mul_zero]
      · intro hh
        have heq := congrArg (τ g⁻¹) hh
        rw [Representation.inv_self_apply,map_zero] at heq
        exact he0 heq
    dsimp only [f]
    rw [dif_pos hs]
    exact same _ g (horbit (τ g e) hs).choose_spec
  have hfe : f e = v := by simpa only [map_one,Module.End.one_apply] using hfg 1
  have hcov (g : J) (x : Six) (hx : pfaffian x = 0) :
      f (exteriorMap (π g).val x) = ρ g (f x) := by
    by_cases hx0 : x = 0
    · simp [hx0,hf0]
    obtain ⟨k,rfl⟩ := horbit x ⟨hx,hx0⟩
    change f (τ g (τ k e)) = ρ g (f (τ k e))
    rw [←Module.End.mul_apply,←map_mul,hfg,hfg,map_mul,Module.End.mul_apply]
  have hdbl (w : W) : w+w = 0 := by
    rw [←two_smul Bit w,show (2:Bit) = 0 by decide,zero_smul]
  have hlines (x y : Six) (hx : pfaffian x = 0) (hy : pfaffian y = 0)
      (hxy : pfaffian (x+y) = 0) : f (x+y) = f x + f y := by
    by_cases hx0 : x = 0
    · simp [hx0,hf0]
    by_cases hy0 : y = 0
    · simp [hy0,hf0]
    by_cases hsame : x = y
    · subst y
      have hx2 : x+x = 0 := by ext i; change x i+x i=0; exact CharTwo.add_self_eq_zero _
      rw [hx2,hf0,hdbl]
    obtain ⟨m,hm0,hm1⟩ := singular_line_orbit x y hx hy hxy hx0 hy0 hsame
    obtain ⟨t,ht⟩ := hπ m
    have ht0 : τ t e = x := by change exteriorMap (π t).val e = x; rw [ht]; exact hm0
    have ht1 : τ (t*a) e = y := by
      rw [map_mul,Module.End.mul_apply]
      change exteriorMap (π t).val (exteriorMap (π a).val e) = y
      rw [ha,ht,hm1]
    have ht2 : τ (t*b) e = x+y := by
      rw [map_mul,Module.End.mul_apply]
      change exteriorMap (π t).val (exteriorMap (π b).val e) = x+y
      rw [hb,map_add,ht,hm0,hm1]
    rw [←ht2,hfg,←ht0,←ht1,hfg,hfg,map_mul,Module.End.mul_apply,
      map_mul,Module.End.mul_apply,←map_add,hline]
  obtain ⟨F,hF,hvalues⟩ := exists_injective_intertwiner π hπ ρ f hf0 hlines hcov
    ⟨e,heS,by rwa [hfe]⟩
  exact ⟨F,hF,(hvalues e heS).trans hfe⟩

end Representation.BinaryParabolicExteriorSquare.SingularPresentation
