module
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.CenterAction
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.MatrixModel
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# Cubic torus control in a marked linear Borel

The actual diagonal diag(t,t⁻²,t) fixes the highest root and scales the
simple roots by t³ and t⁻³. If a two-element preserving both root planes
has only unipotent commutators with these diagonal elements, the induced
automorphism fixes the center when the field has more than four elements.
The proof uses an injective map of the whole Borel and its literal root maps.
Source: Aschbacher–Smith §5.3.7, printed p.660 (`refs/quasithin.pdf`).
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups commutatorElement
namespace Matrix.PSL3.LinearAmbientGeometry
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.CartanActions Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

def borelUnipotent : U F →* borel F :=
  (projective F).codRestrict _ (fun u => unipotent_le_borel F ((projective_range F).le ⟨u,rfl⟩))

theorem borelUnipotent_injective : Function.Injective (borelUnipotent F) :=
  fun _ _ h => projective_injective F (congrArg Subtype.val h)

theorem borelUnipotent_range : (borelUnipotent F).range = (unipotent F).subgroupOf (borel F) := by
  ext b
  constructor
  · rintro ⟨u,rfl⟩
    exact (projective_range F).le ⟨u,rfl⟩
  · intro hb
    obtain ⟨u,hu⟩ := (projective_range F).ge hb
    exact ⟨u,Subtype.ext hu⟩

def centralTorus (t : Fˣ) : borel F :=
  ⟨torusMap F (t,t),torus_le_borel F ⟨(t,t),rfl⟩⟩

def scale (t : Fˣ) (u : U F) : U F :=
  ⟨(t:F)^3*u.x,((t⁻¹:Fˣ):F)^3*u.y,u.c⟩

theorem centralTorus_conj (t : Fˣ) (u : U F) :
    centralTorus F t * borelUnipotent F u * (centralTorus F t)⁻¹ =
      borelUnipotent F (scale F t u) := by
  apply Subtype.ext
  change projection F (torusSL F (t,t)) * projection F (specialLinear F u) *
    (projection F (torusSL F (t,t)))⁻¹ = projection F (specialLinear F (scale F t u))
  rw [←map_inv,←map_mul,←map_mul]
  congr 1
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (torusSL F (t,t)).val * matrix F u = matrix F (scale F t u) * (torusSL F (t,t)).val
  rw [torusSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,scale,Matrix.diagonal_mul,Matrix.mul_diagonal]
  all_goals field_simp

variable {G : Type*} [Group G] [CharP F 2]

omit [CharP F 2] in
/-- The literal cubic torus centralizes the marked highest root. -/
theorem centralTorus_centralizes (f : borel F →* G) (t : Fˣ) :
    f (centralTorus F t) ∈ centralizer (((Z F).map (f.comp (borelUnipotent F))) : Set G) := by
  rintro _ ⟨u,hu,rfl⟩
  have hu' := (mem_Z F u).mp hu
  have hs : scale F t u = u := by apply U.ext <;> simp [scale,hu'.1,hu'.2]
  have hc := congrArg f (centralTorus_conj F t u)
  rw [hs] at hc
  exact (mul_inv_eq_iff_eq_mul.mp (by simpa only [map_mul,map_inv,MonoidHom.comp_apply] using hc)).symm

/-- A two-element preserving the two marked planes and having only unipotent
commutators with the actual torus fixes the entire highest root, for q>4. -/
theorem centralizes_center_of_torus_displacement
    (hq : 4 < Nat.card F) (f : borel F →* G) (hf : Function.Injective f)
    (r : G) (hr : r ∈ normalizer ((f.comp (borelUnipotent F)).range : Set G))
    (h₁ : r ∈ normalizer (((V₁ F).map (f.comp (borelUnipotent F))) : Set G))
    (h₂ : r ∈ normalizer (((V₂ F).map (f.comp (borelUnipotent F))) : Set G))
    (hp : ∃ k : ℕ, r^(2^k)=1)
    (hd : ∀ t : Fˣ, ⁅r,f (centralTorus F t)⁆ ∈ (f.comp (borelUnipotent F)).range) :
    r ∈ centralizer (((Z F).map (f.comp (borelUnipotent F))) : Set G) := by
  let j := f.comp (borelUnipotent F)
  have hj : Function.Injective j := hf.comp (borelUnipotent_injective F)
  let e : U F ≃* j.range := MonoidHom.ofInjective hj
  let q : normalizer (j.range : Set G) →* MulAut (U F) :=
    (MulAut.congr e.symm).toMonoidHom.comp j.range.normalizerMonoidHom
  let a := q ⟨r,hr⟩
  have ha (u : U F) : j (a u) = r*j u*r⁻¹ := by
    change ((e (e.symm (j.range.normalizerMonoidHom ⟨r,hr⟩ (e u)))) : G) = _
    rw [e.apply_symm_apply]
    rfl
  have hp' : ∃ k : ℕ, a^(2^k)=1 := by
    obtain ⟨k,hk⟩ := hp
    refine ⟨k,?_⟩
    change (q ⟨r,hr⟩)^(2^k)=1
    rw [←map_pow,show (⟨r,hr⟩ : normalizer (j.range : Set G))^(2^k)=1 from Subtype.ext hk,map_one]
  have ha₁ (u : U F) (hu : u ∈ V₁ F) : a u ∈ V₁ F := by
    apply (mem_map_iff_mem hj).mp
    rw [ha]
    exact (h₁ (j u)).mp (mem_map_of_mem j hu)
  have ha₂ (u : U F) (hu : u ∈ V₂ F) : a u ∈ V₂ F := by
    apply (mem_map_iff_mem hj).mp
    rw [ha]
    exact (h₂ (j u)).mp (mem_map_of_mem j hu)
  have ht (t : Fˣ) : (a (⟨(t:F)^3,0,0⟩ : U F)).x =
      (t:F)^3*(a (⟨1,0,0⟩ : U F)).x := by
    obtain ⟨v,hv⟩ := hd t
    have hv' : r*f (centralTorus F t)*r⁻¹ = j v * f (centralTorus F t) :=
      mul_inv_eq_iff_eq_mul.mp hv.symm
    have hjt (u : U F) : j (scale F t u) =
        f (centralTorus F t) * j u * (f (centralTorus F t))⁻¹ := by
      symm
      simpa only [j,map_mul,map_inv,MonoidHom.comp_apply] using congrArg f (centralTorus_conj F t u)
    have heq (u : U F) : a (scale F t u) = v * scale F t (a u) * v⁻¹ := by
      apply hj
      rw [ha,hjt,map_mul,map_mul,map_inv,hjt,ha]
      calc
        _ = (r*f (centralTorus F t)*r⁻¹) * (r*j u*r⁻¹) *
            (r*f (centralTorus F t)*r⁻¹)⁻¹ := by group
        _ = _ := by rw [hv']; group
    have hh := congrArg U.x (heq (⟨1,0,0⟩ : U F))
    simpa only [mul_x,show (v⁻¹).x = -v.x from rfl,scale,mul_one,mul_zero,
      add_right_comm,add_neg_cancel,zero_add] using hh
  have hz := center_fixed_of_cubic_torus hq a ha₁ ha₂ hp' ht
  rintro _ ⟨u,hu,rfl⟩
  obtain ⟨c,rfl⟩ := hu
  have heq := (ha (central F c)).symm.trans (congrArg j (hz c.toAdd))
  exact (mul_inv_eq_iff_eq_mul.mp heq).symm
end Matrix.PSL3.LinearAmbientGeometry
