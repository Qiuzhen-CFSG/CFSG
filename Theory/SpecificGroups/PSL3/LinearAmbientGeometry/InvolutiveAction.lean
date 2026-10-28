module
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.CenterAction
public import Theory.FieldTheory.QuadraticFrobeniusTrace

/-!
# Marking a root-plane preserving involution

An automorphism of UT₃ preserving both root planes acts by one common field
automorphism on their coordinates and the center, up to two scalar factors
and additive central shears. For an involution moving the center, that field
automorphism is a nontrivial involution. Scalar norm-one identities and a
trace-one element remove the scalar factors and shears simultaneously.
Thus one coordinate change preserving both root planes makes the action
entrywise field conjugation.

This gives the intrinsic action needed to construct the SAME marked Sylow in
the exceptional q=4 branch, without an ambient automorphism-extension premise.
Source: Aschbacher--Smith §5.3.7 and F.4.29(2), printed pp.660 and 289
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3.LinearAmbientGeometry
open Matrix.PSL3Even.UnipotentGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem comm_coordinates (u v : U F) :
    ⁅u,v⁆ = central F (Multiplicative.ofAdd (u.x*v.y-v.x*u.y)) := by
  apply U.ext <;>
    simp only [commutatorElement_def, mul_x, mul_y, mul_c]
  all_goals dsimp [Inv.inv, central]
  all_goals ring

omit [CharP F 2] in
/-- The same field automorphism acts on both simple roots and on their
commutator; the remaining terms are additive central shears. -/
theorem plane_preserving_coordinates (a : MulAut (U F))
    (h₁ : ∀ u ∈ V₁ F, a u ∈ V₁ F)
    (h₂ : ∀ u ∈ V₂ F, a u ∈ V₂ F) :
    ∃ (r s : F) (σ : F ≃+* F) (P Q : F →+ F), r ≠ 0 ∧ s ≠ 0 ∧
      ∀ u : U F, a u = ⟨r * σ u.x, s * σ u.y,
        r * s * σ u.c + P u.x + Q u.y⟩ := by
  obtain ⟨c,σ,hc,hσ⟩ := center_semilinear a h₁ h₂
  let X (x : F) : U F := ⟨x,0,0⟩
  let Y (y : F) : U F := ⟨0,y,0⟩
  have hX (x : F) : (a (X x)).y = 0 := (mem_V₁ F _).mp (h₁ _ (by simp [X]))
  have hY (y : F) : (a (Y y)).x = 0 := (mem_V₂ F _).mp (h₂ _ (by simp [Y]))
  have hxy (x y : F) : c * σ (x*y) = (a (X x)).x * (a (Y y)).y := by
    have hh := map_commutatorElement a (X x) (Y y)
    rw [comm_coordinates,comm_coordinates] at hh
    change a (central F (Multiplicative.ofAdd (x*y-0*0))) = _ at hh
    rw [zero_mul,sub_zero,hσ] at hh
    have he := congrArg U.c hh
    simpa [central,hX,hY] using he
  let r := (a (X 1)).x
  let s := (a (Y 1)).y
  have hrs : c=r*s := by simpa [r,s] using hxy 1 1
  have hr : r≠0 := fun hh => hc (by simp [hrs,hh])
  have hs : s≠0 := fun hh => hc (by simp [hrs,hh])
  have hx (x : F) : (a (X x)).x=r*σ x := by
    apply mul_right_cancel₀ hs
    have hh := hxy x 1
    simpa only [mul_one,hrs,s,mul_assoc,mul_left_comm,mul_comm] using hh.symm
  have hy (y : F) : (a (Y y)).y=s*σ y := by
    apply mul_left_cancel₀ hr
    have hh := hxy 1 y
    simpa only [one_mul,hrs,r,mul_assoc] using hh.symm
  let P : F →+ F := {
    toFun x := (a (X x)).c
    map_zero' := by change (a 1).c=0; rw [map_one,one_c]
    map_add' x y := by
      have hh : X (x+y)=X x*X y := by apply U.ext <;> simp [X]
      rw [hh,map_mul,mul_c,hX,mul_zero,add_zero] }
  let Q : F →+ F := {
    toFun y := (a (Y y)).c
    map_zero' := by change (a 1).c=0; rw [map_one,one_c]
    map_add' x y := by
      have hh : Y (x+y)=Y x*Y y := by apply U.ext <;> simp [Y]
      rw [hh,map_mul,mul_c,hY,zero_mul,add_zero] }
  refine ⟨r,s,σ,P,Q,hr,hs,fun u => ?_⟩
  have hu : u = X u.x * Y u.y * central F (Multiplicative.ofAdd (u.c-u.x*u.y)) := by
    apply U.ext <;> simp [X,Y,central]
  conv_lhs => rw [hu,map_mul,map_mul,hσ]
  apply U.ext
  · simpa [central,hY] using hx u.x
  · simpa [central,hX] using hy u.y
  · change (a (X u.x)).c + (a (Y u.y)).c + (a (X u.x)).x * (a (Y u.y)).y +
      c * σ (u.c-u.x*u.y) + ((a (X u.x)).x + (a (Y u.y)).x) * 0 = _
    rw [hx,hy,hrs,map_sub,map_mul]
    change P u.x+Q u.y+r*σ u.x*(s*σ u.y)+(r*s)*(σ u.c-σ u.x*σ u.y)+
      (r*σ u.x+(a (Y u.y)).x)*0 = r*s*σ u.c+P u.x+Q u.y
    ring

/-- An involutory action which moves the center has a nontrivial involutory
field coefficient, in the same coordinates. -/
theorem involution_coordinates (a : MulAut (U F))
    (h₁ : ∀ u ∈ V₁ F, a u ∈ V₁ F)
    (h₂ : ∀ u ∈ V₂ F, a u ∈ V₂ F)
    (ha : a^2=1) (hmove : ∃ u ∈ Z F, a u ≠ u) :
    ∃ (r s : F) (σ : F ≃+* F) (P Q : F →+ F), r ≠ 0 ∧ s ≠ 0 ∧
      σ ≠ 1 ∧ Function.Involutive σ ∧ r*σ r=1 ∧ s*σ s=1 ∧
      (∀ u : U F, a u = ⟨r*σ u.x,s*σ u.y,r*s*σ u.c+P u.x+Q u.y⟩) ∧
      (∀ x, r*s*σ (P x)+P (r*σ x)=0) ∧
      (∀ y, r*s*σ (Q y)+Q (s*σ y)=0) := by
  obtain ⟨r,s,σ,P,Q,hr,hs,he⟩ := plane_preserving_coordinates a h₁ h₂
  have haa (u : U F) : a (a u)=u := DFunLike.congr_fun ha u
  have hrσ : r*σ r=1 := by
    have hh := congrArg U.x (haa ⟨1,0,0⟩)
    rw [he,he] at hh
    simpa only [map_one,mul_one] using hh
  have hsσ : s*σ s=1 := by
    have hh := congrArg U.y (haa ⟨0,1,0⟩)
    rw [he,he] at hh
    simpa only [map_one,mul_one] using hh
  have hσσ : Function.Involutive σ := by
    intro x
    have hh := congrArg U.x (haa ⟨x,0,0⟩)
    rw [he,he] at hh
    change r*σ (r*σ x)=x at hh
    simpa only [map_mul,←mul_assoc,hrσ,one_mul] using hh
  have hσne : σ≠1 := by
    intro hσ
    have hr1 : r=1 := by
      have hh : r^2=1 := by simpa [hσ,pow_two] using hrσ
      simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff 2 1 1 r).mp (by simpa using hh)
    have hs1 : s=1 := by
      have hh : s^2=1 := by simpa [hσ,pow_two] using hsσ
      simpa using (ExpChar.pow_prime_pow_mul_eq_one_iff 2 1 1 s).mp (by simpa using hh)
    obtain ⟨u,hu,hnu⟩ := hmove
    have hzero := (mem_Z F u).mp hu
    apply hnu
    rw [he]
    apply U.ext <;> simp [hzero.1,hzero.2,hr1,hs1,hσ]
  refine ⟨r,s,σ,P,Q,hr,hs,hσne,hσσ,hrσ,hsσ,he,?_,?_⟩
  · intro x
    have hh := congrArg U.c (haa ⟨x,0,0⟩)
    rw [he,he] at hh
    simpa only [map_zero,mul_zero,add_zero,zero_add] using hh
  · intro y
    have hh := congrArg U.c (haa ⟨0,y,0⟩)
    rw [he,he] at hh
    simpa only [map_zero,mul_zero,add_zero,zero_add] using hh

omit [Finite F] in
private theorem exists_scalar_fixed (σ : F ≃+* F) (r : F) (hr : r*σ r=1) :
    ∃ l : F, l≠0 ∧ r*σ l=l := by
  by_cases h : r=1
  · exact ⟨1,one_ne_zero,by simp [h]⟩
  refine ⟨1+r,?_,?_⟩
  · intro hh
    exact h ((CharTwo.add_eq_zero.mp hh).symm)
  · rw [map_add,map_one,mul_add,mul_one,hr,add_comm]

omit [Finite F] [CharP F 2] in
private def coordinateChange (l m : F) (hl : l≠0) (hm : m≠0)
    (P Q : F →+ F) : MulAut (U F) where
  toFun u := ⟨l*u.x,m*u.y,l*m*u.c+P u.x+Q u.y⟩
  invFun u := ⟨u.x/l,u.y/m,(u.c-P (u.x/l)-Q (u.y/m))/(l*m)⟩
  left_inv u := by
    apply U.ext
    · exact mul_div_cancel_left₀ _ hl
    · exact mul_div_cancel_left₀ _ hm
    · dsimp
      rw [mul_div_cancel_left₀ _ hl,mul_div_cancel_left₀ _ hm]
      field_simp
      ring
  right_inv u := by
    apply U.ext
    · exact mul_div_cancel₀ _ hl
    · exact mul_div_cancel₀ _ hm
    · dsimp
      field_simp
      ring
  map_mul' u v := by
    apply U.ext
    · exact mul_add _ _ _
    · exact mul_add _ _ _
    · dsimp
      rw [map_add,map_add]
      ring

/-- Every involution preserving the two root planes and moving the center
is a field involution after one change of coordinates preserving both planes.
The same coordinates are used on the center and both simple roots. -/
theorem involution_marked_field_coordinates (a : MulAut (U F))
    (h₁ : ∀ u ∈ V₁ F, a u ∈ V₁ F)
    (h₂ : ∀ u ∈ V₂ F, a u ∈ V₂ F)
    (ha : a^2=1) (hmove : ∃ u ∈ Z F, a u ≠ u) :
    ∃ (σ : F ≃+* F) (b : MulAut (U F)), σ≠1 ∧ Function.Involutive σ ∧
      (∀ u, b u ∈ V₁ F ↔ u ∈ V₁ F) ∧
      (∀ u, b u ∈ V₂ F ↔ u ∈ V₂ F) ∧
      (∀ u, a (b u) = b ⟨σ u.x,σ u.y,σ u.c⟩) := by
  obtain ⟨r,s,σ,P,Q,hr,hs,hσne,hσσ,hrσ,hsσ,he,hP,hQ⟩ :=
    involution_coordinates a h₁ h₂ ha hmove
  obtain ⟨l,hl,hlσ⟩ := exists_scalar_fixed σ r hrσ
  obtain ⟨m,hm,hmσ⟩ := exists_scalar_fixed σ s hsσ
  have hn : ∃ x, σ x≠x := by
    by_contra hh
    push Not at hh
    exact hσne (RingEquiv.ext hh)
  obtain ⟨k,hk⟩ := InvolutiveTrace.exists_trace_one σ hσσ hn
  change k+σ k=1 at hk
  let P' : F →+ F := {
    toFun x := k*P (l*σ x)
    map_zero' := by simp
    map_add' x y := by simp [map_add,mul_add] }
  let Q' : F →+ F := {
    toFun y := k*Q (m*σ y)
    map_zero' := by simp
    map_add' x y := by simp [map_add,mul_add] }
  let b := coordinateChange l m hl hm P' Q'
  have hp (x : F) : r*s*σ (P' x)+P (l*x)=P' (σ x) := by
    have hh := hP (l*σ x)
    rw [map_mul σ,hσσ,←mul_assoc,hlσ] at hh
    have hv : r*s*σ (P (l*σ x))=P (l*x) := CharTwo.add_eq_zero.mp hh
    change r*s*σ (k*P (l*σ x))+P (l*x)=k*P (l*σ (σ x))
    rw [map_mul,hσσ]
    calc
      _ = σ k*(r*s*σ (P (l*σ x)))+P (l*x) := by ring
      _ = (σ k+1)*P (l*x) := by rw [hv]; ring
      _ = k*P (l*x) := by
        have hh : σ k+1=k := by rw [←hk]; simp [CharTwo.add_self_eq_zero,add_left_comm]
        rw [hh]
  have hq (y : F) : r*s*σ (Q' y)+Q (m*y)=Q' (σ y) := by
    have hh := hQ (m*σ y)
    rw [map_mul σ,hσσ,←mul_assoc,hmσ] at hh
    have hv : r*s*σ (Q (m*σ y))=Q (m*y) := CharTwo.add_eq_zero.mp hh
    change r*s*σ (k*Q (m*σ y))+Q (m*y)=k*Q (m*σ (σ y))
    rw [map_mul,hσσ]
    calc
      _ = σ k*(r*s*σ (Q (m*σ y)))+Q (m*y) := by ring
      _ = (σ k+1)*Q (m*y) := by rw [hv]; ring
      _ = k*Q (m*y) := by
        have hh : σ k+1=k := by rw [←hk]; simp [CharTwo.add_self_eq_zero,add_left_comm]
        rw [hh]
  refine ⟨σ,b,hσne,hσσ,?_,?_,?_⟩
  · intro u
    simp only [mem_V₁]
    change m*u.y=0 ↔ u.y=0
    exact mul_eq_zero.trans (or_iff_right (by exact hm))
  · intro u
    simp only [mem_V₂]
    change l*u.x=0 ↔ u.x=0
    exact mul_eq_zero.trans (or_iff_right (by exact hl))
  · intro u
    rw [he]
    apply U.ext
    · change r*σ (l*u.x)=l*σ u.x
      rw [map_mul,←mul_assoc,hlσ]
    · change s*σ (m*u.y)=m*σ u.y
      rw [map_mul,←mul_assoc,hmσ]
    · change r*s*σ (l*m*u.c+P' u.x+Q' u.y)+P (l*u.x)+Q (m*u.y)=
        l*m*σ u.c+P' (σ u.x)+Q' (σ u.y)
      rw [map_add,map_add,map_mul,map_mul]
      calc
        _ = (r*σ l)*(s*σ m)*σ u.c+
            (r*s*σ (P' u.x)+P (l*u.x))+(r*s*σ (Q' u.y)+Q (m*u.y)) := by ring
        _ = _ := by rw [hlσ,hmσ,hp,hq]

end Matrix.PSL3.LinearAmbientGeometry
