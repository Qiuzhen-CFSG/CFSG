module
public import CFSG.Quasithin.ChapterG.Section12.RecognitionOrbits
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup

/-!
# The invariant quadratic form in the nontransitive G.12 branch

Give value zero to the origin and the orbit of the good center, and value
one elsewhere. The G.12.6 orbit dichotomy proves the quadratic addition law
when the first summand is the center. Conjugation gives the same law for
all its orbit; irreducibility makes that orbit span the space, and linear
span induction extends the law to every first summand.

The resulting form has exactly the original alternating polar form and
its nonzero singular set is exactly the original center orbit. This proves
the quadratic construction in G.12.10 and the final paragraph of G.12.1
without their dimension induction. Nontransitivity remains an explicit
branch hypothesis; generation of the full orthogonal residual is separate.
The literal terminal constituent applies this result in its recognition branch.

Source: Aschbacher--Smith, G.12.6, G.12.10 and the conclusion of G.12.1,
printed pp.371, 373--374.
-/

public noncomputable section
open Subgroup Module
namespace CFSG.Quasithin.ChapterG.Section12
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {D : Subgroup (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V}
  {hB : B.IsAlt} {v : V}

private def orbitValue (D : Subgroup (V ≃ₗ[ZMod 2] V)) (v x : V) : ZMod 2 :=
  @ite (ZMod 2) (x=0 ∨ ∃ a∈D,a v=x) (Classical.propDecidable _) 0 1
private theorem orbitValue_zero : orbitValue D v 0=0 := by simp [orbitValue]
private theorem orbitValue_mem {x : V} (hx : ∃ a∈D,a v=x) : orbitValue D v x=0 := by
  simp [orbitValue,hx]
private theorem orbitValue_self : orbitValue D v v=0 := orbitValue_mem ⟨1,D.one_mem,rfl⟩
private theorem orbitValue_one {x : V} (hx : x≠0) (ho : ¬∃ a∈D,a v=x) :
    orbitValue D v x=1 := by simp [orbitValue,hx,ho]
private theorem double (x : V) : x+x=0 := by
  simpa only [two_smul,zero_smul] using congrArg (fun c : ZMod 2 => c • x)
    (show (2 : ZMod 2)=0 from by decide)
private theorem span_bit {x : V} (hx : x∈Submodule.span (ZMod 2) {v}) : x=0 ∨ x=v := by
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hx
  rcases (show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) c with rfl|rfl
  · exact Or.inl (zero_smul _ _)
  · exact Or.inr (one_smul _ _)

private theorem orbitValue_invariant {a : V ≃ₗ[ZMod 2] V} (ha : a∈D) (x : V) :
    orbitValue D v (a x)=orbitValue D v x := by
  have he : (a x=0 ∨ ∃ b∈D,b v=a x) ↔ (x=0 ∨ ∃ b∈D,b v=x) := by
    constructor
    · rintro (hz|⟨b,hb,hbv⟩)
      · exact Or.inl (a.injective (hz.trans a.map_zero.symm))
      · exact Or.inr ⟨a⁻¹*b,D.mul_mem (D.inv_mem ha) hb,
          by change a.symm (b v)=x; rw [hbv,a.symm_apply_apply]⟩
    · rintro (rfl|⟨b,hb,rfl⟩)
      · exact Or.inl a.map_zero
      · exact Or.inr ⟨a*b,D.mul_mem ha hb,rfl⟩
  by_cases hx : x=0 ∨ ∃ b∈D,b v=x
  · simp only [orbitValue,if_pos hx,if_pos (he.mpr hx)]
  · simp only [orbitValue,if_neg hx,if_neg (fun hh => hx (he.mp hh))]

private theorem orbit_span (hirr : Irreducible D) (hv : v≠0) :
    Submodule.span (ZMod 2) {x : V | ∃ a∈D,a v=x}=⊤ := by
  let U := Submodule.span (ZMod 2) {x : V | ∃ a∈D,a v=x}
  have hinv : ∀ a∈D,∀ x∈U,a x∈U := by
    intro a ha x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b,hb,rfl⟩ := hx
      exact Submodule.subset_span ⟨a*b,D.mul_mem ha hb,rfl⟩
    | zero => simp
    | add x y hx hy hax hay => simpa only [map_add] using U.add_mem hax hay
    | smul c x hx hax => simpa only [map_smul] using U.smul_mem c hax
  apply (hirr U hinv).resolve_left
  intro he
  have hm : v∈U := Submodule.subset_span ⟨1,D.one_mem,rfl⟩
  rw [he] at hm
  exact hv hm

variable [FiniteDimensional (ZMod 2) V]
private theorem orbitValue_add_center (hv : GoodVector D B hB v)
    (hnd : B.Nondegenerate) (hD : D ≤ formStabilizer B) (hirr : Irreducible D)
    (hnt : ¬∀ x : V,x≠0 → ∃ a∈D,a v=x) (y : V) :
    orbitValue D v (v+y)=orbitValue D v y+B v y := by
  classical
  by_cases hy0 : y=0
  · subst y
    simp only [add_zero,orbitValue_self,orbitValue_zero,map_zero]
  by_cases hyv : y=v
  · subst y
    rw [double,orbitValue_zero,orbitValue_self,hB v,zero_add]
  have hyv0 : y+v≠0 := by
    intro he
    have hh := congrArg (fun z : V => z+v) he
    exact hyv (by simpa only [add_assoc,double,add_zero,zero_add] using hh)
  by_cases hy : B v y=0
  · have hn : y∉Submodule.span (ZMod 2) {v} :=
      fun hh => (span_bit hh).elim hy0 hyv
    have he := hv.orbit_iff_add_center hy hn
    rw [add_comm v y,hy,add_zero]
    simp only [orbitValue,hy0,hyv0,false_or,← he]
  · have hy1 : B v y=1 :=
      ((show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) _).resolve_left hy
    have he := (hv.outside_orbit_dichotomy hnd hD hirr hy1).resolve_left hnt
    rw [add_comm v y,hy1]
    by_cases ho : ∃ a∈D,a v=y
    · rw [orbitValue_mem ho,orbitValue_one hyv0 (he.mp ho),zero_add]
    · have ho' : ∃ a∈D,a v=y+v := by
        by_contra hn
        exact ho (he.mpr hn)
      rw [orbitValue_mem ho',orbitValue_one hy0 ho]
      decide

private theorem orbitValue_add_orbit (hv : GoodVector D B hB v)
    (hnd : B.Nondegenerate) (hD : D ≤ formStabilizer B) (hirr : Irreducible D)
    (hnt : ¬∀ x : V,x≠0 → ∃ a∈D,a v=x)
    {x : V} (hx : ∃ a∈D,a v=x) (y : V) :
    orbitValue D v (x+y)=orbitValue D v x+orbitValue D v y+B x y := by
  obtain ⟨a,ha,rfl⟩ := hx
  rw [orbitValue_mem ⟨a,ha,rfl⟩,zero_add]
  have he : a v+y=a (v+a.symm y) := by rw [map_add,a.apply_symm_apply]
  rw [he,orbitValue_invariant ha,orbitValue_add_center hv hnd hD hirr hnt]
  have hq := orbitValue_invariant (v := v) ha (a.symm y)
  rw [a.apply_symm_apply] at hq
  rw [← hq]
  congr 1
  have hp := hD ha v (a.symm y)
  rw [a.apply_symm_apply] at hp
  exact hp.symm

private theorem orbitValue_add (hv : GoodVector D B hB v)
    (hnd : B.Nondegenerate) (hD : D ≤ formStabilizer B) (hirr : Irreducible D)
    (hnt : ¬∀ x : V,x≠0 → ∃ a∈D,a v=x) (x y : V) :
    orbitValue D v (x+y)=orbitValue D v x+orbitValue D v y+B x y := by
  have hx : x∈Submodule.span (ZMod 2) {x : V | ∃ a∈D,a v=x} :=
    (orbit_span hirr hv.nonzero).ge Submodule.mem_top
  induction hx using Submodule.span_induction generalizing y with
  | mem x hx => exact orbitValue_add_orbit hv hnd hD hirr hnt hx y
  | zero => simp only [zero_add,orbitValue_zero,map_zero,LinearMap.zero_apply,add_zero]
  | add a b ha hb hqa hqb =>
    rw [add_assoc,hqa,hqb,hqa b]
    simp only [map_add,LinearMap.add_apply]
    ring
  | smul c a ha hqa =>
    rcases (show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) c with rfl|rfl
    · simp only [zero_smul,zero_add,orbitValue_zero,map_zero,LinearMap.zero_apply,add_zero]
    · simpa only [one_smul] using hqa y

/-- In the nontransitive branch the center orbit is exactly the nonzero
singular set of an invariant quadratic form with the original polar form. -/
theorem GoodVector.exists_quadratic_of_not_transitive
    (hv : GoodVector D B hB v)
    (hnd : B.Nondegenerate) (hD : D ≤ formStabilizer B) (hirr : Irreducible D)
    (hnt : ¬∀ x : V,x≠0 → ∃ a∈D,a v=x) :
    ∃ q : QuadraticForm (ZMod 2) V, q.polarBilin=B ∧ D≤q.isometrySubgroup ∧
      ∀ x : V, q x=0 ↔ x=0 ∨ ∃ a∈D,a v=x := by
  classical
  let q : QuadraticForm (ZMod 2) V := {
    toFun := orbitValue D v
    toFun_smul := by
      intro c x
      rcases (show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) c with rfl|rfl <;>
        simp [orbitValue_zero]
    exists_companion' := ⟨B,orbitValue_add hv hnd hD hirr hnt⟩ }
  refine ⟨q,?_,?_,?_⟩
  · apply LinearMap.ext₂
    intro x y
    change orbitValue D v (x+y)-orbitValue D v x-orbitValue D v y=B x y
    rw [orbitValue_add hv hnd hD hirr hnt]
    ring
  · intro a ha
    apply (QuadraticMap.mem_isometrySubgroup q a).mpr
    exact orbitValue_invariant (v := v) ha
  · intro x
    change orbitValue D v x=0 ↔ _
    by_cases hx : x=0 ∨ ∃ a∈D,a v=x
    · simp only [orbitValue,if_pos hx]
      exact iff_of_true trivial hx
    · simp only [orbitValue,if_neg hx]
      exact iff_of_false (by decide) hx
end CFSG.Quasithin.ChapterG.Section12
