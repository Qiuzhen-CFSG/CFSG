module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.OrthogonalInvolutionCoordinates
public import Theory.Representation.SL2OrthogonalCover.SingularOrbit
public import Theory.GroupTheory.ConstantNonidentityAdditive
/-!
# Singular vectors in the marked orthogonal block coordinates

A subgroup centralized by a Sylow two-subgroup lies in its fixed plane,
where the quadratic form is additive. A regular conjugation orbit on its
nonidentity elements makes that form constant, hence zero. Nonzero singular
vectors then form one orbit under the original block, through the literal
quotient and core maps retained in the coordinate packet.

Source: Aschbacher–Smith, the orthogonal geometry used in 2.4.21, p.536.
-/
public section
open Subgroup Representation Representation.OneCohomology
namespace CFSG.Quasithin.ChapterC.OrthogonalInvolutionCoordinates
variable {L : Type*} [Group L] [Finite L] {n : ℕ} {a : MulAut L}

theorem singular_of_regular_sylow_fixed
    (c : OrthogonalInvolutionCoordinates L n a) (P : Sylow 2 L)
    (W : Subgroup L) (hW : W ≤ pCore 2 L)
    (hWP : ∀ u ∈ W, ∀ p ∈ (P : Subgroup L), Commute u p)
    (hcard : 2 < Nat.card W)
    (htrans : ∀ u : W, u≠1 → ∀ v : W, v≠1 → ∃ l : L,
      l*u.val*l⁻¹ = v.val) :
    ∀ (u : L) (hu : u∈W), SL2OrthogonalCover.form (c.core ⟨u,hW hu⟩).toAdd=0 := by
  let e := inclusion hW
  let q := c.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := c.quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  let P' := P.mapSurjective hq
  have hfixed (u : W) : (c.core (e u)).toAdd ∈ fixed
      (SL2OrthogonalCover.action.comp (P' : Subgroup (SL2OrthogonalCover.SL c.F)).subtype) := by
    intro g
    obtain ⟨p,hp,hpg⟩ := g.property
    have he : MulAut.conjNormal p (e u) = e u := by
      apply Subtype.ext
      change p*u.val*p⁻¹=u.val
      rw [←(hWP u.val u.property p hp).eq,mul_assoc,mul_inv_cancel,mul_one]
    change SL2OrthogonalCover.action g.val (c.core (e u)).toAdd=(c.core (e u)).toAdd
    rw [←hpg]
    change SL2OrthogonalCover.action (c.quotient (QuotientGroup.mk' (pCore 2 L) p)) (c.core (e u)).toAdd=_
    rw [←c.conjugation_equivariant,he]
  let f : W → c.F := fun u => SL2OrthogonalCover.form (c.core (e u)).toAdd
  have hf (u v : W) : f (u*v)=f u+f v := by
    change SL2OrthogonalCover.form (c.core (e (u*v))).toAdd=_
    rw [map_mul,map_mul]
    exact SL2OrthogonalCover.form_add_of_sylow_fixed P' _ _ (hfixed u) (hfixed v)
  have hc (u : W) (hu : u≠1) (v : W) (hv : v≠1) : f u=f v := by
    obtain ⟨l,hl⟩ := htrans u hu v hv
    change SL2OrthogonalCover.form (c.core (e u)).toAdd=SL2OrthogonalCover.form (c.core (e v)).toAdd
    have he : MulAut.conjNormal l (e u) = e v := Subtype.ext hl
    rw [←he,c.conjugation_equivariant,SL2OrthogonalCover.form_invariant]
  intro u hu
  exact constant_nonidentity_additive_eq_zero f hf hcard hc ⟨u,hu⟩

omit [Finite L] in
theorem singular_conjugate
    (c : OrthogonalInvolutionCoordinates L n a) (u v : pCore 2 L)
    (hu : SL2OrthogonalCover.form (c.core u).toAdd=0) (hu1 : u≠1)
    (hv : SL2OrthogonalCover.form (c.core v).toAdd=0) (hv1 : v≠1) :
    ∃ l : L, MulAut.conjNormal l u=v := by
  have hn (w : pCore 2 L) (hw : w≠1) : (c.core w).toAdd≠0 := by
    intro hh
    apply hw
    apply c.core.injective
    exact hh.trans c.core.map_one.symm
  obtain ⟨g,hg⟩ := SL2OrthogonalCover.singular_transitive _ _ hu (hn u hu1) hv (hn v hv1)
  obtain ⟨q,rfl⟩ := c.quotient.surjective g
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  refine ⟨l,c.core.injective ?_⟩
  exact (c.conjugation_equivariant l u).trans hg
end CFSG.Quasithin.ChapterC.OrthogonalInvolutionCoordinates
