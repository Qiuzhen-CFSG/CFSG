module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalComplements
public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.OddComparison

/-!
# Maximal stabilizers of the original orthogonal field complements

Projection identifies a field complement to the radical of the nonsplit
five-space with the original natural four-space. Transport its quadratic
form through this exact projection. Its polar form is the literal symplectic
form, and preservation of the transported form is equivalent to stabilizing
the original complement upstairs: the first coordinate and quadratic value
uniquely determine a vector of the odd orthogonal space in characteristic two.
The maximality theorem therefore applies without replacing the cover by a
split module or changing its central quotient map.

Source: Aschbacher--Smith 11.2.2, printed p.767. OriginalMaximality transports
this result to N_L(U); the field-automorphism orbit step remains with
qt-d-1222-natural-weak-parameters, and final source discharge belongs to
qt-d-1222-natural-weak-closure-source.
-/

open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalMaximality
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.ComplementMaximality
open Representation.SymplecticFourOrthogonalCover
open ClassicalOrthogonal ClassicalOrthogonal.TheoremDRootNormalizer
open Matrix.PSp4Three
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

def complementProjection (Q : Submodule F (Space (K := F))) (hQ : IsCompl Q radical) :
    Q ≃ₗ[F] Natural (K := F) :=
  LinearEquiv.ofBijective ((LinearMap.fst F _ _).comp Q.subtype) (by
    constructor
    · apply LinearMap.ker_eq_bot.mp
      apply le_bot_iff.mp
      intro x hx
      exact Subtype.ext (hQ.disjoint.eq_bot.le ⟨x.property,hx⟩)
    · intro v
      have hv : (v,0) ∈ Q ⊔ radical := hQ.sup_eq_top.symm ▸ Submodule.mem_top
      obtain ⟨q,hq,r,hr,he⟩ := Submodule.mem_sup.mp hv
      refine ⟨⟨q,hq⟩,?_⟩
      change q.1 = v
      have hh := congrArg Prod.fst he
      simpa only [Prod.fst_add,show r.1=0 from hr,add_zero] using hh)

def naturalForm (Q : Submodule F (Space (K := F))) (hQ : IsCompl Q radical) :
    QuadraticForm F (Natural (K := F)) :=
  (formB 2 F).comp (Q.subtype.comp (complementProjection Q hQ).symm.toLinearMap)

omit [CharP F 2] [Finite F] in
private theorem complementProjection_first (Q : Submodule F (Space (K := F)))
    (hQ : IsCompl Q radical) (x : Q) : complementProjection Q hQ x = x.val.1 := rfl

omit [CharP F 2] [Finite F] in
private theorem complementProjection_symm_first (Q : Submodule F (Space (K := F)))
    (hQ : IsCompl Q radical) (x : Natural (K := F)) :
    ((complementProjection Q hQ).symm x).val.1 = x :=
  (complementProjection Q hQ).apply_symm_apply x

omit [Finite F] in
theorem naturalForm_polar (Q : Submodule F (Space (K := F))) (hQ : IsCompl Q radical) :
    (naturalForm Q hQ).polarBilin = form := by
  rw [naturalForm,QuadraticMap.polarBilin_comp]
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change (formB 2 F).polarBilin ((complementProjection Q hQ).symm x).val
    ((complementProjection Q hQ).symm y).val = _
  rw [polarB_apply,CharTwo.two_eq_zero (R := F),zero_mul,zero_mul,add_zero,polarD_eq_symplectic,
    complementProjection_symm_first,complementProjection_symm_first]

theorem stabilizer_iff_naturalForm (Q : Submodule F (Space (K := F)))
    (hQ : IsCompl Q radical) (g : Sp 2 F) :
    Q.map (fullAction g) = Q ↔ g ∈ quadraticStabilizer (naturalForm Q hQ) := by
  let e := complementProjection Q hQ
  have hfirst (x : Natural (K := F)) : (e.symm x).val.1 = x := e.apply_symm_apply x
  constructor
  · intro hstab x
    let y : Q := ⟨fullAction g (e.symm x).val,by
      exact hstab.le ⟨(e.symm x).val,(e.symm x).property,rfl⟩⟩
    have hy : e y = g • x := by
      change (fullAction g (e.symm x).val).1 = _
      rw [fullAction_apply,hfirst]
      rfl
    have hye : e.symm (g • x) = y := by rw [←hy,e.symm_apply_apply]
    change formB 2 F (e.symm (g • x)).val = formB 2 F (e.symm x).val
    rw [hye]
    exact fullAction_preserves g _
  · intro hstab
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨x,hx,rfl⟩
      let y := e.symm (g • x.1)
      have hy : y.val = fullAction g x := by
        have hf : y.val.1 = (fullAction g x).1 := (hfirst _).trans rfl
        apply Prod.ext hf
        apply CharTwo.sq_injective
        have he : e.symm x.1 = (⟨x,hx⟩ : Q) := e.symm_apply_apply ⟨x,hx⟩
        have h1 := hstab x.1
        change formB 2 F y.val = formB 2 F (e.symm x.1).val at h1
        rw [he] at h1
        have h2 := fullAction_preserves g x
        rw [formB_apply] at h1 h2
        rw [hf] at h1
        exact add_left_cancel (h1.trans h2.symm)
      rw [←hy]
      exact y.property
    · let a : Space (K := F) ≃ₗ[F] Space (K := F) := {
        fullAction g with
        invFun := fullAction g⁻¹
        left_inv := fullAction.inv_self_apply g
        right_inv := fullAction.self_inv_apply g }
      exact LinearEquiv.finrank_map_eq a Q

/-- Maximality for the same field complement in the full nonsplit cover. -/
theorem field_stabilizer_isCoatom (hF : Nat.card F = 4)
    (Q : Submodule F (Space (K := F))) (hQ : IsCompl Q radical) :
    IsCoatom (quadraticStabilizer (naturalForm Q hQ)) :=
  quadraticStabilizer_isCoatom hF _ (naturalForm_polar Q hQ)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.ComplementMaximality

