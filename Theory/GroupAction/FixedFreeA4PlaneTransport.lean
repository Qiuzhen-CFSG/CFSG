module
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.GroupAction.PermutationFourFixedFreeThree
public import Theory.GroupAction.FixedFreeA4BinaryCertificate
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Group.Equiv.TypeTags

/-!
# Transporting the fixed-free A4 plane obstruction

Let W be an elementary abelian two-group of order sixteen. Suppose an actual
subgroup X of its automorphism group contains a nontrivial involution r and
a fixed-free cubic t satisfying the A4 conjugate relations. If r fixes a
four-element subgroup C pointwise and some element of X moves C, then X is
nonsolvable. The statement retains the supplied X, r, t, C and plane mover.

The finite-vector-space cardinality formula gives dimension four for the
canonical ZMod 2-module on Additive W. A basis identifies W with binary
four-space, and the proved cubic frame theorem adjusts that equivalence to
put t in the canonical form used by the binary certificate. The same change
of coordinates transports both automorphisms, their relations, X and C.
An intertwining identity preserves the actual plane mover, using injectivity
of subgroup map. The binary certificate then proves the image nonsolvable;
the induced equivalence with X gives the result for the original group.

This supplies the representation-independent form of the normalizer
obstruction in Stellmacher (8.6)(b3), Journal of Algebra 190 (1997), printed
p.44. The local construction of W and its automorphisms belongs to the native
Section Eight witness. The finite obstruction is proved in
`FixedFreeA4BinaryCertificate`; it is an imported theorem here.
-/

namespace MulAut
open scoped IsMulCommutative
private abbrev V := Fin 4 → Multiplicative (ZMod 2)

private theorem exists_binary_equiv
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 16) : Nonempty (W ≃* V) := by
  classical
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive W) = 2 ^ 4 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    change Nat.card W = _ at hsize
    simpa only [Nat.card_zmod, hcard, show (2 : ℕ) ^ 4 = 16 by decide] using hsize.symm
  have hdim : Module.finrank (ZMod 2) (Additive W) = 4 :=
    Nat.pow_right_injective (by decide : 1 < 2) hpow
  let basis := Module.finBasisOfFinrankEq (ZMod 2) (Additive W) hdim
  exact ⟨(AddEquiv.toMultiplicativeRight basis.equivFun.toAddEquiv).trans
    (MulEquiv.piMultiplicative fun _ : Fin 4 => ZMod 2)⟩

private theorem fixed_free_congr
    {W W' : Type*} [Group W] [Group W'] (e : W ≃* W') (t : MulAut W)
    (hfixed : ∀ w : W, t w = w → w = 1) :
    ∀ v : W', (MulAut.congr e) t v = v → v = 1 := by
  intro v hv
  change e (t (e.symm v)) = v at hv
  have htv := congrArg e.symm hv
  simp only [MulEquiv.symm_apply_apply] at htv
  have heq := congrArg e (hfixed (e.symm v) htv)
  simpa only [MulEquiv.apply_symm_apply,map_one] using heq

private theorem exists_normalized_binary_equiv
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 16) (t : MulAut W) (hthree : t ^ 3 = 1)
    (hfixed : ∀ w : W, t w = w → w = 1) :
    ∃ e : W ≃* V, ∀ v : V,
      (MulAut.congr e) t v = ![v 1,v 0*v 1,v 2*v 3,v 2] := by
  obtain ⟨e₀⟩ := exists_binary_equiv hcard
  have hthree₀ : ((MulAut.congr e₀) t)^3 = 1 := by rw [←map_pow,hthree,map_one]
  obtain ⟨a,ha⟩ := exists_conjugacy_fixed_free_three_four
    ((MulAut.congr e₀) t) hthree₀ (fixed_free_congr e₀ t hfixed)
  refine ⟨e₀.trans a,?_⟩
  intro v
  have hh := ha (a.symm v)
  change a (e₀ (t (e₀.symm (a.symm v)))) = _ at hh ⊢
  simpa only [MulEquiv.apply_symm_apply] using hh

public theorem not_isSolvable_of_fixed_free_a4_and_plane_move
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 16) (X : Subgroup (MulAut W)) (r t : MulAut W)
    (hr : r ∈ X) (ht : t ∈ X) (hrne : r ≠ 1) (hrtwo : r^2 = 1)
    (htthree : t^3 = 1) (htfixed : ∀ w : W, t w = w → w = 1)
    (hcommute : Commute r (t*r*t⁻¹))
    (hnorm : r*(t*r*t⁻¹)*((t^2)*r*(t^2)⁻¹) = 1)
    (C : Subgroup W) (hCcard : Nat.card C = 4) (hrC : ∀ c : W, c ∈ C → r c = c)
    (hmove : ∃ g : MulAut W, g ∈ X ∧ C.map g.toMonoidHom ≠ C) :
    ¬ Group.IsSolvable X := by
  obtain ⟨e,hcanonical⟩ := exists_normalized_binary_equiv hcard t htthree htfixed
  let f := (MulAut.congr e).toMonoidHom
  let Y := X.map f
  let D := C.map e.toMonoidHom
  have hrY : f r ∈ Y := Subgroup.mem_map_of_mem f hr
  have htY : f t ∈ Y := Subgroup.mem_map_of_mem f ht
  have hrYne : f r ≠ 1 := by
    intro heq
    apply hrne
    apply (MulAut.congr e).injective
    change f r = f 1
    rwa [map_one]
  have hrYtwo : (f r)^2 = 1 := by rw [←map_pow,hrtwo,map_one]
  have htYthree : (f t)^3 = 1 := by rw [←map_pow,htthree,map_one]
  have htYfixed : ∀ v : V, f t v = v → v = 1 := fixed_free_congr e t htfixed
  have hYcommute : Commute (f r) (f t*f r*(f t)⁻¹) := by
    simpa only [map_mul,map_inv] using hcommute.map f
  have hYnorm : f r*(f t*f r*(f t)⁻¹)*(((f t)^2)*f r*((f t)^2)⁻¹) = 1 := by
    simpa only [map_mul,map_inv,map_pow,map_one] using congrArg f hnorm
  have hDcard : Nat.card D = 4 := (Subgroup.card_map_of_injective e.injective).trans hCcard
  have hrD : ∀ d : V, d ∈ D → f r d = d := by
    rintro _ ⟨c,hc,rfl⟩
    change e (r (e.symm (e c))) = e c
    rw [MulEquiv.symm_apply_apply,hrC c hc]
  have hmoveY : ∃ g : MulAut V, g ∈ Y ∧ D.map g.toMonoidHom ≠ D := by
    obtain ⟨g,hg,hgC⟩ := hmove
    refine ⟨f g,Subgroup.mem_map_of_mem f hg,?_⟩
    intro heq
    apply hgC
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    have hcomp : (f g).toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp g.toMonoidHom := by
      apply MonoidHom.ext
      intro w
      change e (g (e.symm (e w))) = e (g w)
      rw [MulEquiv.symm_apply_apply]
    change (C.map e.toMonoidHom).map (f g).toMonoidHom = C.map e.toMonoidHom at heq
    rw [Subgroup.map_map,hcomp] at heq
    rw [Subgroup.map_map]
    exact heq
  have hY := not_isSolvable_of_binary_a4_and_plane_move Y (f r) (f t) hrY htY hrYne hrYtwo htYthree
    htYfixed hcanonical hYcommute hYnorm D hDcard hrD hmoveY
  intro hX
  let _ := hX
  let equiv := X.equivMapOfInjective f (MulAut.congr e).injective
  exact hY (Group.isSolvable_of_surjective (f := equiv.toMonoidHom) equiv.surjective)

end MulAut
