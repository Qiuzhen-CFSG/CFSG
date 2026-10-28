module

public import Theory.AlgebraicGroup.Variety.PolynomialProjBaseChange

/-!
# Even-degree extensionality for polynomial Proj maps

This module proves that two graded endomorphisms of the standard grading on a
multivariable polynomial ring induce the same morphism on `Proj` when they agree on every
even homogeneous component. The result is scheme-theoretic and assumes only that the base
is a commutative ring; in particular, it does not use reducedness.

The proof covers the source by the affine charts `D(f(s ^ 2))`. These have the same open
range as the usual charts `D(f(s))`, so they still cover. On a square chart,
`Proj.awayι_comp_map` reduces the comparison to maps of degree-zero homogeneous
localizations. Every numerator there has even degree, where the two graded maps agree.
Because their images of the square denominator are only propositionally equal, explicit
maps and an equivalence transport `HomogeneousLocalization.Away` across that equality.

This is the Veronese argument needed for the scheme-level projective linear action used in
the formalization of Borel, *Linear Algebraic Groups*, Section 7.2. The chart construction
and functoriality are supplied by Mathlib's projective-spectrum API.
-/

open CategoryTheory AlgebraicGeometry

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

open HomogeneousLocalization

noncomputable section

variable {A : Type u} [CommRing A]
variable {sigma : Type}

/-- Transport an `Away` localization along equality of its polynomial denominator. -/
public noncomputable def polynomialAwayCongrMap
    {f f' : MvPolynomial sigma A} (h : f = f') :
    Away (projectiveGrading A sigma) f →+*
      Away (projectiveGrading A sigma) f' := by
  refine HomogeneousLocalization.map
    (P := Submonoid.powers f) (Q := Submonoid.powers f')
      (.id (projectiveGrading A sigma)) ?_
  intro x hx
  change (GradedRingHom.id (projectiveGrading A sigma)) x ∈ Submonoid.powers f'
  simpa only [GradedRingHom.coe_id, id_eq, h] using hx

/-- The ring equivalence between `Away` localizations whose denominators are equal. -/
public noncomputable def polynomialAwayCongr
    {f f' : MvPolynomial sigma A} (h : f = f') :
    Away (projectiveGrading A sigma) f ≃+*
      Away (projectiveGrading A sigma) f' :=
  RingEquiv.ofBijective (polynomialAwayCongrMap (sigma := sigma) h) (by
    subst f'
    have heq : polynomialAwayCongrMap (sigma := sigma) (Eq.refl f) =
        RingHom.id (Away (projectiveGrading A sigma) f) := by
      simp [polynomialAwayCongrMap]
    rw [heq]
    exact Function.bijective_id)

private theorem polynomialAwayCongr_toRingHom
    {f f' : MvPolynomial sigma A} (h : f = f') :
    (polynomialAwayCongr (sigma := sigma) h).toRingHom =
      polynomialAwayCongrMap (sigma := sigma) h :=
  rfl

private theorem polynomialAwayCongrMap_mk
    {f f' : MvPolynomial sigma A} (h : f = f')
    {d : ℕ} (hf : f ∈ projectiveGrading A sigma d)
    (hf' : f' ∈ projectiveGrading A sigma d)
    (n : ℕ) (p : MvPolynomial sigma A)
    (hp : p ∈ projectiveGrading A sigma (n • d)) :
    polynomialAwayCongrMap (sigma := sigma) h
        (Away.mk (projectiveGrading A sigma) hf n p hp) =
      Away.mk (projectiveGrading A sigma) hf' n p hp := by
  subst f'
  simp [polynomialAwayCongrMap]

/-- Denominator transport is compatible with the standard affine chart immersion into `Proj`. -/
public theorem specMap_polynomialAwayCongr_comp_awayι
    {f f' : MvPolynomial sigma A} (h : f = f')
    {n : ℕ} (hf : f ∈ projectiveGrading A sigma n)
    (hf' : f' ∈ projectiveGrading A sigma n) (hn : 0 < n) :
    Spec.map (CommRingCat.ofHom (polynomialAwayCongr (sigma := sigma) h).toRingHom) ≫
        Proj.awayι (projectiveGrading A sigma) f hf hn =
      Proj.awayι (projectiveGrading A sigma) f' hf' hn := by
  subst f'
  rw [polynomialAwayCongr_toRingHom]
  have heq : polynomialAwayCongrMap (sigma := sigma) (Eq.refl f) =
      RingHom.id (Away (projectiveGrading A sigma) f) := by
    simp [polynomialAwayCongrMap]
  rw [heq]
  simp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def projMapSquareCover
    (f : projectiveGrading A sigma →+*ᵍ projectiveGrading A sigma)
    (hf : HomogeneousIdeal.irrelevant (projectiveGrading A sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading A sigma)).map f) :
    (Proj (projectiveGrading A sigma)).AffineOpenCover where
  I₀ := Σ i : PNat, projectiveGrading A sigma i
  X s := .of (Away (projectiveGrading A sigma) (f ((s.2 : MvPolynomial sigma A) ^ 2)))
  f s := Proj.awayι (projectiveGrading A sigma) (f ((s.2 : MvPolynomial sigma A) ^ 2))
    (f.2 (SetLike.pow_mem_graded 2 s.2.2)) (Nat.mul_pos two_pos s.1.2)
  idx x := (Proj.mapAffineOpenCover f hf).idx x
  covers x := by
    let t := (Proj.mapAffineOpenCover f hf).idx x
    let s : Σ i : PNat, projectiveGrading A sigma i := ⟨t.1, t.2⟩
    let iSq := Proj.awayι (projectiveGrading A sigma)
      (f ((s.2 : MvPolynomial sigma A) ^ 2))
      (f.2 (SetLike.pow_mem_graded 2 s.2.2)) (Nat.mul_pos two_pos s.1.2)
    let iLin := Proj.awayι (projectiveGrading A sigma)
      (f (s.2 : MvPolynomial sigma A)) (f.2 s.2.2) s.1.2
    have : IsOpenImmersion iSq := by
      dsimp only [iSq]
      exact Proj.instIsOpenImmersionAwayι _ _ _ _
    have : IsOpenImmersion iLin := by
      dsimp only [iLin]
      exact Proj.instIsOpenImmersionAwayι _ _ _ _
    change x ∈ Set.range iSq
    have hs : x ∈ Set.range iLin := by
      convert (Proj.mapAffineOpenCover f hf).covers x using 1
      all_goals
        simp [iLin, s, t, Proj.mapAffineOpenCover,
          Proj.affineOpenCoverOfIrrelevantLESpan]
    change x ∈ iSq.opensRange
    change x ∈ iLin.opensRange at hs
    have hSq : iSq.opensRange = Proj.basicOpen (projectiveGrading A sigma)
        ((f (s.2 : MvPolynomial sigma A)) ^ 2) := by
      calc
        iSq.opensRange = Proj.basicOpen (projectiveGrading A sigma)
            (f ((s.2 : MvPolynomial sigma A) ^ 2)) := by
          exact Proj.opensRange_awayι _ _ _ _
        _ = _ := by rw [map_pow]
    have hLin : iLin.opensRange = Proj.basicOpen (projectiveGrading A sigma)
        (f (s.2 : MvPolynomial sigma A)) := by
      exact Proj.opensRange_awayι _ _ _ _
    rw [hSq]
    rw [hLin] at hs
    exact (Proj.basicOpen_pow (projectiveGrading A sigma)
      (f (s.2 : MvPolynomial sigma A)) 2 two_pos) ▸ hs
  map_prop s := Proj.instIsOpenImmersionAwayι _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
Graded endomorphisms of a standard polynomial grading that agree in every even degree
induce equal morphisms on `Proj`, provided both maps satisfy the irrelevant-ideal hypothesis.
-/
public theorem projMap_eq_of_even
    (f g : projectiveGrading A sigma →+*ᵍ projectiveGrading A sigma)
    (hf : HomogeneousIdeal.irrelevant (projectiveGrading A sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading A sigma)).map f)
    (hg : HomogeneousIdeal.irrelevant (projectiveGrading A sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading A sigma)).map g)
    (heven : ∀ (d : ℕ) (p : MvPolynomial sigma A),
      p ∈ projectiveGrading A sigma (2 * d) → f p = g p) :
    Proj.map f hf = Proj.map g hg := by
  refine (projMapSquareCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  change (Σ i : PNat, projectiveGrading A sigma i) at s
  let q : MvPolynomial sigma A := (s.2 : MvPolynomial sigma A) ^ 2
  have hq : q ∈ projectiveGrading A sigma ((s.1 : ℕ) + (s.1 : ℕ)) := by
    simpa only [two_nsmul] using SetLike.pow_mem_graded 2 s.2.2
  have hqpos : 0 < (s.1 : ℕ) + (s.1 : ℕ) :=
    Nat.add_pos_left s.1.2 s.1
  change Proj.awayι (projectiveGrading A sigma) (f q) (f.2 hq) hqpos ≫
      Proj.map f hf =
    Proj.awayι (projectiveGrading A sigma) (f q) (f.2 hq) hqpos ≫
      Proj.map g hg
  have hs : f q = g q := by
    apply heven (s.1 : ℕ)
    simpa [q, two_mul] using hq
  have hmaps :
      Away.map f q =
        (polynomialAwayCongr (sigma := sigma) hs.symm).toRingHom.comp
          (Away.map g q) := by
    apply RingHom.ext
    intro z
    obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective
      (projectiveGrading A sigma) hq z
    simp only [Away.map_mk, RingHom.comp_apply]
    have hdegree : n • ((s.1 : ℕ) + (s.1 : ℕ)) =
        2 * (n * (s.1 : ℕ)) := by
      simp [Nat.mul_add, two_mul]
    have hp' : p ∈ projectiveGrading A sigma (2 * (n * (s.1 : ℕ))) := hdegree ▸ hp
    have hpEq := heven (n * (s.1 : ℕ)) p hp'
    change Away.mk (projectiveGrading A sigma) (f.2 hq) n (f p) (f.2 hp) =
      polynomialAwayCongrMap (sigma := sigma) hs.symm
        (Away.mk (projectiveGrading A sigma) (g.2 hq) n (g p) (g.2 hp))
    rw [polynomialAwayCongrMap_mk (h := hs.symm) (hf := g.2 hq)
      (hf' := f.2 hq) (n := n) (p := g p) (hp := g.2 hp)]
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk]
    rw [hpEq]
    congr 1
  calc
    _ = Spec.map (CommRingCat.ofHom (Away.map f q)) ≫
        Proj.awayι (projectiveGrading A sigma) q hq hqpos :=
      Proj.awayι_comp_map f hf hqpos q hq
    _ = Spec.map (CommRingCat.ofHom
          (polynomialAwayCongr (sigma := sigma) hs.symm).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Away.map g q)) ≫
          Proj.awayι (projectiveGrading A sigma) q hq hqpos := by
      rw [← Category.assoc, ← Spec.map_comp]
      apply congrArg (fun m ↦ m ≫
        Proj.awayι (projectiveGrading A sigma) q hq hqpos)
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      exact hmaps
    _ = Spec.map (CommRingCat.ofHom
          (polynomialAwayCongr (sigma := sigma) hs.symm).toRingHom) ≫
        Proj.awayι (projectiveGrading A sigma) (g q) (g.2 hq) hqpos ≫
          Proj.map g hg := by
      rw [Proj.awayι_comp_map]
    _ = _ := by
      rw [← Category.assoc,
        specMap_polynomialAwayCongr_comp_awayι (sigma := sigma) hs.symm]

end

end Theory.AlgebraicGroup.Variety.Geometric
