module

public import Theory.AlgebraicGroup.Irreducible.Basic

universe u

/-!
Irreducibility of products and connected algebraic groups.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k]

@[expose]
public def Variety.prodSet {V W : Variety k} (S : Set (Variety.Point V))
    (T : Set (Variety.Point W)) : Set (Variety.Point (Variety.prod V W)) :=
  {z | (Variety.prodPointEquiv V W z).1 ∈ S ∧ (Variety.prodPointEquiv V W z).2 ∈ T}

public theorem Variety.prodPointEquiv_val {V W : Variety k}
    (z : Variety.Point (Variety.prod V W)) :
    z.val = Sum.elim (Variety.prodPointEquiv V W z).1.val (Variety.prodPointEquiv V W z).2.val := by
  funext i
  cases i <;> simp [Variety.prodPointEquiv]

/-- Substituting the second-coordinate values of `y` into the first variables
of a polynomial on the affine product. -/
@[expose]
public noncomputable def Variety.restrictToFirst {V W : Variety k} (y : Variety.Point W)
    (p : MvPolynomial (V.Coordinates ⊕ W.Coordinates) k) : MvPolynomial V.Coordinates k :=
  MvPolynomial.bind₁ (Sum.elim (fun i₁ ↦ MvPolynomial.X i₁) (fun i₂ ↦ MvPolynomial.C (y.val i₂))) p

/-- Substituting the first-coordinate values of `x` into the second variables
of a polynomial on the affine product. -/
public noncomputable def Variety.restrictToSecond {V W : Variety k} (x : Variety.Point V)
    (p : MvPolynomial (V.Coordinates ⊕ W.Coordinates) k) : MvPolynomial W.Coordinates k :=
  MvPolynomial.bind₁ (Sum.elim (fun i₁ ↦ MvPolynomial.C (x.val i₁)) (fun i₂ ↦ MvPolynomial.X i₂)) p

public theorem evalPolynomial_restrictToFirst {V W : Variety k}
    {x : Variety.Point V} {y : Variety.Point W}
    (p : MvPolynomial (V.Coordinates ⊕ W.Coordinates) k) :
    evalPolynomial (Sum.elim x.val y.val) p =
      evalPolynomial x.val (Variety.restrictToFirst y p) := by
  rw [Variety.restrictToFirst, evalPolynomial_bind₁]
  congr 1
  funext i
  cases i <;> simp [evalPolynomial]

public theorem evalPolynomial_restrictToSecond {V W : Variety k}
    {x : Variety.Point V} {y : Variety.Point W}
    (p : MvPolynomial (V.Coordinates ⊕ W.Coordinates) k) :
    evalPolynomial (Sum.elim x.val y.val) p =
      evalPolynomial y.val (Variety.restrictToSecond x p) := by
  rw [Variety.restrictToSecond, evalPolynomial_bind₁]
  congr 1
  funext i
  cases i <;> simp [evalPolynomial]

public theorem restrictToFirst_restrictToSecond_eval {V W : Variety k}
    {x : Variety.Point V} {y : Variety.Point W}
    (p : MvPolynomial (V.Coordinates ⊕ W.Coordinates) k) :
    evalPolynomial x.val (Variety.restrictToFirst y p) =
      evalPolynomial y.val (Variety.restrictToSecond x p) := by
  calc
    evalPolynomial x.val (Variety.restrictToFirst y p)
        = evalPolynomial (Sum.elim x.val y.val) p := (evalPolynomial_restrictToFirst p).symm
    _ = evalPolynomial y.val (Variety.restrictToSecond x p) := evalPolynomial_restrictToSecond p

/-- Products of irreducible sets avoid a union of two polynomial zero loci
unless one zero locus contains the product entirely (the `p, q` form). -/
public theorem prodSet_subset_zeroLocus_union_of_irreducible {V W : Variety k}
    {S : Set (Variety.Point V)} {T : Set (Variety.Point W)}
    (hS : IsIrreducible S) (hT : IsIrreducible T)
    (p q : MvPolynomial (V.Coordinates ⊕ W.Coordinates) k)
    (h : Variety.prodSet S T ⊆
      {z : Variety.Point (Variety.prod V W) | evalPolynomial z.val p = 0} ∪
      {z : Variety.Point (Variety.prod V W) | evalPolynomial z.val q = 0}) :
    Variety.prodSet S T ⊆
      {z : Variety.Point (Variety.prod V W) | evalPolynomial z.val p = 0} ∨
    Variety.prodSet S T ⊆
      {z : Variety.Point (Variety.prod V W) | evalPolynomial z.val q = 0} := by
  classical
  let Zp : Set (Variety.Point V) :=
    {x | ∀ y ∈ T, evalPolynomial x.val (Variety.restrictToFirst y p) = 0}
  let Zq : Set (Variety.Point V) :=
    {x | ∀ y ∈ T, evalPolynomial x.val (Variety.restrictToFirst y q) = 0}
  have hZT : S ⊆ Zp ∪ Zq := by
    intro x hx
    by_contra hxZ
    have hxp : x ∉ Zp := by intro h; exact hxZ (Or.inl h)
    have hxq : x ∉ Zq := by intro h; exact hxZ (Or.inr h)
    have hxp' : ¬ ∀ y : Variety.Point W, y ∈ T →
        evalPolynomial x.val (Variety.restrictToFirst y p) = 0 := by
      simpa [Zp] using hxp
    have hxq' : ¬ ∀ y : Variety.Point W, y ∈ T →
        evalPolynomial x.val (Variety.restrictToFirst y q) = 0 := by
      simpa [Zq] using hxq
    push Not at hxp' hxq'
    rcases hxp' with ⟨y₁, hy₁, hpy₁⟩
    rcases hxq' with ⟨y₂, hy₂, hqy₂⟩
    let Ax : Set (Variety.Point W) :=
      {y | evalPolynomial y.val (Variety.restrictToSecond x p) = 0}
    let Bx : Set (Variety.Point W) :=
      {y | evalPolynomial y.val (Variety.restrictToSecond x q) = 0}
    have hAxc : IsClosed Ax := by
      rw [Variety.isClosed_iff_isZariskiClosed]
      exact ⟨{Variety.restrictToSecond x p}, by ext y; simp [Ax]⟩
    have hBxc : IsClosed Bx := by
      rw [Variety.isClosed_iff_isZariskiClosed]
      exact ⟨{Variety.restrictToSecond x q}, by ext y; simp [Bx]⟩
    have hTsub : T ⊆ Ax ∪ Bx := by
      intro y hy
      let z : Variety.Point (Variety.prod V W) := (Variety.prodPointEquiv V W).symm (x, y)
      have hzS : z ∈ Variety.prodSet S T := by
        simpa [Variety.prodSet, Equiv.apply_symm_apply] using ⟨hx, hy⟩
      have hzval : z.val = Sum.elim x.val y.val := by
        simp [z, Variety.prodPointEquiv]
      have hz : z ∈ {z | evalPolynomial z.val p = 0} ∪ {z | evalPolynomial z.val q = 0} :=
        h hzS
      rcases hz with hzp | hzq
      · left
        have hval : evalPolynomial z.val p = evalPolynomial y.val (Variety.restrictToSecond x p) := by
          calc
            evalPolynomial z.val p = evalPolynomial (Sum.elim x.val y.val) p := by
              rw [hzval]
            _ = evalPolynomial y.val (Variety.restrictToSecond x p) := evalPolynomial_restrictToSecond p
        change evalPolynomial y.val (Variety.restrictToSecond x p) = 0
        exact hval ▸ hzp
      · right
        have hval : evalPolynomial z.val q = evalPolynomial y.val (Variety.restrictToSecond x q) := by
          calc
            evalPolynomial z.val q = evalPolynomial (Sum.elim x.val y.val) q := by
              rw [hzval]
            _ = evalPolynomial y.val (Variety.restrictToSecond x q) := evalPolynomial_restrictToSecond q
        change evalPolynomial y.val (Variety.restrictToSecond x q) = 0
        exact hval ▸ hzq
    rcases IsIrreducible.subset_union_of_closed hT hAxc hBxc hTsub with hTA | hTB
    · have hxZp : x ∈ Zp := by
        change ∀ y ∈ T, evalPolynomial x.val (Variety.restrictToFirst y p) = 0
        intro y hy
        calc
          evalPolynomial x.val (Variety.restrictToFirst y p)
              = evalPolynomial y.val (Variety.restrictToSecond x p) := restrictToFirst_restrictToSecond_eval p
          _ = 0 := by simpa [Ax] using hTA hy
      exact hxZ (Or.inl hxZp)
    · have hxZq : x ∈ Zq := by
        change ∀ y ∈ T, evalPolynomial x.val (Variety.restrictToFirst y q) = 0
        intro y hy
        calc
          evalPolynomial x.val (Variety.restrictToFirst y q)
              = evalPolynomial y.val (Variety.restrictToSecond x q) := restrictToFirst_restrictToSecond_eval q
          _ = 0 := by simpa [Bx] using hTB hy
      exact hxZ (Or.inr hxZq)
  have hZp_eq : Zp = ⋂ y : {y : Variety.Point W // y ∈ T},
      {x : Variety.Point V | evalPolynomial x.val (Variety.restrictToFirst y.1 p) = 0} := by
    ext x
    simp [Zp]
  have hZq_eq : Zq = ⋂ y : {y : Variety.Point W // y ∈ T},
      {x : Variety.Point V | evalPolynomial x.val (Variety.restrictToFirst y.1 q) = 0} := by
    ext x
    simp [Zq]
  have hZpc : IsClosed Zp := by
    rw [Variety.isClosed_iff_isZariskiClosed]
    rw [hZp_eq]
    exact isZariskiClosed_iInter (fun y : {y : Variety.Point W // y ∈ T} =>
      {x : Variety.Point V | evalPolynomial x.val (Variety.restrictToFirst y.1 p) = 0}) (by
      intro y
      exact ⟨{Variety.restrictToFirst y.1 p}, by ext x; simp⟩)
  have hZqc : IsClosed Zq := by
    rw [Variety.isClosed_iff_isZariskiClosed]
    rw [hZq_eq]
    exact isZariskiClosed_iInter (fun y : {y : Variety.Point W // y ∈ T} =>
      {x : Variety.Point V | evalPolynomial x.val (Variety.restrictToFirst y.1 q) = 0}) (by
      intro y
      exact ⟨{Variety.restrictToFirst y.1 q}, by ext x; simp⟩)
  rcases IsIrreducible.subset_union_of_closed hS hZpc hZqc hZT with hSZp | hSZq
  · left
    intro z hz
    have hxS : (Variety.prodPointEquiv V W z).1 ∈ S := hz.1
    have hyT : (Variety.prodPointEquiv V W z).2 ∈ T := hz.2
    have hxZ : (Variety.prodPointEquiv V W z).1 ∈ Zp := hSZp hxS
    change evalPolynomial z.val p = 0
    have hval : evalPolynomial z.val p =
        evalPolynomial (Variety.prodPointEquiv V W z).1.val
          (Variety.restrictToFirst (Variety.prodPointEquiv V W z).2 p) := by
      calc
        evalPolynomial z.val p
            = evalPolynomial (Sum.elim (Variety.prodPointEquiv V W z).1.val
                (Variety.prodPointEquiv V W z).2.val) p := by
                  rw [Variety.prodPointEquiv_val]
            _ = evalPolynomial (Variety.prodPointEquiv V W z).1.val
                  (Variety.restrictToFirst (Variety.prodPointEquiv V W z).2 p) :=
                evalPolynomial_restrictToFirst p
    exact hval ▸ hxZ (Variety.prodPointEquiv V W z).2 hyT
  · right
    intro z hz
    have hxS : (Variety.prodPointEquiv V W z).1 ∈ S := hz.1
    have hyT : (Variety.prodPointEquiv V W z).2 ∈ T := hz.2
    have hxZ : (Variety.prodPointEquiv V W z).1 ∈ Zq := hSZq hxS
    change evalPolynomial z.val q = 0
    have hval : evalPolynomial z.val q =
        evalPolynomial (Variety.prodPointEquiv V W z).1.val
          (Variety.restrictToFirst (Variety.prodPointEquiv V W z).2 q) := by
      calc
        evalPolynomial z.val q
            = evalPolynomial (Sum.elim (Variety.prodPointEquiv V W z).1.val
                (Variety.prodPointEquiv V W z).2.val) q := by
                  rw [Variety.prodPointEquiv_val]
            _ = evalPolynomial (Variety.prodPointEquiv V W z).1.val
                  (Variety.restrictToFirst (Variety.prodPointEquiv V W z).2 q) :=
                evalPolynomial_restrictToFirst q
    exact hval ▸ hxZ (Variety.prodPointEquiv V W z).2 hyT

/-- Products of irreducible sets avoid a union of two Zariski-closed sets
unless one of them contains the product entirely. -/
public theorem prodSet_subset_union_of_irreducible {V W : Variety k}
    {S : Set (Variety.Point V)} {T : Set (Variety.Point W)}
    (hS : IsIrreducible S) (hT : IsIrreducible T)
    {A B : Set (Variety.Point (Variety.prod V W))}
    (hA : IsZariskiClosed (Variety.prod V W) A)
    (hB : IsZariskiClosed (Variety.prod V W) B)
    (h : Variety.prodSet S T ⊆ A ∪ B) :
    Variety.prodSet S T ⊆ A ∨ Variety.prodSet S T ⊆ B := by
  classical
  rcases hA with ⟨E, hE⟩
  rcases hB with ⟨F, hF⟩
  by_contra h'
  push Not at h'
  rcases (Set.not_subset.mp h'.1) with ⟨z₁, hz₁, hz₁A⟩
  rcases (Set.not_subset.mp h'.2) with ⟨z₂, hz₂, hz₂B⟩
  have hz₁E : ∃ p ∈ E, evalPolynomial z₁.val p ≠ 0 := by
    by_contra hz
    apply hz₁A
    rw [hE]
    intro p hp
    by_contra hp0
    exact hz ⟨p, hp, hp0⟩
  have hz₂F : ∃ q ∈ F, evalPolynomial z₂.val q ≠ 0 := by
    by_contra hz
    apply hz₂B
    rw [hF]
    intro q hq
    by_contra hq0
    exact hz ⟨q, hq, hq0⟩
  rcases hz₁E with ⟨p, hpE, hp10⟩
  rcases hz₂F with ⟨q, hqF, hq20⟩
  have hsub : Variety.prodSet S T ⊆
      {z : Variety.Point (Variety.prod V W) | evalPolynomial z.val p = 0} ∪
      {z : Variety.Point (Variety.prod V W) | evalPolynomial z.val q = 0} := by
    intro z hz
    rcases h hz with hzA | hzB
    · left
      rw [hE] at hzA
      exact hzA p hpE
    · right
      rw [hF] at hzB
      exact hzB q hqF
  rcases prodSet_subset_zeroLocus_union_of_irreducible hS hT p q hsub with hS1 | hS2
  · exact False.elim (hp10 (hS1 hz₁))
  · exact False.elim (hq20 (hS2 hz₂))

/-- The product of two irreducible point sets is irreducible in the affine
product variety. -/
public theorem prodSet_irreducible_of_irreducible {V W : Variety k}
    {S : Set (Variety.Point V)} {T : Set (Variety.Point W)}
    (hS : IsIrreducible S) (hT : IsIrreducible T) :
    IsIrreducible (Variety.prodSet S T) := by
  constructor
  · rcases hS.1 with ⟨x, hx⟩
    rcases hT.1 with ⟨y, hy⟩
    refine ⟨(Variety.prodPointEquiv V W).symm (x, y), ?_⟩
    simp [Variety.prodSet, hx, hy]
  · intro u v hu hv huS hvS
    by_contra h
    have hsub : Variety.prodSet S T ⊆ uᶜ ∪ vᶜ := by
      intro z hz
      by_contra hzuv
      have hzu : z ∈ u := by
        by_contra hzu'
        exact hzuv (Or.inl hzu')
      have hzv : z ∈ v := by
        by_contra hzv'
        exact hzuv (Or.inr hzv')
      exact h ⟨z, ⟨hz, ⟨hzu, hzv⟩⟩⟩
    have hAu : IsZariskiClosed (Variety.prod V W) uᶜ :=
      Variety.isClosed_iff_isZariskiClosed.mp hu.isClosed_compl
    have hAv : IsZariskiClosed (Variety.prod V W) vᶜ :=
      Variety.isClosed_iff_isZariskiClosed.mp hv.isClosed_compl
    rcases prodSet_subset_union_of_irreducible hS hT hAu hAv hsub with hS1 | hS2
    · rcases huS with ⟨z, hz, hzu⟩
      exact (hS1 hz) hzu
    · rcases hvS with ⟨z, hz, hzv⟩
      exact (hS2 hz) hzv

/-- The point-wise product of two irreducible point sets is irreducible. -/
private lemma mulMorphism_image_prodSet (G : Variety k) [AlgebraicGroup G]
    (S T : Set (Variety.Point G)) :
    (Theory.AlgebraicGroup.mulMorphism G).toFun '' Variety.prodSet S T =
      {z : Variety.Point G | ∃ x ∈ S, ∃ y ∈ T, z = x * y} := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨w, hw, hzdef⟩
    refine ⟨(Variety.prodPointEquiv G G w).1, hw.1, (Variety.prodPointEquiv G G w).2, hw.2, ?_⟩
    calc
      z = (Theory.AlgebraicGroup.mulMorphism G).toFun w := hzdef.symm
      _ = (Variety.prodPointEquiv G G w).1 * (Variety.prodPointEquiv G G w).2 := rfl
  · intro hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    refine ⟨(Variety.prodPointEquiv G G).symm (x, y), ?_, ?_⟩
    · simpa [Variety.prodSet, Equiv.apply_symm_apply] using ⟨hx, hy⟩
    · simp [Theory.AlgebraicGroup.mulMorphism, Variety.prodPointEquiv]

/-- The point-wise product of two irreducible point sets is irreducible. -/
private lemma image_mul_isIrreducible (G : Variety k) [AlgebraicGroup G]
    {S T : Set (Variety.Point G)}
    (hS : IsIrreducible S) (hT : IsIrreducible T) :
    IsIrreducible {z : Variety.Point G | ∃ x ∈ S, ∃ y ∈ T, z = x * y} := by
  rw [← Theory.AlgebraicGroup.mulMorphism_image_prodSet G S T]
  exact IsIrreducible.image (prodSet_irreducible_of_irreducible hS hT)
    (Theory.AlgebraicGroup.mulMorphism G).toFun
    (Theory.AlgebraicGroup.mulMorphism G).continuous.continuousOn

/-- Proposition 1.1.4(f)(⟹): a connected algebraic group is irreducible. -/
public theorem connectedAlgebraicGroup_irreducible (G : Variety k) [AlgebraicGroup G]
    (h : Variety.IsConnected G) :
    IsIrreducible (Set.univ : Set (Variety.Point G)) := by
  classical
  let C : Set (Variety.Point G) := irreducibleComponent (1 : Variety.Point G)
  have hC : C ∈ irreducibleComponents (Variety.Point G) := by
    simpa [C] using irreducibleComponent_mem_irreducibleComponents (1 : Variety.Point G)
  have hCirr : IsIrreducible C := by
    simpa [C] using (isIrreducible_irreducibleComponent (x := (1 : Variety.Point G)))
  have hCe : (1 : Variety.Point G) ∈ C := by
    simpa [C] using (mem_irreducibleComponent (x := (1 : Variety.Point G)))
  have hCclosed : IsClosed C := by
    simpa [C] using (isClosed_irreducibleComponent (x := (1 : Variety.Point G)))
  have hCmulC : {z : Variety.Point G | ∃ x ∈ C, ∃ y ∈ C, z = x * y} ⊆ C := by
    have hirr : IsIrreducible {z : Variety.Point G | ∃ x ∈ C, ∃ y ∈ C, z = x * y} :=
      Theory.AlgebraicGroup.image_mul_isIrreducible G hCirr hCirr
    have hCW : C ⊆ {z : Variety.Point G | ∃ x ∈ C, ∃ y ∈ C, z = x * y} := by
      intro x hx
      exact ⟨x, hx, 1, hCe, by simp⟩
    exact irreducible_subset_of_contains_component hC hCW hirr
  let Cinv : Set (Variety.Point G) := (Theory.AlgebraicGroup.invMorphism G).toFun '' C
  have hCinvirr : IsIrreducible Cinv := by
    simpa [Cinv] using IsIrreducible.image hCirr (Theory.AlgebraicGroup.invMorphism G).toFun
      ((Theory.AlgebraicGroup.invMorphism G).continuous.continuousOn)
  have hCinvC : {z : Variety.Point G | ∃ x ∈ Cinv, ∃ y ∈ C, z = x * y} ⊆ C := by
    have hirr : IsIrreducible {z : Variety.Point G | ∃ x ∈ Cinv, ∃ y ∈ C, z = x * y} :=
      Theory.AlgebraicGroup.image_mul_isIrreducible G hCinvirr hCirr
    have hCW : C ⊆ {z : Variety.Point G | ∃ x ∈ Cinv, ∃ y ∈ C, z = x * y} := by
      intro x hx
      refine ⟨1, ?_, x, hx, by simp⟩
      exact ⟨1, hCe, by simp [Theory.AlgebraicGroup.invMorphism]⟩
    exact irreducible_subset_of_contains_component hC hCW hirr
  have hCinvc : ∀ x ∈ C, x⁻¹ ∈ C := by
    intro x hx
    have hmem : x⁻¹ ∈ {z : Variety.Point G | ∃ u ∈ Cinv, ∃ v ∈ C, z = u * v} := by
      refine ⟨x⁻¹, ?_, 1, hCe, by simp⟩
      exact ⟨x, hx, rfl⟩
    exact hCinvC hmem
  let Csub : Subgroup (Variety.Point G) :=
    { carrier := C
      one_mem' := hCe
      mul_mem' := by
        intro x y hx hy
        exact hCmulC ⟨x, hx, y, hy, rfl⟩
      inv_mem' := by intro a ha; exact hCinvc a ha }
  have hcoset_component : ∀ g : Variety.Point G,
      (fun x ↦ g * x) '' C ∈ irreducibleComponents (Variety.Point G) := by
    intro g
    have hcont : ContinuousOn (fun x : Variety.Point G ↦ g * x) C := by
      have hcontG : Continuous (fun x : Variety.Point G ↦ g * x) := by
        exact (Theory.AlgebraicGroup.leftMulMorphism G g).continuous.congr
          (fun x ↦ (Theory.AlgebraicGroup.leftMulMorphism_apply G g x))
      exact hcontG.continuousOn
    have hirr : IsIrreducible ((fun x : Variety.Point G ↦ g * x) '' C) :=
      IsIrreducible.image hCirr (fun x : Variety.Point G ↦ g * x) hcont
    rcases exists_mem_irreducibleComponents_subset_of_isIrreducible ((fun x : Variety.Point G ↦ g * x) '' C) hirr
      with ⟨Cg, hCg, hsub⟩
    have hCg_eq : Cg = (fun x : Variety.Point G ↦ g * x) '' C := by
      apply Set.Subset.antisymm
      · have hgC : C ⊆ (fun x : Variety.Point G ↦ g⁻¹ * x) '' Cg := by
          intro x hx
          exact ⟨g * x, hsub ⟨x, hx, rfl⟩, by simp⟩
        have hcont2 : ContinuousOn (fun x : Variety.Point G ↦ g⁻¹ * x) Cg := by
          have hcontG : Continuous (fun x : Variety.Point G ↦ g⁻¹ * x) := by
            exact (Theory.AlgebraicGroup.leftMulMorphism G g⁻¹).continuous.congr
              (fun x ↦ (Theory.AlgebraicGroup.leftMulMorphism_apply G g⁻¹ x))
          exact hcontG.continuousOn
        have hirr2 : IsIrreducible ((fun x : Variety.Point G ↦ g⁻¹ * x) '' Cg) :=
          IsIrreducible.image hCg.1 (fun x : Variety.Point G ↦ g⁻¹ * x) hcont2
        have hsub2 : (fun x : Variety.Point G ↦ g⁻¹ * x) '' Cg ⊆ C :=
          irreducible_subset_of_contains_component hC hgC hirr2
        intro y hy
        exact ⟨g⁻¹ * y, hsub2 ⟨y, hy, rfl⟩, by simp⟩
      · exact hsub
    simpa [hCg_eq] using hCg
  let F : Set (Set (Variety.Point G)) :=
    {Z | ∃ g : Variety.Point G, Z = (fun x ↦ g * x) '' C}
  have hFfinite : F.Finite :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Variety.Point G)).subset (by
      intro Z hZ
      rcases hZ with ⟨g, rfl⟩
      exact hcoset_component g)
  have hCopen : IsOpen C := by
    let D : Set (Variety.Point G) := {z | ∃ g : Variety.Point G, g ∉ C ∧ z ∈ (fun x ↦ g * x) '' C}
    have hD : D = Cᶜ := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨g, hg, hzg⟩
        rcases hzg with ⟨y, hy, hzdef⟩
        by_contra hzC
        have hzC' : z ∈ C := by simpa using hzC
        have hgC : g ∈ C := by
          have : z * y⁻¹ ∈ C := Csub.mul_mem hzC' (Csub.inv_mem hy)
          have hg_eq : g = z * y⁻¹ := by
            calc
              g = (g * y) * y⁻¹ := by simp [mul_assoc]
              _ = z * y⁻¹ := by rw [← hzdef]
          exact hg_eq.symm ▸ this
        exact hg hgC
      · intro hz
        exact ⟨z, hz, ⟨1, hCe, by simp⟩⟩
    have hD_eq : D = ⋃₀ (F \ {C}) := by
      ext z
      constructor
      · intro hz
        rcases hz with ⟨g, hg, hzg⟩
        have hZne : (fun x ↦ g * x) '' C ≠ C := by
          intro hEq
          apply hg
          have : g ∈ (fun x ↦ g * x) '' C := ⟨1, hCe, by simp⟩
          simpa [hEq] using this
        exact Set.mem_sUnion.mpr ⟨(fun x ↦ g * x) '' C, ⟨⟨g, rfl⟩, hZne⟩, hzg⟩
      · intro hz
        rcases hz with ⟨Z, hZ, hzZ⟩
        rcases hZ with ⟨⟨g, rfl⟩, hZne⟩
        refine ⟨g, ?_, hzZ⟩
        intro hgC
        apply hZne
        apply Set.Subset.antisymm
        · intro w hw
          rcases hw with ⟨y, hy, rfl⟩
          exact hCmulC ⟨g, hgC, y, hy, rfl⟩
        · intro w hw
          refine ⟨g⁻¹ * w, Csub.mul_mem (Csub.inv_mem hgC) hw, by simp⟩
    have hDclosed : IsClosed D := by
      rw [hD_eq]
      have hF' : (F \ {C}).Finite := hFfinite.sdiff
      convert hF'.isClosed_biUnion
        (f := fun Z : Set (Variety.Point G) ↦ Z) (by
          intro Z hZ
          rcases hZ.1 with ⟨g, rfl⟩
          exact isClosed_of_mem_irreducibleComponents ((fun x ↦ g * x) '' C) (hcoset_component g)) using 1
      ext z
      simp
    have hDcom : Dᶜ = C := by
      ext z
      simp [hD]
    exact hDcom ▸ (isOpen_compl_iff.mpr hDclosed)
  have hCclopen : IsClopen C := ⟨hCclosed, hCopen⟩
  have hXsubC : (Set.univ : Set (Variety.Point G)) ⊆ C := by
    rcases h with ⟨hne, hconn⟩
    by_contra hnot
    rcases (Set.not_subset).mp hnot with ⟨x, hxU, hxC⟩
    have hu : ((Set.univ : Set (Variety.Point G)) ∩ C).Nonempty := ⟨1, ⟨Set.mem_univ 1, hCe⟩⟩
    have hv : ((Set.univ : Set (Variety.Point G)) ∩ Cᶜ).Nonempty := ⟨x, ⟨hxU, hxC⟩⟩
    have hw := hconn C Cᶜ hCclopen.2 hCclopen.1.isOpen_compl
      (by intro z hz; by_cases hzC : z ∈ C; exact Or.inl hzC; exact Or.inr hzC) hu hv
    rcases hw with ⟨z, hzU, hzCC⟩
    rcases hzCC with ⟨hzC₁, hzC₂⟩
    exact hzC₂ hzC₁
  have hCeq : (Set.univ : Set (Variety.Point G)) = C :=
    Set.Subset.antisymm hXsubC (by intro x hx; trivial)
  rw [hCeq]
  exact hCirr

/-- Proposition 1.1.4(f)(⟹): a connected algebraic group has a domain
coordinate ring. -/
public theorem connectedAlgebraicGroup_coordinateRing_domain (G : Variety k) [AlgebraicGroup G]
    (h : Variety.IsConnected G) :
    IsDomain (coordinateRing G) :=
  irreducibleVariety_coordinateRing_domain G (connectedAlgebraicGroup_irreducible G h)

end Theory.AlgebraicGroup
