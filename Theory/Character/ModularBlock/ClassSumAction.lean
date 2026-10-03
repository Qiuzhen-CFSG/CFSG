module

public import Theory.Character.ModularBlock.CentralCharacter

/-!
# Class sums and central-character scalar actions

Conjugacy-class sums over a commutative ring are central and commute with
change of coefficients. Over the complex numbers, a class sum acts on an
irreducible representation by its ordinary central-character value.
Schur's lemma gives a scalar action; taking traces identifies the scalar
as class size times character value divided by character degree. This
supplies the separating class sums for localized block interpolation.

Ported from `public/lean-eval/glauberman_zStar`,
`Submission/ZStar/BlockOrthogonality.lean` (revision `c3503435`).
-/

public section

noncomputable section

open scoped BigOperators

namespace ModularBlock.BlockOrthogonality

open BlockPreliminaries

attribute [local instance] Fintype.ofFinite

universe u v w

/-- The elements of a conjugacy class as a finite set. -/
private noncomputable def classSet
    {G : Type u} [Group G] [Finite G] (c : ConjClasses G) : Finset G :=
  letI : DecidableEq (ConjClasses G) := Classical.decEq (ConjClasses G)
  Finset.univ.filter fun g : G => ConjClasses.mk g = c

private theorem mem_classSet_iff
    {G : Type u} [Group G] [Finite G]
    {c : ConjClasses G} {g : G} :
    g ∈ classSet c ↔ ConjClasses.mk g = c := by
  classical
  simp [classSet]

private theorem classSet_card
    {G : Type u} [Group G] [Finite G]
    (c : ConjClasses G) :
    (classSet c).card = Nat.card c.carrier := by
  classical
  let e : {g : G // g ∈ classSet c} ≃ c.carrier :=
    { toFun := fun x =>
        ⟨x, ConjClasses.mem_carrier_iff_mk_eq.mpr
          (mem_classSet_iff.mp x.2)⟩
      invFun := fun x =>
        ⟨x, mem_classSet_iff.mpr
          (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr e

/-- The sum of the elements in a conjugacy class, over an arbitrary
coefficient ring. -/
noncomputable def classSum
    {G : Type u} [Group G] [Finite G]
    (R : Type v) [CommRing R] (c : ConjClasses G) : MonoidAlgebra R G :=
  ∑ g ∈ classSet c, MonoidAlgebra.single g 1

theorem classSum_coeff
    {G : Type u} [Group G] [Finite G] [DecidableEq (ConjClasses G)]
    (R : Type v) [CommRing R] (c : ConjClasses G) (g : G) :
    (classSum R c).coeff g = if ConjClasses.mk g = c then 1 else 0 := by
  classical
  rw [classSum]
  simp only [MonoidAlgebra.coeff_sum]
  rw [Finset.sum_apply']
  change ∑ x ∈ classSet c, (Finsupp.single x (1 : R)) g = _
  by_cases hgc : ConjClasses.mk g = c
  · rw [if_pos hgc]
    have hgmem : g ∈ classSet c := mem_classSet_iff.mpr hgc
    rw [Finset.sum_eq_single g]
    · simp
    · intro x _hx hxg
      simp [hxg]
    · intro hgnot
      exact (hgnot hgmem).elim
  · rw [if_neg hgc]
    apply Finset.sum_eq_zero
    intro x _hx
    have hxg : x ≠ g := by
      intro hxg
      apply hgc
      simpa [hxg] using (mem_classSet_iff.mp _hx)
    simp [hxg]

private theorem classSum_apply
    {G : Type u} [Group G] [Finite G] [DecidableEq (ConjClasses G)]
    (R : Type v) [CommRing R] (c : ConjClasses G) (g : G) :
    (classSum R c).coeff g = if ConjClasses.mk g = c then 1 else 0 :=
  classSum_coeff R c g

private theorem classSum_single_comm
    {G : Type u} [Group G] [Finite G]
    (R : Type v) [CommRing R] (c : ConjClasses G) (h : G) :
    (MonoidAlgebra.single h 1 : MonoidAlgebra R G) * classSum R c =
      classSum R c * MonoidAlgebra.single h 1 := by
  classical
  ext x
  simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
    one_mul, mul_one, classSum_apply]
  have hconj :
      ConjClasses.mk (h⁻¹ * x) = ConjClasses.mk (x * h⁻¹) := by
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    exact ⟨h, by group⟩
  rw [hconj]

theorem classSum_comm
    {G : Type u} [Group G] [Finite G]
    (R : Type v) [CommRing R] (c : ConjClasses G)
    (a : MonoidAlgebra R G) :
    a * classSum R c = classSum R c * a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [add_mul, mul_add, hx, hy]
  | single g r =>
      ext x
      have hconj :
          ConjClasses.mk (g⁻¹ * x) = ConjClasses.mk (x * g⁻¹) := by
        rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
        exact ⟨g, by group⟩
      simp only [MonoidAlgebra.coeff_single_mul_apply, MonoidAlgebra.coeff_mul_single_apply,
        classSum_apply]
      rw [hconj, mul_comm]

/-- Changing coefficients in a conjugacy-class sum simply changes every
coefficient `1`. -/
theorem mapRingHom_classSum
    {G : Type u} [Group G] [Finite G]
    {R : Type v} {S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) (c : ConjClasses G) :
    MonoidAlgebra.mapRingHom G f (classSum R c) = classSum S c := by
  classical
  simp [classSum]

private noncomputable def centralIntertwiner
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (z : MonoidAlgebra ℂ G)
    (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a) :
    Representation.IntertwiningMap ρ ρ where
  toLinearMap := ρ.asAlgebraHom z
  isIntertwining' g := by
    rw [← Representation.asAlgebraHom_single_one (ρ := ρ) g]
    change ρ.asAlgebraHom z *
        ρ.asAlgebraHom (MonoidAlgebra.single g (1 : ℂ)) =
      ρ.asAlgebraHom (MonoidAlgebra.single g (1 : ℂ)) * ρ.asAlgebraHom z
    rw [← map_mul, ← map_mul]
    exact congrArg ρ.asAlgebraHom (hz (MonoidAlgebra.single g (1 : ℂ))).symm

private lemma centralIntertwiner_eq_scalar
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (z : MonoidAlgebra ℂ G) (hz : ∀ a : MonoidAlgebra ℂ G, a * z = z * a) :
    ∃ a : ℂ, ρ.asAlgebraHom z = a • (1 : Module.End ℂ V) := by
  classical
  have hfin :
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ) = 1 :=
    (irreducible_iff_end_dimension_one (ρ := ρ)).1 inferInstance
  have : Nontrivial V := irreducible_nontrivial (ρ := ρ)
  have hone_ne_zero :
      (1 : Representation.IntertwiningMap ρ ρ) ≠ 0 := by
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hvzero : v = 0 := by
      simpa using congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) h
    exact hv hvzero
  obtain ⟨a, ha⟩ :
      ∃ a : ℂ, a • (1 : Representation.IntertwiningMap ρ ρ) =
        centralIntertwiner ρ z hz :=
    (finrank_eq_one_iff_of_nonzero'
      (K := ℂ) (V := Representation.IntertwiningMap ρ ρ)
      (1 : Representation.IntertwiningMap ρ ρ) hone_ne_zero).mp hfin
      (centralIntertwiner ρ z hz)
  refine ⟨a, ?_⟩
  ext v
  simpa [centralIntertwiner] using
    (congrArg (fun f : Representation.IntertwiningMap ρ ρ => f v) ha).symm

private theorem classSum_trace
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (c : ConjClasses G) :
    LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ c)) =
      ∑ g ∈ classSet c, ρ.character g := by
  classical
  simp [classSum, Representation.character, map_sum]

theorem classSum_action_eq_centralCharacter
    {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    (c : ConjClasses G) :
    ∃ a : ℂ,
      ρ.asAlgebraHom (classSum ℂ c) = a • (1 : Module.End ℂ V) ∧
      a = ordinaryCentralCharacterValue (characterClassFunction ρ)
        (c := c) := by
  classical
  let : Nontrivial V := irreducible_nontrivial (ρ := ρ)
  obtain ⟨a, ha⟩ := centralIntertwiner_eq_scalar ρ (classSum ℂ c)
    (classSum_comm ℂ c)
  have htrace₁ :
      LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ c)) =
        ∑ g ∈ classSet c, ρ.character g := classSum_trace ρ c
  obtain ⟨x, hx⟩ := ConjClasses.exists_rep c
  have hxc : x ∈ c.carrier :=
    ConjClasses.mem_carrier_iff_mk_eq.mpr hx
  have hconst : ∀ g ∈ classSet c, ρ.character g = ρ.character x := by
    intro g hg
    change (characterClassFunction ρ) (ConjClasses.mk g) =
      (characterClassFunction ρ) (ConjClasses.mk x)
    rw [mem_classSet_iff.mp hg, hx]
  have htrace₁' :
      LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ c)) =
        (Nat.card c.carrier : ℂ) * ρ.character x := by
    rw [htrace₁]
    calc
      (∑ g ∈ classSet c, ρ.character g) =
          ∑ _g ∈ classSet c, ρ.character x := by
            apply Finset.sum_congr rfl
            intro g hg
            exact hconst g hg
      _ = (Nat.card c.carrier : ℂ) * ρ.character x := by
            rw [Finset.sum_const, classSet_card]
            simp [nsmul_eq_mul]
  have htrace₂ :
      LinearMap.trace ℂ V (ρ.asAlgebraHom (classSum ℂ c)) =
        a * (Module.finrank ℂ V : ℂ) := by
    rw [ha, map_smul]
    simp
  have hdegree : ρ.character 1 = (Module.finrank ℂ V : ℂ) := by
    simp [Representation.character]
  have hdim_ne : (Module.finrank ℂ V : ℂ) ≠ 0 := by
    have hpos : 0 < Module.finrank ℂ V :=
      (Module.finrank_pos_iff (R := ℂ) (M := V)).2 inferInstance
    exact_mod_cast hpos.ne'
  refine ⟨a, ha, ?_⟩
  rw [ordinaryCentralCharacterValue]
  have hχc : (characterClassFunction ρ) c = ρ.character x := by
    rw [← hx]
    rfl
  have hχone :
      (characterClassFunction ρ) (ConjClasses.mk (1 : G)) = ρ.character 1 := rfl
  rw [hχc, hχone]
  rw [hdegree]
  have hscalar :
      a * (Module.finrank ℂ V : ℂ) =
        (Nat.card c.carrier : ℂ) * ρ.character x :=
    htrace₂.symm.trans htrace₁'
  field_simp [hdim_ne]
  simpa [mul_comm] using hscalar

end ModularBlock.BlockOrthogonality
