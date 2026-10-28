module

public import Theory.Representation.CharacterWeightLines
public import Theory.Representation.AbelianWeightNormalizerSolvable
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.IntegralDomain

/-!
# Noncyclic abelian determinant-one actions in degree three

A faithful cross-characteristic representation of a finite abelian group splits
into simultaneous character spaces over an algebraically closed field. Collect
bases of these spaces. If two of the three basis vectors have the same
character, the determinant-one equation makes that character faithful: its
kernel fixes all three vectors. A finite subgroup of the multiplicative group
of a field is cyclic. Thus a noncyclic group has three distinct weights, each
of dimension one, and its centralizer is abelian.

For matrix groups over an arbitrary field, apply the argument to the entrywise
embedding into the algebraic closure. This preserves the actual determinant
and faithfulness, and does not require a splitting-field assumption on the
original representation.

Source: the degree-three weight calculation underlying Aschbacher–Smith,
A.3.21(c), printed pp.55–56, and the Cartan argument on pp.510–511 of
`refs/quasithin.pdf`.
-/

public section

open Module
namespace Representation
variable {E K V : Type*} [Field E] [Group K]
  [AddCommGroup V] [Module E V] [IsMulCommutative K]
  [FiniteDimensional E V] [IsAlgClosed E]

private theorem exists_character_basis (sigma : Representation E K V)
    (horder : (Nat.card K : E) ≠ 0) (hdim : Module.finrank E V = 3) :
    ∃ (b : Basis (Fin 3) E V) (w : Fin 3 → sigma.CharacterWeight),
      ∀ k i, sigma k (b i) = (w i).val k • b i := by
  classical
  let W : sigma.CharacterWeight → Submodule E V :=
    fun chi => sigma.characterWeightSpace chi.val
  have hind : iSupIndep W :=
    (sigma.characterWeightSpace_independent horder).comp Subtype.val_injective
  have hi : DirectSum.IsInternal W :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind
      (sigma.iSup_characterWeightSpace_eq_top horder)
  let b₀ := hi.collectedBasis (fun chi => Module.finBasis E (W chi))
  let e := b₀.indexEquiv ((Module.finBasis E V).reindex (finCongr hdim))
  refine ⟨b₀.reindex e, fun i => (e.symm i).1, ?_⟩
  intro k i
  have hm := hi.collectedBasis_mem (fun chi => Module.finBasis E (W chi)) (e.symm i)
  have he : ∀ k, sigma k (b₀ (e.symm i)) =
      (((e.symm i).1.val k : Eˣ) : E) • b₀ (e.symm i) := by
    change b₀ (e.symm i) ∈ sigma.characterWeightSpace (e.symm i).1.val at hm
    simpa only [characterWeightSpace, Submodule.mem_iInf,
      Module.End.mem_eigenspace_iff] using hm
  simpa only [Basis.coe_reindex, Function.comp_apply, Units.smul_def] using he k


omit [IsAlgClosed E] in
private theorem three_entries_eq_one (v : Fin 3 → E)
    (hp : v 0 * v 1 * v 2 = 1) (i j : Fin 3) (hij : i ≠ j)
    (hi : v i = 1) (hj : v j = 1) : ∀ a, v a = 1 := by
  fin_cases i <;> fin_cases j <;> simp_all <;> intro a <;> fin_cases a <;> simp_all

variable [Finite K]
/-- Noncyclic faithful determinant-one actions in dimension three have three distinct weights. -/
theorem characterWeight_card_eq_three_of_noncyclic_det_one (sigma : Representation E K V)
    (horder : (Nat.card K : E) ≠ 0) (hdim : Module.finrank E V = 3)
    (hfaith : Function.Injective sigma) (hn : ¬ IsCyclic K)
    (hdet : ∀ k, LinearMap.det (sigma k) = 1) :
    Nat.card sigma.CharacterWeight = 3 := by
  classical
  obtain ⟨b, w, hw⟩ := exists_character_basis sigma horder hdim
  have hmat (k : K) : LinearMap.toMatrix b b (sigma k) =
      Matrix.diagonal (fun i => ((w i).val k : E)) := by
    ext i j
    simp only [LinearMap.toMatrix_apply, hw, Units.smul_def, map_smul,
      Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst j; simp
    · simp [Matrix.diagonal, hij, Ne.symm hij]
  have hprod (k : K) : (((w 0).val k : E) * ((w 1).val k : E)) * ((w 2).val k : E) = 1 := by
    have he := hdet k
    rw [← LinearMap.det_toMatrix b, hmat, Matrix.det_diagonal, Fin.prod_univ_three] at he
    exact he
  have hwi : Function.Injective w := by
    intro i j he
    by_contra hij
    apply hn
    let chi : K →* E := (Units.coeHom E).comp (w i).val
    apply isCyclic_of_injective_ringHom chi
    apply (injective_iff_map_eq_one chi).mpr
    intro k hk
    have hki : ((w i).val k : E) = 1 := hk
    have hkj : ((w j).val k : E) = 1 := by rw [← he]; exact hki
    have hka := three_entries_eq_one (fun a => ((w a).val k : E))
      (hprod k) i j hij hki hkj
    apply hfaith
    rw [map_one]
    apply b.ext
    intro a
    simp only [hw, Units.smul_def, hka, one_smul, Module.End.one_apply]
  have hle := (sigma.characterWeight_card_le horder).2
  let _ := (sigma.characterWeight_card_le horder).1
  have hge := Nat.card_le_card_of_injective w hwi
  rw [Nat.card_fin] at hge
  omega


/-- A noncyclic abelian determinant-one subgroup acting faithfully in dimension
three has abelian centralizer. -/
theorem centralizer_isMulCommutative_of_noncyclic_det_one_three
    {G : Type*} [Group G] (rho : Representation E G V) (A : Subgroup G)
    [Finite A] [IsMulCommutative A]
    (hrho : Function.Injective rho) (horder : (Nat.card A : E) ≠ 0)
    (hdim : Module.finrank E V = 3) (hn : ¬ IsCyclic A)
    (hdet : ∀ a : A, LinearMap.det (rho a.val) = 1) :
    IsMulCommutative (Subgroup.centralizer (A : Set G)) := by
  apply centralizer_isMulCommutative_of_characterWeight_finrank_one rho A hrho horder
  intro chi
  apply characterWeight_finrank_one_of_card_eq_finrank (rho.comp A.subtype) horder
  rw [hdim]
  exact characterWeight_card_eq_three_of_noncyclic_det_one (rho.comp A.subtype) horder hdim
    (hrho.comp A.subtype_injective) hn hdet

end Representation

open scoped MatrixGroups
namespace Representation

/-- The centralizer of a noncyclic cross-characteristic abelian SL₃ subgroup
is abelian, over the original coefficient field. -/
theorem specialLinear_centralizer_isMulCommutative_of_noncyclic
    {F : Type*} [Field F] (A : Subgroup SL(3, F)) [Finite A] [IsMulCommutative A]
    (hn : ¬ IsCyclic A) (horder : (Nat.card A : F) ≠ 0) :
    IsMulCommutative (Subgroup.centralizer (A : Set SL(3, F))) := by
  let E := AlgebraicClosure F
  let f : SL(3, F) →* SL(3, E) := Matrix.SpecialLinearGroup.map (algebraMap F E)
  have hf : Function.Injective f := by
    intro a b h
    ext i j
    apply (algebraMap F E).injective
    exact congrArg (fun c : SL(3, E) => c i j) h
  let rho : Representation E SL(3, F) (Fin 3 → E) := (specialLinearNatural 3).comp f
  have hrho : Function.Injective rho := (specialLinearNatural_injective 3).comp hf
  have horder' : (Nat.card A : E) ≠ 0 := by
    intro h
    apply horder
    apply (algebraMap F E).injective
    simpa using h
  apply centralizer_isMulCommutative_of_noncyclic_det_one_three rho A hrho horder'
    (by simp only [Module.finrank_pi, Fintype.card_fin]) hn
  intro a
  change LinearMap.det (Matrix.toLin' (f a.val).val) = 1
  rw [LinearMap.det_toLin']
  exact (f a.val).property

/-- The same centralizer calculation for determinant-one subgroups presented
inside GL₃; no finiteness of the coefficient field is needed. -/
theorem generalLinear_centralizer_isMulCommutative_of_noncyclic_det_one
    {F : Type*} [Field F] (A : Subgroup (GL (Fin 3) F))
    [Finite A] [IsMulCommutative A]
    (horder : (Nat.card A : F) ≠ 0) (hn : ¬ IsCyclic A)
    (hdet : ∀ a : A, Matrix.GeneralLinearGroup.det a.val = 1) :
    IsMulCommutative (Subgroup.centralizer (A : Set (GL (Fin 3) F))) := by
  let E := AlgebraicClosure F
  let f : GL (Fin 3) F →* GL (Fin 3) E := Matrix.GeneralLinearGroup.map (algebraMap F E)
  have hf : Function.Injective f := by
    intro a b h
    apply Units.ext
    ext i j
    apply (algebraMap F E).injective
    exact congrArg (fun c : GL (Fin 3) E => c i j) h
  let rho : Representation E (GL (Fin 3) F) (Fin 3 → E) := (generalLinearNatural 3).comp f
  have hrho : Function.Injective rho := (generalLinearNatural_injective 3).comp hf
  have horder' : (Nat.card A : E) ≠ 0 := by
    intro h
    apply horder
    apply (algebraMap F E).injective
    simpa using h
  apply centralizer_isMulCommutative_of_noncyclic_det_one_three rho A hrho horder'
    (by simp only [Module.finrank_pi, Fintype.card_fin]) hn
  intro a
  change LinearMap.det (Matrix.toLin' ((f a.val).val)) = 1
  rw [LinearMap.det_toLin']
  change Matrix.det ((algebraMap F E).mapMatrix a.val.val) = 1
  rw [← RingHom.map_det]
  have hd : a.val.val.det = 1 := congrArg Units.val (hdet a)
  rw [hd, map_one]

end Representation
