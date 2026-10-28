module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.CharP.CharAndCard


/-!
# Simultaneous eigenbases from a split unitary spectrum

An odd-order group operator in characteristic two is annihilated by the
separable polynomial `X^|H| - 1`. If its characteristic polynomial splits over
the coefficient field, its squarefree minimal polynomial is a product of
distinct linear factors. The coprime kernel decomposition then shows that its
eigenspaces span. For an abelian group, simultaneous eigenspaces therefore
supply a basis over that same field, including all repeated-weight cases.

The final application retains the actual special-unitary matrices and their
projective basis lines. A separate bridge extracts anisotropic scalar-action
data from a common eigenline using the source no-Borel hypothesis.

This module does not establish splitting from reducibility. That descent is
the remaining input to GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603.
-/

public section

open Polynomial
open scoped IsMulCommutative LinearAlgebra.Projectivization
namespace UnitaryThree.OddTorusNormalizer.AbelianFrame

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

private theorem ker_split_product (f : Module.End E V) (s : Finset E) :
    LinearMap.ker (aeval f (∏ a ∈ s, (X - C a))) =
      ⨆ a ∈ s, f.eigenspace a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Module.End.one_eq_id]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, ← sup_ker_aeval_eq_ker_aeval_mul_of_coprime]
    · simp only [aeval_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one,
        ← Module.End.eigenspace_def, ih]
      simp only [Finset.mem_insert, iSup_or, iSup_sup_eq, iSup_iSup_eq_left]
    · apply IsCoprime.prod_right
      intro b hb
      exact isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr (ne_of_mem_of_not_mem hb ha).symm).isUnit

private theorem eigenspaces_span_of_split [Finite E] [FiniteDimensional E V]
    (f : Module.End E V) (hf : f.IsSemisimple) (hs : f.charpoly.Splits) :
    (⨆ a, f.eigenspace a) = ⊤ := by
  classical
  have hm : (minpoly E f).Splits :=
    hs.of_dvd (LinearMap.charpoly_monic f).ne_zero (LinearMap.minpoly_dvd_charpoly f)
  have hsep : (minpoly E f).Separable :=
    PerfectField.separable_iff_squarefree.mpr hf.minpoly_squarefree
  let s : Finset E := ⟨(minpoly E f).roots, Polynomial.nodup_roots hsep⟩
  have hp : (∏ a ∈ s, (X - C a)) = minpoly E f := by
    exact (hm.eq_prod_roots_of_monic (minpoly.monic (Algebra.IsIntegral.isIntegral f))).symm
  apply top_unique
  calc
    (⊤ : Submodule E V) = LinearMap.ker (aeval f (∏ a ∈ s, (X - C a))) := by
      rw [hp, minpoly.aeval, LinearMap.ker_zero]
    _ = ⨆ a ∈ s, f.eigenspace a := ker_split_product f s
    _ ≤ ⨆ a, f.eigenspace a := iSup_le fun a => iSup_le fun _ => le_iSup _ a

private theorem simultaneous_eigenbasis [Finite E] [FiniteDimensional E V]
    {G : Type*} [Group G] [IsMulCommutative G]
    (ρ : Representation E G V) (horder : (Nat.card G : E) ≠ 0)
    (hsplit : ∀ g, (ρ g).charpoly.Splits) :
    ∃ (b : Module.Basis (Fin (Module.finrank E V)) E V)
      (μ : Fin (Module.finrank E V) → G → E),
      ∀ i g, ρ g (b i) = μ i g • b i := by
  classical
  have hsemi (g : G) : Module.End.IsSemisimple (ρ g) := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := (X : E[X]) ^ Nat.card G - 1)
    · exact (X_pow_sub_one_separable_iff.mpr horder).squarefree
    · have hpow : ρ g ^ Nat.card G = 1 := by
        rw [← map_pow, pow_card_eq_one', map_one]
      simp [hpow]
  have hcomm (g h : G) : Commute (ρ g) (ρ h) := by
    change ρ g * ρ h = ρ h * ρ g
    rw [← map_mul, ← map_mul, mul_comm]
  have hmaps (g h : G) (a : E) : Set.MapsTo (ρ g)
      (Module.End.maxGenEigenspace (ρ h) a) (Module.End.maxGenEigenspace (ρ h) a) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm h g) a
  have heq (g : G) (a : E) :
      Module.End.maxGenEigenspace (ρ g) a = Module.End.eigenspace (ρ g) a :=
    (hsemi g).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace a
  have hind : iSupIndep (fun w : G → E => ⨅ g, Module.End.eigenspace (ρ g) (w g)) := by
    simpa only [heq] using
      Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo ρ hmaps
  have htop : (⨆ w : G → E, ⨅ g, Module.End.eigenspace (ρ g) (w g)) = ⊤ := by
    have hsingle (g : G) : (⨆ a, Module.End.maxGenEigenspace (ρ g) a) = ⊤ := by
      simpa only [heq] using eigenspaces_span_of_split (ρ g) (hsemi g) (hsplit g)
    simpa only [heq] using
      Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo ρ hmaps hsingle
  let hd := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let I := (w : G → E) × Fin (Module.finrank E ↥(⨅ g, Module.End.eigenspace (ρ g) (w g)))
  let b : Module.Basis I E V := hd.collectedBasis fun w =>
    Module.finBasis E ↥(⨅ g, Module.End.eigenspace (ρ g) (w g))
  let : Fintype I := FiniteDimensional.fintypeBasisIndex b
  let e : I ≃ Fin (Module.finrank E V) :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  refine ⟨b.reindex e, fun i => (e.symm i).1, ?_⟩
  intro i g
  have hb := hd.collectedBasis_mem
    (fun w => Module.finBasis E ↥(⨅ g, Module.End.eigenspace (ρ g) (w g))) (e.symm i)
  have hb' : ∀ g, b (e.symm i) ∈ Module.End.eigenspace (ρ g) ((e.symm i).1 g) := by
    simpa only [Submodule.mem_iInf] using hb
  have he := Module.End.mem_eigenspace_iff.mp (hb' g)
  simpa only [Module.Basis.reindex_apply] using he

open BenderSuzuki.MatrixGroups

/-- A basis of actual simultaneous eigenvectors fixes its projective lines. -/
theorem isCommonEigenbasis_of_eigenvectors (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (b : Module.Basis (Fin 3) E (Fin 3 → E))
    (μ : Fin 3 → H → E)
    (hb : ∀ i h, specialNatural J h.val (b i) = μ i h • b i) :
    IsCommonEigenbasis J H b := by
  intro i h hh
  change h.val • Projectivization.mk E (b i) (b.ne_zero i) =
    Projectivization.mk E (b i) (b.ne_zero i)
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  refine ⟨μ i ⟨h, hh⟩, ?_⟩
  exact (hb i ⟨h, hh⟩).symm

/-- The no-Borel hypothesis makes the representative of a common eigenline
anisotropic, and the literal matrices act on that representative by scalars. -/
theorem commonEigenline_rep_spectral_data (J : HermitianForm 3 E)
    (H : Subgroup J.specialSubgroup) (hB : SpecialNoBorel J H)
    {l : ℙ E (Fin 3 → E)} (hl : l ∈ commonEigenlines J H) :
    dotProduct (fun i => J.conj (l.rep i)) (J.form.mulVec l.rep) ≠ 0 ∧
      ∀ h : H, ∃ a : E, specialNatural J h.val l.rep = a • l.rep := by
  constructor
  · intro hzero
    exact commonEigenline_not_isotropic J H hB hl
      ⟨l.rep, l.rep_nonzero, (Projectivization.mk_rep l).symm, hzero⟩
  · intro h
    have hh : h.val.val • l = l := hl h.property
    rw [← Projectivization.mk_rep l, Projectivization.smul_mk,
      Projectivization.mk_eq_mk_iff'] at hh
    obtain ⟨a, ha⟩ := hh
    exact ⟨a, ha.symm⟩

/-- Odd abelian special-unitary actions with split characteristic polynomials
have an actual simultaneous eigenbasis over the original coefficient field. -/
theorem exists_commonEigenbasis_of_split_charpolys [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hcard : Nat.card E = (2 ^ n) ^ 2)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H)) [IsMulCommutative H]
    (hsplit : ∀ h : H, (specialNatural J h.val).charpoly.Splits) :
    ∃ b : Module.Basis (Fin 3) E (Fin 3 → E), IsCommonEigenbasis J H b := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have horder : (Nat.card H : E) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff E 2]
    exact hodd.not_two_dvd_nat
  obtain ⟨b, μ, hb⟩ := simultaneous_eigenbasis ((specialNatural J).comp H.subtype)
    horder hsplit
  have hd : Module.finrank E (Fin 3 → E) = 3 := by simp
  let e : Fin (Module.finrank E (Fin 3 → E)) ≃ Fin 3 := finCongr hd
  refine ⟨b.reindex e, isCommonEigenbasis_of_eigenvectors J H (b.reindex e)
    (fun i => μ (e.symm i)) ?_⟩
  intro i h
  simpa only [Module.Basis.reindex_apply, MonoidHom.comp_apply, Subgroup.subtype_apply]
    using hb (e.symm i) h

end UnitaryThree.OddTorusNormalizer.AbelianFrame
