module

public import Theory.Representation.G2.TensorClassification
public import Theory.Representation.SL3.BinaryFieldDescent
public import Theory.Representation.SL3.BinaryFieldDescent.Fields
public import Theory.Representation.ScalarDescent
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Models
public import CFSG.Quasithin.ChapterG.Section09.Setup
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary.PeriodDescent

/-!
# Tensor parameters and natural-action descent for G₂

The actual tensor-model intertwiner transports the Frobenius period to the
Schur representation. The periodic-word product formula then gives the binary
block parameters. Faithfulness excludes the all-trivial tensor: identity
actions descend through the tensor embedding and the Schur carrier, whereas
the actual root group contains a nonidentity element.

A degree-six tensor has precisely one natural letter. Its tensor-unit
intertwiners identify it with the scalar extension of the trace-zero octonion
quotient, twisted by a field automorphism of the actual group. When the Schur
field and defining field have the same cardinality, compatible embeddings
identify them. Scalar transport and Noether--Deuring descend this genuine
intertwiner and binary restriction gives quasiequivalence. Dimension is used
to locate the letter, not to identify two arbitrary representations.

Source: GLS3, 2.8.6, Remark 2.8.8 and 2.8.10(g); Aschbacher--Smith,
G.9.3(10), printed pp.354,356--357. The unconditional assembly is in
`FrobeniusParameters.lean`.
-/

open scoped MonoidAlgebra TensorProduct
public noncomputable section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary
open Atlas.G2 Atlas.G2.Restricted Atlas.G2.TensorClassification
attribute [local instance] ZMod.algebra
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) (Atlas.G2.Model F) V) [Representation.IsIrreducible ρ]
  (K : Type*) [Field K] [IsAlgClosed K] [CharP K 2]
  [Algebra (Module.End (ZMod 2)[Atlas.G2.Model F] ρ.asModule) K] [Algebra F K]

omit [IsAlgClosed K] [CharP K 2] in
private theorem tensor_nontrivial_of_faithful {n : ℕ} (w : Fin n → Factor)
    (e : (Representation.extendScalars K ρ.endFieldRep).Equiv (tensorRep F K w))
    (hρ : Function.Injective ρ) :
    tensorRep F K w ≠ Representation.trivial K (Model F) (TensorSpace F K w) := by
  intro h
  have hfix (g : Model F) (v : V) : ρ g v = v := by
    apply ρ.asModuleEquiv.symm.injective
    apply (Module.FaithfullyFlat.tensorProduct_mk_injective
      (A := Module.End (ZMod 2)[Model F] ρ.asModule) (B := K) ρ.asModule)
    apply e.toLinearEquiv.injective
    have hh := LinearMap.congr_fun (e.isIntertwining' g)
      ((1 : K) ⊗ₜ[Module.End (ZMod 2)[Model F] ρ.asModule] ρ.asModuleEquiv.symm v)
    have haction : tensorRep F K w g = 1 := congrArg (fun σ => σ g) h
    simp only [LinearMap.comp_apply, haction, Module.End.one_apply] at hh
    simpa only [LinearMap.comp_apply, Representation.extendScalars_apply,
      LinearMap.baseChange_tmul, Representation.endFieldRep_apply,
      LinearEquiv.apply_symm_apply, Representation.Equiv.toLinearEquiv_apply,
      Representation.IntertwiningMap.toLinearMap_apply, TensorProduct.mk_apply] using hh
  have hg (g : Model F) : g = 1 := hρ (by
    ext v
    rw [hfix, map_one, Module.End.one_apply])
  exact one_ne_zero (rootA_injective ((hg (rootA (1 : F))).trans rootA_zero.symm))

private theorem degree_product_range {n : ℕ} (hn : 0 < n) (w : Fin n → Factor) :
    (∏ i ∈ Finset.range n, (periodicWord hn w i).dimension) = ∏ i, (w i).dimension := by
  rw [← Fin.prod_univ_eq_prod_range]
  apply Finset.prod_congr rfl
  intro i hi
  simp only [periodicWord, Nat.mod_eq_of_lt i.isLt]

/-- A genuine tensor-model equivalence supplies every premise of the
Schur-period descent, including exclusion of the all-trivial word. -/
theorem parameters_of_tensor_equiv {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (w : Fin n → Factor)
    (e : (Representation.extendScalars K ρ.endFieldRep).Equiv (tensorRep F K w))
    (hρ : Function.Injective ρ) :
    let s := Representation.schurDegree 2 ρ
    0 < s ∧ ∃ (t : ℕ) (l : List ℕ), 0 < t ∧ l.length = s ∧ n = s * t ∧
      Module.finrank (ZMod 2) V = s * l.prod ^ t ∧ l.prod ≠ 1 ∧
        ∀ a ∈ l, a = 1 ∨ a = 6 ∨ a = 14 ∨ a = 64 := by
  apply parameters_of_periodic_word ρ K n hn (fun i => (periodicWord hn w i).dimension)
  · intro i
    rw [periodicWord_period]
  · exact tensorModel_frobenius_equiv_iff_degree_period F K hF hn w e
  · rw [e.toLinearEquiv.finrank_eq, finrank_tensorSpace, degree_product_range]
  · intro i hi
    cases periodicWord hn w i <;> simp [Factor.dimension]
  · rw [degree_product_range]
    exact tensorDegree_ne_one_of_nontrivial F K hF w
      (tensor_nontrivial_of_faithful ρ K w e hρ)

private theorem one_natural_of_degree_six {n : ℕ} (w : Fin n → Factor)
    (hw : (∏ i, (w i).dimension) = 6) :
    ∃ i, w i = .natural ∧ ∀ j, j ≠ i → w j = .trivial := by
  classical
  have hd (i : Fin n) : (w i).dimension ∣ 6 := by
    rw [← hw]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hi (i : Fin n) : w i = .trivial ∨ w i = .natural := by
    have h := hd i
    cases hwi : w i <;> simp_all [Factor.dimension]
  have hn : ∃ i, w i = .natural := by
    by_contra! h
    have ht : ∀ i, w i = .trivial := fun i => (hi i).resolve_right (h i)
    have hh := (tensorDegree_eq_one_iff w).mpr ht
    omega
  obtain ⟨i, hwi⟩ := hn
  refine ⟨i, hwi, ?_⟩
  have he : (∏ j ∈ Finset.univ.erase i, (w j).dimension) = 1 := by
    have h := Finset.prod_erase_mul (s := Finset.univ) (f := fun j => (w j).dimension)
      (Finset.mem_univ i)
    rw [hwi, Factor.dimension, hw] at h
    omega
  intro j hji
  have hj : (w j).dimension ∣ 1 := by
    rw [← he]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  cases hwj : w j <;> simp_all [Factor.dimension]

omit [IsAlgClosed K] [CharP K 2] in
/-- A degree-six tensor descends to the actual binary natural action when
the Schur degree is the defining-field degree. The proof retains the natural
factor's intertwiner and its actual group-field automorphism. -/
theorem natural_of_schur_tensor {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hs : Representation.schurDegree 2 ρ = n) (w : Fin n → Factor)
    (e : (Representation.extendScalars K ρ.endFieldRep).Equiv (tensorRep F K w))
    (hw : (∏ i, (w i).dimension) = 6) : Quasiequivalent ρ (naturalBinary F) := by
  let E := Module.End (ZMod 2)[Model F] ρ.asModule
  have hcard : Nat.card F = Nat.card E := by
    let : Module.Finite (ZMod 2) E := Module.Finite.of_finite
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E), Nat.card_zmod]
    exact hF.trans (congrArg (2 ^ ·) hs).symm
  obtain ⟨c, hc⟩ := FiniteField.exists_compatible_equiv_of_card_eq
    (algebraMap E K) (algebraMap F K) hcard
  let := Representation.BinaryFieldDescent.scalarModule ρ c
  let : Finite V := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) V)
  let : Module.Finite F V := Module.Finite.of_finite
  let τ := Representation.BinaryFieldDescent.scalarRep ρ c
  let es := Representation.BinaryFieldDescent.scalarExtensionEquiv ρ c hc
  obtain ⟨i, hi, hj⟩ := one_natural_of_degree_six w hw
  let a := Restricted.frobeniusAutomorphism F i.val
  let en := tensorOneNaturalEquiv F K w i hi hj
  have h : Nonempty ((Representation.extendScalars K τ).Equiv
      (Representation.extendScalars K ((Atlas.G2.Natural.action F).comp a.toMonoidHom))) :=
    ⟨es.symm.trans (e.trans en)⟩
  obtain ⟨d⟩ := Representation.repEquiv_of_extendScalars τ
    ((Atlas.G2.Natural.action F).comp a.toMonoidHom)
    (h.map Representation.RepEquiv.ofRepresentationEquiv)
  refine ⟨a, d.toLinearEquiv.restrictScalars (ZMod 2), ?_⟩
  intro g v
  exact d.isIntertwining g v

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.Nonbinary
