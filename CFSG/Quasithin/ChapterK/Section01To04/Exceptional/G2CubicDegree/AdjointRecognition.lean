module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.Arithmetic
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2LowDegree


/-!
# Recognition of the G₂ adjoint at the second binary degree

The genuine tensor classification and Schur-field Frobenius descent leave
only the natural and adjoint actions below binary degree `18*r`. At degree
`14*r`, the tensor has exactly one adjoint letter. Removing its trivial
tensor factors and descending the actual intertwiner over the compatible
Schur field identifies the binary module with the split-octonion derivations.
The marking includes the field Frobenius automorphism of the group.

This does not exclude a cubic actor on the adjoint action. Its concrete
fixed-space calculation, GM04 Proposition 8.2, remains a separate input to
`G2CubicDegree.lean`. The existing natural recognition is reused.

Sources: GLS3 2.8.6–2.8.10(g); Guralnick–Malle, Classification of 2F-modules
II, Lemma 8.5, pp.55–56 of the author manuscript, used in Aschbacher–Smith
K.3, printed p.457. The exact source scope is recorded in `Source.md`.
-/

open scoped MonoidAlgebra
public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree
open Representation
open CFSG.Quasithin.ChapterG.Section09
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
open Atlas.G2 Atlas.G2.Restricted Atlas.G2.TensorClassification
attribute [local instance] ZMod.algebra

/-- The actual split-octonion derivation action restricted to the binary field. -/
@[expose] def adjointBinary (F : Type*) [Field F] [CharP F 2] :
    Representation (ZMod 2) (Atlas.G2.Model F) (Atlas.G2.Restricted.Adjoint.Space F) :=
  Representation.restrictScalars (Atlas.G2.Restricted.Adjoint.action F)

private theorem one_adjoint_of_degree_fourteen {n : ℕ} (w : Fin n → Factor)
    (hw : (∏ i, (w i).dimension) = 14) :
    ∃ i, w i = .adjoint ∧ ∀ j, j ≠ i → w j = .trivial := by
  classical
  have hd (i : Fin n) : (w i).dimension ∣ 14 := by
    rw [← hw]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hi (i : Fin n) : w i = .trivial ∨ w i = .adjoint := by
    have h := hd i
    cases hwi : w i <;> simp_all [Factor.dimension]
  have hn : ∃ i, w i = .adjoint := by
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

private theorem ofFn_one_adjoint {n : ℕ} (w : Fin n → Factor) (i : Fin n)
    (hi : w i = .adjoint) (hw : ∀ j, j ≠ i → w j = .trivial) :
    List.ofFn w = List.replicate i.val .trivial ++
      .adjoint :: List.replicate (n - i.val - 1) .trivial := by
  apply List.ext_getElem
  · simp
    omega
  · intro j hj hk
    simp only [List.getElem_ofFn]
    by_cases hji : j < i.val
    · rw [List.getElem_append_left (by simpa using hji), List.getElem_replicate]
      exact hw _ (by intro he; have hh : j = i.val := congrArg Fin.val he; omega)
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hji)]
      by_cases he : j = i.val
      · subst j
        simpa only [List.length_replicate, Nat.sub_self, List.getElem_cons_zero] using hi
      · have hpos : 0 < j - i.val := by omega
        simp only [List.length_replicate]
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        simp only [hk, List.getElem_cons_succ, List.getElem_replicate]
        exact hw _ (by intro hh; exact he (congrArg Fin.val hh))

private def tensorOneAdjointEquiv (F : Type*) [Field F] [CharP F 2] [Finite F]
    (K : Type*) [Field K] [Algebra F K] {n : ℕ} (w : Fin n → Factor) (i : Fin n)
    (hi : w i = .adjoint) (hw : ∀ j, j ≠ i → w j = .trivial) :
    (tensorRep F K w).Equiv
      (Representation.extendScalars (F := F) (V := Atlas.G2.Restricted.Adjoint.Space F) K
        ((Atlas.G2.Restricted.Adjoint.action F).comp
        (Restricted.frobeniusAutomorphism F i.val).toMonoidHom)) := by
  let T (l : List Factor) :=
    (Representation.extendScalars K (wordRep F 0 l)).Equiv
      (Representation.extendScalars (F := F) (V := Atlas.G2.Restricted.Adjoint.Space F) K
        ((Atlas.G2.Restricted.Adjoint.action F).comp
        (Restricted.frobeniusAutomorphism F i.val).toMonoidHom))
  change T (List.ofFn w)
  rw [ofFn_one_adjoint w i hi hw]
  simpa only [T, factorRep, Restricted.action, Nat.zero_add] using
    extendEquiv F K (oneFactorEquiv F 0 i.val (n - i.val - 1) .adjoint)

variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) (Atlas.G2.Model F) V) [Representation.IsIrreducible ρ]

private theorem adjoint_of_schur_tensor
    (K : Type*) [Field K]
    [Algebra (Module.End (ZMod 2)[Atlas.G2.Model F] ρ.asModule) K] [Algebra F K]
    {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hs : Representation.schurDegree 2 ρ = n) (w : Fin n → Factor)
    (e : (Representation.extendScalars K ρ.endFieldRep).Equiv (tensorRep F K w))
    (hw : (∏ i, (w i).dimension) = 14) : Quasiequivalent ρ (adjointBinary F) := by
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
  obtain ⟨i, hi, hj⟩ := one_adjoint_of_degree_fourteen w hw
  let a := Restricted.frobeniusAutomorphism F i.val
  let en := tensorOneAdjointEquiv F K w i hi hj
  have h : Nonempty ((Representation.extendScalars K τ).Equiv
      (Representation.extendScalars (F := F) (V := Atlas.G2.Restricted.Adjoint.Space F) K
        ((Atlas.G2.Restricted.Adjoint.action F).comp
        a.toMonoidHom))) := ⟨es.symm.trans (e.trans en)⟩
  obtain ⟨d⟩ := Representation.repEquiv_of_extendScalars (S := K)
    (W := Atlas.G2.Restricted.Adjoint.Space F) τ
    ((Atlas.G2.Restricted.Adjoint.action F).comp a.toMonoidHom)
    (h.map Representation.RepEquiv.ofRepresentationEquiv)
  refine ⟨a, d.toLinearEquiv.restrictScalars (ZMod 2), ?_⟩
  intro g v
  exact d.isIntertwining g v

/-- Degree `14*r` identifies the actual adjoint action, with both intertwining maps. -/
theorem adjoint_of_degree_fourteen {r : ℕ} (hr : 2 ≤ r)
    (hF : Nat.card F = 2 ^ r) (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 14 * r) :
    Quasiequivalent ρ (adjointBinary F) := by
  let E := Module.End (ZMod 2)[Model F] ρ.asModule
  let Ω := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap E Ω).injective 2
  let : Algebra (ZMod 2) Ω := ZMod.algebra Ω 2
  let ι : F →+* Ω := (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := Ω)).toRingHom
  let : Algebra F Ω := ι.toAlgebra
  let : Representation.IsAbsolutelyIrreducible ρ.endFieldRep :=
    Representation.endFieldRep_isAbsolutelyIrreducible ρ
  let : Representation.IsIrreducible (Representation.extendScalars Ω ρ.endFieldRep) :=
    Representation.IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep Ω
  obtain ⟨w, ⟨e⟩⟩ := exists_tensorRep_equiv hF
    (Representation.extendScalars Ω ρ.endFieldRep) inferInstance
  obtain ⟨hs, t, l, ht, _, hrt, hdim, hne, hb⟩ :=
    Nonbinary.parameters_of_tensor_equiv ρ Ω (by omega) hF w e hf
  obtain ⟨hsr, _, _⟩ := parameters_below_eighteen l hs ht hb hne hrt hdim
    (by omega : Module.finrank (ZMod 2) V < 18 * r)
  apply adjoint_of_schur_tensor ρ Ω hF hsr w e
  have hdim' := Representation.finrank_eq_schurDegree_mul 2 ρ Ω
  rw [e.toLinearEquiv.finrank_eq, finrank_tensorSpace, hsr, hd] at hdim'
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < r)
  simpa only [Nat.mul_comm r 14] using hdim'.symm

/-- The first two binary degrees are recognized; every remaining module has degree at least `18*r`. -/
theorem natural_or_adjoint_or_large {r : ℕ} (hr : 2 ≤ r)
    (hF : Nat.card F = 2 ^ r) (hf : Function.Injective ρ) :
    Quasiequivalent ρ (naturalBinary F) ∨ Quasiequivalent ρ (adjointBinary F) ∨
      18 * r ≤ Module.finrank (ZMod 2) V := by
  by_cases hlarge : 18 * r ≤ Module.finrank (ZMod 2) V
  · exact Or.inr (Or.inr hlarge)
  obtain ⟨hs, t, l, ht, _, hperiod, hd, hne, hb, hn⟩ :=
    Nonbinary.exists_basic_parameters_and_natural ρ hr hF hf
  obtain ⟨hsr, ht1, hprod⟩ := parameters_below_eighteen l hs ht hb hne hperiod hd
    (by omega)
  rcases hprod with hp6 | hp14
  · exact Or.inl (hn ht1 hp6)
  · right; left
    apply adjoint_of_degree_fourteen ρ hr hF hf
    rw [hsr, ht1, pow_one, hp14] at hd
    simpa only [Nat.mul_comm] using hd

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree
