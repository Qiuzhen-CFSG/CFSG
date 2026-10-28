module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Definitions
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent

/-!
# A source-interface obstruction to the homocyclic placement

The current `localU` definition annotates `A ⊔ zpowers u` as a `Set G`.
Lean therefore elaborates this expression as the union of two sets. The
source instead takes the normalizer of the subgroup join A⟨u⟩.

For the literal union normalizer, an element of V must conjugate u back to
u: the other part of the union lies in L_B, whereas u is outside L_B by
noninnerness. Thus the encoded U lies in L_B ∩ C_G(u) = L. Its two-group
property and the actual binary PSL₂ model force exponent at most two,
excluding the required homocyclic group of exponent four whenever n > 0.

This is an obstruction to the local interface, not a counterexample to the
book theorem or a proof of the unitary exclusion. The original source
hypotheses may themselves be inconsistent in a minimal counterexample.
Definitions and the existing assemblies are preserved; the owning interface
needs a subgroup join before the intended construction can be connected.

Source: GLS, volume 4, Chapter 2, the displayed definitions before Lemma
13.4 and the following paragraph, `refs/KGroup/GLS4/Chapter2.tex`, lines
2397–2430; Chapter 4, Lemmas 3.4(d5) and 3.5(a).
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.Placement
open Subgroup Theory.GroupTheory
universe v
variable {G : Type v} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

omit [Finite G] in
/-- The set annotation in Definitions elaborates the join symbol as set union. -/
public theorem literal_localU_eq_union_normalizer (B : Subgroup G) :
    localU Z M B u = localV Z M B ⊓
      normalizer ((closure (Z ∩ (M : Set G)) : Set G) ∪ (zpowers u : Set G)) := rfl

omit [Finite G] in
/-- The involution inducing the noninner action lies outside the second centralizer. -/
public theorem second_involution_not_mem (d : SecondCentralizerData Z M z t u n) :
    u ∉ distinguishedCentralizer Z d.torus := by
  intro huH
  exact d.noninner ⟨u, huH, fun _ _ => rfl⟩

/-- Normalizing the literal union inside L_B forces fixation of u. -/
public theorem literal_localU_le_centralizer
    (d : SecondCentralizerData Z M z t u n) (hu : PFAppendixIII.IsInvolution u)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    localU Z M d.torus u ≤ centralizer ({u} : Set G) := by
  classical
  have hLH : residualGenerated M z t ≤ distinguishedCentralizer Z d.torus :=
    d.intersection ▸ inf_le_left
  intro g hg
  have hgH : g ∈ distinguishedCentralizer Z d.torus := ((map_subtype_le _) hg.1).2
  have hgu : g * u * g⁻¹ ∈
      (closure (Z ∩ (M : Set G)) : Set G) ∪ (zpowers u : Set G) :=
    (hg.2 u).mp (Or.inr (mem_zpowers u))
  have hnotA : g * u * g⁻¹ ∉ closure (Z ∩ (M : Set G)) := by
    intro hA
    apply second_involution_not_mem d
    have hmem := (distinguishedCentralizer Z d.torus).mul_mem
      ((distinguishedCentralizer Z d.torus).mul_mem
        ((distinguishedCentralizer Z d.torus).inv_mem hgH) (hLH (hAL hA))) hgH
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hmem
  have hpow : g * u * g⁻¹ ∈ zpowers u := hgu.resolve_left hnotA
  have horder : orderOf u = 2 := orderOf_eq_prime hu.sq_eq_one hu.ne_one
  rw [mem_zpowers_iff_mem_range_orderOf, horder] at hpow
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hpow
  have hk2 := Finset.mem_range.mp hk
  have hfix : g * u * g⁻¹ = u := by
    interval_cases k
    · have hzero : g * u * g⁻¹ = 1 := by simpa only [pow_zero] using he.symm
      have heq : MulAut.conj g u = MulAut.conj g 1 := by simpa using hzero
      exact (hu.ne_one ((MulAut.conj g).injective heq)).elim
    · simpa only [pow_one] using he.symm
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)

/-- The encoded U lies in the fixed subgroup L of the second centralizer. -/
public theorem literal_localU_le_residual
    (d : SecondCentralizerData Z M z t u n) (hu : PFAppendixIII.IsInvolution u)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t) :
    localU Z M d.torus u ≤ residualGenerated M z t := by
  rw [← d.fixed]
  exact le_inf (inf_le_left.trans ((map_subtype_le _).trans inf_le_right))
    (literal_localU_le_centralizer d hu hAL)

/-- Every element of the encoded U squares to one in the actual binary PSL₂ model. -/
public theorem literal_localU_pow_two
    (d : SecondCentralizerData Z M z t u n) (hu : PFAppendixIII.IsInvolution u)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (x : localU Z M d.torus u) : x ^ 2 = 1 := by
  let L := residualGenerated M z t
  let U := localU Z M d.torus u
  have hUL : U ≤ L := literal_localU_le_residual d hu hAL
  have hU : IsPGroup 2 U :=
    (pCore_isPGroup.map (M ⊓ distinguishedCentralizer Z d.torus).subtype).to_le inf_le_left
  let q : Converse.SL2 (PFAppendixIII.BinaryGaloisField n) ≃*
      MatrixGroups.PSL2MatrixGroup (PFAppendixIII.BinaryGaloisField n) :=
    MulEquiv.ofBijective (Converse.pi _) ⟨Converse.pi_injective, Converse.pi_surjective⟩
  let f := e.trans q.symm
  let P := U.subgroupOf L
  have hP : IsPGroup 2 P := hU.comap_subtype
  let Q := P.map f.toMonoidHom
  have hQ : IsPGroup 2 Q := hP.map f.toMonoidHom
  let y : L := ⟨x, hUL x.property⟩
  let yQ : Q := ⟨f y, ⟨y, x.property, rfl⟩⟩
  have hs := Matrix.SpecialLinearGroup.twoSubgroup_pow_two Q hQ yQ
  have he : f (y ^ 2) = f 1 := by
    simpa only [map_pow, map_one, coe_pow, coe_one] using
      congrArg (fun a : Q => (a : Converse.SL2 (PFAppendixIII.BinaryGaloisField n))) hs
  exact Subtype.ext (congrArg (fun a : L => (a : G)) (f.injective he))

/-- The encoded U cannot be a positive-rank homocyclic group of exponent four. -/
public theorem literal_localU_not_homocyclic
    (d : SecondCentralizerData Z M z t u n) (hu : PFAppendixIII.IsInvolution u)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n) (hn : 0 < n) :
    ¬ Nonempty (localU Z M d.torus u ≃* StandardHomocyclicCover (Fin n) 4) := by
  rintro ⟨f⟩
  let a : StandardHomocyclicCover (Fin n) 4 := Multiplicative.ofAdd (fun _ => 1)
  have hs : a ^ 2 = 1 := by
    have hh := congrArg f (literal_localU_pow_two d hu hAL e (f.symm a))
    simpa only [map_pow, map_one, f.apply_symm_apply] using hh
  rw [pow_two] at hs
  have hb := congrFun (congrArg Multiplicative.toAdd hs) ⟨0, hn⟩
  change (1 : ZMod 4) + 1 = 0 at hb
  exact (by decide : (1 : ZMod 4) + 1 ≠ 0) hb

/-- The requested record is incompatible with the literal union normalizer. -/
public theorem not_homocyclicLocalData_of_literal_normalizer
    (d : SecondCentralizerData Z M z t u n) (hu : PFAppendixIII.IsInvolution u)
    (hAL : closure (Z ∩ (M : Set G)) ≤ residualGenerated M z t)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n) (hn : 0 < n) :
    ¬ Nonempty (HomocyclicLocalData Z M z t u n d) := by
  rintro ⟨hd⟩
  exact literal_localU_not_homocyclic d hu hAL e hn hd.U_homocyclic

/-- The original source inputs supply the containment needed by the diagnostic.
This detects the normalizer encoding; it is not a counterexample to the book. -/
public theorem not_homocyclicLocalData_of_source_inputs
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hu : PFAppendixIII.IsInvolution u) (hn : 2 ≤ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (d : SecondCentralizerData Z M z t u n) :
    ¬ Nonempty (HomocyclicLocalData Z M z t u n d) :=
  not_homocyclicLocalData_of_literal_normalizer d hu
    (proper_residualGenerated_contains_distinguishedClosure h r ha hz hzM ht htM hL heven)
    e (by omega)

end BenderSuzuki.ZD.UnitaryExclusion.Placement
