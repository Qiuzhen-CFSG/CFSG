module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration.Residual
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration.Quotient
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration.RankTwo
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryModule

/-!
# Binary minimal-parabolic generation and its marked quotient

This proves the generation, embedded residual, relative normality, core,
index and actual S₃ quotient family of 12.8.9(1). The original g∈P−H
and right-conjugated subgroups are retained throughout. The quotient
comparison has the literal conjugation equation on its representatives.
The source's displayed H-span is corrected to the G₂-span established
by its proof, since H already normalizes U.

The exact earlier 12.8.3–8 inputs stay explicit: elementary V, the full
LT action, its two-core kernel, the commutator and square bounds, the
plane H-span and nonabelianness. The setup and preliminary owners supply
these to the parent final 12.8.9–10 assembly. No conclusion of 12.8.9 is
an input to the terminal theorems here. The rank-two adapter derives the
full LT action from that alternative's original S₃ quotient.

The final consumers discharge every 12.8.9(1) premise in the existing
binary core, intersection-commutator and natural-quotient proofs, yielding
the literal S/E representation and fixed/moved-space marks of (2–3).
Center calculations and earlier-source discharge remain with their owners.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.9, printed pp.852–853 (PDF pp.869–870), refs/quasithin.pdf.
-/

public section

open Subgroup
open scoped IsMulCommutative Pointwise _root_.TensorProduct
open InvertedCubicTensor
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The genuine generation, residual normality and marked quotient family
in 12.8.9(1), with preceding 12.8.3–8 source inputs explicit. -/
theorem binary_generation (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
    (hn : 2 ≤ n) (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hkernel : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* Equiv.Perm (Fin 3),
      F.I₂ L = (pResidual 2 (F.P L)).map (F.P L).subtype ⊔ F.U ∧
      F.I₂ L = F.U ⊔ conjugate F.U g ∧
      F.I₂ L = conjugateSpanBy F.U (F.Gi 2) ∧
      F.I₂ L ≤ F.Gi 2 ∧ ((F.I₂ L).subgroupOf (F.Gi 2)).Normal ∧
      (pResidual 2 (F.P L)).map (F.P L).subtype ≤ F.Gi 2 ∧
      (((pResidual 2 (F.P L)).map (F.P L).subtype).subgroupOf (F.Gi 2)).Normal ∧
      F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L ∧ (F.P L).pCoreIn 2 ≤ F.H ∧
      F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2 ∧
      F.W.relIndex F.U = 2 ∧
      ∀ (x : F.I₂ L) (v : F.Vi 2),
        ((F.binaryPlaneLabel hn).symm (e (QuotientGroup.mk x)) v : G) =
          (x : G) * (v : G) * (x : G)⁻¹ := by
  obtain ⟨hgen,hfactor⟩ := F.binary_two_conjugate_generation hn L hL hfull hkernel
    hsquare hspan hne g hgP hgH
  obtain ⟨hGspan,hIG,hIN⟩ := F.binary_parabolic_span_normality hn L hL hfull hcomm
  obtain ⟨hcore,e,he⟩ := F.binary_I₂_quotient hn L hL hfull hkernel hfactor
  refine ⟨e, (F.binary_residual_supplement (by omega) L hsquare hfactor).1,
    hgen.symm,hGspan,hIG,hIN,?_,?_,hfactor,?_,hcore,?_,he⟩
  · exact (le_sup_left.trans (F.binary_residual_supplement (by omega) L hsquare hfactor).1.ge).trans hIG
  · exact F.binary_residual_normal_in_G₂ (by omega) L hsquare hfactor hIG hIN
  · exact (F.binary_parabolic_core hn L hL hfull hkernel).2
  · exact F.binary_U_action_index hn L hL hsquare hspan hne

/-- The new source generation and quotient results discharge the earlier
12.8.9(1) premises of both binary core and intersection consumers. -/
theorem binary_source_core_and_intersection (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hkernel : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (F.I₂ L).pCoreIn 2 = F.W ⊔ F.X g ∧ ⁅F.E g, F.I₂ L⁆ = F.Vi 2 := by
  obtain ⟨e,_,hgen,_,_,_,_,_,hfactor,hPH,hcore,hindex,_⟩ :=
    F.binary_generation hn L hL hfull hkernel hcomm hsquare hspan hne g hgP hgH
  exact ⟨F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hcore hindex,
    F.binary_intersection_commutator hn L hL g hgP hgH hgen.symm hcomm hindex⟩

/-- The literal natural quotient and all three fixed/moved-space marks in
12.8.9(2–3), now with the generation premises proved from earlier source data.
The existential proofs expose the exact normality and elementarity instances
used to form S/E; none is an added hypothesis. -/
theorem binary_source_natural_quotient (F : InvariantFlag T V n)
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hfull : Function.Surjective (F.binarySeedAction L hL))
    (hkernel : (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃)
      (hfactor : F.P L = (F.P L).pCoreIn 2 ⊔ F.I₂ L)
      (hPH : (F.P L).pCoreIn 2 ≤ F.H)
      (hgen : F.U ⊔ conjugate F.U g = F.I₂ L)
      (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
      (hindex : F.W.relIndex F.U = 2),
      (∀ (x : F.I₂ L) (v : F.Vi 2),
        ((F.binaryPlaneLabel hn).symm (e (QuotientGroup.mk x)) v : G) =
          (x : G) * (v : G) * (x : G)⁻¹) ∧
    letI := F.binary_source_E_normal_in_core L hL g hgP hgen hcomm
    letI := F.binary_source_quotient_elementary L hL g hgP hgen hcore
      (F.binary_core_normalizes_U L hfactor hPH)
      (F.binary_core_factorization L g hgP hfactor hPH hgen e hcore hindex) hcomm hsquare
    ∃ (σ : Representation (ZMod 2) S₃
        (Additive (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2))))
      (d : Representation.BinaryConjugationSection (F.I₂ L) ((F.I₂ L).pCoreIn 2)
        (F.E g) (σ.comp (F.binaryCoreProjection L e))),
      (∀ s : (F.I₂ L).pCoreIn 2, (d.coordinates s).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) s)) ∧
      Finite (multiplicitySpace σ) ∧
      (∃ j : multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2]
            Additive (((F.I₂ L).pCoreIn 2) ⧸ (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)),
          ∀ a z, j ((Representation.tprod (Representation.trivial (ZMod 2) S₃
              (multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a z) =
            σ a (j z)) ∧
      ∀ u : F.I₂ L, (u : G) ∈ F.U → (u : G) ∉ F.W →
          LinearMap.ker (σ (F.binaryCoreProjection L e u) - 1) = d.imageSpace F.W ∧
          LinearMap.range (σ (F.binaryCoreProjection L e u) - 1) = d.imageSpace F.W ∧
          (d.imageSpace (F.X g)).map (σ (F.binaryCoreProjection L e u) - 1) =
            d.imageSpace F.W := by
  obtain ⟨e,_,hgen,_,_,_,_,_,hfactor,hPH,hcore,hindex,heval⟩ :=
    F.binary_generation hn L hL hfull hkernel hcomm hsquare hspan hne g hgP hgH
  exact ⟨e,hfactor,hPH,hgen.symm,hcore,hindex,heval,
    F.binary_natural_quotient L hL g hgP hfactor hPH hgen.symm e hcore hindex hcomm hsquare⟩

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
