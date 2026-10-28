module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryModule
public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.NaturalCoordinates.Marking
public import Theory.Representation.BinaryConjugationSection.ElementaryFactors
public import Theory.GroupTheory.QuaternionCentralProductInvolutionGeneration

/-!
# The elementary factors in the original rank-two parabolic

Apply the invariant-plane construction to the literal section O₂(I₂)/E
and its actual source 12.8.9 conjugation representation. The equality E=V
and the parabolic centralizer identity give the central elementary kernel.
The marked W-image and involution generation construct both factors, and
the original two-core commutator gives their normalization by I₂ Q.

This proves the elementary factor part of Aschbacher–Smith 14.3.18(4),
printed p.996. The source 14.3.15 orthogonal calculation must still supply
E=V, the two-dimensional fixed mark and involution generation of W.
The subsequent t-swap, maximality and A₆ recognition are not asserted here.
-/

public section
open Subgroup InvertedCubicTensor

namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource
open Chapter12.Section08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}
  [IsElementaryAbelian 2 V]

omit [IsElementaryAbelian 2 V] in
/-- The original W inherits involution generation from its actual
noncentral involution-centralizer description inside U. -/
theorem block_W_involution_generated (F : InvariantFlag T V 2)
    (dU : QuaternionCentralProductData F.U) (t : F.U) (ht : orderOf t = 2)
    (hnc : t ∉ center F.U)
    (hW : F.W = (centralizer ({t} : Set F.U)).map F.U.subtype) :
    closure {x : F.W | x ^ 2 = 1} = ⊤ :=
  QuaternionCentralProductData.ambient_involution_centralizer_generated
    F.U F.W dU t ht hnc hW

theorem block_elementary_factors
    (F : InvariantFlag T V 2) (L : Subgroup G) (g : G)
    (e : ((F.I₂ L) ⧸ pCore 2 (F.I₂ L)) ≃* S₃)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) S₃ W)
    (d : Representation.BinaryConjugationSection (F.I₂ L) ((F.I₂ L).pCoreIn 2)
      (F.E g) (σ.comp (F.binaryCoreProjection L e)))
    (hE : F.E g = V)
    (hcore : F.I₂ L ⊓ centralizer (F.Vi 2 : Set G) = (F.I₂ L).pCoreIn 2)
    (hW : F.W ≤ (F.I₂ L).pCoreIn 2)
    (hmark : d.imageSpace F.W = multiplicitySpace σ)
    (hfree : ∀ w, σ cubic w = w → w = 0)
    (hdim : Module.finrank (ZMod 2) (multiplicitySpace σ) = 2)
    (hgen : closure {x : F.W | x ^ 2 = 1} = ⊤)
    (hQ : ⁅(F.I₂ L).pCoreIn 2, (F.H).pCoreIn 2⁆ ≤ F.E g) :
    ∃ A B : Subgroup G,
      A ≤ (F.I₂ L).pCoreIn 2 ∧ B ≤ (F.I₂ L).pCoreIn 2 ∧ V ≤ A ∧ V ≤ B ∧
      IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
      Nat.card A = 16 ∧ Nat.card B = 16 ∧
      A ⊓ B = V ∧ A ⊔ B = (F.I₂ L).pCoreIn 2 ∧
      Nat.card ((F.I₂ L).pCoreIn 2) = 64 ∧
      F.I₂ L ⊔ (F.H).pCoreIn 2 ≤ normalizer (A : Set G) ∧
      F.I₂ L ⊔ (F.H).pCoreIn 2 ≤ normalizer (B : Set G) := by
  have hc : Nat.card (F.E g) = 4 := by
    rw [hE]
    simpa only [F.last,show (2 : ℕ)^2 = 4 by decide] using F.card 2 le_rfl
  have hcentral : F.E g ≤ centralizer (((F.I₂ L).pCoreIn 2) : Set G) := by
    intro v hv r hr
    have hh := (hcore.ge hr).2
    exact (hh v (F.last.symm ▸ (hE ▸ hv))).symm
  have hsquare : ∀ v ∈ F.E g, v ^ 2 = 1 := by
    intro v hv
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) v (hE ▸ hv)
  obtain ⟨A,B,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hs,hRc,hAN,hBN,hN⟩ :=
    d.exists_elementary_factors σ (F.binaryCoreProjection L e) F.W hW hmark
      (by
        intro s
        obtain ⟨i,hi⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.I₂ L)) (e.symm s)
        exact ⟨i,by rw [F.binaryCoreProjection_apply,hi,e.apply_symm_apply]⟩)
      hfree hdim hgen hc hcentral hsquare
  rw [hE] at hVA hVB hi
  exact ⟨A,B,hAR,hBR,hVA,hVB,hEA,hEB,hAc,hBc,hi,hs,hRc,
    sup_le hAN (hN _ hQ).1,sup_le hBN (hN _ hQ).2⟩

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource
