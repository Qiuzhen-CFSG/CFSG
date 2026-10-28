module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Reduction
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.LinearAlgebra.SpecialLinearDeterminantKernel
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition.ProjectiveResidual
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Cyclic abelianizations of PSL₃ involution centralizers

The determinant kernel in GL₂ is the perfect group SL₂ when the field has
more than three elements. Thus its abelianization embeds in the cyclic
multiplicative group of the field. The block centralizer isomorphism gives
the SL₃ assertion, and the actual scalar quotient maps this centralizer
onto the centralizer of the projective involution. Surjectivity transfers
cyclic abelianization. Finally an actual model equivalence transfers the
result to Q. No position of a Sylow complement is assumed or concluded.

Source: Aschbacher–Smith, A.3.21(a), printed p.55, and the split case in the
proof of Proposition 1.3.4, printed p.511 (PDF p.528 of refs/quasithin.pdf).
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial

private theorem cyclic_abelianization_of_perfect_kernel
    {G A : Type*} [Group G] [CommGroup A] [IsCyclic A]
    (f : G →* A) [Group.IsPerfect f.ker] : IsCyclic (Abelianization G) := by
  have hker : f.ker ≤ commutator G := by
    have h := f.ker.map_subtype_commutator
    rw [Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
    exact h.le.trans (commutator_mono le_top le_top)
  apply isCyclic_of_injective (Abelianization.lift f)
  exact (QuotientGroup.injective_lift_iff _ _ (Abelianization.commutator_subset_ker f)).mpr
    (le_antisymm (Abelianization.commutator_subset_ker f) hker)

private theorem cyclic_abelianization_of_surjective
    {G H : Type*} [Group G] [Group H] [IsCyclic (Abelianization G)]
    (f : G →* H) (hf : Function.Surjective f) : IsCyclic (Abelianization H) := by
  apply isCyclic_of_surjective (Abelianization.map f)
  rintro ⟨y⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Abelianization.of x, rfl⟩

private theorem gl2_cyclic_abelianization (F : Type*) [Field F] [Finite F]
    (hF : 3 < Nat.card F) : IsCyclic (Abelianization (GL (Fin 2) F)) := by
  let _ := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hF
  let e := Matrix.SpecialLinearGroup.determinantKernelEquiv (Fin 2) F
  let _ : Group.IsPerfect (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F)).ker :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact cyclic_abelianization_of_perfect_kernel (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := F))

private theorem sl3_cyclic_abelianization (F : Type*) [Field F] [Finite F]
    (hF : 3 < Nat.card F) (h2 : (2 : F) ≠ 0)
    (z : Matrix.SpecialLinearGroup (Fin 3) F) (hz : orderOf z = 2) :
    IsCyclic (Abelianization (centralizer ({z} : Set (Matrix.SpecialLinearGroup (Fin 3) F)))) := by
  let _ := gl2_cyclic_abelianization F hF
  exact (Matrix.SL3.involutionCentralizerEquiv F z hz h2).abelianizationCongr.isCyclic.mpr inferInstance

open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan

private theorem psl3_cyclic_abelianization (F : Type*) [Field F] [Finite F]
    (hF : 3 < Nat.card F) (h2 : (2 : F) ≠ 0)
    (z : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) (hz : orderOf z = 2) :
    IsCyclic (Abelianization (centralizer ({z} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)))) := by
  obtain ⟨w, hw, hw2⟩ := psl3_involution_lift F z hz
  let C := centralizer ({w} : Set (Matrix.SpecialLinearGroup (Fin 3) F))
  let D := centralizer ({z} : Set (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F))
  let f := Matrix.PSL3.projection F
  have hCD : D.comap f = C := by
    dsimp only [D, f]
    rw [← hw]
    exact sl3_comap_projective_involution_centralizer F w hw2
  let c : C →* D := f.restrict (by rw [← hCD]; exact fun _ h => h)
  have hc : Function.Surjective c := by
    intro x
    obtain ⟨y, hy⟩ := Matrix.PSL3.projection_surjective F x
    have hyC : y ∈ C := by rw [← hCD]; change f y ∈ D; rw [hy]; exact x.property
    exact ⟨⟨y, hyC⟩, Subtype.ext hy⟩
  let _ : IsCyclic (Abelianization C) := sl3_cyclic_abelianization F hF h2 w hw2
  exact cyclic_abelianization_of_surjective c hc

private noncomputable def centralizerEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (z : G) : centralizer ({z} : Set G) ≃* centralizer ({e z} : Set H) where
  toFun x := ⟨e x, mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp x.property))⟩
  invFun y := ⟨e.symm y, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp y.property)⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (e.map_mul x y)

/-- Every involution centralizer in an actual PSL₃(p), for p > 3, has cyclic
abelianization. This does not assert that the complement lies in it. -/
theorem involutionCentralizer_abelianization_isCyclic {Q : Type*} [Group Q]
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hm : ClassicalGroup.IsPSL Q 3 p) (z : Q) (hz : orderOf z = 2) :
    IsCyclic (Abelianization (centralizer ({z} : Set Q))) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fintype F := Fintype.ofFinite F
  let _ : CharP F p := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have h2 : (2 : F) ≠ 0 := by
    exact CharP.cast_ne_zero_of_ne_of_prime F (p := p) (q := 2) Nat.prime_two
      (ne_of_gt (lt_trans (by decide : 2 < 3) hlarge))
  let _ := psl3_cyclic_abelianization F (by omega) h2 (e z) ((e.orderOf_eq z).trans hz)
  exact (centralizerEquiv e z).abelianizationCongr.isCyclic.mpr inferInstance

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial
