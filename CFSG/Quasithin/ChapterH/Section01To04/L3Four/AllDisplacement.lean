module
public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.Displacement
public import Theory.Representation.SL3.BinaryDefiningFactors.CubicTensorRank

/-!
# Involution displacement including the nine-dimensional modules

The natural cubic eigenbases give rank six on both natural tensor words.
Descent through the original Schur field retains this rank on the binary
nine-dimensional modules. The previously proved non-nine calculation gives
rank at least twelve on the other modules. Every ambient involution inverts
a cubic in the actual generalized Fitting subgroup, so its displacement is
at least three in all cases, and at least six outside dimension nine.

This proves the lower-bound clause of Aschbacher–Smith H.4.7, printed
pp.382–383 of refs/quasithin.pdf. The characterization of equality is not
asserted here. The parity displacement consumer uses the uniform bound on
its literal residual quotient, including the nine-dimensional constituents.
-/

public noncomputable section
open scoped MatrixGroups
open Representation Representation.SL3.BinaryDefiningFactors Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
  (SplittingField)
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four
namespace CubicSpectrum
variable {F K : Type*} [Field F] [Field K] [Finite F] [CharP F 2]
  [IsAlgClosed K] [CharP K 2]

/-- The two natural tensor words both have projective cubic displacement six. -/
theorem projective_cubic_natural_word_ranks (hcard : Nat.card F = 4)
    (ι : F →+* K) (g : SL(3,F))
    (hg : orderOf (QuotientGroup.mk' (Subgroup.center SL(3,F)) g) = 3) :
    Module.finrank K (LinearMap.range (wordRep ι [.natural,.natural] g - 1)) = 6 ∧
    Module.finrank K (LinearMap.range (wordRep ι [.dual,.dual] g - 1)) = 6 := by
  obtain ⟨ω,hω,_,_⟩ := paired_adjointCubicEigenbasis_of_natural ι g
    (fun η ω hω => projective_cubic_natural_eigenbasis hcard η g hg ω hω)
  obtain ⟨b,hb⟩ := projective_cubic_natural_eigenbasis hcard ι g hg ω hω
  obtain ⟨c,hc⟩ := projective_cubic_natural_eigenbasis hcard
    ((frobenius K 2).comp ι) g hg ω hω
  exact natural_pair_cubic_ranks_of_eigenbases ι g ω hω b c hb hc

private theorem displacement_equiv {k X U W : Type*} [Field k] [Group X]
    [AddCommGroup U] [Module k U] [AddCommGroup W] [Module k W]
    {σ : Representation k X U} {τ : Representation k X W} (e : σ.Equiv τ) (g : X) :
    Module.finrank k (LinearMap.range (σ g - 1)) =
      Module.finrank k (LinearMap.range (τ g - 1)) := by
  have he (v : U) : e.toLinearEquiv ((σ g - 1) v) = (τ g - 1) (e.toLinearEquiv v) := by
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    exact congrArg (fun w => w - e.toLinearEquiv v)
      (Representation.IntertwiningMap.isIntertwining σ τ e.toIntertwiningMap g v)
  have hm : (LinearMap.range (σ g - 1)).map e.toLinearEquiv.toLinearMap =
      LinearMap.range (τ g - 1) := by
    ext y
    constructor
    · rintro ⟨x,⟨z,rfl⟩,rfl⟩
      exact ⟨e.toLinearEquiv z,(he z).symm⟩
    · rintro ⟨x,rfl⟩
      obtain ⟨z,rfl⟩ := e.toLinearEquiv.surjective x
      exact ⟨(σ g - 1) z,⟨z,rfl⟩,he z⟩
  rw [← hm,e.toLinearEquiv.finrank_map_eq]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The actual binary nine-dimensional action retains cubic displacement six. -/
theorem binary_nine_cubic_displacement
    (ρ : Representation (ZMod 2) SL(3,F) V) [IsIrreducible ρ]
    (hcard : Nat.card F = 4)
    (hcenter : Subgroup.center SL(3,F) ≤ ρ.ker) (hact : ∃ g, ρ g ≠ 1)
    (hdim : Module.finrank (ZMod 2) V = 9) (g : SL(3,F))
    (hg : orderOf (QuotientGroup.mk' (Subgroup.center SL(3,F)) g) = 3) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ g - 1)) = 6 := by
  obtain ⟨ι,b,c,hbc,⟨e⟩,hs,hd⟩ := exists_nontrivial_binary_pair_model ρ hcard hcenter hact
  have hr := binary_displacement_eq_schurDegree_mul ρ g
  rw [displacement_equiv e g,hs] at hr
  rcases hbc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · simpa only [ite_true,one_mul,(projective_cubic_natural_word_ranks hcard ι g hg).1]
      using hr
  · simpa only [ite_true,one_mul,(projective_cubic_natural_word_ranks hcard ι g hg).2]
      using hr
  all_goals
    norm_num [wordDegree,Factor.dimension,
      show Factor.trivial ≠ Factor.adjoint by decide,
      show Factor.adjoint ≠ Factor.trivial by decide] at hd
    omega

variable {M : Type*} [Group M]

/-- A cubic in the genuine component moves six dimensions in the nine-dimensional case. -/
theorem source_psl3Four_nine_cubic_displacement
    (e : Matrix.PSL3Four.PSL ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V)
    [IsIrreducible (ρ.comp (generalizedFitting M).subtype)] (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) V = 9)
    (x : M) (hx : x ∈ generalizedFitting M) (horder : orderOf x = 3) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) = 6 := by
  let y : generalizedFitting M := ⟨x,hx⟩
  obtain ⟨g,hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center Matrix.PSL3Four.SL) (e.symm y)
  have hgo : orderOf (QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL) g) = 3 := by
    rw [hg]
    exact (orderOf_injective e.symm.toMonoidHom e.symm.injective y).trans
      ((Subgroup.orderOf_coe y).symm.trans horder)
  have hcov : componentCover e g = x := by
    change ((e (QuotientGroup.mk' (Subgroup.center Matrix.PSL3Four.SL) g) :
      generalizedFitting M) : M) = x
    rw [hg,e.apply_symm_apply]
  have hr := binary_nine_cubic_displacement (coverRep e ρ) Matrix.PSL3Four.card_F
    (le_of_eq (coverRep_ker e ρ hρ).symm) (coverRep_nontrivial e ρ hρ) hdim g hgo
  have he : coverRep e ρ g = ρ x := by
    change ρ (componentCover e g) = ρ x
    rw [hcov]
  rwa [he] at hr

/-- Uniform cubic displacement, without an exclusion of dimension nine. -/
theorem source_psl3Four_cubic_displacement_ge_six
    (e : Matrix.PSL3Four.PSL ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V)
    [IsIrreducible (ρ.comp (generalizedFitting M).subtype)] (hρ : Function.Injective ρ)
    (x : M) (hx : x ∈ generalizedFitting M) (horder : orderOf x = 3) :
    6 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) := by
  by_cases hd : Module.finrank (ZMod 2) V = 9
  · exact le_of_eq (source_psl3Four_nine_cubic_displacement e ρ hρ hd x hx horder).symm
  · exact (by decide : 6 ≤ 12).trans
      (source_psl3Four_cubic_displacement e ρ hρ hd x hx horder)
end CubicSpectrum

open Representation.BinaryOffender
variable {M V : Type*} [Group M] [Finite M] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The lower-bound clause of H.4.7, including both nine-dimensional models. -/
theorem source_psl3Four_involution_displacement_ge_three
    (e : Matrix.PSL3Four.PSL ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V)
    [IsIrreducible (ρ.comp (generalizedFitting M).subtype)] (hρ : Function.Injective ρ)
    (t : M) (ht : orderOf t = 2) :
    3 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) := by
  obtain ⟨y,hy,hty⟩ := InvertedCubic.exists_inverted_cubic e t ht
  have horder : orderOf (y : M) = 3 := (Subgroup.orderOf_coe y).trans hy
  have hlow := CubicSpectrum.source_psl3Four_cubic_displacement_ge_six e ρ hρ
    y y.property horder
  have hupper := fixedCodim_three_le_twice_of_inverted ρ (y : M) t horder hty
  simp only [fixedCodim_zpowers_eq_displacement_rank,Module.End.one_eq_id] at hlow hupper ⊢
  omega

/-- Displacement below six forces the nine-dimensional constituent in H.4.7. -/
theorem source_psl3Four_small_involution_dimension
    (e : Matrix.PSL3Four.PSL ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V)
    [IsIrreducible (ρ.comp (generalizedFitting M).subtype)] (hρ : Function.Injective ρ)
    (t : M) (ht : orderOf t = 2)
    (hsmall : Module.finrank (ZMod 2) (LinearMap.range (ρ t - 1)) < 6) :
    Module.finrank (ZMod 2) V = 9 := by
  by_contra hd
  exact (not_lt_of_ge (source_psl3Four_involution_displacement e ρ hρ hd t ht)) hsmall

end CFSG.Quasithin.ChapterH.Section01To04.L3Four
