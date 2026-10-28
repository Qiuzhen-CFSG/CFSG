module
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceTransport
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.DualCommutator
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Geometry
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
/-!
# The common transvection contradiction on the actual doubled module

An inner actor acts faithfully on a natural module and its contragredient.
If their total moved dimension is at most two, each moved space is a line.
Duality makes both fixed codimensions one; the displacement-map bound then
forces actor rank at most one. This proves the contradiction used in both
mutual-normalization branches of 12.1.3 without assuming a transvection
classification.

The ambient application bounds the linear displacement span by the literal
subgroup commutator and applies the result to its actual induced automizer.
The degree-five branch analysis must still produce the actor and its bounds.
Source: Aschbacher--Smith, 12.1.3, printed pp.789--790 (PDF pp.806--807).
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation.BinaryOffender Module
open CFSG.Quasithin.ChapterH.NaturalDual
open BinaryNaturalDual

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
variable {n : ℕ} {M X : Type*} [Group M] [Finite M]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  (S : SourceSetup n M X)

private theorem product_rank_le_one {K Y : Type*} [Group K] [Finite K]
    [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    (ρ : Representation (ZMod 2) K Y) (hf : Function.Injective ρ)
    (A : Subgroup K)
    (hm : finrank (ZMod 2) (subspaceCommutator (ρ.prod ρ.dual) ⊤ A) ≤ 2) :
    rank A ≤ 1 := by
  by_cases hz : A = ⊥
  · simp [hz, rank]
  have hp := fixedCodim_pos_of_faithful ρ hf hz
  have hq := fixedCodim_pos_of_faithful ρ.dual (faithful_dual ρ hf) hz
  have hr := rank_le_fixedCodim_mul_dual ρ hf A
  rw [moved_finrank_prod, ← fixedCodim_dual_eq_moved_finrank] at hm
  have he : fixedCodim ρ A = finrank (ZMod 2) (subspaceCommutator ρ.dual ⊤ A) := by
    rw [subspaceCommutator_top_eq_coinvariants]
    exact Representation.finrank_quotient_invariants_eq_dual_commutator (ρ.comp A.subtype)
  rw [← he] at hm
  have ha : fixedCodim ρ A = 1 := by omega
  have hb : fixedCodim ρ.dual A = 1 := by omega
  simpa only [ha, hb, mul_one] using hr

omit [FiniteDimensional (ZMod 2) X] in
/-- An inner actor moving at most a plane has binary image rank at most one. -/
theorem inner_small_moved (I : Subgroup M) (hI : I ≤ componentLayer M)
    (hm : finrank (ZMod 2) (Representation.Coinvariants.ker
      (S.representation.comp I.subtype)) ≤ 2) : rank I ≤ 1 := by
  let f : I →* BinaryLinear.OuterCyclic.LinearGroup n :=
    S.layer.toMonoidHom.comp (Subgroup.inclusion hI)
  let ρ : Representation (ZMod 2) I (BinaryLinear.OuterCyclic.Space n) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f
  have hf : Function.Injective ρ := by
    intro a b he
    have h : f a = f b := LinearEquiv.toLinearMap_injective he
    exact (Subgroup.inclusion_injective hI) (S.layer.injective h)
  have ha (a : I) (x : X) :
      S.model.coordinates (S.representation a x) =
        (ρ.prod ρ.dual) a (S.model.coordinates x) := by
    rw [S.model.equivariant]
    rw [show S.model.group a = MulAut.conj (f a) from
      S.model.on_layer (Subgroup.inclusion hI a)]
    rw [(BinaryNaturalDual.ModelOrbits.AutomorphismModel.coordinateAction S.degree).on_inner]
    rw [naturalDualRepresentation_apply]
    apply Prod.ext
    · rfl
    · apply LinearMap.ext
      intro y
      change (S.model.coordinates x).2 ((f a).symm y) =
        (S.model.coordinates x).2 (f a⁻¹ y)
      rw [map_inv]
      rfl
  have he := BinaryNaturalDual.Transport.commutator_map
    (S.representation.comp I.subtype) (ρ.prod ρ.dual) (MulEquiv.refl I)
    S.model.coordinates ha ⊤
  change (Representation.Coinvariants.ker
    ((S.representation.comp I.subtype).comp (⊤ : Subgroup I).subtype)).map
      S.model.coordinates.toLinearMap =
    Representation.Coinvariants.ker ((ρ.prod ρ.dual).comp
      ((⊤ : Subgroup I).map (MonoidHom.id I)).subtype) at he
  rw [Subgroup.map_id] at he
  have hd : finrank (ZMod 2) (subspaceCommutator (ρ.prod ρ.dual) ⊤ ⊤) ≤ 2 := by
    rw [subspaceCommutator_top_eq_coinvariants, ← he,
      S.model.coordinates.finrank_map_eq]
    have he' : Representation.Coinvariants.ker
        ((S.representation.comp I.subtype).comp (⊤ : Subgroup I).subtype) =
        Representation.Coinvariants.ker (S.representation.comp I.subtype) := by
      unfold Representation.Coinvariants.ker
      congr 1
      ext v
      constructor
      · rintro ⟨⟨a,w⟩,rfl⟩
        exact ⟨(a.val,w),rfl⟩
      · rintro ⟨⟨a,w⟩,rfl⟩
        exact ⟨(⟨a,Subgroup.mem_top a⟩,w),rfl⟩
    rw [he']
    exact hm
  simpa [rank] using product_rank_le_one ρ hf ⊤ hd
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
open CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G}
  [IsElementaryAbelian 2 W]

/-- The same bound for the literal ambient commutator and conjugation image. -/
theorem actual_inner_small_moved {n : ℕ}
    (S : SourceSetup n (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W)
    (A : Subgroup G) (hA : A ≤ normalizer (W : Set G))
    (hi : inducedAutomizer W A ≤ componentLayer (Automizer W))
    (hd : rank ⁅W,A⁆ ≤ 2) : rank (inducedAutomizer W A) ≤ 1 := by
  apply inner_small_moved S _ hi
  have hle : Representation.Coinvariants.ker
      (S.representation.comp (inducedAutomizer W A).subtype) ≤
      subgroupSpace W ⁅W,A⁆ := by
    rw [hρ]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,w⟩,rfl⟩
    obtain ⟨b,hb,he⟩ := a.property
    change automizerRepresentation W (a : Automizer W) w - w ∈ _
    rw [← he]
    apply (mem_subgroupSpace W _ _).mpr
    rw [toMul_sub, div_eq_mul_inv]
    change (b : G) * (w.toMul : G) * (b : G)⁻¹ * (w.toMul : G)⁻¹ ∈ ⁅W,A⁆
    rw [Subgroup.commutator_comm]
    exact commutator_mem_commutator hb w.toMul.property
  have hh := Submodule.finrank_mono hle
  rw [subgroupSpace_finrank W _ (le_normalizer_iff_commutator_le_left.mp hA)] at hh
  exact hh.trans hd
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure.Mutual
