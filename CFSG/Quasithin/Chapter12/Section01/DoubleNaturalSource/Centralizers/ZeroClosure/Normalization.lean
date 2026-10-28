module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.FiveGeometry
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Geometry

/-!
# Zeroth-closure normalizer and fixed-space reductions

For a whole conjugate A of W which normalizes W, E.3.4 bounds its
faithful action rank if W fails to normalize A. E.3.32 puts its generated
cores in N_W(A), with no prior positive weak-closure assumption. H.9.2
therefore forces mutual normalization in dimension five when r ≥ 5.

If the natural summand intersects A trivially, the displacement of a
natural vector in N_W(A) under an inner actor lies in that intersection.
It vanishes. The linear/group core comparison applies this observation
to the exact H.9.3 core used in dimension four.
Source: Aschbacher--Smith, E.3.4, E.3.32, H.9.2 and 12.1.3,7,
printed pp.231,238,390--391,789--790,792.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterH.NaturalDual
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G} [IsElementaryAbelian 2 W]

omit [Finite G] [IsElementaryAbelian 2 W] in
/-- E.3.4(2), on a whole conjugate normalizing the original module. -/
theorem rank_ge_of_not_normalized (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G))
    (hn : ¬ W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G))
    {r : ℕ} (hr : (r : ℕ∞) ≤ globalR W) :
    r ≤ rank (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom)) := by
  have hb := hr.trans (globalR_le_conjugate_centralizer_corank g hn)
  rw [← rank_inducedAutomizer W _ hA] at hb
  exact_mod_cast hb

/-- E.3.32 at index zero needs no positive-weak-closure premise. -/
theorem core_le_normalizer (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G))
    {r k : ℕ} (hr : (r : ℕ∞) ≤ globalR W) (hk : k < r) :
    automizerDualCore W (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom)) k ≤
      W ⊓ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G) := by
  have he : offenderNormalizer W g = W.map (MulAut.conj g).toMonoidHom :=
    inf_eq_left.mpr hA
  have hc : subgroupCorank (W.map (MulAut.conj g).toMonoidHom)
      (offenderNormalizer W g) = 0 := by
    rw [he]
    simp [subgroupCorank]
  have hh := automizerDualCore_le_conjugate_normalizer (V := W) g k
    (by rw [hc, Nat.cast_zero, zero_add]
        exact lt_of_lt_of_le (by exact_mod_cast hk) hr)
  rwa [he] at hh

/-- H.9.2(5) excludes one-sided normalization in dimension five. -/
theorem five_normalizes_conjugate
    (S : SourceSetup 5 (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W)
    (hr : (5 : ℕ∞) ≤ globalR W) (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G)) :
    W ≤ normalizer (W.map (MulAut.conj g).toMonoidHom : Set G) := by
  by_contra hn
  let : IsElementaryAbelian 2 (W.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  let := inducedAutomizer_elementary W (W.map (MulAut.conj g).toMonoidHom) hA
  have hc := WeakClosure.five_core_eq_orbit S hρ _ (rank_ge_of_not_normalized g hA hn hr)
  have hb := core_le_normalizer g hA hr (by decide : 3 < 5)
  rw [hc] at hb
  exact hn (hb.trans inf_le_right)

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure
variable {G : Type*} [Group G] [Finite G] {W : Subgroup G} [IsElementaryAbelian 2 W]

omit [Finite G] in
/-- The linear H.9 core is the literal E.3.30 subgroup core in the ambient group. -/
theorem mem_core_iff (I : Subgroup (Automizer W)) (k : ℕ) (u : Additive W) :
    (u.toMul : G) ∈ automizerDualCore W I k ↔
      u ∈ BinaryNaturalDual.generatedCore ((automizerRepresentation W).comp I.subtype) k := by
  have ha : BinaryNaturalDual.multiplicativeAction ((automizerRepresentation W).comp I.subtype) =
      ((Automizer W).subtype.comp I.subtype) := by
    ext a w
    rfl
  have hc := generatedCore_subgroup ((automizerRepresentation W).comp I.subtype) k
  rw [ha] at hc
  have hc' : (BinaryNaturalDual.subgroupOrderIso
      (BinaryNaturalDual.generatedCore ((automizerRepresentation W).comp I.subtype) k) :
        Subgroup W) = dualGeneratedCore ((Automizer W).subtype.comp I.subtype) k := hc
  rw [automizerDualCore, ← hc']
  constructor
  · rintro ⟨w, hw, he⟩
    have he' : w = u.toMul := Subtype.ext he
    rw [he'] at hw
    exact hw
  · intro hu
    exact ⟨u.toMul, hu, rfl⟩

omit [Finite G] in
/-- A pure vector normalizing an intersecting conjugate is fixed by its inner actor.
The displacement lies in both the natural summand and the conjugate. -/
theorem natural_normalizer_le_inner_fixed {n : ℕ}
    (S : SourceSetup n (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W) (g : G)
    (hz : S.natural ⊓ subgroupSpace W (W.map (MulAut.conj g).toMonoidHom) = ⊥) :
    S.natural ⊓ subgroupSpace W (normalizer (W.map (MulAut.conj g).toMonoidHom : Set G)) ≤
      S.fixed (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom) ⊓
        componentLayer (Automizer W)) := by
  intro u hu a
  have hnat : S.representation (a : Automizer W) u ∈ S.natural := by
    let l : componentLayer (Automizer W) := ⟨a, a.property.2⟩
    have he := S.natural_action l (S.naturalCoordinates ⟨u, hu.1⟩)
    rw [S.naturalCoordinates.symm_apply_apply] at he
    rw [he]
    exact Subtype.coe_prop _
  have hd : S.representation (a : Automizer W) u - u ∈
      S.natural ⊓ subgroupSpace W (W.map (MulAut.conj g).toMonoidHom) := by
    refine ⟨S.natural.sub_mem hnat hu.1, ?_⟩
    obtain ⟨b, hb, he⟩ := a.property.1
    apply (mem_subgroupSpace W _ _).mpr
    rw [hρ, ← he, toMul_sub, div_eq_mul_inv]
    change (b : G) * (u.toMul : G) * (b : G)⁻¹ * (u.toMul : G)⁻¹ ∈
      W.map (MulAut.conj g).toMonoidHom
    have hnorm := (mem_subgroupSpace W _ u).mp hu.2
    have hconj := (mem_normalizer_iff.mp hnorm) (b : G)⁻¹
    have hinv := (W.map (MulAut.conj g).toMonoidHom).inv_mem hb
    have hh := (W.map (MulAut.conj g).toMonoidHom).mul_mem hb (hconj.mp hinv)
    simpa only [Subgroup.subtype_apply, mul_assoc] using hh
  rw [hz] at hd
  exact sub_eq_zero.mp hd

/-- E.3.32 and the zero pure intersection impose the fixed-space condition
that the remaining H.9.3 actor calculation must contradict. -/
theorem natural_core_le_inner_fixed {n : ℕ}
    (S : SourceSetup n (Automizer W) (Additive W))
    (hρ : S.representation = automizerRepresentation W) (g : G)
    (hA : W.map (MulAut.conj g).toMonoidHom ≤ normalizer (W : Set G))
    (hz : S.natural ⊓ subgroupSpace W (W.map (MulAut.conj g).toMonoidHom) = ⊥)
    {r k : ℕ} (hr : (r : ℕ∞) ≤ globalR W) (hk : k < r) :
    S.natural ⊓ BinaryNaturalDual.generatedCore
      (S.representation.comp (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom)).subtype) k ≤
      S.fixed (inducedAutomizer W (W.map (MulAut.conj g).toMonoidHom) ⊓
        componentLayer (Automizer W)) := by
  apply le_trans _ (natural_normalizer_le_inner_fixed S hρ g hz)
  apply inf_le_inf_left
  intro u hu
  rw [hρ] at hu
  exact (mem_subgroupSpace W _ u).mpr
    (core_le_normalizer g hA hr hk ((mem_core_iff _ k u).mpr hu)).2

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.ZeroClosure
