module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Alternating.ProperComponents.PrimitiveRecognition.Inputs
public import Theory.SpecificGroups.BinaryLinear.FourCentralizerOvergroups.Directions
public import Theory.SpecificGroups.BinaryLinear.NestedRadicals
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# Abelian normal subgroups of eight-point Sylow overgroups

Use the actual exceptional A₈ ≃ PSL₄(2) ≃ GL₄(2) equivalences. A Sylow
two-subgroup of the binary linear group fixes a nonzero vector. It normalizes
that vector's line radical, so Sylow maximality puts the radical inside the
Sylow subgroup. Thus the overgroup has a nonzero full transvection direction.

The full transvection directions form an invariant subspace. This subspace
is proper when the overgroup is proper, since all transvections generate
GL₄(2). Its block-unipotent radical is nontrivial and abelian. The overgroup
normalizes it, and Sylow maximality again places it inside the overgroup.
Restricting this radical and transporting through the actual subgroup
isomorphism constructs the required normal subgroup inside X itself.
The exact primitive contract follows from this stronger Sylow-overgroup result.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.13,
printed p.74 (PDF p.85), final paragraph, invoking the Sylow-overgroup
structure in A.3.12. The imported exceptional equivalence compares the
actual exterior-square and deleted-permutation-module actions.
-/

public section

open Subgroup BinaryLinear
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

private theorem radical_le_sylow {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (S : Sylow 2 (BinaryLinear.GL V)) (W : Submodule (ZMod 2) V)
    (hSP : (S : Subgroup (BinaryLinear.GL V)) ≤ parabolic W) :
    radical W ≤ (S : Subgroup (BinaryLinear.GL V)) := by
  have he := S.is_maximal' (S.isPGroup'.to_sup_of_normal_right' (radical_two W)
    (hSP.trans (parabolic_le_normalizer W))) le_sup_left
  exact he ▸ le_sup_right

theorem exists_invariant_subspace
    (S : Sylow 2 (BinaryLinear.GL (Fin 4 → ZMod 2)))
    (X : Subgroup (BinaryLinear.GL (Fin 4 → ZMod 2))) (hSX : (S : Subgroup _) ≤ X)
    (hX : X ≠ ⊤) :
    ∃ W : Submodule (ZMod 2) (Fin 4 → ZMod 2),
      W ≠ ⊥ ∧ W ≠ ⊤ ∧ X ≤ parabolic W := by
  have hcard : 2 ∣ Nat.card (Fin 4 → ZMod 2) := by
    simp
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fixedSpace_ne_bot hcard S.isPGroup')
  let L := Submodule.span (ZMod 2) {w}
  have hSP : (S : Subgroup _) ≤ parabolic L := by
    intro g hg v
    constructor
    · intro hv
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
      apply Submodule.mem_span_singleton.mpr
      refine ⟨a, g.injective ?_⟩
      simpa only [map_smul, show g w = w from hw g hg] using ha
    · intro hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, show g w = w from hw g hg]
      exact L.smul_mem a (Submodule.mem_span_singleton_self w)
  have hRX : radical L ≤ X := (radical_le_sylow S L hSP).trans hSX
  let W := FourCentralizerOvergroups.directions X
  have hwW : w ∈ W := by
    intro f hf
    exact hRX (transvection_mem (Submodule.mem_span_singleton_self w)
      ((Submodule.span_singleton_le_iff_mem w f.ker).mpr hf))
  refine ⟨W, ?_, ?_, FourCentralizerOvergroups.le_parabolic_directions X⟩
  · intro hW
    exact hw0 (by simpa only [hW, Submodule.mem_bot] using hwW)
  · exact fun hW => hX (FourCentralizerOvergroups.eq_top_of_directions_eq_top X hW)

private theorem linear_four_abelian_normal
    (S : Sylow 2 (BinaryLinear.GL (Fin 4 → ZMod 2)))
    (X : Subgroup (BinaryLinear.GL (Fin 4 → ZMod 2))) (hSX : (S : Subgroup _) ≤ X)
    (hX : X ≠ ⊤) : ∃ A : Subgroup X, A.Normal ∧ IsMulCommutative A ∧ A ≠ ⊥ := by
  obtain ⟨W, hW0, hWt, hXP⟩ := exists_invariant_subspace S X hSX hX
  have hRX : radical W ≤ X := (radical_le_sylow S W (hSX.trans hXP)).trans hSX
  let A := (radical W).subgroupOf X
  have hn : A.Normal := (normal_subgroupOf_iff_le_normalizer hRX).mpr
    (hXP.trans (parabolic_le_normalizer W))
  let : IsMulCommutative (radical W) :=
    commutator_self_eq_bot_iff.mp (radical_commutative W)
  refine ⟨A, hn, inferInstance, ?_⟩
  intro hA
  apply radical_ne_bot hW0 hWt
  apply bot_unique
  intro g hg
  have hgA : (⟨g, hRX hg⟩ : X) ∈ A := hg
  rw [hA] at hgA
  change (⟨g, hRX hg⟩ : X) = 1 at hgA
  exact congrArg Subtype.val hgA

/-- Every proper Sylow-two overgroup in A₈ contains an actual nontrivial
abelian normal subgroup, transported from its binary linear parabolic radical. -/
theorem alternating_eight_proper_sylow_overgroup_abelian_normal
    (S : Sylow 2 (alternatingGroup (Fin 8)))
    (X : Subgroup (alternatingGroup (Fin 8))) (hSX : (S : Subgroup _) ≤ X)
    (hX : X ≠ ⊤) : ∃ A : Subgroup X, A.Normal ∧ IsMulCommutative A ∧ A ≠ ⊥ := by
  let e : alternatingGroup (Fin 8) ≃* BinaryLinear.GL (Fin 4 → ZMod 2) :=
    Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide))
  let Y := X.map e.toMonoidHom
  let T : Sylow 2 (BinaryLinear.GL (Fin 4 → ZMod 2)) :=
    S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hTY : (T : Subgroup _) ≤ Y := Subgroup.map_mono hSX
  have hY : Y ≠ ⊤ := by
    intro h
    apply hX
    apply (Subgroup.map_injective (f := e.toMonoidHom) e.injective)
    exact h.trans (Subgroup.map_top_of_surjective e.toMonoidHom e.surjective).symm
  obtain ⟨B, hn, hc, hb⟩ := linear_four_abelian_normal T Y hTY hY
  let d : Y ≃* X := (e.subgroupMap X).symm
  let := hn
  let := hc
  refine ⟨B.map d.toMonoidHom, hn.map _ d.surjective, inferInstance, ?_⟩
  intro h
  apply hb
  apply Subgroup.map_injective (f := d.toMonoidHom) d.injective
  simpa only [Subgroup.map_bot] using h

/-- The degree-eight normal-subgroup input to the primitive branch of B.1.13. -/
theorem alternating_primitive_eight_abelian_normal :
    AlternatingPrimitiveEightAbelianNormal := by
  intro S X hSX hX _ _ _
  exact alternating_eight_proper_sylow_overgroup_abelian_normal S X hSX hX

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
