module
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.SpecificGroups.BinaryLinear.NestedRadicals
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore
public import Theory.SpecificGroups.BinaryLinear.SylowFlagOvergroups.Covers

/-!
# Binary parabolic radicals control their Sylow intervals

A subspace invariant under the full elementary radical at W is comparable
with W. In particular, a radical lying in a full flag determines the cut of
its dimension. Apply this to every retained cut of a partial flag. Inner
automorphisms preserve their dimensions, and inverse-transpose automorphisms
reverse them. A symmetric partial flag is consequently preserved by every
automorphism normalizing any subgroup between its two-core and the full flag.

Every Sylow overgroup is a partial flag. An outer actor preserving it and
the original Sylow forces its cuts to be symmetric. Thus the same interval
normalizers preserve its embedded two-residual. This proves the precise
binary dimension-four/five weak-closure calculation needed in source 10.2.5,
without assuming the full general Lie-type conjugation-family theorem I.2.5.

Source: Aschbacher--Smith, printed pp.409--414 and 747--748. The original
Chapter 10 quotient application is BinaryThreeAction/Linear.lean.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The invariant subspaces of a full elementary parabolic radical are
exactly those comparable with its marked subspace. -/
theorem radical_le_parabolic_iff_comparable (W U : Submodule (ZMod 2) V) :
    radical W ≤ parabolic U ↔ U ≤ W ∨ W ≤ U := by
  constructor
  · intro h
    by_cases hUW : U ≤ W
    · exact Or.inl hUW
    · right
      obtain ⟨u,hu,huW⟩ := SetLike.not_le_iff_exists.mp hUW
      obtain ⟨f,hfu,hfW⟩ := W.exists_le_ker_of_notMem huW
      have hf1 : f u = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hfu
      intro w hw
      have htu := (h (transvection_mem hw hfW) u).mpr hu
      change u + f u • w ∈ U at htu
      have hd := U.sub_mem htu hu
      simpa only [hf1,one_smul,add_sub_cancel_left] using hd
  · rintro (h | h)
    · exact radical_le_smaller_parabolic h
    · exact radical_le_nested_parabolic h

/-- A radical in an equal-dimensional parabolic determines that parabolic. -/
theorem eq_of_radical_le_parabolic [FiniteDimensional (ZMod 2) V]
    {W U : Submodule (ZMod 2) V} (h : radical W ≤ parabolic U)
    (hd : Module.finrank (ZMod 2) W = Module.finrank (ZMod 2) U) : W = U := by
  rcases (radical_le_parabolic_iff_comparable W U).mp h with hUW | hWU
  · exact (Submodule.eq_of_le_of_finrank_eq hUW hd.symm).symm
  · exact Submodule.eq_of_le_of_finrank_eq hWU hd

namespace InvariantNodeActions
open OuterCyclic
private instance (n : ℕ) : Finite (LinearGroup n) :=
  Finite.of_injective (fun g : LinearGroup n => (g : Space n → Space n)) DFunLike.coe_injective

/-- Each retained cut radical lies in the two-core of the full partial flag. -/
theorem cut_radical_le_core {m : ℕ} (b : Basis m) (cuts : Set (Fin m))
    {i : Fin m} (hi : i ∈ cuts) :
    radical (cutSpace b i) ≤ (cutStabilizer b cuts).pCoreIn 2 := by
  apply le_pCoreIn_of_normalizes (radical_two _) ?_ ?_
  · intro g hg
    rw [mem_cutStabilizer]
    intro j _
    rcases le_total i j with hij | hji
    · exact radical_le_nested_parabolic (cutSpace_mono b hij) hg
    · exact radical_le_smaller_parabolic (cutSpace_mono b hji) hg
  · apply le_trans _ (parabolic_le_normalizer (cutSpace b i))
    intro g hg
    exact (mem_cutStabilizer b cuts g).mp hg i hi

/-- Mapping a parabolic also maps its literal unipotent radical. -/
theorem radical_map_of_parabolic_map {m : ℕ}
    (W U : Submodule (ZMod 2) (Space (m+1))) (a : MulAut (LinearGroup (m+1)))
    (h : (parabolic W).map a.toMonoidHom = parabolic U) :
    (radical W).map a.toMonoidHom = radical U := by
  rw [← SmallParabolicLevi.map_twoCore_eq_radical W,
    ← SmallParabolicLevi.map_twoCore_eq_radical U]
  change ((parabolic W).pCoreIn 2).map a.toMonoidHom = (parabolic U).pCoreIn 2
  rw [map_pCoreIn_of_injective 2 _ a.toMonoidHom a.injective,h]

/-- Any radical carried into a full flag has the flag's cut of its dimension. -/
theorem eq_cut_of_radical_le_fullFlag {m : ℕ} (b : Basis m)
    (W : Submodule (ZMod 2) (Space (m+1))) (i : Fin m)
    (h : radical W ≤ cutStabilizer b Set.univ)
    (hd : Module.finrank (ZMod 2) W = i.val+1) : W = cutSpace b i := by
  apply eq_of_radical_le_parabolic
  · apply h.trans
    intro g hg
    exact (mem_cutStabilizer b Set.univ g).mp hg i (Set.mem_univ i)
  · rw [hd,cutSpace_finrank]

/-- Every automorphism normalizing a subgroup between the unipotent radical
and the original full flag preserves the symmetric partial flag. -/
theorem map_symmetric_flag_of_core_interval {m : ℕ}
    (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4) (b : Basis m) (cuts : Set (Fin m))
    (hsym : ∀ i : Fin m, i.rev ∈ cuts ↔ i ∈ cuts)
    (U : Subgroup (LinearGroup (m+1)))
    (hcore : (cutStabilizer b cuts).pCoreIn 2 ≤ U)
    (hUS : U ≤ cutStabilizer b Set.univ)
    (a : MulAut (LinearGroup (m+1))) (ha : U.map a.toMonoidHom = U) :
    (cutStabilizer b cuts).map a.toMonoidHom = cutStabilizer b cuts := by
  have hr (i : Fin m) (hi : i ∈ cuts) :
      (radical (cutSpace b i)).map a.toMonoidHom ≤ cutStabilizer b Set.univ := by
    exact ((map_mono ((cut_radical_le_core b cuts hi).trans hcore)).trans_eq ha).trans hUS
  obtain ⟨g,hg | hg⟩ := smallDimension_inner_graph (by omega) (by omega) a
  · subst a
    have hcut (i : Fin m) (hi : i ∈ cuts) :
        (cutSpace b i).map g.toLinearMap = cutSpace b i := by
      apply eq_cut_of_radical_le_fullFlag b _ i
      · have hp : (parabolic (cutSpace b i)).map (MulAut.conj g).toMonoidHom =
          parabolic ((cutSpace b i).map g.toLinearMap) := inner_map_parabolic _ _
        rw [← radical_map_of_parabolic_map _ _ _ hp]
        exact hr i hi
      · rw [LinearEquiv.finrank_map_eq,cutSpace_finrank]
    have hgin : g ∈ cutStabilizer b cuts := by
      rw [mem_cutStabilizer_maps]
      intro i hi v hv
      rw [← hcut i hi]
      exact Submodule.mem_map_of_mem hv
    exact mem_normalizer_iff_map_conj_eq.mp ((cutStabilizer b cuts).le_normalizer hgin)
  · subst a
    have hp (i : Fin m) (hi : i ∈ cuts) :
        (parabolic (cutSpace b i)).map (graphLinear (m+1) * MulAut.conj g).toMonoidHom =
          parabolic (cutSpace b i.rev) := by
      have he : flagOrthogonal ((cutSpace b i).map g.toLinearMap) = cutSpace b i.rev := by
        apply eq_cut_of_radical_le_fullFlag b _ i.rev
        · rw [← radical_map_of_parabolic_map _ _ _ (graph_inner_map_parabolic (cutSpace b i) g)]
          exact hr i hi
        · rw [graph_inner_cut_finrank,Fin.val_rev]
          have := i.isLt
          omega
      rw [graph_inner_map_parabolic,he]
    ext x
    rw [Subgroup.mem_map_equiv,mem_cutStabilizer,mem_cutStabilizer]
    have hx (i : Fin m) (hi : i ∈ cuts) :
        (graphLinear (m+1) * MulAut.conj g).symm x ∈ parabolic (cutSpace b i) ↔
          x ∈ parabolic (cutSpace b i.rev) := by
      rw [← hp i hi,Subgroup.mem_map_equiv]
    constructor
    · intro h i hi
      have hh := (hx i.rev ((hsym i).mpr hi)).mp (h i.rev ((hsym i).mpr hi))
      change x ∈ parabolic (cutSpace b i)
      simpa only [Fin.rev_rev] using hh
    · intro h i hi
      exact (hx i hi).mpr (h i.rev ((hsym i).mpr hi))

/-- The same automorphism preserves the embedded two-residual, exactly as
required in the binary rank-four/five normalizer calculation. -/
theorem map_symmetric_flag_residual_of_core_interval {m : ℕ}
    (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4) (b : Basis m) (cuts : Set (Fin m))
    (hsym : ∀ i : Fin m, i.rev ∈ cuts ↔ i ∈ cuts)
    (U : Subgroup (LinearGroup (m+1)))
    (hcore : (cutStabilizer b cuts).pCoreIn 2 ≤ U)
    (hUS : U ≤ cutStabilizer b Set.univ)
    (a : MulAut (LinearGroup (m+1))) (ha : U.map a.toMonoidHom = U) :
    ((pResidual 2 (cutStabilizer b cuts)).map (cutStabilizer b cuts).subtype).map
      a.toMonoidHom = (pResidual 2 (cutStabilizer b cuts)).map (cutStabilizer b cuts).subtype := by
  rw [map_embedded_pResidual,
    map_symmetric_flag_of_core_interval hm₀ hm₁ b cuts hsym U hcore hUS a ha]

/-- An outer actor preserving the original Sylow and an overgroup forces the
parabolic's cuts to be symmetric. The radical-interval calculation therefore
controls every automorphism normalizing any intermediate subgroup. -/
theorem map_residual_of_outer_invariant_sylow_overgroup {m : ℕ}
    (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4) (S : Sylow 2 (LinearGroup (m+1)))
    (B U : Subgroup (LinearGroup (m+1))) (hSB : (S : Subgroup (LinearGroup (m+1))) ≤ B)
    (hcore : B.pCoreIn 2 ≤ U) (hUS : U ≤ (S : Subgroup (LinearGroup (m+1))))
    (outer : MulAut (LinearGroup (m+1))) (hout : outer ∉ MulAut.innerSubgroup _)
    (hoS : (S : Subgroup (LinearGroup (m+1))).map outer.toMonoidHom = S)
    (hoB : B.map outer.toMonoidHom = B)
    (a : MulAut (LinearGroup (m+1))) (ha : U.map a.toMonoidHom = U) :
    ((pResidual 2 B).map B.subtype).map a.toMonoidHom = (pResidual 2 B).map B.subtype := by
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  obtain ⟨cuts,rfl⟩ := SylowFlagOvergroups.overgroup_eq_cutStabilizer S b hb B hSB
  rw [hb] at hUS hoS
  obtain ⟨g,hg⟩ := outer_eq_graph_inner (by omega) (by omega) outer hout
  have hp (i : Fin m) : (parabolic (cutSpace b i)).map outer.toMonoidHom =
      parabolic (cutSpace b i.rev) := by
    rw [hg,graph_inner_map_parabolic,
      graph_inner_cutSpace_of_fullFlag b g (hg ▸ hoS)]
  have hrev (i : Fin m) (hi : i ∈ cuts) : i.rev ∈ cuts := by
    have hle : cutStabilizer b cuts ≤ parabolic (cutSpace b i) :=
      fun x hx => (mem_cutStabilizer b cuts x).mp hx i hi
    have him := map_mono (f := outer.toMonoidHom) hle
    rw [hoB,hp] at him
    obtain ⟨j,hj,he⟩ := (cutStabilizer_le_parabolic_iff b cuts (cutSpace b i.rev)
      (cutSpace_ne_bot b i.rev) (cutSpace_ne_top b i.rev)).mp him
    have hd := congrArg (fun W : Submodule (ZMod 2) (Space (m+1)) =>
      Module.finrank (ZMod 2) W) he
    rw [cutSpace_finrank,cutSpace_finrank] at hd
    have heij : j = i.rev := Fin.ext (by omega)
    exact heij ▸ hj
  apply map_symmetric_flag_residual_of_core_interval hm₀ hm₁ b cuts ?_ U hcore hUS a ha
  intro i
  exact ⟨fun hi => by simpa only [Fin.rev_rev] using hrev i.rev hi,hrev i⟩

end InvariantNodeActions
end BinaryLinear
