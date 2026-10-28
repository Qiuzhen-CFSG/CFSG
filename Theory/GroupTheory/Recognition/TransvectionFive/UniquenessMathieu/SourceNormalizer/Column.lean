module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Intersections
public import Theory.LinearAlgebra.FiniteSubspaceTransport

/-!
# The point-centralizer branch at the 45-point end

If the row normalizer is larger than the point centralizer, source 39.3
gives its full action on the binary four-space. Every automorphism of the
marked row-plane intersection extends to that four-space. Its stabilizer
therefore has an orbit of length seven on the nonidentity intersection
elements. The proved marked normalizer intersection places this stabilizer
between the point stabilizer and the ambient plane normalizer, so seven
divides the plane fusion count. A count of 45 is impossible.

Apply this to the opposite marking: the oriented literal column normalizer
equals C_G(z). This proves that clause of Aschbacher, *Sporadic Groups*
(1994), 40.5(2), printed p.218, directly from the proved 39.3 action and
39.6 fusion results. The row movement and two rectangle quotient types
remain separate source obligations.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear

private theorem subgroup_aut_transitive {E : Type*} [Group E]
    (e : E ≃* Multiplicative (Fin 4 → ZMod 2)) (D : Subgroup E)
    (x y : E) (hxD : x ∈ D) (hyD : y ∈ D) (hx : x ≠ 1) (hy : y ≠ 1) :
    ∃ a : MulAut E, a x = y ∧ ∀ d ∈ D, a d ∈ D := by
  let P := D.map e.toMonoidHom
  let W := AddSubgroup.toZModSubmodule 2 P.toAddSubgroup'
  have hm (u : E) : (e u).toAdd ∈ W ↔ u ∈ D := by
    change e u ∈ D.map e.toMonoidHom ↔ u ∈ D
    exact mem_map_equiv.trans (by rw [e.symm_apply_apply])
  let xW : W := ⟨(e x).toAdd, (hm x).mpr hxD⟩
  let yW : W := ⟨(e y).toAdd, (hm y).mpr hyD⟩
  have hxW : xW ≠ 0 := by
    intro h
    apply hx
    apply e.map_eq_one_iff.mp
    exact congrArg (fun u : W => (u : Fin 4 → ZMod 2)) h
  have hyW : yW ≠ 0 := by
    intro h
    apply hy
    apply e.map_eq_one_iff.mp
    exact congrArg (fun u : W => (u : Fin 4 → ZMod 2)) h
  have hf : ∃ f : W ≃ₗ[ZMod 2] W, f xW = yW := by
    by_cases hxy : xW = yW
    · exact ⟨LinearEquiv.refl _ _, hxy⟩
    · obtain ⟨f, hf, _⟩ := BinaryLinear.exists_linearEquiv_pair xW yW yW xW
        hxW hyW hyW hxW hxy (Ne.symm hxy)
      exact ⟨f, hf⟩
  obtain ⟨f, hf⟩ := hf
  obtain ⟨g, hg⟩ := W.exists_linearEquiv_restrict_eq f
  let a : MulAut E := (e.trans g.toAddEquiv.toMultiplicative).trans e.symm
  refine ⟨a, ?_, ?_⟩
  · apply e.injective
    change e (e.symm _) = e y
    rw [e.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    exact (hg xW).symm.trans (congrArg (fun u : W => (u : Fin 4 → ZMod 2)) hf)
  · intro d hd
    apply (hm (a d)).mp
    change (e (e.symm _)).toAdd ∈ W
    rw [e.apply_symm_apply]
    change g (e d).toAdd ∈ W
    rw [← hg ⟨(e d).toAdd, (hm d).mpr hd⟩]
    exact (f _).property

variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

private theorem row_intersection_orbit
    (hne : rowNormalizer F ≠ centralizer ({z} : Set G)) :
    let D := F.row ⊓ F.plane
    let K := rowNormalizer F ⊓ normalizer (D : Set G)
    (centralizer ({z} : Set G)).relIndex K = 7 := by
  let D := F.row ⊓ F.plane
  let K := rowNormalizer F ⊓ normalizer (D : Set G)
  let : MulAction K G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp K.subtype)
  have hzD : z ∈ D := ⟨point_mem_row F, point_mem_plane F⟩
  have hz : z ≠ 1 := by
    intro h
    have he := F.point_orderOf
    rw [h, orderOf_one] at he
    omega
  have hstab : (centralizer ({z} : Set G)).subgroupOf K = MulAction.stabilizer K z := by
    ext g
    change (g : G) ∈ centralizer ({z} : Set G) ↔ g • z = z
    rw [mem_centralizer_singleton_iff]
    change (g : G) * z = z * (g : G) ↔ (g : G) * z * (g : G)⁻¹ = z
    exact mul_inv_eq_iff_eq_mul.symm
  have horbit : MulAction.orbit K z = (D : Set G) \ {1} := by
    ext y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨(mem_normalizer_iff.mp g.property.2 z).mp hzD, ?_⟩
      change g • z ≠ 1
      exact fun h => hz ((MulAut.conj (g : G)).map_eq_one_iff.mp h)
    · rintro ⟨hyD, hy⟩
      let p : F.row := ⟨z, point_mem_row F⟩
      let q : F.row := ⟨y, hyD.1⟩
      obtain ⟨a, hap, haD⟩ := subgroup_aut_transitive (rowCoordinates F) (D.subgroupOf F.row)
        p q hzD hyD (fun h => hz (congrArg Subtype.val h))
        (fun h => hy (congrArg Subtype.val h))
      obtain ⟨g, hg⟩ := row_action_surjective_of_normalizer_ne_centralizer F hne a
      have hgn : (g : G) ∈ normalizer (D : Set G) := by
        apply mem_normalizer_iff_map_conj_eq.mpr
        apply eq_of_le_of_card_ge
        · rintro _ ⟨d, hd, rfl⟩
          have h := haD ⟨d, hd.1⟩ hd
          rw [← hg] at h
          exact h
        · exact (Nat.card_congr
            (D.equivMapOfInjective (MulAut.conj (g : G)).toMonoidHom
              (MulAut.conj (g : G)).injective).toEquiv).le
      refine ⟨⟨g, g.property, hgn⟩, ?_⟩
      have h := congrArg (fun u : F.row => (u : G)) hap
      rw [← hg] at h
      exact h
  change ((centralizer ({z} : Set G)).subgroupOf K).index = 7
  rw [hstab, MulAction.index_stabilizer, horbit,
    Set.ncard_sdiff (Set.singleton_subset_iff.mpr D.one_mem), Set.ncard_singleton]
  change Nat.card D - 1 = 7
  rw [row_plane_card F]

/-- Full row action forces the plane fusion count to be divisible by seven.
The row-intersection stabilizer lies between the point stabilizer and the
plane normalizer, and its orbit has the seven nonzero points of the hyperplane. -/
theorem seven_dvd_plane_fusion_of_row_moves (hfusion : F.MathieuFusion)
    (hne : rowNormalizer F ≠ centralizer ({z} : Set G)) :
    7 ∣ (F.fusion F.plane).ncard := by
  let H := centralizer ({z} : Set G)
  let M := planeNormalizer F
  let K := rowNormalizer F ⊓ normalizer ((F.row ⊓ F.plane : Subgroup G) : Set G)
  have hKM : K ≤ M := inf_le_right.trans (row_plane_intersection_normalizer_le F hfusion)
  have hHK : H ⊓ M ≤ K := by
    intro h hh
    have hr := point_centralizer_le_row_normalizer F hh.1
    exact ⟨hr, inf_normalizer_le_normalizer_inf ⟨hr, hh.2⟩⟩
  have ht := relIndex_mul_relIndex (H ⊓ M) K M hHK hKM
  have he : (H ⊓ M).relIndex K = H.relIndex K := by
    rw [relIndex, relIndex]
    congr 1
    ext k
    exact and_iff_left (hKM k.property)
  rw [he, inf_relIndex_right, row_intersection_orbit F hne] at ht
  have hi : H.relIndex M = (F.fusion F.plane).ncard := by
    rcases hfusion with h | h
    · rw [plane_relative_index F h, h.1]
    · have ho : MathieuFusionOrientation (oppositeMarking F) := by
        simpa only [MathieuFusionOrientation, MarkedCentralizer.fusion,
          oppositeMarking_plane, oppositeMarking_threeSpace] using h.symm
      have hm := threeSpace_relative_index (oppositeMarking F) ho
      simpa only [threeSpaceNormalizer, oppositeMarking_threeSpace, h.1] using hm
  exact ⟨K.relIndex M, by rw [← hi]; exact ht.symm⟩

/-- The 45-point end cannot have full four-dimensional row action. -/
theorem row_normalizer_eq_of_fortyfive (hfusion : F.MathieuFusion)
    (h45 : (F.fusion F.plane).ncard = 45) :
    rowNormalizer F = centralizer ({z} : Set G) := by
  by_contra hne
  have hd := seven_dvd_plane_fusion_of_row_moves F hfusion hne
  rw [h45] at hd
  norm_num at hd

/-- Source 40.5(2): at the oriented 45-point end the literal column
normalizer is the full centralizer of the original marked involution. -/
theorem column_normalizer_eq (hcounts : MathieuFusionOrientation F) :
    columnNormalizer F = centralizer ({z} : Set G) := by
  have hf : (oppositeMarking F).MathieuFusion := by
    right
    simpa only [MarkedCentralizer.fusion, oppositeMarking_plane,
      oppositeMarking_threeSpace] using hcounts.symm
  have hc : ((oppositeMarking F).fusion (oppositeMarking F).plane).ncard = 45 := by
    simpa only [MarkedCentralizer.fusion, oppositeMarking_plane] using hcounts.2
  simpa only [rowNormalizer, oppositeMarking_row] using
    row_normalizer_eq_of_fortyfive (oppositeMarking F) hf hc

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
