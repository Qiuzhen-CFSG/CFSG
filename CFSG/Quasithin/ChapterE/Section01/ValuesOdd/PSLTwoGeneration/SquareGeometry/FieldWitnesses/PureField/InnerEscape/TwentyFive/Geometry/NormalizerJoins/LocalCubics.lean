module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Inputs
public import Theory.SpecificGroups.PSL2.FiveProjectivePermutation
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Cubic normalizers of the marked characteristic-five subgroups

Restrict the frame's common Sylow subgroup to either actual centralizer and
project through its prescribed comparison to PGL₂(5) ≃ S₅. The projection
has a two-group kernel, so the marked large subgroup is exactly the full
preimage of the Sylow intersection with A₅. The A₄ normalizer of that
four-group has order divisible by three; Cauchy's theorem in its full
preimage supplies a cubic normalizing the literal ambient large subgroup.

The image of the local derived group is [C,C]. Every element of C normalizes
this image, so the same cubic normalizes its intersection with the large
subgroup, which is the literal small subgroup. This preimage argument retains
an arbitrary frame comparison without requiring a separate product-subgroup
calculation or a chosen order-three lift.

This discharges the local-cubic premise of the normalizer-join assembly for
Aschbacher–Smith E.1.14(6), printed p.214, citing Asc82a Lemma 4.10. The
E-generation and subgroup transport conventions are E.1.5 and E.1.8,
printed pp.210–211. The independent centralizer-intersection calculation
remains with the join assembly owner.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry

private abbrev S5 := Equiv.Perm (Fin 5)
private abbrev A5 := alternatingGroup (Fin 5)

private lemma stabilizer_card (i : Fin 5) :
    Nat.card (MulAction.stabilizer A5 i) = 12 := by
  let (j : Fin 5) : DecidablePred (· ∈ MulAction.stabilizer A5 j) :=
    fun x => inferInstanceAs (Decidable (x.val j = j))
  rw [Nat.card_eq_fintype_card]
  revert i
  decide +kernel

private theorem exists_cubic_normalizer_preimage {C : Type*} [Group C] [Finite C]
    (q : C →* S5) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (T : Sylow 2 C) :
    ∃ x : C, x ∈ normalizer (((T : Subgroup C) ⊓ A5.comap q : Subgroup C) : Set C) ∧
      orderOf x = 3 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P : Sylow 2 S5 := T.mapSurjective hq
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal A5
  let V : Subgroup S5 := (R : Subgroup A5).map A5.subtype
  have hV : V = (P : Subgroup S5) ⊓ A5 := by
    change (R : Subgroup A5).map A5.subtype = _
    rw [hR, subgroupOf_map_subtype]
  have hvq : V.comap q = (T : Subgroup C) ⊓ A5.comap q := by
    rw [hV, comap_inf]
    change ((T : Subgroup C).map q).comap q ⊓ A5.comap q = _
    rw [comap_map_eq_self (hk.le_sylow_of_normal T)]
  let N : Subgroup A5 := normalizer (R : Set A5)
  obtain ⟨j, hj⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  have hN : Nat.card N = 12 := by
    change Nat.card (normalizer (R : Set A5)) = _
    rw [hj, stabilizer_card]
  let M : Subgroup C := (N.map A5.subtype).comap q
  have hdiv : 3 ∣ Nat.card M := by
    have hcard : Nat.card (N.map A5.subtype) = Nat.card N :=
      card_map_of_injective A5.subtype_injective
    have hd := card_dvd_of_surjective (q.subgroupComap (N.map A5.subtype))
      (q.subgroupComap_surjective_of_surjective (N.map A5.subtype) hq)
    rw [hcard, hN] at hd
    exact dvd_trans (by decide : 3 ∣ 12) hd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) 3 hdiv
  refine ⟨x, ?_, (Subgroup.orderOf_coe x).trans hx⟩
  rw [← hvq]
  apply le_normalizer_comap q
  exact le_normalizer_map A5.subtype x.property

open GorensteinWalter Matrix
namespace Frame

variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}
variable (c : Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)
variable [Finite (innerModel F σ)]

/-- A cubic in either actual centralizer normalizes both marked ambient subgroups.
No intersection, fusion, generation or escape hypothesis is required. -/
theorem exists_local_normalizer_cubic (i : Bool) :
    ∃ x : innerModel F σ, x ∈ c.centralizerAt i ∧
      x ∈ normalizer (c.small hF hσ i : Set _) ∧
      x ∈ normalizer (c.large hF hσ i : Set _) ∧ orderOf x = 3 := by
  let K := FixedPoints.subfield (zpowers σ) F
  have hK : Nat.card K = 5 := fixedSubfield_card hF σ
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).1
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
  obtain ⟨e⟩ := Theory.PSL2.exists_pgl2_five_equiv K hK
  let C := c.centralizerAt i
  let π := c.projection hF hσ i
  let q : C →* Equiv.Perm (Fin 5) := e.toMonoidHom.comp π
  have hq : Function.Surjective q := e.surjective.comp
    ((projectiveProjection_surjective hF σ hσ).comp (c.comparisonAt i).surjective)
  have hk : IsPGroup 2 q.ker := by
    let j : q.ker →* (projectiveProjection hF σ hσ).ker :=
      ((c.comparisonAt i).toMonoidHom.comp q.ker.subtype).codRestrict _ (by
        intro x
        apply e.injective
        exact x.property.trans (map_one e).symm)
    apply (projectiveProjection_two_kernel hF σ hσ).of_injective j
    intro x y h
    exact Subtype.ext ((c.comparisonAt i).injective (congrArg Subtype.val h))
  let T : Sylow 2 C := c.T.subtype (c.sylow_le i)
  have hA : (alternatingGroup (Fin 5)).comap q =
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range.comap π := by
    ext x
    change e (π x) ∈ alternatingGroup (Fin 5) ↔
      π x ∈ (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range
    rw [← Theory.PSL2.pgl2_five_equiv_maps_psl K hK e, mem_map_equiv]
    simp only [MulEquiv.symm_apply_apply]
  have hlarge : (((T : Subgroup C) ⊓ (alternatingGroup (Fin 5)).comap q).map
      C.subtype) = c.large hF hσ i := by
    rw [Subgroup.map_inf _ _ C.subtype C.subtype_injective, hA]
    have hT : (T : Subgroup C).map C.subtype = (c.T : Subgroup (innerModel F σ)) := by
      change ((c.T : Subgroup (innerModel F σ)).subgroupOf C).map C.subtype = _
      rw [subgroupOf_map_subtype, inf_eq_left.mpr (c.sylow_le i)]
    rw [hT]
    rfl
  obtain ⟨x, hx, ho⟩ := exists_cubic_normalizer_preimage q hq hk T
  have hxl : (x : innerModel F σ) ∈ normalizer (c.large hF hσ i : Set _) := by
    rw [← hlarge]
    exact le_normalizer_map C.subtype ⟨x, hx, rfl⟩
  refine ⟨x, x.property, ?_, hxl, (Subgroup.orderOf_coe x).trans ho⟩
  apply inf_normalizer_le_normalizer_inf
  refine ⟨hxl, ?_⟩
  rw [map_subtype_commutator]
  exact normalizer_commutator_ge_left C C x.property

end Frame
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry
