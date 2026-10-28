module

public import Theory.SpecificGroups.SU3.GraphFixedSylowCenters
public import Theory.SpecificGroups.SU3.EvenRootPairs
public import BenderSuzuki.External.Huppert.II.theorem_10_13
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# A marked linear block through the unitary Sylow center

The graph-fixed SL₂ block has a Sylow two-subgroup equal to the whole
center of an ambient unitary Sylow subgroup. Conjugate that construction to
the prescribed Sylow. Its intersection with the block is precisely the
block Sylow, by maximality. The ambient normalizer of the center equals
the normalizer of the Sylow: otherwise two distinct Sylow subgroups would
generate the whole simple group while centralizing that nontrivial center.
Thus the original ambient Borel intersection is exactly the block Borel.

Source: Aschbacher--Smith E.2.7, printed p.218, Bender-group paragraph;
the concrete block and root centers are Huppert II.10.12.
-/

public section
noncomputable section
open Subgroup Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.TwoConjugateWitness

private theorem center_image_centralized {G : Type*} [Group G] (S : Subgroup G) :
    S ≤ centralizer ((center S).map S.subtype : Set G) := by
  intro s hs
  apply mem_centralizer_iff.mpr
  rintro _ ⟨z, hz, rfl⟩
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨s, hs⟩).symm

private theorem center_normalizer_eq_of_generation
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G)
    (hne : (center S).map (S : Subgroup G).subtype ≠ ⊥)
    (hgen : ∀ Q : Sylow 2 G, S ≠ Q → (S : Subgroup G) ⊔ Q = ⊤) :
    normalizer ((center S).map (S : Subgroup G).subtype : Set G) =
      normalizer (S : Set G) := by
  let Z := (center S).map (S : Subgroup G).subtype
  apply le_antisymm
  · intro g hg
    let f := (MulAut.conj g).toMonoidHom
    let Q := S.mapSurjective (f := f) (MulAut.conj g).surjective
    have hZ : Z.map f = Z := mem_normalizer_iff_map_conj_eq.mp hg
    have hCQ : Q ≤ centralizer (Z : Set G) := by
      rw [map_embeddedCenter (S : Subgroup G) f (MulAut.conj g).injective] at hZ
      rw [← hZ]
      exact center_image_centralized (Q : Subgroup G)
    by_cases he : S = Q
    · apply mem_normalizer_iff_map_conj_eq.mpr
      exact congrArg Sylow.toSubgroup he.symm
    · have hC : centralizer (Z : Set G) = ⊤ := top_unique (by
        rw [← hgen Q he]
        exact sup_le (center_image_centralized (S : Subgroup G)) hCQ)
      have hZC : Z ≤ center G := centralizer_eq_top_iff_subset.mp hC
      have hc : center G = ⊤ := by
        rcases (inferInstance : (center G).Normal).eq_bot_or_eq_top with hc | hc
        · exact False.elim (hne (bot_unique (hc ▸ hZC)))
        · exact hc
      let : IsMulCommutative G := center_eq_top_iff.mp hc
      exact le_normalizer_of_normal (mem_top g)
  · intro g hg
    have he : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = S := by
      exact mem_normalizer_iff_map_conj_eq.mp hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh := map_embeddedCenter (S : Subgroup G) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
    rw [he] at hh
    exact hh

private instance {E : Type*} [Field E] [Finite E] : Finite (ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

variable {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

omit [CharP E 2] in
include hn hcard hfixed in
/-- The original unitary Sylow normalizer is determined by its whole center. -/
theorem sylow_center_normalizer (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hne : (center S).map (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype ≠ ⊥) :
    normalizer ((center S).map (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
    (Nat.pow_le_pow_right (by decide) hn)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    External.huppert_II_10_13 J (2 ^ n) hq hcard hfixed
  exact center_normalizer_eq_of_generation S hne (fun Q hQ =>
    EvenRootPairs.sylow_sup_eq_top J (by omega) hcard
      (External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed) S Q hQ)

/-- One concrete linear block, retaining the prescribed ambient Sylow center
and the original normalizer intersection. -/
structure MarkedBlock (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) (n : ℕ) where
  subgroup : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)
  equiv : subgroup ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 n)
  sylow : Sylow 2 subgroup
  center_eq : (sylow : Subgroup subgroup).map subgroup.subtype =
    (center S).map (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype
  sylow_eq : (sylow : Subgroup subgroup) =
    (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subgroupOf subgroup
  normalizer_eq : normalizer (sylow : Set subgroup) =
    (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))).subgroupOf subgroup

include hJ hn hcard hfixed in
/-- Construct the marked rank-one block on the actual projective unitary
carrier, without a subgroup-recognition or embedding premise. -/
theorem exists_marked_block (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hne : (center S).map (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype ≠ ⊥) :
    Nonempty (MarkedBlock J S n) := by
  let W := (J.projectiveGraphAut hJ).fixedSubgroup
  let P : Sylow 2 W := default
  obtain ⟨S₀, hS₀⟩ := GraphFixedSylowCenters.exists_sylow_center_eq J hJ hn hcard hfixed P
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S₀ S
  let f := (MulAut.conj c).toMonoidHom
  let L := W.map f
  let d := W.equivMapOfInjective f (MulAut.conj c).injective
  let Q := P.mapSurjective (f := d.toMonoidHom) d.surjective
  have hS : (S₀ : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map f = S :=
    congrArg Sylow.toSubgroup hc
  have hcenter : (Q : Subgroup L).map L.subtype =
      (center S).map (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype := by
    change ((P : Subgroup W).map d.toMonoidHom).map L.subtype = _
    have hd : L.subtype.comp d.toMonoidHom = f.comp W.subtype := rfl
    rw [Subgroup.map_map, hd, ← Subgroup.map_map, ← hS₀, map_embeddedCenter _ f (MulAut.conj c).injective, hS]
  have hQS : (Q : Subgroup L) ≤ (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subgroupOf L := by
    apply map_le_iff_le_comap.mp
    rw [hcenter]
    exact map_subtype_le _
  have hQ : (Q : Subgroup L) = (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subgroupOf L :=
    (Q.is_maximal' S.isPGroup'.comap_subtype hQS).symm
  have hN : normalizer (Q : Set L) =
      (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))).subgroupOf L := by
    rw [← sylow_center_normalizer J hn hcard hfixed S hne, ← hcenter,
      subgroupOf_normalizer_eq (map_subtype_le _)]
    congr 1
    rw [← Q.coe_coe]
    exact congrArg (fun A : Subgroup L => (A : Set L))
      (comap_map_eq_self_of_injective L.subtype_injective (Q : Subgroup L)).symm
  let K := FixedBy.subfield E J.conj
  let := ZMod.algebra K 2
  let eK : K ≃+* GaloisField 2 n :=
    (GaloisField.algEquivGaloisField 2 n (show Nat.card K = 2 ^ n from hfixed)).toRingEquiv
  let eW : W ≃* SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    ((J.projectiveGraphFixedEquivSpecial hJ).trans (J.specialGraphFixedEquivSL2 hJ)).trans
      (Atlas.fieldEquivSL 2 eK)
  exact ⟨⟨L, d.symm.trans eW, Q, hcenter, hQ, hN⟩⟩

end BenderSuzuki.MatrixGroups.HermitianForm.TwoConjugateWitness
end
