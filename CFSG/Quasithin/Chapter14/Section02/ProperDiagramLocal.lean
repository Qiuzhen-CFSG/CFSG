module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramModelGeometry
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.SylowNormalSupplementRecognition
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels
/-!
# Local component and Sylow supplement for a selected diagram residual

The residual selected from a proper diagram parabolic is a perfect subgroup
whose 2-core quotient is a rank-two projective special linear group.  This
module records the two local consequences needed by the source 14.2.9
assembly: it is a C-component of its join with the Sylow subgroup, and the
2-subgroup obtained by intersecting the normalizer is Sylow in that join.

The component step is the standard perfect-central-quotient criterion.  The
Sylow step is the normal-supplement lemma (C.2.7) after transporting the
Sylow intersection through `subgroupOf`.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
variable {H : Type*} [Group H] [Finite H]

private theorem perfect_pPerfect (L : Type*) [Group L] [Finite L] [Group.IsPerfect L] :
    IsPPerfect 2 L := by
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (L ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (L ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (L ⧸ N) inferInstance

theorem perfect_binary_rank_one_local_component
    (L S : Subgroup H) (hn : S ≤ normalizer (L : Set H))
    (hp : Group.IsPerfect L) {F : Type} [Field F] [Finite F]
    (h4 : 4 ≤ Nat.card F)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    (L.subgroupOf (L ⊔ S)).IsCComponent := by
  let := hp
  let X := L ⧸ pCore 2 L
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  let : IsSimpleGroup X := e.isSimpleGroup
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hc : center X = ⊥ := by
    rcases (inferInstance : (center X).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp h)).elim
  let : IsQuasisimple X := { simple :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).isSimpleGroup }
  let A := L.subgroupOf (L ⊔ S)
  let d : A ≃* L := subgroupOfEquivOfLe (show L ≤ L ⊔ S from le_sup_left)
  let : IsQuasisimple ((L.subgroupOf (L ⊔ S)) ⧸ pCore 2 (L.subgroupOf (L ⊔ S))) :=
    IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm
  have hn' : (L.subgroupOf (L ⊔ S)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le L.le_normalizer hn)
  apply isCComponent_of_isPPerfect_of_quasisimple_core_quotient (p := 2) hn'.isSubnormal
  exact (perfect_pPerfect L).of_surjective d.symm.toMonoidHom d.symm.surjective

theorem sylow_in_normalized_join (L S : Subgroup H)
    (hn : S ≤ normalizer (L : Set H)) (hp : IsPGroup 2 S)
    (hs : Chapter1.IsSylowIn 2 (S ⊓ L) L) :
    Chapter1.IsSylowIn 2 S (L ⊔ S) := by
  let X := L ⊔ S
  let C := L.subgroupOf X
  let R := S.subgroupOf X
  let : C.Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le L.le_normalizer hn)
  obtain ⟨P,hP⟩ := hs
  let d : L ≃* C := (subgroupOfEquivOfLe (show L ≤ X from le_sup_left)).symm
  let P' := P.mapSurjective (f := d.toMonoidHom) d.surjective
  have hgen : C ⊔ R = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show L ≤ X from le_sup_left),
      map_subgroupOf_eq_of_le (show S ≤ X from le_sup_right),
      ← MonoidHom.range_eq_map, range_subtype]
  have hPR : (P' : Subgroup C).map C.subtype ≤ R := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    exact (show (y : H) ∈ S from
      (hP ▸ mem_map_of_mem L.subtype hy : (y : H) ∈ S ⊓ L).1)
  obtain ⟨Q,hQ⟩ := exists_sylow_eq_of_normal_supplement C R hp.comap_subtype hgen P' hPR
  refine ⟨Q,?_⟩
  rw [hQ,map_subgroupOf_eq_of_le (show S ≤ X from le_sup_right)]
end CFSG.Quasithin.Chapter14.Section02
