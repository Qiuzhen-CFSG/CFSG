module
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.SylowNormalizedEnlargement
public import Stellmacher.BaumannTwoOvergroupTransport
public import Stellmacher.BaumannMap
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# A Sylow extension in a Baumann conjugate span

Suppose R lies in a Sylow two-subgroup T and contains Baum(T). If R is
Sylow in D and a Sylow Q of K·Baum(T) lies in its conjugate span under
a subgroup normalizing D, conjugate Q inside D into R. Baumann weak
closure makes this conjugator fix Baum(T), while normality fixes K.
The resulting Sylow of K·Baum(T) inside R enlarges to R in KR.

Source application: the S₅ alternative of Aschbacher–Smith 3.1.7,
printed pp.575–576. The index-two value is not needed by this transport.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem baumann_conjugate_eq_of_le (T : Sylow 2 G) (g : G)
    (h : (baumann (T : Subgroup G)).map (MulAut.conj g).toMonoidHom ≤ T) :
    (baumann (T : Subgroup G)).map (MulAut.conj g).toMonoidHom =
      baumann (T : Subgroup G) := by
  let P := T.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have he : baumann (P : Subgroup G) =
      (baumann (T : Subgroup G)).map (MulAut.conj g).toMonoidHom := by
    exact (baumann_map_injective _ (MulAut.conj g).injective _).symm
  exact he.symm.trans ((twoSubgroup_thompson_baumann_eq P T T.isPGroup' (he.le.trans h)).2.symm)

/-- Any two-subgroup in D is conjugate into its prescribed Sylow R. -/
theorem exists_conjugate_le_relative_sylow (D R Q : Subgroup G)
    (hR : Chapter1.IsSylowIn 2 R D) (hQ : IsPGroup 2 Q) (hQD : Q ≤ D) :
    ∃ g ∈ D, Q.map (MulAut.conj g).toMonoidHom ≤ R := by
  obtain ⟨S,hS⟩ := hR
  obtain ⟨P,hP⟩ := (hQ.comap_subtype : IsPGroup 2 (Q.subgroupOf D)).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D P S
  refine ⟨g,g.property,?_⟩
  have he : (P : Subgroup D).map (MulAut.conj g).toMonoidHom = S := by
    have hh := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul] at hh
    exact hh
  have hm := map_mono (f := D.subtype) ((map_mono hP).trans_eq he)
  rw [hS, map_map] at hm
  have hc : D.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (g : G)).toMonoidHom.comp D.subtype := rfl
  rw [hc, ← map_map] at hm
  have hmap : (Q.comap D.subtype).map D.subtype = Q := map_subgroupOf_eq_of_le hQD
  rw [hmap] at hm
  exact hm

/-- A normal span in D supplies a suitable Sylow conjugate inside R. -/
theorem sylow_sup_of_baumann_span (T : Sylow 2 G) (K D R E Q : Subgroup G)
    [K.Normal] (hRT : R ≤ T) (hBR : baumann (T : Subgroup G) ≤ R)
    (hR : Chapter1.IsSylowIn 2 R D) (hED : E ≤ normalizer (D : Set G))
    (hQ : Chapter1.IsSylowIn 2 Q (K ⊔ baumann (T : Subgroup G)))
    (hBQ : baumann (T : Subgroup G) ≤ Q)
    (hspan : Q ≤ conjugateSpanBy (baumann (T : Subgroup G)) E) :
    Chapter1.IsSylowIn 2 R (K ⊔ R) := by
  let B := baumann (T : Subgroup G)
  have hQD : Q ≤ D := hspan.trans (conjugateSpanBy_le
    (hBR.trans (Chapter1.isSylowIn_iff.mp hR).2.1) hED)
  obtain ⟨g,hg,hgQ⟩ := exists_conjugate_le_relative_sylow D R Q hR
    (Chapter1.isSylowIn_iff.mp hQ).1 hQD
  have heB : B.map (MulAut.conj g).toMonoidHom = B :=
    baumann_conjugate_eq_of_le T g ((map_mono hBQ).trans (hgQ.trans hRT))
  have heK : K.map (MulAut.conj g).toMonoidHom = K :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
  have hs := (Chapter1.IsSylowIn.map_iff (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).mpr hQ
  rw [Subgroup.map_sup,heK,heB] at hs
  have htop : (K ⊔ B) ⊔ R = K ⊔ R := by rw [sup_assoc, sup_eq_right.mpr hBR]
  have hn : R ≤ normalizer ((K ⊔ B : Subgroup G) : Set G) :=
    (le_inf (le_normalizer_of_normal : R ≤ normalizer (K : Set G))
      ((hRT.trans (T : Subgroup G).le_normalizer).trans (normalizer_le_normalizer_baumann _))).trans
        (normalizer_inf_normalizer_le_normalizer_sup K B)
  have hQK : Q.map (MulAut.conj g).toMonoidHom ≤ K ⊔ B :=
    (Chapter1.isSylowIn_iff.mp hs).2.1
  have hjoin : (K ⊔ B) ⊔ Q.map (MulAut.conj g).toMonoidHom = K ⊔ B :=
    sup_eq_left.mpr hQK
  have hs' : Chapter1.IsSylowIn 2 (Q.map (MulAut.conj g).toMonoidHom)
      ((K ⊔ B) ⊔ Q.map (MulAut.conj g).toMonoidHom) := hjoin.symm ▸ hs
  obtain ⟨P',hP'⟩ := hs'
  have hout : Chapter1.IsSylowIn 2 R ((K ⊔ B) ⊔ R) :=
    IsPGroup.exists_sylow_sup_of_smaller_sylow (K ⊔ B)
      (Q.map (MulAut.conj g).toMonoidHom) R (T.isPGroup'.to_le hRT) hgQ hn P' hP'
  exact htop ▸ hout
end CFSG.Quasithin.ChapterB
