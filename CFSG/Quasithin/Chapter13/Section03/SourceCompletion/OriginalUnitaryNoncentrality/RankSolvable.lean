module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalUnitaryNoncentrality.ResidualIntersection
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound.OddMover
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import Theory.GroupTheory.PrimeRankNormalPair

/-!
# Solvability and odd rank from the unitary intersection

The centralizing residual is normal in the plane centralizer and subnormal
in its normalizer. The genuine SQTK quotient there and the odd conjugator
exclude nonsolvable components. Rank addition on the mutually normalizing
conjugates bounds every odd-prime rank by one. All quotients and relative
subnormality are in that original plane normalizer.

Source: Aschbacher--Smith 13.3.14(b), printed p.891.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Noncentrality
variable {G : Type*} [Group G] [Finite G]

theorem unitary_residual_solvable_of_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (Z B U H : Subgroup G) (hZB : Z ≤ B) (hBU : B ≤ U)
    (hH : H = normalizer (Z : Set G)) (hB : Nat.card B = 4)
    (g : G) (hgB : g ∈ normalizer (B : Set G)) (hodd : Odd (orderOf g))
    (hI : let Y := centralizingResidual (conjugateSpanBy U H)
      IsPGroup 2 (Y ⊓ Y.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    Group.IsSolvable (centralizingResidual (conjugateSpanBy U H)) := by
  let Y := centralizingResidual (conjugateSpanBy U H)
  let C := centralizer (B : Set G)
  let N := normalizer (B : Set G)
  have hYC : Y ≤ C :=
    (centralizingResidual_le_seed_centralizer U H).trans (centralizer_le hBU)
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hCBH : C ≤ H := by
    rw [hH]
    exact (centralizer_le hZB).trans (Subgroup.centralizer_le_normalizer _)
  have hCY : C ≤ normalizer (Y : Set G) :=
    hCBH.trans (normalizes_centralizingResidual U H)
  let A := Y.subgroupOf N
  let Cn := C.subgroupOf N
  have hAB : A ≤ Cn := fun _ hx => hYC hx
  have hBN : Cn.Normal := inferInstance
  have hAN : (A.subgroupOf Cn).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hAB).mpr
    apply le_normalizer_iff.mpr
    intro c hc a ha
    exact le_normalizer_iff.mp hCY c.val hc a.val ha
  have hAsub : A.IsSubnormal := .step A Cn hAB hBN.isSubnormal hAN
  let gn : N := ⟨g,hgB⟩
  have hgn : Odd (orderOf gn) := by
    rw [← orderOf_injective N.subtype N.subtype_injective]
    exact hodd
  have hIn : IsPGroup 2 (A ⊓ A.map (MulAut.conj gn).toMonoidHom : Subgroup N) := by
    apply hI.comap_subtype.to_le
    rintro x ⟨hx,⟨y,hy,hyx⟩⟩
    exact ⟨hx,⟨y.val,hy,congrArg Subtype.val hyx⟩⟩
  have hne : B ≠ ⊥ := by intro h; have hc := hB; simp [h] at hc
  have htwo : IsPGroup 2 B := IsPGroup.of_card (n := 2) hB
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk hG
    (Chapter1.mem_H_of_isTwoLocal (show IsTwoLocal N from ⟨B,hne,htwo,rfl⟩))
  let := ChapterA.Section03.ComponentOrbitBound.isSolvable_of_subnormal_odd_conjugate_intersection
    hQ A hAsub gn hgn hIn
  exact Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (hYC.trans hCN)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (hYC.trans hCN)).symm.injective

/-- Rank addition on the two literal mutually normalizing residuals. -/
theorem unitary_residual_odd_rank_of_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (Z B U H : Subgroup G) (hZB : Z ≤ B) (hBU : B ≤ U)
    (hH : H = normalizer (Z : Set G)) (hB : Nat.card B = 4)
    (g : G) (hgB : g ∈ normalizer (B : Set G))
    (hI : let Y := centralizingResidual (conjugateSpanBy U H)
      IsPGroup 2 (Y ⊓ Y.map (MulAut.conj g).toMonoidHom : Subgroup G))
    (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    primeRank p (centralizingResidual (conjugateSpanBy U H)) ≤ 1 := by
  let := Fact.mk hp
  let Y := centralizingResidual (conjugateSpanBy U H)
  let Yg := Y.map (MulAut.conj g).toMonoidHom
  obtain ⟨hlocal,hYYg,hYgY⟩ := unitary_residual_conjugate_local_data Z B U H hZB hBU hH g hgB
  have hr := Theory.GroupTheory.primeRank_add_le_of_normalizes_of_twoGroup_intersection
    ho Y Yg hYYg hYgY hI
  have he : primeRank p Yg = primeRank p Y :=
    (primeRank_congr p (Y.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective)).symm
  have hne : B ≠ ⊥ := by intro h; simp [h] at hB
  have htwo : IsPGroup 2 B := IsPGroup.of_card (n := 2) hB
  have hbound := isQuasithin_iff_twoLocal.mp hG.quasithin
      (normalizer (B : Set G)) ⟨B,hne,htwo,rfl⟩ p hp ho
  have hmono : primeRank p (Y ⊔ Yg : Subgroup G) ≤ primeRank p (normalizer (B : Set G)) :=
    primeRank_mono p (hlocal.trans (Subgroup.centralizer_le_normalizer _))
  have hh : 2 * primeRank p Y ≤ 2 := calc
    _ = primeRank p Y + primeRank p Yg := by omega
    _ ≤ primeRank p (Y ⊔ Yg : Subgroup G) := hr
    _ ≤ primeRank p (normalizer (B : Set G)) := hmono
    _ ≤ 2 := hbound
  change primeRank p Y ≤ 1
  omega
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
