module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.NoncentralComponentSource
public import Theory.GroupTheory.DisjointSupplementIntersection

/-!
# The centralizer and two-core of the fixed conjugate span

The fixed-block actor has centralizer contained in Z(Lₛ) times the original
central involution. Its outside conjugate has a disjoint fixed center, so the
invariant centralizer and the two-core meet both products only in that
involution subgroup. These constructors consume the actual fixed-block marks;
no component model or full-Sylow assumption is used.
Source: Aschbacher–Smith 2.4.23(5), printed pp.537–538.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open Theory.GroupTheory
variable {G : Type*} [Group G]
/-- The two disjoint fixed centers remove every centralizer element except
for the common central supplement. -/
theorem fixed_pair_centralizer_eq
    (L R S T D : Subgroup G) {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (hST : S≤T) (hi : S.relIndex T=2) (hSL : S≤normalizer (L:Set G))
    (hTR : T≤normalizer (R:Set G))
    (x:G) (hxT:x∈T) (hxS:x∉S)
    (hnc : ¬ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer ((ChapterC.blockU L).map L.subtype : Set G))
    (hZR : (center L).map L.subtype≤R)
    (hRD : Disjoint R D) (hxD : x∈normalizer (D:Set G))
    (hZZ : Disjoint ((center L).map L.subtype)
      (((center L).map L.subtype).map (MulAut.conj x⁻¹).toMonoidHom))
    (hcent : S⊓centralizer (L:Set G)≤(center L).map L.subtype⊔D) :
    let K := L⊔L.map (MulAut.conj x⁻¹).toMonoidHom
    D≤T⊓centralizer (K:Set G) → T⊓centralizer (K:Set G)=D := by
  dsimp only
  let K := L⊔L.map (MulAut.conj x⁻¹).toMonoidHom
  let Z := (center L).map L.subtype
  let C := T⊓centralizer (K:Set G)
  intro hDC
  have hTK := index_two_normalizes_pair S T L hST hi x hxT hxS hSL
  have hTC : T≤normalizer (C:Set G) :=
    (le_inf T.le_normalizer (hTK.trans (normalizer_le_normalizer_centralizer K))).trans
      inf_normalizer_le_normalizer_inf
  have hCL : C≤centralizer (L:Set G) :=
    inf_le_right.trans (centralizer_le (show L≤K from le_sup_left))
  have hCS : C≤S := by
    apply (le_inf inf_le_left ?_).trans (fixed_module_normalizer_le L S T hL hi hSL x hxT hxS hnc)
    exact (hCL.trans (centralizer_le (map_subtype_le _))).trans (Subgroup.centralizer_le_normalizer _)
  have hCD : C≤D := by
    apply le_supplement_of_invariant_disjoint_conjugate C Z R D
      ((le_inf hCS hCL).trans hcent) hZR hRD ?_ (MulAut.conj x⁻¹)
      (mem_normalizer_iff_map_conj_eq.mp (hTC (T.inv_mem hxT)))
      (mem_normalizer_iff_map_conj_eq.mp (hTR (T.inv_mem hxT)))
      (mem_normalizer_iff_map_conj_eq.mp ((normalizer (D:Set G)).inv_mem hxD)) hZZ
    exact ((map_subtype_le _).trans (le_centralizer_iff.mp (hDC.trans hCL))).trans
      (Subgroup.centralizer_le_normalizer _)
  exact le_antisymm hCD hDC

/-- Centralization of the fixed natural block and the same disjoint-center
argument identify the full ambient two-core with the central supplement. -/
theorem fixed_pair_twoCore_eq
    (L R S T X D : Subgroup G) {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    [Group.IsPerfect L] (hLX:L≤X) (hTX:T≤X)
    (hi : S.relIndex T=2) (hSL : S≤normalizer (L:Set G))
    (hcore : pCore 2 L=ChapterC.blockU L)
    (hUR : (ChapterC.blockU L).map L.subtype≤R) (hRL:R≤L)
    (hTR : T≤normalizer (R:Set G)) (hQT:twoCore X≤T)
    (x:G) (hxT:x∈T) (hxS:x∉S)
    (hnc : ¬ ((ChapterC.blockU L).map L.subtype).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer ((ChapterC.blockU L).map L.subtype : Set G))
    (hZR : (center L).map L.subtype≤R)
    (hRD : Disjoint R D) (hxD : x∈normalizer (D:Set G))
    (hZZ : Disjoint ((center L).map L.subtype)
      (((center L).map L.subtype).map (MulAut.conj x⁻¹).toMonoidHom))
    (hcent : S⊓centralizer (L:Set G)≤(center L).map L.subtype⊔D)
    (hD : IsPGroup 2 D) (hDX : D≤X) (hXD : X≤centralizer (D:Set G)) :
    twoCore X=D := by
  let Q := twoCore X
  have hTS := fixed_module_normalizer_le L S T hL hi hSL x hxT hxS hnc
  have hQL : Q≤centralizer (L:Set G) := le_centralizer_iff.mp
    (core_centralizes_of_fixed_pair L R S T X hL hLX hTX hcore hUR hRL hTR hTS hSL hQT x hxT hnc)
  have hQS : Q≤S :=
    (le_inf hQT ((hQL.trans (centralizer_le (map_subtype_le _))).trans
      (Subgroup.centralizer_le_normalizer _))).trans hTS
  have hQD : Q≤D := by
    apply le_supplement_of_invariant_disjoint_conjugate Q ((center L).map L.subtype) R D
      ((le_inf hQS hQL).trans hcent) hZR hRD ?_ (MulAut.conj x⁻¹)
      (mem_normalizer_iff_map_conj_eq.mp (le_normalizer_twoCore X (X.inv_mem (hTX hxT))))
      (mem_normalizer_iff_map_conj_eq.mp (hTR (T.inv_mem hxT)))
      (mem_normalizer_iff_map_conj_eq.mp ((normalizer (D:Set G)).inv_mem hxD)) hZZ
    exact ((map_subtype_le _).trans (hLX.trans hXD)).trans (Subgroup.centralizer_le_normalizer _)
  exact le_antisymm hQD (le_pCoreIn_of_normalizes hD hDX
    (hXD.trans (Subgroup.centralizer_le_normalizer _)))
end CFSG.Quasithin.Chapter2.LinearShadows.Single
