module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointCoreNormalizer
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PointResidualMovement
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockSylowOuter
public import Theory.GroupTheory.CyclicNormalOddQuotient.CyclicImage
/-!
# The noncyclic original point-Sylow quotient

The literal C_L(z) map takes T intersect L onto a Sylow two-subgroup of
the even four-block stabilizer. Its image modulo the intrinsic two-core
is noncyclic. Restricting O₂(L₁T) to C_L(z) lies in O₂(C_L(z)), so no map
from the original T to a cyclic group can have kernel contained in R₁.
The map and full original Sylow are retained throughout the comparison.

Source: Aschbacher--Smith 12.6.31, printed p.836, refs/quasithin.pdf.
The cyclic outer-action application is in AbelianNormalOuter.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- No cyclic image of the original Sylow group can have kernel in O₂(L₁T). -/
theorem SourceHypothesis.original_point_sylow_cyclic_kernel_impossible
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {X : Type*} [Group X] [IsCyclic X] (f : T →* X)
    (hk : f.ker ≤ ((D.fullSetup hZ T z).R₁).subgroupOf T) : False := by
  let E := D.fullSetup hZ T z
  let C := L ⊓ E.Gz
  have hTC : (T : Subgroup G) ≤ E.Gz := hTz.trans
    (normalizer_le_centralizer_of_card_two E.V₁ (E.point_card hz))
  have hnC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf S.chosen.sylow_normalizes_component (hTC.trans E.Gz.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  let J := C ⊔ (T : Subgroup G)
  have hCJ : C ≤ J := le_sup_left
  let : (C.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le C.le_normalizer hnC)
  obtain ⟨P₀,hP₀⟩ := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal
    (C.subgroupOf J)
  let e := subgroupOfEquivOfLe hCJ
  let P := P₀.mapSurjective (f := e.toMonoidHom) e.surjective
  have hP : (P : Subgroup C) = (T : Subgroup G).subgroupOf C := by
    change (P₀ : Subgroup (C.subgroupOf J)).map e.toMonoidHom = _
    rw [hP₀]
    ext c
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ha
    · intro ht
      exact ⟨⟨⟨c,hCJ c.property⟩,c.property⟩,ht,rfl⟩
  let i : P →* T := (C.subtype.comp (P : Subgroup C).subtype).codRestrict T (fun x => hP.le x.property)
  obtain ⟨_,a,ha,_,_⟩ := S.original_point_stabilizer_map D hZ z hz hTz
  let q := QuotientGroup.mk' (pCore 2 BinaryPermutation.TerminalOrthogonal.FourBlockResidual.P)
  let b := q.comp a
  let g := b.subgroupMap (P : Subgroup C)
  have hCE : C ≤ E.L₁ ⊔ (T : Subgroup G) := by
    rw [S.original_point_join_eq D hZ z hz hTz]
    exact le_inf (inf_le_left.trans le_sup_left) inf_le_right
  have hg : (f.comp i).ker ≤ g.ker := by
    intro x hx
    have hR : ((x : C) : G) ∈ E.R₁ := hk hx
    have hc : ((x : C) : G) ∈ C.pCoreIn 2 :=
      (inf_pCoreIn_le_of_le 2 hCE) ⟨x.val.property,hR⟩
    have hc' : (x : C) ∈ pCore 2 C := by
      obtain ⟨y,hy,he⟩ := hc
      exact (Subtype.ext he : y = x.val) ▸ hy
    have hm : (pCore 2 C).map a ≤ pCore 2 BinaryPermutation.TerminalOrthogonal.FourBlockResidual.P :=
      le_sSup ⟨(inferInstance : (pCore 2 C).Normal).map a ha,pCore_isPGroup.map a⟩
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr (hm (mem_map_of_mem a hc'))
  have hcyc : IsCyclic ((P : Subgroup C).map b) :=
    isCyclic_of_surjective_of_ker_le_cyclic (f.comp i) g (b.subgroupMap_surjective _) hg
  apply BinaryPermutation.TerminalOrthogonal.FourBlockResidual.sylow_core_image_not_cyclic
    (P.mapSurjective (f := a) ha)
  change IsCyclic (((P : Subgroup C).map a).map q)
  rw [map_map]
  exact hcyc
end CFSG.Quasithin.Chapter12.Section06
