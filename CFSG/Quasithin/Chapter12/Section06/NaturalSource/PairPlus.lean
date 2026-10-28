module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.PairGeometry
public import Theory.GroupTheory.ExtraspecialSquare
public import Theory.GroupTheory.DihedralCentralProductFourSix

/-!
# Plus type of the original pair seed

The actual extraspecial seed of order 512 contains the original elementary
V5 of order 32 and its center V1. Intrinsic dihedral splitting identifies it
with the explicit fourfold central product of dihedral eights.

The square form on the same central quotient is nondegenerate of dimension
eight. The two original seeds have singular images of dimension four;
they generate the quotient and hence are complementary. No type, basis,
or replacement-module hypothesis is assumed. Earlier point, fixed-space,
intersection and nonsingular-centralizer inputs remain explicit.
Source: Aschbacher--Smith F.9.5(6.ii), pp.319--320, and 12.6.26, p.831.
-/

public section
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup Theory.GroupTheory
open ChapterF.Section09.Setup.Hypothesis
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The actual non-two pair seed is the fourfold plus central product.
Its original first seed gives a singular four-space in its nondegenerate
binary central quotient of dimension eight. -/
theorem SourceHypothesis.original_non_two_pair_plus
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (g : G) (hg : g ∈ H)
    (hn : ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let E := D.fullSetup hZ T z
    let P := E.pairSeed g
    Nonempty (P ≃* DihedralCentralProductFourSix.FourModel) ∧
      ∃ hs : IsExtraspecial 2 P, letI := hs;
        (ExtraspecialSquare.form P).polarBilin.Nondegenerate ∧
        Module.finrank (ZMod 2) (ExtraspecialSquare.Space P) = 8 ∧
        Module.finrank (ZMod 2) (ExtraspecialSquare.imageSpace P (E.V₅.subgroupOf P)) = 4 ∧
        (∀ v ∈ ExtraspecialSquare.imageSpace P (E.V₅.subgroupOf P), ExtraspecialSquare.form P v=0) ∧
        Module.finrank (ZMod 2) (ExtraspecialSquare.imageSpace P
          ((E.V₅.map (MulAut.conj g).toMonoidHom).subgroupOf P)) = 4 ∧
        (∀ v ∈ ExtraspecialSquare.imageSpace P ((E.V₅.map (MulAut.conj g).toMonoidHom).subgroupOf P),
          ExtraspecialSquare.form P v=0) ∧
        IsCompl (ExtraspecialSquare.imageSpace P (E.V₅.subgroupOf P))
          (ExtraspecialSquare.imageSpace P ((E.V₅.map (MulAut.conj g).toMonoidHom).subgroupOf P)) := by
  let E := D.fullSetup hZ T z
  let P := E.pairSeed g
  obtain ⟨hc,hcard,hs,_,_⟩ := S.original_non_two_pair_geometry D hZ z hz hTV hTz hbound hns hH g hg hn
  let : IsExtraspecial 2 P := hs
  let A := E.V₅.subgroupOf P
  have h5P : E.V₅ ≤ P := le_sup_left
  let : IsElementaryAbelian 2 E.V := E.elementary
  let : IsElementaryAbelian 2 E.V₅ := IsElementaryAbelian.of_le E.V₅_le
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf h5P
  have ha : Nat.card A = 2^5 :=
    (Nat.card_congr (subgroupOfEquivOfLe h5P).toEquiv).trans (E.perpendicular_card hz)
  have hza : center P ≤ A := by
    intro x hx
    exact E.V₁_le_V₅ (hc.le (mem_map_of_mem P.subtype hx))
  let B := E.V₅.map (MulAut.conj g).toMonoidHom
  let C := B.subgroupOf P
  have hBP : B ≤ P := le_sup_right
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.subgroupOf hBP
  have hb : Nat.card C = 2^5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBP).toEquiv,
      card_map_of_injective (MulAut.conj g).injective,E.perpendicular_card hz]
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hzmap : E.V₁.map (MulAut.conj g).toMonoidHom = E.V₁ :=
    mem_normalizer_iff_map_conj_eq.mp
      ((h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)) hg)
  have hzc : center P ≤ C := by
    intro x hx
    exact (hzmap.symm.le.trans (map_mono E.V₁_le_V₅)) (hc.le (mem_map_of_mem P.subtype hx))
  have hgen : A ⊔ C = ⊤ := by
    rw [←subgroupOf_sup h5P hBP]
    exact subgroupOf_self P
  have hd := ExtraspecialSquare.space_finrank P 8 hcard
  have hda := ExtraspecialSquare.imageSpace_finrank P A hza 4 ha
  have hdb := ExtraspecialSquare.imageSpace_finrank P C hzc 4 hb
  have hsum : ExtraspecialSquare.imageSpace P A ⊔ ExtraspecialSquare.imageSpace P C = ⊤ := by
    rw [←ExtraspecialSquare.imageSpace_sup,hgen,ExtraspecialSquare.imageSpace_top]
  have hcompl : IsCompl (ExtraspecialSquare.imageSpace P A) (ExtraspecialSquare.imageSpace P C) := by
    refine ⟨disjoint_iff.mpr ?_,codisjoint_iff.mpr hsum⟩
    apply Submodule.finrank_eq_zero.mp
    have hh := Submodule.finrank_sup_add_finrank_inf_eq
      (ExtraspecialSquare.imageSpace P A) (ExtraspecialSquare.imageSpace P C)
    rw [hsum,finrank_top,hd,hda,hdb] at hh
    omega
  refine ⟨⟨DihedralCentralProductFourSix.fourRecognition hcard A ha hza⟩,
    hs,ExtraspecialSquare.polar_nondegenerate P,ExtraspecialSquare.space_finrank P 8 hcard,
    hda,ExtraspecialSquare.imageSpace_singular P A,hdb,
    ExtraspecialSquare.imageSpace_singular P C,hcompl⟩

end CFSG.Quasithin.Chapter12.Section06
