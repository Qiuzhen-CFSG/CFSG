module
public import CFSG.Quasithin.ChapterE.Section02.SolvableStructure.CubicActors
public import Theory.GroupAction.Extraspecial27DihedralActor
public import Theory.GroupTheory.PCoreOddJoin
public import Theory.GroupTheory.GeneralizedFitting.ResidualCentralizer
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The extraspecial residual and actual cyclic-four source image

Under the full E.2.1 escape hypothesis, a nontrivial two-residual of the
canonical core excludes the cyclic and elementary residual models: their
Frattini subgroup is trivial. Thus P=O²(H/O₂(H)) is extraspecial of order27,
and the canonical core image is Z(P). Its actual S₃/wreath quotient gives
a faithful dihedral Sylow actor. The center kernel is cyclic of order four.

Mapping the exact X=O²(J) and R=O₂(XT) through O₂(H) identifies R's image
with this Sylow centralizer. The map to H/J is injective on that two-group,
so the original action image of R is cyclic of order four, and R∩J=O₂(H).
No extraspecial model, cyclic-four image, kernel intersection, or faithful
actor conclusion is assumed by the final source theorem.

Source: Aschbacher–Smith, E.2.1 p.215 and original 13.2.9 p.881.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.SolvableMinimalParabolic
open ChapterB
variable {H : Type*} [Group H] [Finite H]
theorem extraspecial_of_cubicModels_and_core_residual
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (hm : CubicResidualModels H) (hne : pResidual 2 (minimalParabolicCore T hP) ≠ ⊥) :
    Nat.card (pResidual 2 (H ⧸ pCore 2 H)) = 27 ∧
      IsExtraspecial 3 (pResidual 2 (H ⧸ pCore 2 H)) ∧
      Nonempty (pResidual 2 (H ⧸ pCore 2 H) ≃* HeisenbergPrime 3) ∧
      minimalParabolicCoreImage T hP =
        (center (pResidual 2 (H ⧸ pCore 2 H))).map (pResidual 2 (H ⧸ pCore 2 H)).subtype := by
  let P := pResidual 2 (H ⧸ pCore 2 H)
  obtain ⟨p,hp,ho,hres,hq,hphi,_⟩ := minimalParabolic_solvable_structure T hP hs
  rw [← hres] at hphi
  have hexclude (he : IsElementaryAbelian 3 P) : False := by
    let := he
    let : Fact (IsPGroup 3 P) := ⟨IsElementaryAbelian.isPGroup 3 P⟩
    have him : minimalParabolicCoreImage T hP = ⊥ := by
      rw [hphi,frattiniAmbient,frattini_eq_bot_of_isElementaryAbelian (p := 3) (R := P),Subgroup.map_bot]
    have hle : minimalParabolicCore T hP ≤ pCore 2 H := by
      change (minimalParabolicCore T hP).map (QuotientGroup.mk' (pCore 2 H)) = ⊥ at him
      simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp him
    have hj2 : IsPGroup 2 (minimalParabolicCore T hP) := pCore_isPGroup.to_le hle
    have hb : pResidual 2 (minimalParabolicCore T hP) = ⊥ := by
      apply bot_unique
      exact pResidual_le_ker_of_isPGroup 2 (MonoidHom.id _) hj2
    exact hne hb
  rcases hm with ⟨hc,⟨e⟩⟩ | ⟨hc,⟨e⟩⟩ | ⟨hc,he,hmodel⟩
  · apply False.elim
    apply hexclude
    let : IsElementaryAbelian 3 (Multiplicative (ZMod 3)) := by
      refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
      exact Monoid.exponent_dvd_of_forall_pow_eq_one (by decide +kernel)
    exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  · apply False.elim
    apply hexclude
    let : IsElementaryAbelian 3 (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) := by
      refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
      exact Monoid.exponent_dvd_of_forall_pow_eq_one (by decide +kernel)
    exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  · let := he
    refine ⟨hc,he,hmodel,?_⟩
    rw [hphi,frattiniAmbient,IsExtraspecial.frattini_eq_center (p := 3)]
end CFSG.Quasithin.ChapterE.SolvableMinimalParabolic

namespace CFSG.Quasithin.ChapterE.SolvableMinimalParabolic
open ChapterB Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
variable {H : Type*} [Group H] [Finite H]
theorem core_residual_cyclicFour_of_models
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (hm : CubicResidualModels H) (hne : pResidual 2 (minimalParabolicCore T hP) ≠ ⊥)
    (ha : Nonempty ((H ⧸ minimalParabolicCore T hP) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∨
      Nonempty ((H ⧸ minimalParabolicCore T hP) ≃*
        RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)))) :
    let J := minimalParabolicCore T hP
    let X := (pResidual 2 J).map J.subtype
    let R := (X ⊔ (T : Subgroup H)).pCoreIn 2
    let q := QuotientGroup.mk' J
    pCore 2 H ≤ R ∧ pCore 2 H = R ⊓ J ∧
      IsCyclic (R.map q) ∧ Nat.card (R.map q) = 4 := by
  let Q := pCore 2 H
  let π := QuotientGroup.mk' Q
  let hπ := QuotientGroup.mk'_surjective Q
  let J := minimalParabolicCore T hP
  let X := (pResidual 2 J).map J.subtype
  let R := (X ⊔ (T : Subgroup H)).pCoreIn 2
  let P := pResidual 2 (H ⧸ Q)
  let Z := (center P).map P.subtype
  let S := T.mapSurjective hπ
  obtain ⟨hPcard,hPextra,hPmodel,hZeq⟩ := extraspecial_of_cubicModels_and_core_residual T hP hs hm hne
  let := hPextra
  have hJimage : J.map π = Z := hZeq
  have hZcard : Nat.card Z = 3 := by rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 3 P]
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  have hXimage : X.map π = Z := by
    rw [map_embedded_pResidual, hJimage]
    have ht : pResidual 2 Z = ⊤ := by
      apply top_unique
      intro z _
      exact mem_pResidual_of_orderOf_coprime ((hZp.orderOf_coprime (by decide : Nat.Coprime 3 2) z).symm)
    rw [ht, ← MonoidHom.range_eq_map, range_subtype]
  have hQJ : Q ≤ J := minimalParabolicTwoCore_le_core T hP
  let q := QuotientGroup.mk' J
  let f : (H ⧸ Q) →* (H ⧸ J) := QuotientGroup.lift Q q (by change Q ≤ (QuotientGroup.mk' J).ker; rwa [QuotientGroup.ker_mk'])
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective J y
    exact ⟨π x,rfl⟩
  have hcomp : f.comp π = q := rfl
  have hker : f.ker = Z := by
    rw [← hJimage]
    apply comap_injective hπ
    rw [MonoidHom.comap_ker,hcomp,QuotientGroup.ker_mk',comap_map_eq_self]
    simpa only [QuotientGroup.ker_mk'] using hQJ
  have htwo : pCore 2 (H ⧸ Q) = ⊥ := by
    rw [← pCore_map_mk'_eq_of_normal_isPGroup (p := 2) Q (pCore_isPGroup (G := H) (p := 2))]
    exact (Subgroup.map_eq_bot_iff _).mpr (by simp [Q])
  have hcentral : centralizer (P : Set (H ⧸ Q)) ≤ P := centralizer_pResidual_le_of_pCore_eq_bot htwo
  obtain ⟨hDcyc,hDcard⟩ := Extraspecial27Dihedral.centerSylow_cyclic_of_small_quotient P hPcard hcentral S f hf hker ha
  have hRimage : R.map π = (S : Subgroup (H ⧸ Q)) ⊓ centralizer (Z : Set (H ⧸ Q)) := by
    rw [map_pCoreIn_of_ker_isPGroup π (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup (p := 2) (G := H)),Subgroup.map_sup,hXimage]
    exact core_join_odd_eq_sylow_centralizer Z hZp S
  have hRcyc : IsCyclic (R.map π) := hRimage.symm ▸ hDcyc
  have hRcard : Nat.card (R.map π) = 4 := hRimage.symm ▸ hDcard
  have hQR : Q ≤ R := le_pCoreIn_of_normalizes pCore_isPGroup
    ((pCore_isPGroup.le_sylow_of_normal T).trans le_sup_right) le_normalizer_of_normal
  have hinter : Q = R ⊓ J := by
    apply le_antisymm (le_inf hQR hQJ)
    intro x hx
    have hd := (isPGroup_pCoreIn 2 (X ⊔ (T : Subgroup H))).map π |>.disjoint_of_coprime hZp (by decide : Nat.Coprime 2 3)
    have hxin : π x ∈ (R.map π) ⊓ Z := ⟨mem_map_of_mem π hx.1,hJimage ▸ mem_map_of_mem π hx.2⟩
    exact (QuotientGroup.eq_one_iff _).mp (hd.le_bot hxin)
  have hif := injective_comp_subtype_of_coprime_ker f (by rw [hker,hZcard]; decide : Nat.Coprime 2 (Nat.card f.ker))
    (R.map π) ((isPGroup_pCoreIn 2 (X ⊔ (T : Subgroup H))).map π)
  let eR : R.map π ≃* (R.map π).map f := MulEquiv.ofBijective (f.subgroupMap (R.map π))
    ⟨fun x y h => hif (congrArg Subtype.val h), f.subgroupMap_surjective _⟩
  have hmap : (R.map π).map f = R.map q := by rw [Subgroup.map_map,hcomp]
  let := hRcyc
  have hc : IsCyclic ((R.map π).map f) := isCyclic_of_surjective eR.toMonoidHom eR.surjective
  have hcard : Nat.card ((R.map π).map f) = 4 := (Nat.card_congr eR.toEquiv).symm.trans hRcard
  exact ⟨hQR,hinter,hmap ▸ hc,hmap ▸ hcard⟩
end CFSG.Quasithin.ChapterE.SolvableMinimalParabolic

namespace CFSG.Quasithin.ChapterE.SolvableMinimalParabolic
open ChapterB Subgroup Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]
theorem source_cyclicFour_image {K : GroupClass} (hH : IsSQTK K H)
    (T : Sylow 2 H) (hP : IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (hescape : ¬ (minimalParabolicMax T hP).pCoreIn 2 ≤ pCore 2 H ∨
      ¬ centralizerModulo (T : Subgroup H) (minimalParabolicCore T hP)
        ((minimalParabolicCore T hP).pCoreIn 2) ≤ pCore 2 H)
    (hne : pResidual 2 (minimalParabolicCore T hP) ≠ ⊥)
    (ha : Nonempty ((H ⧸ minimalParabolicCore T hP) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∨
      Nonempty ((H ⧸ minimalParabolicCore T hP) ≃*
        RegularWreathProduct (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)))) :
    let J := minimalParabolicCore T hP
    let X := (pResidual 2 J).map J.subtype
    let R := (X ⊔ (T : Subgroup H)).pCoreIn 2
    let q := QuotientGroup.mk' J
    pCore 2 H ≤ R ∧ pCore 2 H = R ⊓ J ∧
      IsCyclic (R.map q) ∧ Nat.card (R.map q) = 4 := by
  have hthree : 3 ∣ Nat.card (H ⧸ minimalParabolicCore T hP) := by
    have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide +kernel
    rcases ha with h | h
    · obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv,hSL]
      decide
    · obtain ⟨e⟩ := h
      rw [Nat.card_congr e.toEquiv,RegularWreathProduct.card,hSL]
      norm_num [Nat.card_eq_fintype_card]
  have hm := source_cubic_models_of_surjective hH T hP hs hescape
    (QuotientGroup.mk' (minimalParabolicCore T hP)) (QuotientGroup.mk'_surjective _) hthree
  exact core_residual_cyclicFour_of_models T hP hs hm hne ha
end CFSG.Quasithin.ChapterE.SolvableMinimalParabolic
