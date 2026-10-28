module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics.Basic
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.Normalizers
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.BorelOvergroups
public import Theory.AtlasPort.LinearGroups.G2.EvenBorelTorus
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Borel
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Perfectness
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Perfectness
public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.SylowAlignment
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.SpecificGroups.Triality.ConcreteBruhat.CartanNormalizer

/-!
# Nonlinear Lie parabolics have no order-sixteen two-core

The three nonlinear carriers in A.3.14(1) are handled by their actual models.
Each proof aligns the given Sylow normalizer with the standard Borel, uses
maximality to upgrade a model parabolic containment to equality, and computes
the intrinsic two-core of the full parabolic residual.  The G₂ and triality
steps retain the full-parabolic residual calculation; they do not identify a
local group's residual with the residual of the enclosing parabolic by fiat.

Source: Aschbacher--Smith A.3.14(1), printed pp.49--50, and Lemma 14.4.9,
printed p.1010; concrete local calculations are in the imported theory files.
-/

public section
noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter1.Section02
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.ThreeResidualPlacement
open Theory.SpecificGroups.SymplecticFour.BorelActionGeometry
open Theory.SpecificGroups.SymplecticFour.EvenTwoRank
open Atlas.G2 Atlas.G2.LieParabolicSetup
open Atlas.G2.EvenLocal.BorelOvergroups
open Atlas.G2.EvenBorelTorus
open Atlas.G2.DerivedNormalizerSolvable
open Atlas.G2.SylowNormalizer
open Atlas.G2.EvenLocal.NormalizerCover
open Triality.Standard
open Triality.Standard.Parabolics
open Triality.Standard.ConcreteBruhat
open Triality.Standard.TwoRank.Derived
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private def pointRadicalCoordinates : pointRadical (F := F) ≃ F × F × F where
  toFun q := (q.val.val.val (.inl 1) (.inr 0), q.val.val.val (.inr 1) (.inr 0),
    q.val.val.val (.inl 0) (.inr 0))
  invFun x := ⟨pointRadicalElement x.1 x.2.1 x.2.2, pointRadicalElement_mem _ _ _⟩
  left_inv q := Subtype.ext (pointRadical_eq_element q.val q.property).symm
  right_inv _ := rfl

private theorem symplectic_case {L F : Type*} [Group L] [Finite L] [Field F]
    [Finite F] [CharP F 2] (hF : Nat.card F = 4) (e : L ≃* ClassicalGroup.PSp 2 F)
    (P : Subgroup L) (hP : LieParabolicTwo P) (hmax : IsCoatom P) :
    Nat.card (pCore 2 (embeddedResidual P)) ≠ 16 := by
  let φ := e.trans (EvenProjective.equiv (F := F)).symm
  let P₀ : Subgroup (Sp F) := P.map φ.toMonoidHom
  have hP₀ : LieParabolicTwo P₀ := by
    exact parabolic_map hP φ
  have hmax₀ : IsCoatom P₀ := by
    -- map under an equivalence
    exact (φ.mapSubgroup.isCoatom_iff P).mpr hmax
  obtain ⟨S, hS⟩ := hP₀
  have hSP : (S : Subgroup (Sp F)) ≤ P₀ := le_normalizer.trans hS
  have hFgt : 2 < Nat.card F := by omega
  have hproper₀ : P₀ ≠ ⊤ := hmax₀.ne_top
  obtain ⟨g, hg⟩ := proper_sylow_overgroup_parabolic_cover hFgt S P₀ hSP hproper₀
  rcases hg with hg | hg
  · have hmaxg : IsCoatom (P₀.map (MulAut.conj g).toMonoidHom) := by
      exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup P₀).mpr hmax₀
    have heq : P₀.map (MulAut.conj g).toMonoidHom = pointParabolic (F := F) :=
      ((hmaxg.le_iff_eq (pointParabolic_isCoatom (F := F)).ne_top).mp hg).symm
    have hconj : Nat.card (pCore 2 (embeddedResidual P₀)) =
        Nat.card (pCore 2 (embeddedResidual (pointParabolic (F := F)))) := by
      have heq' := card_twoCore_congr ((MulAut.conj g).subgroupMap
        (embeddedResidual P₀))
      have hres := embeddedResidual_map P₀ (MulAut.conj g)
      have hs : (embeddedResidual P₀).map (MulAut.conj g).toMonoidHom =
          embeddedResidual (pointParabolic (F := F)) := by
        rw [hres, heq]
      change Nat.card (pCore 2 (embeddedResidual P₀)) =
        Nat.card (pCore 2 ((embeddedResidual P₀).map (MulAut.conj g).toMonoidHom)) at heq'
      rw [hs] at heq'
      exact heq'
    have hmodel : Nat.card (pCore 2 (embeddedResidual (pointParabolic (F := F)))) = 64 := by
      rw [show embeddedResidual (pointParabolic (F := F)) = pointLocal (F := F) by
        simpa [embeddedResidual] using pointParabolic_solvableResidual_eq
          (show Nat.card F = 2 ^ 2 by norm_num [hF]) (by decide)]
      rw [pointLocal_core_eq (show Nat.card F = 2 ^ 2 by norm_num [hF]) (by decide)]
      rw [Nat.card_congr (pointRadicalCoordinates (F := F)),
        Nat.card_prod, Nat.card_prod]
      norm_num [hF]
    have htransport : Nat.card (pCore 2 (embeddedResidual P)) =
        Nat.card (pCore 2 (embeddedResidual P₀)) := by
      have heq' := card_twoCore_congr (φ.subgroupMap (embeddedResidual P))
      have hres := embeddedResidual_map P φ
      have hs : (embeddedResidual P).map φ.toMonoidHom =
          embeddedResidual P₀ := by
        rw [hres]
      change Nat.card (pCore 2 (embeddedResidual P)) =
        Nat.card (pCore 2 ((embeddedResidual P).map φ.toMonoidHom)) at heq'
      rw [hs] at heq'
      exact heq'
    rw [htransport, hconj, hmodel]
    norm_num
  · have hmaxg : IsCoatom (P₀.map (MulAut.conj g).toMonoidHom) := by
      exact (OrderIso.isCoatom_iff (MulAut.conj g).mapSubgroup P₀).mpr hmax₀
    have heq : P₀.map (MulAut.conj g).toMonoidHom = planeParabolic (F := F) :=
      ((hmaxg.le_iff_eq (planeParabolic_isCoatom (F := F)).ne_top).mp hg).symm
    have hconj : Nat.card (pCore 2 (embeddedResidual P₀)) =
        Nat.card (pCore 2 (embeddedResidual (planeParabolic (F := F)))) := by
      have heq' := card_twoCore_congr ((MulAut.conj g).subgroupMap
        (embeddedResidual P₀))
      have hres := embeddedResidual_map P₀ (MulAut.conj g)
      have hs : (embeddedResidual P₀).map (MulAut.conj g).toMonoidHom =
          embeddedResidual (planeParabolic (F := F)) := by
        rw [hres, heq]
      change Nat.card (pCore 2 (embeddedResidual P₀)) =
        Nat.card (pCore 2 ((embeddedResidual P₀).map (MulAut.conj g).toMonoidHom)) at heq'
      rw [hs] at heq'
      exact heq'
    have hmodel : Nat.card (pCore 2 (embeddedResidual (planeParabolic (F := F)))) = 64 := by
      rw [show embeddedResidual (planeParabolic (F := F)) = planeLocal (F := F) by
        simpa [embeddedResidual] using planeParabolic_solvableResidual_eq
          (show Nat.card F = 2 ^ 2 by norm_num [hF]) (by decide)]
      rw [planeLocal_core_eq (show Nat.card F = 2 ^ 2 by norm_num [hF]) (by decide)]
      rw [card_plane_radical]
      norm_num [hF]
    have htransport : Nat.card (pCore 2 (embeddedResidual P)) =
        Nat.card (pCore 2 (embeddedResidual P₀)) := by
      have heq' := card_twoCore_congr (φ.subgroupMap (embeddedResidual P))
      have hres := embeddedResidual_map P φ
      have hs : (embeddedResidual P).map φ.toMonoidHom =
          embeddedResidual P₀ := by
        rw [hres]
      change Nat.card (pCore 2 (embeddedResidual P)) =
        Nat.card (pCore 2 ((embeddedResidual P).map φ.toMonoidHom)) at heq'
      rw [hs] at heq'
      exact heq'
    rw [htransport, hconj, hmodel]
    norm_num

private theorem residual_short (hq : 2 < Nat.card F) :
    (solvableResidual (parabolic₁ (F := F))).map parabolic₁.subtype = local₁ := by
  let := local₁_isPerfect (F := F) hq
  let := Atlas.G2.LieParabolicSetup.local₁_normal_in_parabolic₁ (F := F)
  have hlocal : local₁ (F := F) ≤ parabolic₁ := by
    rw [← local₁_sup_borel]
    exact le_sup_left
  have hsup : (local₁ (F := F)).subgroupOf parabolic₁ ⊔
      (borel (K := F)).subgroupOf parabolic₁ = ⊤ := by
    apply map_injective parabolic₁.subtype_injective
    simp [Subgroup.map_sup, map_subgroupOf_eq_of_le hlocal,
      map_subgroupOf_eq_of_le borel_le_parabolic₁, local₁_sup_borel,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let : Group.IsSolvable (borel (K := F)) := isSolvable_borel
  let q := QuotientGroup.mk' ((local₁ (F := F)).subgroupOf parabolic₁)
  have hsurj : Function.Surjective
      (q.comp (Subgroup.inclusion borel_le_parabolic₁)) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      ((local₁ (F := F)).subgroupOf parabolic₁) z
    have hx : x ∈ (local₁ (F := F)).subgroupOf parabolic₁ ⊔
        (borel (K := F)).subgroupOf parabolic₁ := hsup ▸ mem_top _
    obtain ⟨n, hn, b, hb, hxb⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hx
    have hqn : q n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    refine ⟨⟨b.val, hb⟩, ?_⟩
    change q b = q x
    rw [← hxb, map_mul, hqn, one_mul]
  let := Group.isSolvable_of_surjective hsurj
  have hle := solvableResidual_le_of_solvable_quotient
    ((local₁ (F := F)).subgroupOf parabolic₁)
  apply le_antisymm
  · calc
      (solvableResidual (parabolic₁ (F := F))).map parabolic₁.subtype ≤
          ((local₁ (F := F)).subgroupOf parabolic₁).map parabolic₁.subtype :=
        map_mono (f := parabolic₁.subtype) hle
      _ = local₁ := map_subgroupOf_eq_of_le hlocal
  · exact le_map_solvableResidual_of_isPerfect _ _ hlocal

private theorem residual_long (hq : 2 < Nat.card F) :
    (solvableResidual (parabolic₂ (F := F))).map parabolic₂.subtype = local₂ := by
  let := local₂_isPerfect (F := F) hq
  let := Atlas.G2.LieParabolicSetup.local₂_normal_in_parabolic₂ (F := F)
  have hlocal : local₂ (F := F) ≤ parabolic₂ := by
    rw [← local₂_sup_borel]
    exact le_sup_left
  have hsup : (local₂ (F := F)).subgroupOf parabolic₂ ⊔
      (borel (K := F)).subgroupOf parabolic₂ = ⊤ := by
    apply map_injective parabolic₂.subtype_injective
    simp [Subgroup.map_sup, map_subgroupOf_eq_of_le hlocal,
      map_subgroupOf_eq_of_le borel_le_parabolic₂, local₂_sup_borel,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  let : Group.IsSolvable (borel (K := F)) := isSolvable_borel
  let q := QuotientGroup.mk' ((local₂ (F := F)).subgroupOf parabolic₂)
  have hsurj : Function.Surjective
      (q.comp (Subgroup.inclusion borel_le_parabolic₂)) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      ((local₂ (F := F)).subgroupOf parabolic₂) z
    have hx : x ∈ (local₂ (F := F)).subgroupOf parabolic₂ ⊔
        (borel (K := F)).subgroupOf parabolic₂ := hsup ▸ mem_top _
    obtain ⟨n, hn, b, hb, hxb⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hx
    have hqn : q n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
    refine ⟨⟨b.val, hb⟩, ?_⟩
    change q b = q x
    rw [← hxb, map_mul, hqn, one_mul]
  let := Group.isSolvable_of_surjective hsurj
  have hle := solvableResidual_le_of_solvable_quotient
    ((local₂ (F := F)).subgroupOf parabolic₂)
  apply le_antisymm
  · calc
      (solvableResidual (parabolic₂ (F := F))).map parabolic₂.subtype ≤
          ((local₂ (F := F)).subgroupOf parabolic₂).map parabolic₂.subtype :=
        map_mono (f := parabolic₂.subtype) hle
      _ = local₂ := map_subgroupOf_eq_of_le hlocal
  · exact le_map_solvableResidual_of_isPerfect _ _ hlocal


private theorem g2_case {L F : Type*} [Group L] [Finite L] [Field F]
    [Finite F] [CharP F 2] (hF : Nat.card F = 4) (e : L ≃* Atlas.G2.Model F)
    (Q : Subgroup L) (hP : LieParabolicTwo Q) (hmax : IsCoatom Q) :
    Nat.card (pCore 2 (embeddedResidual Q)) ≠ 16 := by
  let P : Subgroup (Atlas.G2.Model F) := Q.map e.toMonoidHom
  have hP' : LieParabolicTwo P := parabolic_map hP e
  have hmax' : IsCoatom P := (OrderIso.isCoatom_iff e.mapSubgroup Q).mpr hmax
  obtain ⟨S, hS⟩ := hP'
  have hSP : (S : Subgroup (Atlas.G2.Model F)) ≤ P := le_normalizer.trans hS
  have hproper : P ≠ ⊤ := hmax'.ne_top
  obtain ⟨g, hg⟩ := sylow_normalizer_conjugate S
  let c := MulAut.conj g
  have hBmap : (borel (K := F)).map c.toMonoidHom ≤ P := by
    simpa [c] using (hg.2.symm ▸ hS)
  have hBinv : borel (K := F) ≤ P.map c.symm.toMonoidHom := by
    have := map_mono (f := c.symm.toMonoidHom) hBmap
    have hcomp : c.symm.toMonoidHom.comp c.toMonoidHom =
        MonoidHom.id _ := by
      ext x
      simp
    have hleft : ((borel (K := F)).map c.toMonoidHom).map c.symm.toMonoidHom =
        borel (K := F) := by
      rw [map_map, hcomp, map_id]
    rw [hleft] at this
    exact this
  have hmaxc : IsCoatom (P.map c.symm.toMonoidHom) := by
    exact (OrderIso.isCoatom_iff c.symm.mapSubgroup P).mpr hmax'
  have hproper' : P.map c.symm.toMonoidHom ≠ ⊤ := hmaxc.ne_top
  have htransport0 : Nat.card (pCore 2 (embeddedResidual Q)) =
      Nat.card (pCore 2 (embeddedResidual P)) := by
    have hh := card_twoCore_congr (e.subgroupMap (embeddedResidual Q))
    change Nat.card (pCore 2 (embeddedResidual Q)) =
      Nat.card (pCore 2 ((embeddedResidual Q).map e.toMonoidHom)) at hh
    rw [embeddedResidual_map Q e] at hh
    exact hh
  rcases le_parabolic (F := F) (P.map c.symm.toMonoidHom) hBinv
    (lt_top_iff_ne_top.mpr hproper') with ha | ha
  · have heq : P.map c.symm.toMonoidHom = parabolic₁ (F := F) :=
      ((hmaxc.le_iff_eq
        (_root_.Atlas.G2.EvenLocal.NormalizerCover.short_parabolic_ne_top (F := F))).mp ha).symm
    have hmodel : Nat.card (pCore 2 (embeddedResidual (parabolic₁ (F := F)))) =
        1024 := by
      rw [show embeddedResidual (parabolic₁ (F := F)) = local₁ (F := F) by
        simpa [embeddedResidual] using residual_short (F := F) (by omega)]
      rw [card_local₁_pCore]
      norm_num [hF]
    have htransport1 : Nat.card (pCore 2 (embeddedResidual P)) =
        Nat.card (pCore 2 (embeddedResidual (P.map c.symm.toMonoidHom))) := by
      have heq' := card_twoCore_congr (c.symm.subgroupMap (embeddedResidual P))
      have hres := embeddedResidual_map P c.symm
      have hs : (embeddedResidual P).map c.symm.toMonoidHom =
          embeddedResidual (P.map c.symm.toMonoidHom) := hres
      change Nat.card (pCore 2 (embeddedResidual P)) =
        Nat.card (pCore 2 ((embeddedResidual P).map c.symm.toMonoidHom)) at heq'
      rw [hs] at heq'
      exact heq'
    rw [htransport0, htransport1, heq, hmodel]
    norm_num
  · have heq : P.map c.symm.toMonoidHom = parabolic₂ (F := F) :=
      ((hmaxc.le_iff_eq
        (_root_.Atlas.G2.EvenLocal.NormalizerCover.long_parabolic_ne_top (F := F))).mp ha).symm
    have hmodel : Nat.card (pCore 2 (embeddedResidual (parabolic₂ (F := F)))) =
        1024 := by
      rw [show embeddedResidual (parabolic₂ (F := F)) = local₂ (F := F) by
        simpa [embeddedResidual] using residual_long (F := F) (by omega)]
      rw [card_local₂_pCore]
      norm_num [hF]
    have htransport1 : Nat.card (pCore 2 (embeddedResidual P)) =
        Nat.card (pCore 2 (embeddedResidual (P.map c.symm.toMonoidHom))) := by
      have heq' := card_twoCore_congr (c.symm.subgroupMap (embeddedResidual P))
      have hres := embeddedResidual_map P c.symm
      have hs : (embeddedResidual P).map c.symm.toMonoidHom =
          embeddedResidual (P.map c.symm.toMonoidHom) := hres
      change Nat.card (pCore 2 (embeddedResidual P)) =
        Nat.card (pCore 2 ((embeddedResidual P).map c.symm.toMonoidHom)) at heq'
      rw [hs] at heq'
      exact heq'
    rw [htransport0, htransport1, heq, hmodel]
    norm_num

private theorem residual_parabolic (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) (a : Node) :
    (solvableResidual (parabolic P a)).map (parabolic P a).subtype = localFactor P a := by
  let := localFactor_isPerfect P hp hq a
  let := localFactor_normal P a
  have hlocal : localFactor P a ≤ parabolic P a := localFactor_le_parabolic P a
  have hsup : (localFactor P a).subgroupOf (parabolic P a) ⊔
      (borel P).subgroupOf (parabolic P a) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hlocal (borel_le_parabolic P a),
      localFactor_sup_borel_binary P hp a, Subgroup.subgroupOf_self]
  let : IsCyclic (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    parabolic_quotient_isCyclic P hp a
  let : CommGroup (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    IsCyclic.commGroup
  let := (inferInstance : Group.IsSolvable
    (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)))
  have hle := solvableResidual_le_of_solvable_quotient
    ((localFactor P a).subgroupOf (parabolic P a))
  apply le_antisymm
  · calc
      (solvableResidual (parabolic P a)).map (parabolic P a).subtype ≤
          ((localFactor P a).subgroupOf (parabolic P a)).map (parabolic P a).subtype :=
        map_mono (f := (parabolic P a).subtype) hle
      _ = localFactor P a := map_subgroupOf_eq_of_le hlocal
  · exact le_map_solvableResidual_of_isPerfect _ _ hlocal


private theorem triality_case {L : Type*} [Group L] [Finite L]
    (e : L ≃* BinaryCarrier 2 (by decide)) (Q : Subgroup L)
    (hP : LieParabolicTwo Q) (hmax : IsCoatom Q) :
    Nat.card (pCore 2 (embeddedResidual Q)) ≠ 16 := by
  let P' : Subgroup (BinaryCarrier 2 (by decide)) := Q.map e.toMonoidHom
  have hP' : LieParabolicTwo P' := parabolic_map hP e
  have hmax' : IsCoatom P' := by
    exact (OrderIso.isCoatom_iff e.mapSubgroup Q).mpr hmax
  obtain ⟨S, hS⟩ := hP'
  have hSP : (S : Subgroup (BinaryCarrier 2 (by decide))) ≤ P' := le_normalizer.trans hS
  let U := (unipotentSylow (binaryParameters 2 (by decide)) rfl)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (BinaryCarrier 2 (by decide)) U S
  have hmap : (U : Subgroup (BinaryCarrier 2 (by decide))).map
      (MulAut.conj g).toMonoidHom = (S : Subgroup _) :=
    congrArg Sylow.toSubgroup hg
  have hBmap : (borel (binaryParameters 2 (by decide))).map
      (MulAut.conj g).toMonoidHom ≤ P' := by
    have hu : (U : Subgroup (BinaryCarrier 2 (by decide))) =
        unipotent (binaryParameters 2 (by decide)) := coe_unipotentSylow _ rfl
    let NU : Subgroup (BinaryCarrier 2 (by decide)) :=
      normalizer (unipotent (binaryParameters 2 (by decide)) : Set _)
    have huSet : (U : Subgroup (BinaryCarrier 2 (by decide))).carrier =
        (unipotent (binaryParameters 2 (by decide))).carrier :=
      congrArg (fun H : Subgroup (BinaryCarrier 2 (by decide)) => H.carrier) hu
    have hNU : NU = normalizer (U : Subgroup (BinaryCarrier 2 (by decide))).carrier := by
      dsimp [NU]
      rw [huSet]
      rfl
    have hnorm : NU.map (MulAut.conj g).toMonoidHom = normalizer (S : Set _) := by
      have hmapSet : ((U : Subgroup (BinaryCarrier 2 (by decide))).map
          (MulAut.conj g).toMonoidHom : Set (BinaryCarrier 2 (by decide))) =
          (S : Set (BinaryCarrier 2 (by decide))) :=
        congrArg (fun K : Subgroup (BinaryCarrier 2 (by decide)) =>
          (K : Set (BinaryCarrier 2 (by decide)))) hmap
      rw [hNU]
      rw [← hmapSet, ← map_equiv_normalizer_eq]
      rfl
    have hbu : NU =
        borel (binaryParameters 2 (by decide)) := by
      exact ConcreteBruhat.normalizer_unipotent_eq_borel
        (binaryParameters 2 (by decide)) rfl
    calc
      (borel (binaryParameters 2 (by decide))).map (MulAut.conj g).toMonoidHom =
          NU.map (MulAut.conj g).toMonoidHom := by
            rw [← hbu]
      _ = normalizer (S : Set _) := hnorm
      _ ≤ P' := hS
  let c := MulAut.conj g
  have hBinv : borel (binaryParameters 2 (by decide)) ≤ P'.map c.symm.toMonoidHom := by
    have h := map_mono (f := c.symm.toMonoidHom) hBmap
    have hcomp : c.symm.toMonoidHom.comp c.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    have hleft : ((borel (binaryParameters 2 (by decide))).map c.toMonoidHom).map
        c.symm.toMonoidHom = borel (binaryParameters 2 (by decide)) := by
      rw [map_map, hcomp, map_id]
    rw [hleft] at h
    exact h
  have hmaxc : IsCoatom (P'.map c.symm.toMonoidHom) := by
    exact (OrderIso.isCoatom_iff c.symm.mapSubgroup P').mpr hmax'
  have hproperc : P'.map c.symm.toMonoidHom ≠ ⊤ := hmaxc.ne_top
  obtain ⟨a, ha⟩ := le_parabolic_of_borel_le 2 (by decide)
    (P'.map c.symm.toMonoidHom) hBinv hproperc
  have heq : P'.map c.symm.toMonoidHom = parabolic (binaryParameters 2 (by decide)) a :=
    ((hmaxc.le_iff_eq (parabolic_ne_top_binary _ rfl a)).mp ha).symm
  have hmodel : Nat.card (pCore 2
      (embeddedResidual (parabolic (binaryParameters 2 (by decide)) a))) ≠ 16 := by
    rw [show embeddedResidual (parabolic (binaryParameters 2 (by decide)) a) =
        localFactor (binaryParameters 2 (by decide)) a from
      residual_parabolic _ rfl (by decide) a]
    cases a with
    | arms =>
      rw [localFactor_arms_twoCore_card _ rfl]
      decide
    | central =>
      rw [localFactor_central_twoCore_card _ rfl]
      decide
  have ht0 : Nat.card (pCore 2 (embeddedResidual Q)) =
      Nat.card (pCore 2 (embeddedResidual P')) := by
    have hh := card_twoCore_congr (e.subgroupMap (embeddedResidual Q))
    change Nat.card (pCore 2 (embeddedResidual Q)) =
      Nat.card (pCore 2 ((embeddedResidual Q).map e.toMonoidHom)) at hh
    rw [embeddedResidual_map Q e] at hh
    exact hh
  have ht1 : Nat.card (pCore 2 (embeddedResidual P')) =
      Nat.card (pCore 2 (embeddedResidual (P'.map c.symm.toMonoidHom))) := by
    have hh := card_twoCore_congr (c.symm.subgroupMap (embeddedResidual P'))
    change Nat.card (pCore 2 (embeddedResidual P')) =
      Nat.card (pCore 2 ((embeddedResidual P').map c.symm.toMonoidHom)) at hh
    rw [embeddedResidual_map P' c.symm] at hh
    exact hh
  rw [ht0, ht1, heq]
  exact hmodel



/-- A nonlinear A.3.14(1) parabolic residual cannot have a two-core of order 16. -/
theorem nonlinear_core_order_exclusion {L : Type*} [Group L] [Finite L]
    (hL : NonlinearFamily L) (P : Subgroup L)
    (hP : LieParabolicTwo P) (hmax : IsCoatom P) :
    Nat.card (pCore 2 (embeddedResidual P)) ≠ 16 := by
  rcases hL with hSp | hG2 | hTr
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hSp
    let : CharP F 2 := EvenProjective.charTwo_of_card
      (show Nat.card F = 2 ^ 2 by norm_num [hF])
    exact symplectic_case hF e P hP hmax
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hG2
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (p := 2) (f := 2) (by
        convert hF using 1 <;> norm_num [Nat.card_eq_fintype_card])
    exact g2_case hF e P hP hmax
  · obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff L 2 (by decide)).mp hTr
    exact triality_case e P hP hmax

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics
