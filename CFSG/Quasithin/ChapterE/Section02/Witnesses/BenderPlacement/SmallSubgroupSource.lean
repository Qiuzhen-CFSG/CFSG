module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.SmallResidualNineExclusion
public import Theory.GroupTheory.GeneralizedFitting.PrimeCoreNormalized
public import Theory.Representation.BinaryOffender.CubicRatio.Monotonicity
/-!
# Restricting the original small-automizer source to a subgroup

For V ≤ L, restrict the original U-action to U ∩ L and take its literal
image in D. Its kernel is the centralizer of V inside U ∩ L. The subgroup
identification of V gives an equivariant linear equivalence, so injective
actor monotonicity preserves the strict lower bound on the cubic ratio.

The source consumer places a Sylow subgroup of L inside the original Sylow
subgroup, inherits the SQTK and characteristic-two hypotheses, and applies
the solvable order-nine residual exclusion. No local action, faithfulness,
module marking or ratio premise is added to the subgroup geometry.

Source: Aschbacher–Smith E.2.17, printed p.230, the solvable H₀ reduction
in the paired linear-two and linear-three over the three-element field cases.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H D : Type*} [Group H] [Finite H] [Group D] [Finite D]
  {V U : Subgroup H} [IsElementaryAbelian 2 V]
omit [Finite H] [Finite D] in
/-- Restrict the given faithful conjugation action to its actual subgroup image. -/
theorem subgroup_small_action
    (L : Subgroup H) (hVL : V ≤ L) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U) :
    letI : IsElementaryAbelian 2 (V.subgroupOf L) := IsElementaryAbelian.subgroupOf hVL
    ∃ hn : U.subgroupOf L ≤ normalizer (V.subgroupOf L : Set L),
    ∃ D₀ : Subgroup D, ∃ f₀ : U.subgroupOf L →* D₀,
    ∃ hf₀ : Function.Surjective f₀,
    ∃ hk₀ : f₀.ker = (centralizer (V.subgroupOf L : Set L)).subgroupOf (U.subgroupOf L),
      cubicRatio (DihedralCubic.representation U V hU f hf hk) ≤
        cubicRatio (DihedralCubic.representation (U.subgroupOf L) (V.subgroupOf L) hn f₀ hf₀ hk₀) := by
  let : IsElementaryAbelian 2 (V.subgroupOf L) := IsElementaryAbelian.subgroupOf hVL
  have hn : U.subgroupOf L ≤ normalizer (V.subgroupOf L : Set L) := by
    rw [←subgroupOf_normalizer_eq hVL]
    exact comap_mono hU
  let j : U.subgroupOf L →* U := {
    toFun x := ⟨x.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let g := f.comp j
  let f₀ := g.rangeRestrict
  have hf₀ : Function.Surjective f₀ := g.rangeRestrict_surjective
  have hk₀ : f₀.ker = (centralizer (V.subgroupOf L : Set L)).subgroupOf (U.subgroupOf L) := by
    rw [MonoidHom.ker_rangeRestrict,←MonoidHom.comap_ker,hk]
    ext x
    change ((x : L) : H) ∈ centralizer (V : Set H) ↔
      (x : L) ∈ centralizer (V.subgroupOf L : Set L)
    constructor
    · intro hc y hy
      exact Subtype.ext (hc y hy)
    · intro hc y hy
      exact congrArg Subtype.val (hc ⟨y,hVL hy⟩ hy)
  refine ⟨hn,g.range,f₀,hf₀,hk₀,?_⟩
  let e := subgroupOfEquivOfLe hVL
  let E : Additive (V.subgroupOf L) ≃ₗ[ZMod 2] Additive V :=
    LinearEquiv.ofBijective (e.toMonoidHom.toAdditive.toZModLinearMap 2) e.bijective
  apply cubicRatio_le_of_injective_equivariant
    (DihedralCubic.representation (U.subgroupOf L) (V.subgroupOf L) hn f₀ hf₀ hk₀)
    (DihedralCubic.representation U V hU f hf hk) g.range.subtype g.range.subtype_injective E
  intro a v
  obtain ⟨x,rfl⟩ := hf₀ a
  apply Additive.toMul.injective
  apply Subtype.ext
  change (((DihedralCubic.representation (U.subgroupOf L) (V.subgroupOf L) hn f₀ hf₀ hk₀
    (f₀ x) v).toMul : L) : H) =
    ((DihedralCubic.representation U V hU f hf hk (f (j x)) (E v)).toMul : H)
  rw [DihedralCubic.representation_apply,DihedralCubic.representation_apply]
  rfl

/-- Apply the solvable source exclusion inside the literal subgroup L,
constructing every action and inheritance premise from the ambient data. -/
theorem source_subgroup_small_residual_nine_false
    {κ : GroupClass} (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hVT : V ≤ T) (hvn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hfit : generalizedFitting H = pCore 2 H) (hV : Nat.card V = 16)
    (hTU : (T : Subgroup H) ≤ U) (hU : U ≤ normalizer (V : Set H))
    (f : U →* D) (hf : Function.Surjective f)
    (hk : f.ker = (centralizer (V : Set H)).subgroupOf U)
    (hD : Nat.card D ≤ 4)
    (hratio : 1 < cubicRatio (DihedralCubic.representation U V hU f hf hk))
    (L : Subgroup H) (hVL : V ≤ L) (hLn : pCore 2 H ≤ normalizer (L : Set H))
    (S : Sylow 2 L) (hST : (S : Subgroup L).map L.subtype ≤ T)
    (hP₀ : ChapterB.IsMinimalParabolicOver S ⊤) (hs₀ : Group.IsSolvable L)
    (hVM₀ : V.subgroupOf L ≤ (ChapterB.minimalParabolicMax S hP₀).pCoreIn 2)
    (hout₀ : ¬ V.subgroupOf L ≤ ChapterB.minimalParabolicCore S hP₀)
    (hres₀ : (pResidual 2 (ChapterB.minimalParabolicMax S hP₀)).map
      (ChapterB.minimalParabolicMax S hP₀).subtype ≤ centralizer (V.subgroupOf L : Set L))
    (hJ₀ : ChapterB.minimalParabolicCore S hP₀ = pCore 2 L)
    (h9 : Nat.card (pResidual 2 (L ⧸ pCore 2 L)) = 9) : False := by
  let : IsElementaryAbelian 2 (V.subgroupOf L) := IsElementaryAbelian.subgroupOf hVL
  have hST' : (S : Subgroup L) ≤ (T : Subgroup H).subgroupOf L :=
    (map_le_iff_le_comap).mp hST
  have hTS : (T : Subgroup H).subgroupOf L = S :=
    S.is_maximal' T.isPGroup'.comap_subtype hST'
  have hVS : V.subgroupOf L ≤ S := by
    rw [←hTS]
    exact comap_mono hVT
  have hTV := (normal_subgroupOf_iff_le_normalizer hVT).mp hvn
  have hSn : (S : Subgroup L) ≤ normalizer (V.subgroupOf L : Set L) := by
    rw [←subgroupOf_normalizer_eq hVL]
    exact hST'.trans (comap_mono hTV)
  have hVn : ((V.subgroupOf L).subgroupOf (S : Subgroup L)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVS).mpr hSn
  have hSU : (S : Subgroup L) ≤ U.subgroupOf L := hST'.trans (comap_mono hTU)
  obtain ⟨hn,D₀,f₀,hf₀,hk₀,hle⟩ := subgroup_small_action L hVL hU f hf hk
  have hD₀ : Nat.card D₀ ≤ 4 :=
    (Nat.card_le_card_of_injective D₀.subtype D₀.subtype_injective).trans hD
  have hV₀ : Nat.card (V.subgroupOf L) = 16 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv).trans hV
  exact source_solvable_small_residual_nine_false (hH.subgroup L) S hP₀ hs₀
    hVS hVn hVM₀ hout₀ (generalizedFitting_eq_pCore_of_normalized_by_pCore L hfit hLn)
    hV₀ hSU hn f₀ hf₀ hk₀ hD₀ (lt_of_lt_of_le hratio hle) hres₀ hJ₀ h9
end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
