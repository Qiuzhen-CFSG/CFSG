module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.SingleCenter
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.SourceFactors
public import Theory.ElementaryAbelian.Join

/-!
# The actual single-factor commutator line

The complete B.2.16 application inside YT has one natural plane because the
actual residual quotient has order three. Its cubic action has no fixed point,
while the Thompson involution fixes a line. Baumann's decomposition and the
cardinal-four saturation lemma identify the literal line [E,Y] intersect E.
All transport uses the original subgroup embedding YT into G.

Source: Aschbacher--Smith, B.2.18, 15.4.12 and 15.4.18, pp.81,1160--1163.
-/

public noncomputable section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource FamilySource.ModuleStructure BaumannSylow
open Chapter1.RadicalNormalizers.ThompsonSource FamilySource.ThompsonFactors
open ChapterB ChapterB.BaumannArgument LocalSetup.TwoFactors LocalSetup.TwoFactors.SourceFactors
universe u
variable {G : Type u} [Group G] [Finite G]

private noncomputable def fixedEquiv (W : Subgroup G) [W.Normal] (A : Subgroup G) :
    (W ⊓ centralizer (A : Set G) : Subgroup G) ≃
      FixedPoints.subgroup (A.map (MulAut.conjNormal : G →* MulAut W)) W where
  toFun w := ⟨⟨w,w.property.1⟩, by
    rw [FixedPoints.mem_subgroup]
    rintro ⟨a,⟨g,hg,rfl⟩⟩
    apply Subtype.ext
    change g*(w:G)*g⁻¹=w
    exact mul_inv_eq_iff_eq_mul.mpr (w.property.2 g hg)⟩
  invFun w := ⟨w.val,w.val.property, by
    intro a ha
    have hw := (FixedPoints.mem_subgroup
      (M := A.map (MulAut.conjNormal : G →* MulAut W)) (α := W) (a := w.val)).mp
      w.property ⟨MulAut.conjNormal a,mem_map_of_mem _ ha⟩
    have hh := congrArg (fun x : W => (x:G)) hw
    change a*(w.val:G)*a⁻¹=w.val at hh
    exact mul_inv_eq_iff_eq_mul.mp hh⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem one_plane_fixed_geometry
    (R : Sylow 2 G) (W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 4) (hWR : W ≤ (R : Subgroup G))
    (hker : IsPGroup 2 (centralizer (W : Set G)))
    (hLcard : Nat.card ((pResidual 2 G).map
      (MulAut.conjNormal : G →* MulAut W)) = 3)
    (hJcard : Nat.card ((elementaryAbelianMaxJ (R : Subgroup G)).map
      (MulAut.conjNormal : G →* MulAut W)) = 2) :
    let E := thompsonAlpha (R : Subgroup G)
    let Y := pResidual 2 G
    (E ⊓ centralizer (Y : Set G)) ⊔ (⁅E,Y⁆ ⊓ E) = E ∧
      Disjoint (E ⊓ centralizer (Y : Set G)) (⁅E,Y⁆ ⊓ E) ∧
      Nat.card (⁅E,Y⁆ ⊓ E : Subgroup G) = 2 := by
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  let : IsKleinFour W := ⟨hcard,IsElementaryAbelian.exponent_eq_prime⟩
  let E := thompsonAlpha (R : Subgroup G)
  let Y := pResidual 2 G
  let C := E ⊓ centralizer (Y : Set G)
  let F := W ⊓ centralizer (elementaryAbelianMaxJ (R : Subgroup G) : Set G)
  let : IsElementaryAbelian 2 E := omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (show C ≤ E from inf_le_left)
  have hE := alpha_decomposition_from_one_plane R W hcard hWR hker hLcard hJcard
  have hfree : W ⊓ centralizer (Y : Set G) = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (fixedEquiv W Y)]
    exact IsKleinFour.three_fixed_card _ hLcard
  have hFcard : Nat.card F = 2 := by
    rw [Nat.card_congr (fixedEquiv W (elementaryAbelianMaxJ (R : Subgroup G)))]
    exact IsKleinFour.two_fixed_card _ hJcard
  have hWne : W ≠ ⊥ := by intro he; have hh := card_eq_one.mpr he; omega
  have hWY : W ≤ Y := by
    rw [← four_module_saturation (E := W) le_rfl le_rfl hWne hcard hfree
      (commutator_le_left W Y)]
    exact commutator_le_right W Y
  have hCW : C ≤ centralizer (W : Set G) :=
    inf_le_right.trans (centralizer_le hWY)
  let : IsElementaryAbelian 2 (C ⊔ W : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hCW)
  have hd : Disjoint C W := by
    apply disjoint_iff.mpr
    exact le_bot_iff.mp (by intro x hx; exact hfree.le ⟨hx.2,hx.1.2⟩)
  have hf := fixed_decomposition_of_four_module
    (U := C ⊔ W) le_sup_left le_sup_right hE.symm (show F ≤ W from inf_le_left)
    hd (show C ≤ centralizer (Y : Set G) from inf_le_right) hfree hcard hFcard
    (le_normalizer_of_normal (H := W))
  exact ⟨hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1⟩

private theorem source_join_exceptional {κ : GroupClass}
    (hB : TheoremB216.{u}) {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input κ T M X s) :
    ∃ hE : IsElementaryAbelian 2
      (Chapter1.RadicalNormalizers.ThompsonSource.closure
        (T.subtype (show (T : Subgroup G) ≤ X ⊔ T from le_sup_right))),
      ∃ d : @Exceptional (X ⊔ (T : Subgroup G) : Subgroup G) _
        (T.subtype (show (T : Subgroup G) ≤ X ⊔ T from le_sup_right)) hE,
        d.count = 1 ∨ d.count = 2 := by
  let H := X ⊔ (T : Subgroup G)
  let : Group.IsSolvable M := h.solvable
  have hHM : H ≤ M := sup_le h.member_le h.sylow_le
  have hsol : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective (inclusion_injective hHM)
  have hb := hB H hsol h.join_generalizedFitting (T.subtype le_sup_right)
  let := hb.elementary
  refine ⟨hb.elementary,?_⟩
  rcases hb.alternatives with hj | hex
  · exfalso
    apply member_internal_thompson_not_centralizes T h.member h.center_centralizer
    have hh := hj.1
    rwa [ThompsonSource.closure_eq_internalModule] at hh
  · obtain ⟨d⟩ := hex
    refine ⟨d,d.count_eq_one_or_two ?_ ?_⟩
    · rw [ThompsonSource.star_kernel T H le_sup_right h.center_centralizer]
      exact pCore_isPGroup
    · exact h.join_sqtk.stronglyQuasithin 3 Nat.prime_three (by decide)

theorem source_single_fixed_geometry {κ : GroupClass}
    (hB : TheoremB216.{u}) {T : Sylow 2 G} {M X : Subgroup G}
    (h : Input κ T M X 1) :
    let E := thompsonAlpha (T : Subgroup G)
    (E ⊓ centralizer (X : Set G)) ⊔ (⁅E,X⁆ ⊓ E) = E ∧
      Disjoint (E ⊓ centralizer (X : Set G)) (⁅E,X⁆ ⊓ E) ∧
      Nat.card (⁅E,X⁆ ⊓ E : Subgroup G) = 2 := by
  let H := X ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  obtain ⟨hE,d,hc⟩ := source_join_exceptional hB h
  let := hE
  have hk := ThompsonSource.star_kernel T H le_sup_right h.center_centralizer
  have hu := (member_internal_minimalParabolic T h.member h.quotient_elementary).1
  have hres : (pResidual 2 H).map H.subtype = X := member_residual_join T h.member
  have hres' : pResidual 2 H = X.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hres,map_subgroupOf_eq_of_le (show X ≤ H from le_sup_left)]
  let e := ThompsonSource.coreQuotientEquiv T H le_sup_right h.center_centralizer
  have hq : e.toMonoidHom.comp (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure S)) =
      quotientMap H := by
    ext m
    exact ThompsonSource.coreQuotientEquiv_apply T H le_sup_right h.center_centralizer m
  have hcard : Nat.card ((pResidual 2 H).map
      (starMap (Chapter1.RadicalNormalizers.ThompsonSource.closure S))) = 3 := by
    rw [← card_map_of_injective (f := e.toMonoidHom) e.injective,map_map,hq,hres']
    obtain ⟨f,_⟩ := member_quotient_compatible (show X ≤ H from le_sup_left)
      (YFamily.normal_in_join h.member)
    exact (Nat.card_congr f.toEquiv).symm.trans (by simpa only [pow_one] using h.quotient_card)
  have hcount : d.count = 1 := by
    rw [residual_star_image d hc hk hu] at hcard
    have hi : (Finset.univ : Finset (Fin d.count)).card = 1 ∨
        (Finset.univ : Finset (Fin d.count)).card = 2 := by simpa using hc
    have hh := cubicProduct_card d Finset.univ hi
    rw [Finset.card_univ,Fintype.card_fin] at hh
    rcases hc with hc | hc
    · exact hc
    · rw [hcard,hc] at hh
      omega
  have hmodule : Nat.card (moduleGroup d) = 4 := by
    simpa only [hcount,Nat.mul_one,show 2^2=4 from rfl] using moduleGroup_card d (Or.inl hcount)
  have horders := exceptional_action_orders d (Or.inl hcount) hk hu
  have hgeometry := one_plane_fixed_geometry S (moduleGroup d) hmodule
    (moduleGroup_le_sylow d) (moduleGroup_centralizer_two d (Or.inl hcount) hk hu)
    (by simpa only [hcount,pow_one] using horders.1) (by simpa only [hcount,pow_one] using horders.2)
  have hJ : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective _ H.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right]
  have hAlpha : (thompsonAlpha (S : Subgroup H)).map H.subtype =
      thompsonAlpha (T : Subgroup G) := by
    change (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup H))).map _ = _
    rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,hJ]
    rfl
  have hmap : (thompsonAlpha (S : Subgroup H) ⊓ centralizer (pResidual 2 H : Set H)).map H.subtype =
      thompsonAlpha (T : Subgroup G) ⊓ centralizer (X : Set G) := by
    rw [map_inf _ _ _ H.subtype_injective,map_centralizer_subtype,hAlpha,hres]
    have hAH : thompsonAlpha (T : Subgroup G) ≤ H := hAlpha ▸ map_subtype_le _
    rw [← inf_assoc,inf_of_le_left hAH]
  have hmoved : (⁅thompsonAlpha (S : Subgroup H),pResidual 2 H⁆ ⊓
      thompsonAlpha (S : Subgroup H)).map H.subtype =
        ⁅thompsonAlpha (T : Subgroup G),X⁆ ⊓ thompsonAlpha (T : Subgroup G) := by
    rw [map_inf _ _ _ H.subtype_injective,map_commutator,hAlpha,hres]
  have hsplit := congrArg (Subgroup.map H.subtype) hgeometry.1
  rw [Subgroup.map_sup,hmap,hmoved,hAlpha] at hsplit
  have hdis := Subgroup.disjoint_map H.subtype_injective hgeometry.2.1
  rw [hmap,hmoved] at hdis
  refine ⟨hsplit,hdis,?_⟩
  rw [← hmoved,card_map_of_injective H.subtype_injective]
  exact hgeometry.2.2

end CFSG.Quasithin.Chapter15.Section04.InitialSource
