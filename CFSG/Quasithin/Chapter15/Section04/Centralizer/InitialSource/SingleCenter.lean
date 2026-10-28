module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.BaumannSylow.Source
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.DoubleCenter

/-!
# The single-factor fixed index and the complete coordinate alternatives

Apply the full solvable Thompson theorem inside the actual YT. Its residual
is the original Y, so the order-three residual quotient forces exactly one
natural binary plane. The checked Baumann argument gives the Thompson-center
decomposition; the involution image fixes a line, while the cubic residual
fixes no nonidentity vector. Thus C_E(Y) has index two in E. Together with
the actual double-factor quotient this supplies the source coordinate and
central-hyperplane assertions for either factor count.

Source: Aschbacher--Smith, 15.4.12(4),(6) and 15.4.14(1), pp.1160--1161.
-/

public noncomputable section
open Subgroup Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource FamilySource.ModuleStructure BaumannSylow
open Chapter1.RadicalNormalizers.ThompsonSource FamilySource.ThompsonFactors
open ChapterB ChapterB.BaumannArgument
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

private theorem one_plane_alpha_index
    (R : Sylow 2 G) (W : Subgroup G) [W.Normal] [IsElementaryAbelian 2 W]
    (hcard : Nat.card W = 4) (hWR : W ≤ (R : Subgroup G))
    (hker : IsPGroup 2 (centralizer (W : Set G)))
    (hLcard : Nat.card ((pResidual 2 G).map
      (MulAut.conjNormal : G →* MulAut W)) = 3)
    (hJcard : Nat.card ((elementaryAbelianMaxJ (R : Subgroup G)).map
      (MulAut.conjNormal : G →* MulAut W)) = 2) :
    (thompsonAlpha (R : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)).relIndex
      (thompsonAlpha (R : Subgroup G)) = 2 := by
  let : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; decide)
  let : IsKleinFour W := ⟨hcard,IsElementaryAbelian.exponent_eq_prime⟩
  let E := thompsonAlpha (R : Subgroup G)
  let C := E ⊓ centralizer (pResidual 2 G : Set G)
  let F := W ⊓ centralizer (elementaryAbelianMaxJ (R : Subgroup G) : Set G)
  let : IsElementaryAbelian 2 E := omegaOneCenterAmbient_elementaryAbelian _
  have hE := alpha_decomposition_from_one_plane R W hcard hWR hker hLcard hJcard
  have hFE : F ≤ E := le_sup_right.trans_eq hE.symm
  have hcomm : C ≤ centralizer (F : Set G) :=
    inf_le_left.trans ((le_centralizer E).trans (centralizer_le hFE))
  have hfree : W ⊓ centralizer (pResidual 2 G : Set G) = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (fixedEquiv W (pResidual 2 G))]
    exact IsKleinFour.three_fixed_card _ hLcard
  apply LocalSetup.TwoFactors.centralizer_index_two_of_fixed_complement hE.symm hcomm
    (show C ≤ centralizer (pResidual 2 G : Set G) from inf_le_right)
    (le_bot_iff.mp ((inf_le_inf_right _ inf_le_left).trans hfree.le))
  rw [Nat.card_congr (fixedEquiv W (elementaryAbelianMaxJ (R : Subgroup G)))]
  exact IsKleinFour.two_fixed_card _ hJcard

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

/-- The Baumann Sylow conclusion for either actual source parameter. -/
theorem source_member_baumann_sylow {κ : GroupClass}
    (hB : TheoremB216.{u}) {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input κ T M X s) :
    Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (X ⊔ baumann (T : Subgroup G)) := by
  obtain ⟨hE,d,hc⟩ := source_join_exceptional hB h
  let := hE
  have hs := ambient_sylow_of_exceptional T (X ⊔ (T : Subgroup G)) le_sup_right
    h.center_centralizer (member_minimalParabolic T h.member h.quotient_elementary) d hc
  rwa [member_residual_join T h.member] at hs

/-- The one-factor source input forces an index-two centralizer in the
original Thompson omega center. -/
theorem source_single_alpha_index {κ : GroupClass}
    (hB : TheoremB216.{u}) {T : Sylow 2 G} {M X : Subgroup G}
    (h : Input κ T M X 1) :
    (thompsonAlpha (T : Subgroup G) ⊓ centralizer (X : Set G)).relIndex
      (thompsonAlpha (T : Subgroup G)) = 2 := by
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
  have hindex := one_plane_alpha_index S (moduleGroup d) hmodule
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
  rw [← hmap,← hAlpha,relIndex_map_map_of_injective _ _ H.subtype_injective]
  exact hindex

/-- Both source parameters give the coordinate alternatives used by 15.4.14. -/
theorem source_member_coordinates {κ : GroupClass}
    (hB : TheoremB216.{u}) {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input κ T M X s) :
    ((thompsonAlpha (T : Subgroup G) ⊓ centralizer (X : Set G)).relIndex
      (thompsonAlpha (T : Subgroup G)) = 2) ∨
    Nonempty (LocalSetup.TwoFactors.SwappedBinaryQuotient
      (thompsonAlpha (T : Subgroup G)) (T : Subgroup G) X) := by
  rcases h.parameter with hs | hs
  · subst s
    exact Or.inl (source_single_alpha_index hB h)
  · subst s
    exact Or.inr (LocalSetup.SourceWitnesses.source_swappedBinaryQuotient h)

/-- The original central omega subgroup has a fixed hyperplane for every
source member, before any cardinality assumption on that subgroup. -/
theorem source_member_hyperplane {κ : GroupClass}
    (hB : TheoremB216.{u}) {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input κ T M X s) :
    (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (X : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2 := by
  have hne : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ centralizer (X : Set G) := by
    intro hc
    have hXT : X ≤ (T : Subgroup G) := (le_centralizer_iff.mp hc).trans_eq h.center_centralizer
    have hp : IsPGroup 2 X := T.isPGroup'.of_injective (inclusion hXT) (inclusion_injective hXT)
    exact member_core_ne_top _ h.member (top_unique (le_sSup ⟨inferInstance,
      hp.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup X) ≃* X).symm⟩))
  rcases source_member_coordinates hB h with hi | hd
  · exact LocalSetup.TwoFactors.centralizer_index_two_of_single_factor
      (LocalSetup.TwoFactors.centralOmega_le_thompsonAlpha _) hi hne
  · obtain ⟨d⟩ := hd
    apply LocalSetup.TwoFactors.centralizer_index_two_of_swapped_quotient d
      (LocalSetup.TwoFactors.centralOmega_le_thompsonAlpha _) _ hne
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm

/-- The complete source Baumann-normalizer conclusion for either parameter. -/
theorem source_member_baumann_normalizer
    (hB : TheoremB216.{u}) (h311 : RatioSource.Earlier311 (G := G))
    {T : Sylow 2 G} {M X : Subgroup G} {s : ℕ}
    (h : Input KnownSimple.IsKnownSimple T M X s)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ (T : Subgroup G) ≤ N → N = M) :
    normalizer (baumann (T : Subgroup G) : Set G) ≤ M := by
  apply LocalSetup.lemma_15_4_16 h.ambient ?_ T h.maximal h.sylow_le h.member_le
    ((normal_subgroupOf_iff_le_normalizer h.member_le).mp h.normal)
    (YFamily.perfect h.member) (member_core_ne_top _ h.member)
    (member_quotient_irreducible T h.member h.quotient_elementary)
    (by simpa only [ChapterB.thompsonJ_zero] using h.member.2)
    (source_member_baumann_sylow hB h) hunique
  intro hG S R M₀ H hM₀ hH hu hRne hRS hs hn
  obtain ⟨N,hNR,hNne,hN⟩ := h311 S hG M₀ H R hM₀ hH hu hRne hRS hs
    (Chapter3.normalIn_iff_le_normalizer.mp hn).2
  exact ⟨N,hNne,hNR,by simpa only [Chapter3.generated_eq_sup] using hN⟩

end CFSG.Quasithin.Chapter15.Section04.InitialSource
