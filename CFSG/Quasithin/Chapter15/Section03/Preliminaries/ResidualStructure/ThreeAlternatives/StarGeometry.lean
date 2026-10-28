module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.Inputs
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.ChapterA.Section02.OddPrimeRank

/-!
# The actual star quotient and its central commutators

Normality of the literal residual identifies its intrinsic two-core quotient
with its image in `M/O₂(M)`. The natural action descends to that quotient;
its kernel is the star image of `C_M(V)`. Since the residual's action image
is E₉, its commutator lies in this kernel. The centralization assertion of
14.1.17(3) then puts that commutator in the center of `Y*`.

The rank upper bound uses only subgroup monotonicity and lifting through a
normal two-kernel. Generation by order-three elements and the three-group
assertion remain separate obligations, before applying A.1.24.

Source: Aschbacher–Smith, Lemma 15.3.7, printed p.1122.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives
variable {G : Type*} [Group G]

/-- The compatible actor homomorphism on the actual star quotient. -/
@[expose] public def starActor {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (hQ : pCore 2 M ≤ d.actor.ker) : StarGroup M →* OrthogonalActor :=
  QuotientGroup.lift (pCore 2 M) d.actor hQ

/-- Passing through the star quotient does not change the action image. -/
public theorem map_starActor {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (hQ : pCore 2 M ≤ d.actor.ker) (X : Subgroup G) :
    (star M X).map (starActor d hQ) = (X.subgroupOf M).map d.actor := by
  rw [star, map_map, starActor, QuotientGroup.lift_comp_mk']

/-- The star actor's kernel is precisely the star centralizer, not a two-group. -/
public theorem ker_starActor {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (hQ : pCore 2 M ≤ d.actor.ker) :
    (starActor d hQ).ker = star M (M ⊓ centralizer (V : Set G)) := by
  rw [starActor, QuotientGroup.ker_lift, d.ker_actor, star]
  congr 1
  ext x
  exact ⟨fun hx => ⟨x.property, hx⟩, fun hx => hx.2⟩

/-- The source quotient is genuinely isomorphic to the actual star residual. -/
public noncomputable def residualCoreQuotientEquivStar [Finite G] (M Mc : Subgroup G) :
    (residualY M Mc ⧸ pCore 2 (residualY M Mc)) ≃* star M (residualY M Mc) := by
  let N := (residualY M Mc).subgroupOf M
  let : N.Normal := residualY_normal M Mc
  let e := (subgroupOfEquivOfLe
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)).symm
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (coreQuotientEquivImage 2 N)

/-- The quotient identification sends each representative to its actual star image. -/
@[simp] public theorem residualCoreQuotientEquivStar_apply_mk [Finite G]
    (M Mc : Subgroup G) (y : residualY M Mc) :
    ((residualCoreQuotientEquivStar M Mc)
      (QuotientGroup.mk' (pCore 2 (residualY M Mc)) y) : StarGroup M) =
    QuotientGroup.mk' (pCore 2 M)
      (Subgroup.inclusion (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) y) := by
  let : ((residualY M Mc).subgroupOf M).Normal := residualY_normal M Mc
  change ((coreQuotientEquivImage 2 ((residualY M Mc).subgroupOf M))
    (QuotientGroup.mk' _ ((subgroupOfEquivOfLe
      (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)).symm y)) : StarGroup M) = _
  exact coreQuotientEquivImage_apply_mk _ _ _

/-- E₉ as action image and the star centralization give class at most two. -/
public theorem star_class_two [Finite G] {M Mc V : Subgroup G} {T : Sylow 2 G}
    {d : NaturalOrthogonalAction M V} (h : SourceInputs M Mc V T d) :
    _root_.commutator (star M (residualY M Mc)) ≤
      center (star M (residualY M Mc)) := by
  let P := star M (residualY M Mc)
  let f := starActor d h.core_le_kernel
  have hf : P.map f = ((residualY M Mc).subgroupOf M).map d.actor :=
    map_starActor d h.core_le_kernel _
  obtain ⟨e⟩ := h.image_model
  have hAb : IsMulCommutative (P.map f) := by
    rw [hf]
    exact ⟨⟨fun a b => e.injective (by simp only [map_mul, mul_comm])⟩⟩
  have hder : ⁅P, P⁆ ≤ f.ker := by
    rw [← Subgroup.map_eq_bot_iff, map_commutator]
    exact commutator_self_eq_bot_iff.mpr hAb
  have hc : f.ker ≤ centralizer (P : Set (StarGroup M)) := by
    rw [ker_starActor]
    exact h.star_centralizes.trans (centralizer_le
      (show (P : Set (StarGroup M)) ⊆
        ((P ⊔ star M (Rc M Mc) : Subgroup (StarGroup M)) : Set (StarGroup M)) from
        show P ≤ P ⊔ star M (Rc M Mc) from le_sup_left))
  intro x hx
  have hxder : (x : StarGroup M) ∈ ⁅P, P⁆ := by
    rw [← P.map_subtype_commutator]
    exact mem_map_of_mem _ hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact mem_centralizer_iff.mp (hc (hder hxder)) y y.property

/-- The source quasithin rank bound survives the star quotient. -/
public theorem star_rank_le_two [Finite G] {M Mc V : Subgroup G} {T : Sylow 2 G}
    {d : NaturalOrthogonalAction M V} (h : SourceInputs M Mc V T d) :
    primeRank 3 (star M (residualY M Mc)) ≤ 2 := by
  exact (primeRank_subgroup_le 3 _).trans
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 M)
      pCore_isPGroup).trans h.rank_bound)

private theorem elementaryNine_card : Nat.card ElementaryNine = 3 ^ 2 := by
  simp [ElementaryNine, Nat.card_eq_fintype_card]

private theorem elementaryNine_cube : ∀ x : ElementaryNine, x ^ 3 = 1 := by
  decide +kernel

private theorem elementaryNine_rank : primeRank 3 ElementaryNine = 2 := by
  apply le_antisymm
  · apply (primeRank_le_iff_elementary_card_le ElementaryNine).mpr
    intro E _
    exact E.card_le_card_group.trans elementaryNine_card.le
  · exact primeRank_ge_of_elementary_embedding elementaryNine_cube elementaryNine_card
      (MonoidHom.id _) Function.injective_id

/-- The star residual has rank exactly two, since it maps onto the actual E₉. -/
public theorem star_rank [Finite G] {M Mc V : Subgroup G} {T : Sylow 2 G}
    {d : NaturalOrthogonalAction M V} (h : SourceInputs M Mc V T d) :
    primeRank 3 (star M (residualY M Mc)) = 2 := by
  apply le_antisymm (star_rank_le_two h)
  let P := star M (residualY M Mc)
  let f := starActor d h.core_le_kernel
  obtain ⟨e⟩ := h.image_model
  let e' : (P.map f) ≃* ElementaryNine :=
    (MulEquiv.subgroupCongr (map_starActor d h.core_le_kernel _)).trans e
  let g := e'.toMonoidHom.comp (f.subgroupMap P)
  have honto : Function.Surjective g := e'.surjective.comp (f.subgroupMap_surjective P)
  have hr := PrimeRank.le_of_surjective_of_target_le_two (by decide : 3 ≠ 2)
    g honto elementaryNine_rank.le
  rwa [elementaryNine_rank] at hr

end CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives
