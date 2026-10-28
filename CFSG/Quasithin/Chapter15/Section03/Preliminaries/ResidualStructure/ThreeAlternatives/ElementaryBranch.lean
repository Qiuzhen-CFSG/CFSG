module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.StarGeometry
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# The elementary-nine alternative of 15.3.7

An actual isomorphism `Y* ≃ E₉` makes the action on `Y*` faithful: its
image also has order nine. Via the representative-compatible identification
`Y/O₂(Y) ≃ Y*`, the action kernel is therefore exactly `O₂(Y) = C_Y(V)`.

The star image of `C_M(V)` centralizes `Y*` and is disjoint from it. Additivity
of prime rank on commuting disjoint subgroups, together with `m₃(M) ≤ 2`,
shows that this kernel has order prime to three. The actual action-image
calculation and the Sylow two-subgroup then give a supplement to `Y*` and
prove that `Y` has index prime to three in `M`. Finally, `Y/O₂(Y)` is a
three-group, so the quotient of `Y` by its prime-to-three residual is a
two-group; the already proved two-perfectness of `Y` makes it trivial.

Thus all three clauses of the elementary alternative follow from the
published preceding inputs and the genuine elementary-nine branch witness.
The parent assembly supplies that witness through A.1.24.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 15.3.7(1), printed p.1122 (PDF p.1139).
-/

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives
variable {G : Type*} [Group G] [Finite G]
variable {M Mc V : Subgroup G} {T : Sylow 2 G} {d : NaturalOrthogonalAction M V}

private theorem elementary_star_disjoint_kernel (h : SourceInputs M Mc V T d)
    (he : Nonempty (star M (residualY M Mc) ≃* ElementaryNine)) :
    Disjoint (star M (residualY M Mc)) (starActor d h.core_le_kernel).ker := by
  let P := star M (residualY M Mc)
  let f := starActor d h.core_le_kernel
  obtain ⟨e⟩ := he
  obtain ⟨a⟩ := h.image_model
  have hc : Nat.card P = Nat.card (P.map f) := by
    rw [map_starActor]
    exact (Nat.card_congr e.toEquiv).trans (Nat.card_congr a.toEquiv).symm
  have hi : Function.Injective (f.subgroupMap P) :=
    ((f.subgroupMap_surjective P).bijective_of_nat_card_le hc.le).1
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  intro x hx
  have hx1 : (⟨x, hx.1⟩ : P) = 1 := hi (Subtype.ext (by simpa using hx.2))
  exact congrArg Subtype.val hx1

private theorem elementary_core_eq_centralizer (h : SourceInputs M Mc V T d)
    (he : Nonempty (star M (residualY M Mc) ≃* ElementaryNine)) :
    (residualY M Mc).pCoreIn 2 = residualY M Mc ⊓ centralizer (V : Set G) := by
  let Y := residualY M Mc
  let e := residualCoreQuotientEquivStar M Mc
  let i := Subgroup.inclusion (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)
  let q := QuotientGroup.mk' (pCore 2 Y)
  have hd := elementary_star_disjoint_kernel h he
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    have hq : q y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
    have hs : QuotientGroup.mk' (pCore 2 M) (i y) = 1 := by
      rw [← residualCoreQuotientEquivStar_apply_mk]
      change (e (q y) : StarGroup M) = 1
      rw [hq, map_one, OneMemClass.coe_one]
    have ha : d.actor (i y) = 1 := by
      have hh := congrArg (starActor d h.core_le_kernel) hs
      simpa [starActor] using hh
    change i y ∈ (centralizer (V : Set G)).subgroupOf M
    rw [← d.ker_actor]
    exact ha
  · rintro x ⟨hxY, hxC⟩
    let y : Y := ⟨x, hxY⟩
    have ha : d.actor (i y) = 1 := by
      change i y ∈ d.actor.ker
      rw [d.ker_actor]
      exact hxC
    have hs : (e (q y) : StarGroup M) = 1 := by
      apply (disjoint_iff.mp hd).le
      refine ⟨(e (q y)).property, ?_⟩
      change starActor d h.core_le_kernel (e (q y)) = 1
      rw [residualCoreQuotientEquivStar_apply_mk]
      exact ha
    have hq : q y = 1 := e.injective (by apply Subtype.ext; simpa using hs)
    exact ⟨y, (QuotientGroup.eq_one_iff y).mp hq, rfl⟩

private theorem elementary_star_kernel_coprime (h : SourceInputs M Mc V T d)
    (he : Nonempty (star M (residualY M Mc) ≃* ElementaryNine)) :
    Nat.Coprime 3 (Nat.card (starActor d h.core_le_kernel).ker) := by
  let P := star M (residualY M Mc)
  let C := (starActor d h.core_le_kernel).ker
  have hc : C ≤ centralizer (P : Set (StarGroup M)) := by
    dsimp only [C]
    rw [ker_starActor]
    exact h.star_centralizes.trans (centralizer_le
      (show P ≤ P ⊔ star M (Rc M Mc) from le_sup_left))
  have hr := primeRank_subgroup_le 3 (P ⊔ C)
  rw [primeRank_sup_eq_add_of_disjoint_commuting P C
    (elementary_star_disjoint_kernel h he) (le_centralizer_iff.mp hc), star_rank h] at hr
  have hs : primeRank 3 (StarGroup M) ≤ 2 :=
    (primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 M)
    pCore_isPGroup).trans h.rank_bound
  have hz : primeRank 3 C = 0 := by omega
  exact Nat.prime_three.coprime_iff_not_dvd.mpr
    (PrimeRank.eq_zero_iff_not_dvd_card.mp hz)

private theorem elementary_star_supplement (h : SourceInputs M Mc V T d) :
    (star M (residualY M Mc) ⊔ (starActor d h.core_le_kernel).ker) ⊔
      star M (T : Subgroup G) = ⊤ := by
  let f := starActor d h.core_le_kernel
  have himage : (star M (residualY M Mc) ⊔ star M (T : Subgroup G)).map f = ⊤ := by
    rw [Subgroup.map_sup, map_starActor, map_starActor, h.residual_image]
    exact twoResidualAmbient_top_sup_sylow ((T.subtype h.sylow_le).mapSurjective d.onto)
  have hh := congrArg (fun A : Subgroup OrthogonalActor => A.comap f) himage
  simpa only [comap_map_eq, comap_top, sup_assoc, sup_comm, sup_left_comm] using hh

private theorem elementary_star_index_coprime (h : SourceInputs M Mc V T d)
    (he : Nonempty (star M (residualY M Mc) ≃* ElementaryNine)) :
    Nat.Coprime 3 (star M (residualY M Mc)).index := by
  let P := star M (residualY M Mc)
  let C := (starActor d h.core_le_kernel).ker
  let R := star M (T : Subgroup G)
  let : ((residualY M Mc).subgroupOf M).Normal := residualY_normal M Mc
  let : P.Normal := (inferInstance : ((residualY M Mc).subgroupOf M).Normal).map
    (QuotientGroup.mk' (pCore 2 M)) (QuotientGroup.mk'_surjective _)
  have hR : IsPGroup 2 R := T.isPGroup'.comap_subtype.map _
  have hRc : Nat.Coprime 3 (Nat.card R) := by
    obtain ⟨n, hn⟩ := hR.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  have hi : Nat.Coprime 3 (P ⊔ C).index := by
    rw [← relIndex_top_right, ← elementary_star_supplement h, relIndex_sup_left]
    exact hRc.coprime_dvd_right (relIndex_dvd_card _ _)
  rw [← relIndex_mul_index (show P ≤ P ⊔ C from le_sup_left)]
  apply Nat.Coprime.mul_right _ hi
  rw [relIndex_sup_left]
  exact (elementary_star_kernel_coprime h he).coprime_dvd_right (relIndex_dvd_card _ _)

private theorem elementary_residual_index_coprime (h : SourceInputs M Mc V T d)
    (he : Nonempty (star M (residualY M Mc) ≃* ElementaryNine)) :
    Nat.Coprime 3 ((residualY M Mc).subgroupOf M).index := by
  let N := (residualY M Mc).subgroupOf M
  let : N.Normal := residualY_normal M Mc
  have hi := elementary_star_index_coprime h he
  have heq : (star M (residualY M Mc)).index = (N ⊔ pCore 2 M).index := by
    rw [star, index_map, QuotientGroup.ker_mk',
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), index_top, mul_one]
  rw [heq] at hi
  have hcore : Nat.Coprime 3 (Nat.card (pCore 2 M)) := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := M)).exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 3 2).pow_right n).coprime_dvd_right hn
  rw [← relIndex_mul_index (show N ≤ N ⊔ pCore 2 M from le_sup_left)]
  apply Nat.Coprime.mul_right _ hi
  rw [relIndex_sup_left]
  exact hcore.coprime_dvd_right (relIndex_dvd_card _ _)

private theorem elementary_primeToResidual_top
    (he : Nonempty (star M (residualY M Mc) ≃* ElementaryNine)) :
    primeToResidual 3 (residualY M Mc) = ⊤ := by
  let Y := residualY M Mc
  let Q := pCore 2 Y
  let N := primeToResidual 3 Y
  let q := QuotientGroup.mk' Q
  obtain ⟨e⟩ := he
  let e' := (residualCoreQuotientEquivStar M Mc).trans e
  have hp : IsPGroup 3 (Y ⧸ Q) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr e'.toEquiv]
    simp [ElementaryNine, Nat.card_eq_fintype_card]
  have hres : primeToResidual 3 (Y ⧸ Q) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨n, hn⟩ := hp y
    exact mem_primeToResidual_of_pow hn
  have hm : N.map q = ⊤ := by
    rw [map_primeToResidual_of_surjective 3 q (QuotientGroup.mk'_surjective Q), hres]
  have hs : N ⊔ Q = ⊤ := by
    have hh := congrArg (fun A : Subgroup (Y ⧸ Q) => A.comap q) hm
    simpa only [comap_map_eq, q, QuotientGroup.ker_mk', comap_top] using hh
  exact residualY_isPPerfect M Mc N inferInstance
    (isPGroup_quotient_of_sup_eq_top N Q pCore_isPGroup hs)

private theorem elementary_residual_eq_primeToResidual (h : SourceInputs M Mc V T d)
    (he : Nonempty (star M (residualY M Mc) ≃* ElementaryNine)) :
    residualY M Mc = (primeToResidual 3 M).map M.subtype := by
  let N := (residualY M Mc).subgroupOf M
  let : N.Normal := residualY_normal M Mc
  apply le_antisymm
  · intro x hx
    let y : residualY M Mc := ⟨x, hx⟩
    let i := Subgroup.inclusion (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)
    have hy : y ∈ primeToResidual 3 (residualY M Mc) := by
      rw [elementary_primeToResidual_top he]
      trivial
    exact ⟨i y, map_primeToResidual_le_of_hom 3 i (mem_map_of_mem _ hy), rfl⟩
  · have hn : primeToResidual 3 M ≤ N :=
      primeToResidual_le N (elementary_residual_index_coprime h he)
    have hh := map_mono (f := M.subtype) hn
    rwa [map_subgroupOf_eq_of_le (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)] at hh

/-- The complete elementary-nine branch: its exact two-core, quotient model,
and prime-to-three residual identity. -/
public theorem elementaryAlternative_of_star_equiv (h : SourceInputs M Mc V T d)
    (he : Nonempty (star M (residualY M Mc) ≃* ElementaryNine)) :
    ElementaryAlternative M Mc V := by
  refine ⟨elementary_core_eq_centralizer h he, ?_, elementary_residual_eq_primeToResidual h he⟩
  obtain ⟨e⟩ := he
  exact ⟨(residualCoreQuotientEquivStar M Mc).trans e⟩

end CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives
