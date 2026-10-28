module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.Intersection
public import Theory.GroupTheory.SylowSubgroupNormalizerImage
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Lifting the radical normalizer through the actual component action

The source identity O₂(KzT) = C_T(VK) puts the Sylow intersection with
ker(KzT → KzT/C(VK)) inside R₁. Relative Sylow conjugacy therefore lifts
the whole normalizer of the R₁ image, including odd kernel factors.
An odd-primary subgroup of the lifted normalizer lies in Kz because
KzT/Kz is a two-group. A Sylow choice supplies a rank-two actor whenever
the image normalizer has rank two. No Hall subgroup or nilpotence input
is needed. The actual chosen-flag contradiction applies the earlier
prime-residual and fixed-space results to this constructed actor.

The quotient normalizer's rank and its ambient placement remain local
geometric obligations of qt-d-1222-shadow-component-comparison. The earlier
source inputs retain final discharge by qt-d-1222-shadow-components.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The original R1 normalizer maps onto the normalizer of its actual VK-action image. -/
theorem radical_normalizer_image
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) :
    (normalizer (radical E : Set (localGroup E))).map (projection E) =
      normalizer ((radical E).map (projection E) : Set (ActionQuotient E)) := by
  apply (sylow E).normalizer_map_of_contains_kernel_intersection
    (radical E) (fun _ hx => radical_le_sylow E hx) (projection E)
    (QuotientGroup.mk'_surjective _)
  have he := (action_structure E h hf hne hstar hcent).1
  simpa only [projection, ChapterB.InternalThompsonAction.actionMk,
    QuotientGroup.ker_mk', ← he] using intrinsic_core_le_radical E

/-- Every odd-primary subgroup of KzT lies in Kz, since KzT/Kz is a two-group. -/
theorem odd_subgroup_le_component (h : EarlierGeometry E)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup (localGroup E)) (hA : IsPGroup p A) : A ≤ component E := by
  let := component_normal E h
  have hq : IsPGroup 2 (localGroup E ⧸ component E) :=
    isPGroup_quotient_of_sup_eq_top (component E) (sylow E : Subgroup (localGroup E))
      (sylow E).isPGroup' (component_sup_sylow E)
  let q := QuotientGroup.mk' (component E)
  have hd := (hA.map q).disjoint_of_coprime (hq.of_injective (⊤ : Subgroup _).subtype Subtype.val_injective)
    hp.coprime_two_right
  have hb : A.map q = ⊥ := by simpa using hd.eq_bot
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff A).mp hb

/-- A rank-two normalizer image supplies a genuine odd-primary actor in the
original point component and the original radical normalizer. -/
theorem exists_odd_actor_of_normalizer_rank
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hr : 2 ≤ primeRank p (normalizer
      ((radical E).map (projection E) : Set (ActionQuotient E)))) :
    ∃ Y : Subgroup G, Y ≤ E.Kz ∧ Y ≤ normalizer (E.R₁ : Set G) ∧
      IsPGroup p Y ∧ 2 ≤ primeRank p Y := by
  let N := normalizer (radical E : Set (localGroup E))
  let q := (projection E).comp N.subtype
  have hrq : 2 ≤ primeRank p q.range := by
    have he : q.range = N.map (projection E) := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [he, radical_normalizer_image E h hf hne hstar hcent]
    exact hr
  have hrN := two_le_primeRank_of_image hp q hrq
  let P : Sylow p N := default
  let A := (P : Subgroup N).map N.subtype
  have hA : IsPGroup p A := P.isPGroup'.map _
  have hAc := odd_subgroup_le_component E h hp A hA
  let Y := A.map (localGroup E).subtype
  refine ⟨Y, ?_, ?_, hA.map _, ?_⟩
  · rintro _ ⟨a,ha,rfl⟩
    exact hAc ha
  · have hR : E.R₁ ≤ localGroup E := (radical_le_sylow E).trans le_sup_right
    have he : (normalizer (radical E : Set (localGroup E))).map (localGroup E).subtype =
        normalizer (E.R₁ : Set G) ⊓ localGroup E := by
      rw [radical, ← subgroupOf_normalizer_eq hR, subgroupOf_map_subtype]
    exact (map_mono (map_subtype_le (P : Subgroup N))).trans (he.le.trans inf_le_left)
  · rw [← primeRank_equiv p (A.equivMapOfInjective
      (localGroup E).subtype (localGroup E).subtype_injective),
      ← primeRank_equiv p ((P : Subgroup N).equivMapOfInjective N.subtype N.subtype_injective),
      ← P.primeRank_eq]
    exact hrN

variable {E}

/-- The actual chosen-flag contradiction now constructs its odd actor.
Only the quotient normalizer rank and its ambient placement remain local
geometric inputs; all lifting and prime-residual intersections are proved. -/
theorem ofFlag_false_of_radical_normalizer_rank
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hstar : (ofFlag S f X z H).Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    (hNM : normalizer ((ofFlag S f X z H).R₁ : Set G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hd : p ∣ 2 ^ S.field.degree - 1)
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      ∀ y ∈ normalizer (L : Set G), orderOf y = 3 → y ∈ L)
    (hr : 2 ≤ primeRank p (normalizer
      ((radical (ofFlag S f X z H)).map (projection (ofFlag S f X z H)) :
        Set (ActionQuotient (ofFlag S f X z H))))) : False := by
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  obtain ⟨Y,hYK,hYR,_,hrY⟩ := exists_odd_actor_of_normalizer_rank
    (ofFlag S f X z H) h hf hne hstar hcent hp hr
  have hYL := hYR.trans hNM
  rw [← primeRank_intersection_eq_of_source S c Y hYL hp hd
    (fun hs y hy h3 => hcubic hs y (hYL hy) h3)] at hrY
  exact ofFlag_false_of_rank_two_cartan S f X z H h hlinear h1132
    (Y ⊓ L) (inf_le_left.trans hYK) inf_le_right hp hrY

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
