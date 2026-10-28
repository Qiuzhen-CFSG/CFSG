module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.Rank
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.FixedSpaces
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall.Placement

/-!
# The rank-two Hall/Cartan endpoint on the original chosen flag

Odd-prime rank two forces the fixed space of an actor in L to be exactly
C_V(L), through the literal map L → L/O₂(L) and the original natural
projection. Since z is a nonidentity point fixed by Kz, this bounds the
odd-prime rank of Kz intersect L by one. Source 11.4.1 discharges vanishing
of C_V(L) from the authorized earlier inputs.

The final endpoint applies this bound to O³(Y) Ω₁(O₃(Y)), preserving the
actual Y-image in KzT/C(VK) and its projection to L/O₂(L). The 11.0.4
residual step is proved for all three markings, with only the earlier
SL₃ cubic clause explicit. Constructing a nilpotent odd actor in Kz
normalizing L with the stated prime support and image rank remains this
task's Hall-geometry obligation. No Hall existence or full 11.4.2 result
is asserted here. Earlier-source discharge remains with
qt-d-1222-shadow-components; the proper-overcomponent comparison and
final local assembly remain with qt-d-1222-shadow-component-comparison.
Source: Aschbacher--Smith, 11.4.2, printed pp.776--777.
-/

@[expose] public noncomputable section
open Subgroup Matrix Theory.GroupTheory Representation
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
open LocalGeometry CommonCore CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {F : BinaryField}

/-- Any odd-prime rank-two subgroup of the marked model fixes only zero. -/
theorem model_fixed_zero (c : Coordinates D F)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (A : Subgroup c.ModelGroup)
    (hr : 2 ≤ primeRank p A) (v : c.Space)
    (hv : ∀ a ∈ A, c.modelAction a v = v) : v = 0 := by
  cases c with
  | sl3 m => exact sl3_fixed_eq_zero hp A hr v hv
  | sp4 m => exact sp4_fixed_eq_zero hp A hr v hv
  | g2 m => exact g2_fixed_eq_zero hp A hr v hv

/-- Rank-two Cartan actors have exactly the original L-fixed space on V,
including its central kernel. No diagonal marking is assumed. -/
theorem natural_fixed_space_of_rank_two (c : Coordinates D F)
    (A : Subgroup G) (hAL : A ≤ L)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hr : 2 ≤ primeRank p A) :
    V ⊓ centralizer (A : Set G) = V ⊓ centralizer (L : Set G) := by
  apply le_antisymm _ (inf_le_inf_left _ (centralizer_le hAL))
  rintro v ⟨hv,hfix⟩
  refine ⟨hv,?_⟩
  let B := (A.subgroupOf L).map c.quotientMap
  have hk : IsPGroup 2 c.quotientMap.ker := by
    rw [Coordinates.quotientMap, MonoidHom.ker_comp_of_injective _ _ c.groupEquiv.injective,
      QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hrB : 2 ≤ primeRank p B := by
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel hp c.quotientMap hk,
      primeRank_equiv p (subgroupOfEquivOfLe hAL)]
    exact hr
  have he : (c.projection ⟨v,hv⟩).toAdd = 0 := by
    apply model_fixed_zero c hp B hrB
    rintro _ ⟨a,ha,rfl⟩
    rw [← c.projection_component_conjugation]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hfix a ha)
  exact (c.projection_eq_one_iff ⟨v,hv⟩).mp he

/-- The actual point fixed by Kz contradicts any rank-two Cartan subgroup
of Kz lying in L. The 11.4.1 fixed-space
premise is discharged by the original chosen-module theorem. -/
theorem ofFlag_false_of_rank_two_cartan
    (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (A : Subgroup G) (hAK : A ≤ (ofFlag S f X z H).Kz) (hAL : A ≤ L)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hr : 2 ≤ primeRank p A) : False := by
  have hzV : z ∈ V := D.centralQuotientPreimage_le _ h.point_mem
  have hzA : z ∈ centralizer (A : Set G) := by
    intro a ha
    exact (mem_centralizer_singleton_iff.mp (h.point_component.1 (hAK ha)))
  have he := natural_fixed_space_of_rank_two c A hAL hp hr
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  exact h.point_ne_one (hf.le (he.le ⟨hzV,hzA⟩))

/-- On the literal chosen flag, the intersection of the point component
with L has odd-prime rank at most one. This is the obstruction used by the
Hall construction; all fixed-space hypotheses come from 11.4.1. -/
theorem ofFlag_intersection_primeRank_le_one
    (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) :
    primeRank p ((ofFlag S f X z H).Kz ⊓ L : Subgroup G) ≤ 1 := by
  by_contra! hr
  exact ofFlag_false_of_rank_two_cartan S f X z H h hlinear h1132
    _ inf_le_left inf_le_right hp (by omega)

/-- The Hall actor uses the original inclusion in KzT and its actual VK-action quotient. -/
def pointHallProjection (E : Closure.Geometry D) (Y : Subgroup G) (hYK : Y ≤ E.Kz) :
    Y →* ActionQuotient E :=
  (projection E).comp (inclusion (hYK.trans (show E.Kz ≤ localGroup E from le_sup_left)))

/-- Representatives retain the same ambient element throughout the Hall action. -/
@[simp] theorem pointHallProjection_apply (E : Closure.Geometry D) (Y : Subgroup G)
    (hYK : Y ≤ E.Kz) (y : Y) :
    pointHallProjection E Y hYK y = projection E
      ⟨y,(hYK.trans (show E.Kz ≤ localGroup E from le_sup_left)) y.property⟩ := rfl

/-- Its image is precisely the source Y-star in KzT/C(VK). -/
theorem pointHallProjection_range (E : Closure.Geometry D) (Y : Subgroup G)
    (hYK : Y ≤ E.Kz) :
    (pointHallProjection E Y hYK).range = (Y.subgroupOf (localGroup E)).map (projection E) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact mem_map_of_mem (projection E) y.property
  · rintro ⟨y,hy,rfl⟩
    exact ⟨⟨y,hy⟩,rfl⟩

/-- Literal Hall-rank application: the source Y1 is constructed by its
three-residual and omega-three subgroup. Only placement, nilpotence and
rank of the actual Y-image remain to be supplied by the Hall geometry. -/
theorem ofFlag_false_of_hall_image
    (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (Y : Subgroup G) [Group.IsNilpotent Y]
    (hYK : Y ≤ (ofFlag S f X z H).Kz) (hYL : oddCartanPart Y ≤ L)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hr : 2 ≤ primeRank p (pointHallProjection (ofFlag S f X z H) Y hYK).range) : False := by
  apply ofFlag_false_of_rank_two_cartan S f X z H h hlinear h1132
    (oddCartanPart Y) ((oddCartanPart_le Y).trans hYK) hYL hp
  have hq := oddCartanPart_quotient_rank_two L Y hYL hp
    (pointHallProjection (ofFlag S f X z H) Y hYK) hr
  rwa [componentQuotient_primeRank L _ hYL hp] at hq

/-- The source Hall/Cartan endpoint with 11.0.4 placement discharged by the
actual residual theorems. Its remaining local obligation is to construct a
nilpotent odd actor in Kz normalizing L with the stated prime support and
rank-two image. The SL3 cubic input is the earlier source clause. -/
theorem ofFlag_false_of_source_hall
    (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (Y : Subgroup G) [Group.IsNilpotent Y]
    (hYK : Y ≤ (ofFlag S f X z H).Kz)
    (hYM : Y ≤ normalizer (L : Set G)) (ho : Odd (Nat.card Y))
    (hsupport : ∀ p : ℕ, p.Prime → p ∣ Nat.card Y → p ∣ 2 ^ S.field.degree - 1)
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      ∀ y ∈ Y, orderOf y = 3 → y ∈ L)
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hr : 2 ≤ primeRank p (pointHallProjection (ofFlag S f X z H) Y hYK).range) : False :=
  ofFlag_false_of_hall_image S f X z H h hlinear h1132 Y hYK
    (oddCartanPart_le_of_source S c Y hYM ho hsupport hcubic) hp hr

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
