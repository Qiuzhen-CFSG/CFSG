module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Pair
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.FullAction
public import Theory.SpecificGroups.SL2.TwoCore

/-!
# The actual action kernel in the opposite-pair construction

The kernel of LT on the original V is a two-group: its intersection with L
is O₂(L), and LT/L is a two-group. Consequently it is exactly O₂(LT).
An opposite pair with SL₂ action image therefore has its two-core inside
O₂(LT). No containment in O₂(G₁) is used here.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The action on the original V, with domain the literal LT. -/
def largeAction : (L ⊔ (T : Subgroup G) : Subgroup G) →* MulAut V :=
  V.normalizerMonoidHom.comp (inclusion (sup_le D.normalizes E.input.sylow_normalizes))

include E

theorem largeAction_ker : (largeAction E).ker =
    (centralizer (V : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) := by
  ext x
  change V.normalizerMonoidHom _ = 1 ↔ _
  rw [← MonoidHom.mem_ker, normalizerMonoidHom_ker]
  rfl

/-- The kernel calculation keeps both original subgroup inclusions. -/
theorem largeAction_kernel_isPGroup : IsPGroup 2 (largeAction E).ker := by
  let J := L ⊔ (T : Subgroup G)
  let N := L.subgroupOf J
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer
    (show L ≤ J from le_sup_left)).mpr
      (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hgen : N ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup (show L ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hquot : IsPGroup 2 (J ⧸ N) := isPGroup_quotient_of_sup_eq_top N
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype hgen
  let f := largeAction E
  let q := (QuotientGroup.mk' N).comp f.ker.subtype
  have hqker : IsPGroup 2 q.ker := by
    let r : q.ker →* L :=
      (J.subtype.comp (f.ker.subtype.comp q.ker.subtype)).codRestrict L (by
        intro x
        exact (QuotientGroup.eq_one_iff (N := N) x.val.val).mp x.property)
    have hr : ∀ x : q.ker, r x ∈ pCore 2 L := by
      intro x
      apply (FullAction.componentHom_ker E).le
      change FullAction.componentHom (D := D) (r x) = 1
      exact x.val.property
    let r' : q.ker →* pCore 2 L := r.codRestrict _ hr
    apply pCore_isPGroup.of_injective r'
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 L => (x.val : G)) hab
  have hp := (hquot.to_subgroup ⊤).comap_of_ker_isPGroup q hqker
  rw [comap_top] at hp
  exact hp.of_equiv topEquiv

/-- The full-module kernel is precisely the original large two-core. -/
theorem large_centralizer_eq_core :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hk : (largeAction E).ker ≤ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) :=
    le_sSup ⟨inferInstance, largeAction_kernel_isPGroup E⟩
  have hm := map_mono (f := (L ⊔ (T : Subgroup G)).subtype) hk
  rw [largeAction_ker, subgroupOf_map_subtype, inf_comm] at hm
  exact le_antisymm hm (le_inf (pCoreIn_le 2 _) D.core_centralizes)

/-- Computing images through LT gives the same original normalizer action. -/
theorem largeAction_image (A : Subgroup G) (hA : A ≤ L ⊔ (T : Subgroup G)) :
    (A.subgroupOf (L ⊔ (T : Subgroup G))).map (largeAction E) =
      actionImage (V := V) A := by
  rw [largeAction, ← map_map]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ha
  · intro hx
    exact ⟨⟨x, hA hx⟩, hx, Subtype.ext rfl⟩

/-- The kernel proof applies to every original subgroup of LT. -/
theorem actionImage_core (A : Subgroup G) (hA : A ≤ L ⊔ (T : Subgroup G)) :
    actionImage (V := V) (A.pCoreIn 2) = (actionImage (V := V) A).pCoreIn 2 := by
  rw [← largeAction_image E _ ((pCoreIn_le 2 A).trans hA),
    ← pCoreIn_subgroupOf 2 A _ hA,
    map_pCoreIn_of_ker_isPGroup (largeAction E) (largeAction_kernel_isPGroup E),
    largeAction_image E A hA]

/-- A trivial core of the genuine action image forces the desired core bound. -/
theorem core_le_large_core_of_image (A : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G))
    (himage : (actionImage (V := V) A).pCoreIn 2 = ⊥) :
    A.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [← large_centralizer_eq_core E]
  refine le_inf ((pCoreIn_le 2 A).trans hA) ?_
  have he : actionImage (V := V) (A.pCoreIn 2) = ⊥ :=
    (actionImage_core E A hA).trans himage
  intro a ha
  have hn := (hA.trans (sup_le D.normalizes E.input.sylow_normalizes))
    (pCoreIn_le 2 A ha)
  have hm : V.normalizerMonoidHom ⟨a,hn⟩ ∈ actionImage (V := V) (A.pCoreIn 2) :=
    mem_map_of_mem _ ha
  rw [he] at hm
  have hk : (⟨a,hn⟩ : normalizer (V : Set G)) ∈ V.normalizerMonoidHom.ker :=
    mem_bot.mp hm
  rwa [normalizerMonoidHom_ker] at hk

/-- The temporary W and both generators of I really lie in LT. -/
theorem oppositeJoin_le_large (m : MarkedFlag E) (hW : E.W ≤ E.G₁.pCoreIn 2)
    {y : G} (hy : y ∈ L) : oppositeJoin (auxiliaryW E) y ≤ L ⊔ (T : Subgroup G) := by
  have hT : E.G₁.pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le m.sylow_le_point_normalizer] using
      pCoreIn_le_sylow E.G₁ (T.subtype m.sylow_le_point_normalizer)
  have hWL : auxiliaryW E ≤ L ⊔ (T : Subgroup G) :=
    ((auxiliaryW_le_W E).trans hW).trans (hT.trans le_sup_right)
  apply sup_le hWL
  exact (map_mono hWL).trans_eq (mem_normalizer_iff_map_conj_eq.mp
    ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hy)))

/-- Apply the defining-characteristic SL₂ core theorem to the actual pair image. -/
theorem opposite_core_le_large_core (m : MarkedFlag E) (hW : E.W ≤ E.G₁.pCoreIn 2)
    {y : G} (hy : y ∈ L)
    (e : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) ≃*
      Matrix.SpecialLinearGroup (Fin 2) E.input.field.Carrier) :
    (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  apply core_le_large_core_of_image E _ (oppositeJoin_le_large E m hW hy)
  have he : pCore 2 (actionImage (V := V) (oppositeJoin (auxiliaryW E) y)) = ⊥ := by
    apply (map_injective (f := e.toMonoidHom) e.injective)
    rw [pCore_map_iso, Subgroup.map_bot, Matrix.SL2.twoCore_eq_bot]
  rw [pCoreIn, he, Subgroup.map_bot]


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
