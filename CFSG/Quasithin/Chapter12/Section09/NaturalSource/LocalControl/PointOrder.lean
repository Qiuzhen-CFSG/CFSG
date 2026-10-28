module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.CoreMovement
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.LocalControl.PointJoin
public import Theory.SpecificGroups.BinaryLinear.PointStabilizerPerfect

/-!
# The alternating-seven plane-movement case

The original residual L₁ induces the entire point parabolic on the original
V, with the literal centralizer as kernel. If O₂(K₁) fixes V₂, normality
propagates fixation to the point span and hence to V. The point action then
factors through the image of L₁ in K₁/O₂(K₁). Its full order, including the
displacement kernel, must divide the component quotient order.

For n=4 and5 these orders are 1344 and322560; neither divides |A₇|=2520.
Thus the A₇ component core moves the plane. The actual new I₂ then gives
all three clauses of 12.9.6, including the S₃ quotient and the B.6.1 minimal
parabolic. The LocalControl application discharges its movement premise
in this row. Its centralizer bounds, the other model rows and final
NaturalBranchInput assembly remain with qt-d-1291-natural-source.

Source: Aschbacher--Smith, 12.9.6, printed pp.861--862 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag Section08.NormalGeometry
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The full point-parabolic action of the original residual, with its literal kernel. -/
theorem point_residual_full_action
    (h : HigherRankHypothesis K T L V n) (hn : 4 ≤ n) (F : InvariantFlag T V n) :
    letI := h.chosen.elementary
    ∃ f : F.Li L 1 →* BinaryLinear.parabolic (space (V := V) (F.Vi 1)),
      Function.Surjective f ∧ f.ker = (centralizer (V : Set G)).subgroupOf (F.Li L 1) := by
  let := h.chosen.elementary
  let : Finite (BinaryLinear.GL (Additive V)) := Finite.of_injective
    (fun g : BinaryLinear.GL (Additive V) => (g : Additive V → Additive V)) DFunLike.coe_injective
  let W := space (V := V) (F.Vi 1)
  let d := h.naturalMarking.geometryAction
  let N : Subgroup G := L ⊓ F.H
  let f₀ := d.action.comp (inclusion (show N ≤ L from inf_le_left))
  let f₁ : N →* BinaryLinear.parabolic W := f₀.codRestrict _ (fun x =>
    (action_mem_parabolic_iff d _ (F.le_seed 1) (inclusion inf_le_left x)).mpr x.property.2)
  have hf₁ : Function.Surjective f₁ := by
    intro g
    obtain ⟨l,hl⟩ := d.surjective g.val
    refine ⟨⟨l,l.property,?_⟩,Subtype.ext hl⟩
    exact (action_mem_parabolic_iff d _ (F.le_seed 1) l).mp (hl ▸ g.property)
  have hv : Module.finrank (ZMod 2) (Additive V) = n :=
    h.naturalMarking.coordinates.finrank_eq.trans (by simp)
  let : Group.IsPerfect (BinaryLinear.parabolic W) :=
    BinaryLinear.PointStabilizerPerfect.parabolic_isPerfect (by rw [hv]; exact hn) W
      (Components.flag_space_finrank F 1 (by have := h.rank; omega))
  have hp : pResidual 2 (BinaryLinear.parabolic W) = ⊤ := by
    apply (pResidual_eq_top_iff 2 _).mpr
    intro R hn hR
    let := hn
    by_contra hne
    let : Nontrivial ((BinaryLinear.parabolic W) ⧸ R) := QuotientGroup.nontrivial_iff.mpr hne
    exact Group.IsPerfect.not_isNilpotent _ hR.isNilpotent
  have hLi : F.Li L 1 = (pResidual 2 N).map N.subtype := by
    unfold Li
    rw [if_neg (by omega)]
    rfl
  let f := f₁.comp (inclusion (show F.Li L 1 ≤ N from F.Li_le L 1))
  refine ⟨f,?_,?_⟩
  · intro a
    have hm : (pResidual 2 N).map f₁ = ⊤ := by
      rw [map_pResidual_of_surjective 2 f₁ hf₁,hp]
    obtain ⟨r,hr,he⟩ := mem_map.mp (hm.symm ▸ mem_top a)
    let k : F.Li L 1 := ⟨r,by rw [hLi]; exact mem_map.mpr ⟨r,hr,rfl⟩⟩
    exact ⟨k,he⟩
  · ext k
    change f k = 1 ↔ (k : G) ∈ centralizer (V : Set G)
    constructor
    · intro hk v hv
      have he := congrArg (fun a : BinaryLinear.parabolic W => ((a.val (Additive.ofMul ⟨v,hv⟩)).toMul : G)) hk
      change ((d.action ⟨k,(F.Li_le L 1 k.property).1⟩ (Additive.ofMul ⟨v,hv⟩)).toMul : G) = v at he
      rw [d.conjugation] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hk
      apply Subtype.ext
      apply LinearEquiv.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      change ((d.action ⟨k,(F.Li_le L 1 k.property).1⟩ v).toMul : G) = v.toMul
      rw [d.conjugation,← hk v.toMul v.toMul.property,mul_inv_cancel_right]

/-- Fixation by the original component core makes the full point-parabolic order
    divide the intrinsic component quotient order. -/
theorem point_parabolic_order_dvd_of_core_centralizes
    (h : HigherRankHypothesis K T L V n) (hn : 4 ≤ n) (F : InvariantFlag T V n)
    (C : ComponentGeometry F L)
    (hc : C.K1.pCoreIn 2 ≤ centralizer (V : Set G)) :
    2 ^ (n-1) * Nat.card (LinearGroup (n-1)) ∣ Nat.card (C.K1 ⧸ pCore 2 C.K1) := by
  let := h.chosen.elementary
  obtain ⟨f,hf,hker⟩ := point_residual_full_action h hn F
  let g := (QuotientGroup.mk' (pCore 2 C.K1)).comp (inclusion C.contains)
  have hk : g.ker ≤ f.ker := by
    intro b hb
    rw [hker]
    apply hc
    apply mem_map.mpr
    refine ⟨inclusion C.contains b,?_,rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp hb
  have hd := card_dvd_of_surjective (QuotientGroup.lift g.ker f hk)
    (QuotientGroup.lift_surjective_of_surjective g.ker f hf hk)
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at hd
  have hd' := hd.trans g.range.card_subgroup_dvd_card
  rw [BinaryLinear.PointStabilizerPerfect.parabolic_card _
    (Components.flag_space_finrank F 1 (by have := h.rank; omega))] at hd'
  have hv : Module.finrank (ZMod 2) (Additive V) = n :=
    h.naturalMarking.coordinates.finrank_eq.trans (by simp)
  rwa [hv] at hd'

/-- Failure of the source movement assertion imposes the same original quotient-order obstruction. -/
theorem point_parabolic_order_dvd_of_plane_fixed
    (h : HigherRankHypothesis K T L V n) (hn : 4 ≤ n) (F : InvariantFlag T V n)
    (C : ComponentGeometry F L) (hm : ⁅F.Vi 2, C.K1.pCoreIn 2⁆ = ⊥) :
    2 ^ (n-1) * Nat.card (LinearGroup (n-1)) ∣ Nat.card (C.K1 ⧸ pCore 2 C.K1) :=
  point_parabolic_order_dvd_of_core_centralizes h hn F C
    ((core_centralizes_point_span_of_plane_fixed h F C hm).trans
      (centralizer_le (le_conjugateSpanBy V F.H)))

private theorem linear_card (d : ℕ) :
    Nat.card (LinearGroup d) = ∏ i : Fin d, (2^d - 2^i.val) := by
  rw [← Nat.card_congr (matrixEquivLinear d).toEquiv, Matrix.card_GL_field]
  simp

/-- The alternating-seven point component moves the original plane. This
    discharges the A₇ case of source 12.9.6(1) without an added action premise. -/
theorem point_core_moves_plane_of_alternating_seven
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n) (C : ComponentGeometry F L)
    (hm : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7) :
    ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥ := by
  intro hfix
  have hd := point_parabolic_order_dvd_of_plane_fixed h (by omega) F C hfix
  obtain ⟨e⟩ := hm
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,linear_card] at hd
  rcases hn with rfl | rfl <;> norm_num [Fin.prod_univ_succ, Nat.factorial] at hd

/-- All three source 12.9.6 clauses in the alternating-seven case, on the
original plane normal closure and actual minimal-parabolic predicate. -/
theorem alternating_seven_plane_local_control
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (C : ComponentGeometry F L)
    (hm : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7) :
    ⁅F.Vi 2, C.K1.pCoreIn 2⁆ ≠ ⊥ ∧
      ((planeCoreClosure F).subgroupOf (F.Gi 2)).Normal ∧
      planeCoreClosure F ⊔ (T : Subgroup G) = F.P L ∧
      ChapterB.IsMinimalParabolicOver T (planeCoreClosure F ⊔ (T : Subgroup G)) ∧
      (T : Subgroup G).relIndex (planeCoreClosure F ⊔ (T : Subgroup G)) = 3 ∧
      (planeCoreClosure F).pCoreIn 2 = planeCoreClosure F ⊓ centralizer (F.Vi 2 : Set G) ∧
      Nonempty (((planeCoreClosure F) ⧸ pCore 2 (planeCoreClosure F)) ≃* Equiv.Perm (Fin 3)) ∧
      primeRank 3 (centralizer (F.Vi 2 : Set G)) ≤ 1 := by
  have hmove := point_core_moves_plane_of_alternating_seven h hn F C hm
  exact ⟨hmove,plane_local_control_with_minimal_parabolic h earlier F C hmove⟩

/-- The literal LocalControl consumer now has no movement premise in the A₇ row.
The two source centralizer bounds remain with qt-d-1291-natural-source. -/
theorem localControl_of_alternating_seven_and_centralizers
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (C : ComponentGeometry F L)
    (hm : Chapter1.Section02.LocalModels.IsAlternating (C.K1 ⧸ pCore 2 C.K1) 7)
    (hcentral : pointQuotientCentralizer C ≤ normalizer (L : Set G))
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G)) : LocalControl C :=
  localControl_of_plane_centralizer_and_models h earlier F C hcentral (Or.inl hm)
    (point_core_moves_plane_of_alternating_seven h hn F C hm) hplane

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
