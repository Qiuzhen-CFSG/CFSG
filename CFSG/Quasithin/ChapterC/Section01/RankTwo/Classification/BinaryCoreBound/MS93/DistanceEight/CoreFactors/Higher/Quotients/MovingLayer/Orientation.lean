module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.Displacement
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Natural orientation of the first moving source factor

Small-involution recognition gives coordinates up to an automorphism of
SL3(2). The original forward actor fixes a subgroup of index at most two,
while its displacement on the original natural module has order four.
Dual coordinates would provide two independent fixed covectors annihilating
that displacement, forcing its order to be at most two. Hence the moving
factor is natural with exactly the CommonFacts marking.

The only finite certificate counts the common orthogonal space of two
independent vectors in the eight-element binary three-space. The source
consumer supplies faithfulness, smallness, and both actor bounds itself.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.4)(iv), p.899.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
open DistanceFour.Linear SecondLayer.Recognition

private theorem orthogonal_pair_card : ∀ u v : W, u ≠ 0 → v ≠ 0 → u ≠ v →
    Fintype.card {w : W // dotProduct u w = 0 ∧ dotProduct v w = 0} = 2 := by
  decide +kernel

private def dotHom (u : W) : Multiplicative W →* Multiplicative (ZMod 2) where
  toFun v := Multiplicative.ofAdd (dotProduct u v.toAdd)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change dotProduct u (0 : W) = 0
    exact dotProduct_zero u
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    change dotProduct u (x.toAdd + y.toAdd) = dotProduct u x.toAdd + dotProduct u y.toAdd
    exact dotProduct_add u x.toAdd y.toAdd

private theorem exists_two_nonzero {E : Type*} [Group E] [Finite E] (h : 2 < Nat.card E) :
    ∃ u v : E, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v := by
  classical
  let : Nontrivial E := by
    by_contra hn
    let : Subsingleton E := not_nontrivial_iff_subsingleton.mp hn
    have hc : Nat.card E = 1 := Nat.card_unique
    omega
  obtain ⟨u,hu⟩ := exists_ne (1 : E)
  by_contra! hn
  have hi : Function.Injective (fun x : E => decide (x = 1)) := by
    intro x y he
    by_cases hx : x = 1
    · have hy : y = 1 := of_decide_eq_true (he.symm.trans (by simp only [hx,decide_true]))
      exact hx.trans hy.symm
    · by_cases hy : y = 1
      · simp only [hy, decide_true, decide_eq_true_eq] at he
        exact (hx he).elim
      · exact (hn x u hx hu).trans (hn y u hy hu).symm
  have hb := Nat.card_le_card_of_injective _ hi
  have hc : Nat.card Bool = 2 := by simp only [Nat.card_eq_fintype_card,Fintype.card_bool]
  omega

/-- A fixed subgroup of index two excludes the dual orientation when the
same actor has natural displacement of order four. -/
theorem no_dual_of_small_fixed {E : Type*} [Group E] [Finite E]
    (ρ : SL →* MulAut E) (κ : SL ≃* SL) (P : Subgroup SL)
    (hfix : (FixedPoints.subgroup (P.map ρ) E).index ≤ 2)
    (hmove : Nat.card (commutatorAction (P.map (naturalAction κ)) (Multiplicative W)) = 4)
    (f : E ≃* Multiplicative W)
    (hf : ∀ g x, (f (ρ g x)).toAdd = dual (κ g) (f x).toAdd) : False := by
  let B := FixedPoints.subgroup (P.map ρ) E
  have hE : Nat.card E = 8 := (Nat.card_congr f.toEquiv).trans (by
    simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fin, ZMod.card])
  have hc := B.card_mul_index
  rw [hE] at hc
  have hB : 2 < Nat.card B := by nlinarith
  obtain ⟨u,v,hu,hv,huv⟩ := exists_two_nonzero hB
  let u' := (f (u : E)).toAdd
  let v' := (f (v : E)).toAdd
  have hu' : u' ≠ 0 := by
    intro h
    apply hu
    apply Subtype.ext
    apply f.injective
    exact (Multiplicative.toAdd.injective h).trans f.map_one.symm
  have hv' : v' ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    apply f.injective
    exact (Multiplicative.toAdd.injective h).trans f.map_one.symm
  have huv' : u' ≠ v' := by
    intro h
    exact huv (Subtype.ext (f.injective (Multiplicative.toAdd.injective h)))
  have hfixed (g : SL) (hg : g ∈ P) (z : B) : dual (κ g) (f (z : E)).toAdd = (f (z : E)).toAdd := by
    rw [← hf]
    exact congrArg (fun z : E => (f z).toAdd) (z.property ⟨ρ g,mem_map_of_mem _ hg⟩)
  have hkill (z : B) : commutatorAction (P.map (naturalAction κ)) (Multiplicative W) ≤
      (dotHom (f (z : E)).toAdd).ker := by
    rw [commutatorAction_eq_closure, closure_le]
    rintro _ ⟨⟨a,g,hg,rfl⟩,w,rfl⟩
    change dotProduct (f (z : E)).toAdd (-w.toAdd + (κ g).val.mulVec w.toAdd) = 0
    have hh := hfixed g⁻¹ (P.inv_mem hg) z
    simp only [map_inv,dual,inv_inv] at hh
    rw [dotProduct_add, dotProduct_neg, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, hh, neg_add_cancel]
  let T := (dotHom u').ker ⊓ (dotHom v').ker
  have hCT : commutatorAction (P.map (naturalAction κ)) (Multiplicative W) ≤ T :=
    le_inf (hkill u) (hkill v)
  let e : T ≃ {w : W // dotProduct u' w = 0 ∧ dotProduct v' w = 0} := {
    toFun x := ⟨x.val.toAdd, x.property⟩
    invFun x := ⟨Multiplicative.ofAdd x.val,x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have ht : Nat.card T = 2 := (Nat.card_congr e).trans
    (by rw [Nat.card_eq_fintype_card]; exact orthogonal_pair_card u' v' hu' hv' huv')
  have hb := card_le_of_le hCT
  rw [hmove,ht] at hb
  omega

/-- The intrinsic action on the moving summand of an actual action. -/
@[expose] noncomputable def movingAction {E : Type*} [Group E] (ρ : SL →* MulAut E) :
    SL →* MulAut (commutatorAction ρ.range E) := by
  letI : IsInvariant ρ.range E (commutatorAction ρ.range E) := commutatorAction_isInvariant
  exact (MulDistribMulAction.toMulAut ρ.range (commutatorAction ρ.range E)).comp ρ.rangeRestrict

theorem movingAction_apply {E : Type*} [Group E] (ρ : SL →* MulAut E) (g : SL)
    (x : commutatorAction ρ.range E) : (movingAction ρ g x : E) = ρ g x := rfl

/-- Small-involution recognition with the prescribed natural marking.
The same actor's fixed and moved orders select the natural orientation. -/
theorem natural_moving_coordinates {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (ρ : SL →* MulAut E) (κ : SL ≃* SL)
    (hfaith : Function.Injective ρ) (hsmall : Escape.Initial.Natural.Splitting.HasSmallInvolution ρ)
    (P : Subgroup SL) (hfix : (FixedPoints.subgroup (P.map ρ) E).index ≤ 2)
    (hmove : Nat.card (commutatorAction (P.map (naturalAction κ)) (Multiplicative W)) = 4) :
    ∃ f : commutatorAction ρ.range E ≃* Multiplicative W,
      ∀ g x, (f (movingAction ρ g x)).toAdd = (κ g).val.mulVec (f x).toAdd := by
  obtain ⟨n⟩ := Escape.Initial.Natural.Splitting.naturalActionSplitting_of_small_involution ρ hfaith hsmall
  have ha : ∀ g x, (n.coordinates (movingAction ρ g x)).toAdd =
      (n.marking g).val.mulVec (n.coordinates x).toAdd := fun g x => n.action g x _ rfl
  rcases natural_or_dual_of_coordinates (movingAction ρ) κ n.coordinates n.marking ha with h | h
  · exact h
  obtain ⟨f,hf⟩ := h
  exfalso
  apply no_dual_of_small_fixed (movingAction ρ) κ P ?_ hmove f hf
  let C := commutatorAction ρ.range E
  let F := FixedPoints.subgroup (P.map ρ) E
  have he : FixedPoints.subgroup (P.map (movingAction ρ)) C = F.subgroupOf C := by
    ext x
    constructor
    · intro hx a
      obtain ⟨g,hg,he⟩ := a.property
      have hh := congrArg Subtype.val (hx ⟨movingAction ρ g,mem_map_of_mem _ hg⟩)
      change ρ g (x : E) = (x : E) at hh
      change (a : MulAut E) (x : E) = (x : E)
      rwa [he] at hh
    · intro hx a
      obtain ⟨g,hg,he⟩ := a.property
      have hh := hx ⟨ρ g,mem_map_of_mem _ hg⟩
      apply Subtype.ext
      change ((a : MulAut C) x : E) = (x : E)
      rw [← he]
      exact hh
  rw [he]
  have hb := relIndex_le_of_le_right (show C ≤ ⊤ from le_top)
    (show F.relIndex ⊤ ≠ 0 from index_ne_zero_of_finite)
  rw [relIndex_top_right] at hb
  exact hb.trans hfix

open Stellmacher.PushingUp.AmalgamGraph
variable {M : Type*} [Group M] [Finite M] {R L : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

/-- The actual first moving factor is natural under the original marking.
All action, faithfulness, smallness and orientation premises are discharged. -/
theorem source_moving_natural_coordinates (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    ∃ s : MovingModule source (Early.Orbit.SourceApplications.higherPath geometry p),
      let := s.normal
      ∃ f : commutatorAction s.action.range
          (MovingSpace (Early.Orbit.SourceApplications.higherPath geometry p)) ≃* Multiplicative W,
        ∀ g x, (f (movingAction s.action g x)).toAdd =
          (common.natural.marking g).val.mulVec (f x).toAdd := by
  obtain ⟨s,he,hfaith⟩ := source_moving_module common earlier p
  let := s.normal
  let := s.finite
  let := he
  refine ⟨s,?_⟩
  have hadj : Adjacent R (alpha R) (p.walk.getVert 5) := by
    simpa only [p.center_eq] using p.adjacent (i := 4) (by decide)
  exact natural_moving_coordinates s.action common.natural.marking hfaith
    (s.source_small_involution common earlier p) _
    (s.source_fixed_index common earlier p)
    (SecondLayer.Recognition.Displacement.edge_product_natural_card source common earlier hadj
      (SecondLayer.SourceRecognition.first_actor_source common earlier p).1).1

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer
