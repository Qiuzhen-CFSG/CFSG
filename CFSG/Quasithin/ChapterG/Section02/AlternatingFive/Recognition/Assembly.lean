module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Recognition.Cardinality
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Structure.Starred

/-!
# Conditional recognition and exact orders for G.2.4(6–7)

The genuine five-point action identifies the actual local two-residual with
N_(L*)(U*). This discharges the remaining Borel premise of the marked projective
orbit construction. Apply the universal G.1.3 implication to that constructed
map on the literal S/S₂, then transport its binary coordinates to NaturalLayer.

The marked W-image is contained in the U*-fixed space. The equivariant natural
coordinates identify the latter with the root-fixed vectors in s natural planes,
whose order is 2^(2s). The marked complement has that same order, so inclusion
is equality. Transport back through the original starred projection gives the
common fixed subgroup of the original U-action. All statements include s = 0.

The quotient kernel is W∩S₂, not an assumed containment S₂≤W. Its established
intersection count gives |U|=2^(2s+5)[S₂:V_L]; the same natural coordinates give
|S|=2^(4s+4)[S₂:V_L]. The orthogonal coordinates on V_L remain distinct.

Only genuine G.1.3 and the explicitly displayed earlier structural conclusions
remain inputs. The G.1/G.2 source owners discharge G.1.3; qt-g024-structure
produces the structural inputs and qt-g02-alternating-five assembles the source
lemma. No projective-map, fixed-space or natural-decomposition witness is assumed.

Source: Aschbacher–Smith, G.1.3 and G.1.5, printed pp.327–328, and
G.2.4(6–7), printed pp.334–335, combined manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup Recognition Recognition.ProjectiveGeometry
namespace Hypothesis
universe u
variable {G : Type u} [Group G] [Finite G] {D : Setup G} {g : G}
  (d : Hypothesis D g)
include d

/-- The source Borel is exactly the relative normalizer needed by G.1.5(3).
Its five-point marking comes from the original hypothesis. -/
theorem star_local_eq_root_normalizer :
    (D.star D.L₁).subgroupOf (D.star D.L) =
      normalizer (((D.star D.U).subgroupOf (D.star D.L)) : Set (D.star D.L)) := by
  apply le_antisymm
  · exact (comap_mono d.star_local_normalizes_U).trans
      ((D.star D.U).le_normalizer_comap (D.star D.L).subtype)
  · intro x hx
    have hx' : (x : D.Star) ∈ normalizer (D.star D.U : Set D.Star) := by
      rw [← map_subgroupOf_eq_of_le d.star_U_le_L]
      exact le_normalizer_map _ (mem_map_of_mem _ hx)
    have hs : d.starAction x ∈ normalizer
        (Starred.FiniteBorel.four d.pointIndex : Set (Equiv.Perm (Fin 5))) := by
      rw [← d.star_U_action]
      exact le_normalizer_map _ (mem_map_of_mem _ hx')
    have he := mem_normalizer_iff_map_conj_eq.mp hs
    change (Starred.FiniteBorel.four d.pointIndex).map
      (MulAut.conj (d.starAction x)).toMonoidHom = _ at he
    rw [Starred.FiniteBorel.four_conjugate] at he
    have hfix : d.starAction x d.pointIndex = d.pointIndex := by
      by_contra hn
      have hgen := Starred.FiniteBorel.distinct_four_generate d.pointIndex
        (d.starAction x d.pointIndex) (Ne.symm hn)
      rw [he, sup_idem] at hgen
      have hc := Starred.FiniteBorel.four_card d.pointIndex
      rw [hgen, nat_card_alternatingGroup] at hc
      norm_num [Nat.factorial] at hc
    have hm : d.starAction x ∈ (D.star D.L₁).map d.starAction := by
      rw [d.star_local_action]
      exact ⟨by rw [d.starAction_on_L]; exact (d.model x).property, hfix⟩
    obtain ⟨y, hy, he⟩ := hm
    change (x : D.Star) ∈ D.star D.L₁
    exact (d.starAction_injective he) ▸ hy

/-- Conditional G.2.4(6), with literal complementary images and the original
U-action. The multiplicity and actual equivariant coordinates are constructed
from genuine G.1.3; the fixed-space conclusion is proved by cardinality. -/
theorem natural_upper_layer_of_recognition
    (hrec : RecognitionInput.{0,u} F4)
    (hI : D.I g = D.L ⊔ D.U)
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2)
    (hsplit : D.S g = D.W g ⊔ conjugate (D.W g) g)
    (hVV : D.V ⊔ conjugate D.V g = D.VL) :
    let hLI : D.L ≤ D.I g := le_sup_left.trans hI.ge
    let := d.second_normal_in_core hLI
    ∃ (s : ℕ) (c : NaturalLayer D g F4 s hLI),
      IsCompl (upperImage D g (D.W g))
        (upperImage D g (conjugate (D.W g) g)) ∧
      upperImage D g (D.W g) = c.action.commonFixed (D.U.subgroupOf (D.I g)) ∧
      Nat.card (upperImage D g (D.W g)) = 2 ^ (2 * s) := by
  let hLI : D.L ≤ D.I g := le_sup_left.trans hI.ge
  let hILT := d.upper_actor_le hI
  let hstar := d.upper_actor_star hI d.star_U_le_L
  let := d.second_normal_in_core hLI
  let := d.upper_elementary hLI hcore hsplit
  let : Module (ZMod 2) F4 := (ZMod.algebra F4 2).toModule
  obtain ⟨model, σ, b, φ, hroot, hq, hcriterion, _, _⟩ :=
    d.exists_upper_projective_geometry hI hcore hsplit hVV d.star_U_sylow
      d.star_local_eq_root_normalizer
  obtain ⟨s, e, he⟩ := hrec (Additive (UpperQuotient D g)) σ φ hcriterion
  let σ₀ := σ.comp model.toMonoidHom
  let b₀ : Representation.BinaryConjugationSection (D.I g) (D.S g) (S₂ D g)
      (σ₀.comp (upperStarProjection D g hILT hstar)) := b
  obtain ⟨c⟩ := naturalLayer_of_equivariant d hLI hILT hstar σ₀ b₀ hq field_card
    model s e (fun a v j => he (model a) v j)
  have hcard := d.upperImage_card_of_naturalLayer hI d.star_U_le_L hcore hsplit hVV c
  have hfixed : ∀ v, v ∈ b₀.imageSpace (D.W g) ↔
      ∀ a ∈ (D.star D.U).subgroupOf (D.star D.L), σ₀ a v = v := by
    let X := {v : Additive (UpperQuotient D g) //
      ∀ a ∈ (D.star D.U).subgroupOf (D.star D.L), σ₀ a v = v}
    have hiff (v : Additive (UpperQuotient D g)) :
        (∀ a ∈ (D.star D.U).subgroupOf (D.star D.L), σ₀ a v = v) ↔
        ∀ a ∈ RootGroup F4 standardPoint.val, ∀ j,
          Matrix.mulVec a.val (e v j) = e v j := by
      constructor
      · intro hv a ha j
        rw [← hroot] at ha
        obtain ⟨a, ha, rfl⟩ := ha
        rw [← he]
        change e (σ₀ a v) j = e v j
        rw [hv a ha]
      · intro hv a ha
        apply e.injective
        funext j
        exact (he (model a) v j).trans (hv (model a) (hroot ▸ mem_map_of_mem _ ha) j)
    have hX : Nat.card X = 2 ^ (2 * s) :=
      (Nat.card_congr (e.toEquiv.subtypeEquiv hiff)).trans (fixed_copies_card s)
    have hle (v : b₀.imageSpace (D.W g)) :
        ∀ a ∈ (D.star D.U).subgroupOf (D.star D.L), σ₀ a v = v :=
      fun a ha => (d.upper_star_root_bounds hcore hILT hstar σ₀ b₀ a ha).2 v v.property
    let f : b₀.imageSpace (D.W g) → X := fun v => ⟨v, hle v⟩
    have hf : Function.Surjective f := by
      apply ((Nat.bijective_iff_injective_and_card f).mpr ⟨?_, ?_⟩).2
      · intro v w hvw
        exact Subtype.ext (show (v : Additive (UpperQuotient D g)) = w from
          congrArg (fun z : X => z.val) hvw)
      · rw [hX, ← hcard, upper_imageSpace_eq hILT hstar σ₀ b₀ hq]
        rfl
    intro v
    constructor
    · intro hv
      exact hle ⟨v, hv⟩
    · intro hv
      obtain ⟨w, hw⟩ := hf ⟨v, hv⟩
      have hw' : (w : Additive (UpperQuotient D g)) = v :=
        congrArg (fun z : X => z.val) hw
      exact hw' ▸ w.property
  exact ⟨s, c, d.upperImages_complement hI d.star_U_le_L hcore hsplit hVV,
    upperImage_eq_fixed_of_binary hILT hstar σ₀ b₀ hq hfixed c.action c.action_mk,
    hcard⟩

/-- Conditional G.2.4(6–7), using the same natural-layer multiplicity in
all three counts. The structural premises have producer qt-g024-structure. -/
theorem natural_upper_layer_and_order
    (hrec : RecognitionInput.{0,u} F4)
    (hI : D.I g = D.L ⊔ D.U)
    (hcore : D.S g = D.I g ⊓ D.LT.pCoreIn 2)
    (hsplit : D.S g = D.W g ⊔ conjugate (D.W g) g)
    (hVV : D.V ⊔ conjugate D.V g = D.VL)
    (hVU : D.VL ⊓ D.U = D.V) (hV : Nat.card D.V = 8)
    (hUW : (D.W g).relIndex D.U = 4) :
    let hLI : D.L ≤ D.I g := le_sup_left.trans hI.ge
    let := d.second_normal_in_core hLI
    ∃ (s : ℕ) (c : NaturalLayer D g F4 s hLI),
      IsCompl (upperImage D g (D.W g))
        (upperImage D g (conjugate (D.W g) g)) ∧
      upperImage D g (D.W g) = c.action.commonFixed (D.U.subgroupOf (D.I g)) ∧
      Nat.card (upperImage D g (D.W g)) = 2 ^ (2 * s) ∧
      Nat.card D.U = 2 ^ (2 * s + 5) * D.VL.relIndex (S₂ D g) ∧
      Nat.card (D.S g) = 2 ^ (4 * s + 4) * D.VL.relIndex (S₂ D g) := by
  let hLI : D.L ≤ D.I g := le_sup_left.trans hI.ge
  let := d.second_normal_in_core hLI
  obtain ⟨s, c, hcompl, hfixed, hcard⟩ :=
    d.natural_upper_layer_of_recognition hrec hI hcore hsplit hVV
  exact ⟨s, c, hcompl, hfixed, hcard,
    d.order_of_naturalLayer hI d.star_U_le_L hcore hsplit hVV hVU hV hUW c,
    d.core_order_of_naturalLayer hLI c⟩

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
