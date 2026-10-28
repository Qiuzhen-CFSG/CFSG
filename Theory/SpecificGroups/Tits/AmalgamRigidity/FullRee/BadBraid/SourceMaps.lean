module
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.BadBraid.FirstCoordinates
public import Theory.SpecificGroups.Tits.AmalgamRigidity.FullRee.SecondSeparator.SecondExtension.WeylVerification
public import Theory.GroupTheory.Amalgam.RankTwoCompletion
/-!
# Literal completion maps for the binary Ree local word calculation

The common coordinate Sylow group maps through the original middle inclusion.
Both commuting squares identify this map with the endpoint maps. Thus the
first-endpoint word calculation applies to the very same marked generators
in an arbitrary faithful completion, without an ambient recognition premise.

Source: Aschbacher–Smith F.4.4 and F.4.8, with the verified Shinoda root marking.
-/
@[expose] public section
noncomputable section
namespace Tits.AmalgamRigidity.FullRee.BadBraid
open ReeTwo Subgroup.CosetWordCertificate Theory.GroupTheory FirstRestrictions
variable {G : Type*} [Group G]
abbrev Completion := RankTwoAmalgam.FaithfulCompletion
    ExceptionalParabolics.FullRee.amalgam (G := G)
def middleMap (c : Completion (G := G)) : SylowModel →* G :=
  c.middle.comp borelEquiv.toMonoidHom
def leftMap (c : Completion (G := G)) : Centralizer →* G :=
  c.left.comp ParabolicMarkedComparison.Verified.firstEquiv.toMonoidHom

theorem middle_left (c : Completion (G := G)) (x : SylowModel) :
    middleMap c x = leftMap c (SylowModel.embedding x) := by
  exact congrArg c.left (coordinateAmalgamIso.left_commutes x).symm

theorem middle_right (c : Completion (G := G)) (x : SylowModel) :
    middleMap c x = c.right (SecondExtension.inclusion x) := by
  exact DFunLike.congr_fun c.compatible (borelEquiv x)

def generator (c : Completion (G := G)) : Nat → G
 | 0 => middleMap c SylowModel.rootOne
 | 1 => middleMap c (SylowModel.root 0)
 | 2 => middleMap c (SylowModel.root 2)
 | 3 => leftMap c Centralizer.weyl
 | 4 => c.right SecondExtension.reflection
 | 5 => middleMap c (SylowModel.root 1)
 | 6 => middleMap c (SylowModel.root 3)
 | _ => 1

private theorem eval_map {H : Type*} [Group H] (f : H →* G) (g : Nat → H)
    (w : Word Nat) : f (eval g w) = eval (fun i => f (g i)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons, map_mul, ih, eval_cons]
    congr 1
    cases a.2 <;> simp

private theorem eval_congr_on {g h : Nat → G} (w : Word Nat)
    (he : ∀ a ∈ w, g a.1 = h a.1) : eval g w = eval h w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [eval_cons, eval_cons, he a (List.mem_cons_self ..),
      ih (fun z hz => he z (List.mem_cons_of_mem _ hz))]

private theorem first_letter (c : Completion (G := G)) (j : Nat) (hj : j < 4) :
    leftMap c (equiv (firstGens j)) = generator c j := by
  interval_cases j
  · rw [generator, middle_left]
    congr 1
  · rw [generator, middle_left]
    rfl
  · rw [generator, middle_left]
    rfl
  · change leftMap c (SemidirectProduct.inr (Core.complementEquiv FiveFour.r)) =
      leftMap c (SemidirectProduct.inr Core.complementR)
    rw [Core.complementEquiv_r]

theorem first_source_relations (c : Completion (G := G)) (i : Fin 22) :
    eval (generator c) (relator ⟨i.val, Nat.lt_trans i.isLt (show 22 < 39 from Nat.lt_of_sub_eq_succ rfl)⟩) = 1 := by
  have he := congrArg ((leftMap c).comp equiv.toMonoidHom) (first_relations i)
  rw [eval_map, map_one] at he
  refine (eval_congr_on _ ?_).trans he
  intro a ha
  apply (first_letter c a.1 ?_).symm
  exact (by decide +kernel : ∀ i : Fin 22, ∀ a ∈ relator ⟨i.val, Nat.lt_trans i.isLt (show 22 < 39 from Nat.lt_of_sub_eq_succ rfl)⟩,
    a.1 < 4) i a ha
end Tits.AmalgamRigidity.FullRee.BadBraid
