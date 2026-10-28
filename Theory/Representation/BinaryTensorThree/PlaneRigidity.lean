module
public import Theory.Representation.BinaryTensorThree.PlaneFixedAction

/-!
# Detecting the paired plane-radical action

The tensors e₂⊗e₀ and e₀⊗e₂ detect the two plane-radical factors. Each
factor has order four, so its projection kernel has index at most four.
If fixed spaces do not change upon restriction to subgroups of those
indices, both factors act trivially. The original tensor weak-closure
consumer supplies this rigidity from s(G,V)=3.
Source: Aschbacher--Smith H.4.4, 7.3.3 and 8.3.3, pp.383,699,723.
-/

public noncomputable section
open Subgroup
namespace BinaryTensorThree.PlaneFixed

private def probeLeft : Space := !![0,0,0;0,0,0;1,0,0]
private def probeRight : Space := !![0,0,1;0,0,0;0,0,0]

private theorem probes_detect (a b : Two)
    (hleft : action (PointParabolic.tensorHom (radicalPair (a,b))) probeLeft = probeLeft)
    (hright : action (PointParabolic.tensorHom (radicalPair (a,b))) probeRight = probeRight) :
    (a,b) = 1 := by
  rw [radical_action] at hleft hright
  have h0 := congrArg (fun X : Space => X 0 0) hleft
  have h1 := congrArg (fun X : Space => X 1 0) hleft
  have h2 := congrArg (fun X : Space => X 0 0) hright
  have h3 := congrArg (fun X : Space => X 0 1) hright
  simp [radical,radicalMatrix,probeLeft,probeRight,Matrix.mul_apply,
    Matrix.transpose_apply,Fin.sum_univ_three] at h0 h1 h2 h3
  apply Prod.ext
  · change a.toAdd = 0
    funext i
    fin_cases i
    · exact h0
    · exact h1
  · change b.toAdd = 0
    funext i
    fin_cases i
    · exact h2
    · exact h3

private theorem left_probe_fixed (b : Two) :
    action (PointParabolic.tensorHom (radicalPair (1,b))) probeLeft = probeLeft := by
  rw [radical_action]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radical,radicalMatrix,probeLeft,Matrix.mul_apply,Matrix.transpose_apply,
      Fin.sum_univ_three]

private theorem right_probe_fixed (a : Two) :
    action (PointParabolic.tensorHom (radicalPair (a,1))) probeRight = probeRight := by
  rw [radical_action]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [radical,radicalMatrix,probeRight,Matrix.mul_apply,Matrix.transpose_apply,
      Fin.sum_univ_three]

private theorem radicalPair_injective : Function.Injective radicalPair := by
  apply (injective_iff_map_eq_one _).mpr
  rintro ⟨a,b⟩ hab
  apply probes_detect a b
  · rw [hab,map_one,map_one]
    rfl
  · rw [hab,map_one,map_one]
    rfl

/-- A radical action whose fixed spaces are unchanged at index at most four is trivial. -/
theorem radical_action_trivial_of_rigidity
    {A : Type*} [_root_.Group A] [Finite A] (f : A →* Actor)
    (hf : ∀ a, f a ∈ radicalPair.range)
    (hfix : ∀ B : Subgroup A, Nat.log 2 B.index < 3 →
      ∀ X : Space, (∀ b : B, action (PointParabolic.tensorHom (f b.val)) X = X) →
        ∀ a : A, action (PointParabolic.tensorHom (f a)) X = X) :
    ∀ a : A, f a = 1 := by
  let r : A →* Two × Two :=
    (MonoidHom.ofInjective radicalPair_injective).symm.toMonoidHom.comp
      (f.codRestrict radicalPair.range hf)
  have he (a : A) : radicalPair (r a) = f a := by
    exact congrArg Subtype.val
      ((MonoidHom.ofInjective radicalPair_injective).apply_symm_apply
        (f.codRestrict radicalPair.range hf a))
  have hidx (q : A →* Two) : Nat.log 2 q.ker.index < 3 := by
    rw [index_ker]
    apply Nat.log_lt_of_lt_pow' (by decide)
    have hle := Nat.card_le_card_of_injective q.range.subtype q.range.subtype_injective
    have hc : Nat.card Two = 4 := by simp [Two,Nat.card_eq_fintype_card]
    rw [hc] at hle
    omega
  intro a
  have hleft := hfix ((MonoidHom.fst Two Two).comp r).ker (hidx _)
    probeLeft (by
      intro b
      rw [←he]
      have hb : (r b.val).1 = 1 := b.property
      rw [show r b.val = ((r b.val).1,(r b.val).2) from rfl,hb]
      exact left_probe_fixed _) a
  have hright := hfix ((MonoidHom.snd Two Two).comp r).ker (hidx _)
    probeRight (by
      intro b
      rw [←he]
      have hb : (r b.val).2 = 1 := b.property
      rw [show r b.val = ((r b.val).1,(r b.val).2) from rfl,hb]
      exact right_probe_fixed _) a
  rw [←he] at hleft hright ⊢
  have hr := probes_detect (r a).1 (r a).2 hleft hright
  rw [show r a = ((r a).1,(r a).2) from rfl,hr,map_one]

end BinaryTensorThree.PlaneFixed
