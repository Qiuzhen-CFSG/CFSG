module

public import Theory.SpecificGroups.ReeTwo.CyclicFourCentralExtension

/-!
# Changing coordinates and actors in marked cyclic-four extensions

An intertwining core automorphism extends coordinatewise to the cyclic-four
models, preserving the embedded last root. Replacing an actor by `root 2`
times that actor preserves its fourth power whenever the actor inverts root 2.
The universal property then identifies the corresponding inner-twisted actions.

Source: the cyclic carry construction in `CyclicFourCentralExtension` and
ordinary collected-word identities in a group.
-/

@[expose] public section
namespace ReeTwo.CyclicFourCentralExtension

variable {β δ : MulAut Core} {hβ : β ^ 4 = 1} {hδ : δ ^ 4 = 1} {ε : Bool}

private theorem intertwine_pow (γ : MulAut Core)
    (h : ∀ q, γ (β q) = δ (γ q)) (n : ℕ) (q : Core) :
    γ ((β ^ n) q) = (δ ^ n) (γ q) := by
  induction n generalizing q with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih, h]

/-- Intertwining core automorphisms preserve the marked carry construction. -/
def congr (γ : MulAut Core) (h : ∀ q, γ (β q) = δ (γ q)) :
    Model β hβ ε ≃* Model δ hδ ε where
  toFun x := ⟨γ x.core, x.idx⟩
  invFun x := ⟨γ.symm x.core, x.idx⟩
  left_inv x := by cases x; simp
  right_inv x := by cases x; simp
  map_mul' x y := by
    apply Model.ext
    · change γ (x.core * (β ^ x.idx.val) y.core *
          mark ε ^ ((x.idx.val + y.idx.val) / 4)) =
        γ x.core * (δ ^ x.idx.val) (γ y.core) * mark ε ^ ((x.idx.val + y.idx.val) / 4)
      rw [map_mul, map_mul, map_pow, aut_mark, intertwine_pow γ h]
    · rfl

@[simp] theorem congr_embed (γ : MulAut Core) (h : ∀ q, γ (β q) = δ (γ q)) (q : Core) :
    congr (hβ := hβ) (hδ := hδ) (ε := ε) γ h (embed q) = embed (γ q) := rfl

@[simp] theorem congr_root_nine (γ : MulAut Core) (h : ∀ q, γ (β q) = δ (γ q)) :
    congr (hβ := hβ) (hδ := hδ) (ε := ε) γ h (embed (Core.root 9)) =
      embed (Core.root 9) := by
  rw [congr_embed, Core.aut_root_nine]

/-- Multiplying the actor by the middle root. -/
def shiftedActor : Model β hβ ε := embed (Core.root 2) * actor

private theorem shiftedActor_square (hinv : β (Core.root 2) = (Core.root 2)⁻¹) :
    (shiftedActor : Model β hβ ε) ^ 2 = actor ^ 2 := by
  have hc := actor_conj (beta := β) (hbeta := hβ) (epsilon := ε) (Core.root 2)
  rw [hinv, map_inv] at hc
  have he := mul_inv_eq_iff_eq_mul.mp hc
  simp only [shiftedActor, pow_two]
  calc
    (embed (Core.root 2) * actor) * (embed (Core.root 2) * actor) =
        embed (Core.root 2) * (actor * embed (Core.root 2)) * actor := by group
    _ = actor * actor := by rw [he]; group

/-- Inversion of the middle root ensures the fourth-power parameter is unchanged. -/
theorem shiftedActor_four (hinv : β (Core.root 2) = (Core.root 2)⁻¹) :
    (shiftedActor : Model β hβ ε) ^ 4 = embed (mark ε) := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, shiftedActor_square hinv, ← pow_mul]
  exact actor_four

theorem shiftedActor_conj (q : Core) :
    (shiftedActor : Model β hβ ε) * embed q * shiftedActor⁻¹ =
      embed (Core.root 2 * β q * (Core.root 2)⁻¹) := by
  simp only [shiftedActor, mul_inv_rev, map_mul, map_inv]
  calc
    (embed (Core.root 2) * actor) * embed q * (actor⁻¹ * (embed (Core.root 2))⁻¹) =
        embed (Core.root 2) * (actor * embed q * actor⁻¹) * (embed (Core.root 2))⁻¹ := by group
    _ = _ := by rw [actor_conj]

theorem shiftedActor_generate :
    (embed (beta := β) (hbeta := hβ) (epsilon := ε)).range ⊔
      Subgroup.zpowers shiftedActor = ⊤ := by
  apply top_unique
  rw [← generate (beta := β) (hbeta := hβ) (epsilon := ε)]
  apply sup_le le_sup_left
  apply Subgroup.zpowers_le.mpr
  have he : (actor : Model β hβ ε) = (embed (Core.root 2))⁻¹ * shiftedActor := by
    simp [shiftedActor]
  rw [he]
  apply Subgroup.mul_mem
  · exact (show (embed (beta := β) (hbeta := hβ) (epsilon := ε)).range ≤ _ from le_sup_left) ((embed (beta := β) (hbeta := hβ) (epsilon := ε)).range.inv_mem ⟨_, rfl⟩)
  · exact (show Subgroup.zpowers (shiftedActor : Model β hβ ε) ≤ _ from le_sup_right) (Subgroup.mem_zpowers _)

/-- Changing the actor realizes an inner twist of the core action. -/
noncomputable def shiftEquiv
    (hinv : β (Core.root 2) = (Core.root 2)⁻¹)
    (h : ∀ q, δ q = Core.root 2 * β q * (Core.root 2)⁻¹) :
    Model δ hδ ε ≃* Model β hβ ε :=
  equiv embed shiftedActor
    (fun q => (shiftedActor_conj q).trans (congrArg embed (h q).symm))
    (shiftedActor_four hinv) card shiftedActor_generate

@[simp] theorem shiftEquiv_embed
    (hinv : β (Core.root 2) = (Core.root 2)⁻¹)
    (h : ∀ q, δ q = Core.root 2 * β q * (Core.root 2)⁻¹) (q : Core) :
    shiftEquiv (hβ := hβ) (hδ := hδ) (ε := ε) hinv h (embed q) = embed q :=
  equiv_embed ..

end ReeTwo.CyclicFourCentralExtension
