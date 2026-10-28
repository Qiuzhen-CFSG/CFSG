module
public import Theory.GroupTheory.SubgroupTransport.IntervalDiagram
public import Theory.GroupTheory.SubgroupTransport.TwistedIteration
public import Theory.GroupTheory.SylowTwistedGeneratingPair.Formula
/-!
# The half-period twist in the exact Niles diagram

Literal partial transport shifts intervals while their right endpoints
stay in its domain. For v = 2w and k = 5w, the shifted errors from N/V
and Q/M remain respectively in N and Q. A terminal center commutator
which escapes its predecessor therefore escapes Q after two twists by
alpha^w. No extension of the partial isomorphism is assumed.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 6.4, pp.53--54.
The actual original-degree application is in
`Glauberman.PushingUpSL2DegreeReduction`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

theorem iterate_image_intervalDiagram (φ : S ≃* T) (w a b r : ℕ) (hr : b+r ≤ w) :
    (image φ)^[r] (intervalDiagram φ w a b) = intervalDiagram φ w (a+r) (b+r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply',ih (by omega),image_intervalDiagram φ (by omega)]
    simp only [Nat.add_succ]

private theorem iterate_image_mono (φ : S ≃* T) (r : ℕ) {A B : Subgroup G} (h : A ≤ B) :
    (image φ)^[r] A ≤ (image φ)^[r] B := by
  induction r with
  | zero => exact h
  | succ r ih => simpa only [Function.iterate_succ_apply'] using image_mono φ ih

private theorem intervalDiagram_le_domain (φ : S ≃* T) {w a b : ℕ} (hb : b < w) :
    intervalDiagram φ w a b ≤ S :=
  (intervalCell_antitone φ (Nat.zero_le a) (by omega)).trans (intervalCell_initial_left φ).le

/-- Successive partial shifts reflect subgroup containment while both
bounded intervals stay in the domain. -/
theorem iterate_image_reflect_on_intervals (φ : S ≃* T) (w a b c d r : ℕ)
    (A B : Subgroup G) (hA : A ≤ intervalDiagram φ w a b)
    (hB : B ≤ intervalDiagram φ w c d) (hb : b+r ≤ w) (hd : d+r ≤ w)
    (h : (image φ)^[r] A ≤ (image φ)^[r] B) : A ≤ B := by
  induction r with
  | zero => exact h
  | succ r ih =>
    apply ih (by omega) (by omega)
    have ha := iterate_image_mono φ r hA
    rw [iterate_image_intervalDiagram φ w a b r (by omega)] at ha
    have hb' := iterate_image_mono φ r hB
    rw [iterate_image_intervalDiagram φ w c d r (by omega)] at hb'
    have hh := image_mono φ.symm h
    simpa only [Function.iterate_succ_apply',image_symm φ _
      (ha.trans (intervalDiagram_le_domain φ (by omega))),image_symm φ _
      (hb'.trans (intervalDiagram_le_domain φ (by omega)))] using hh

/-- The literal intervals in Niles 6.4 discharge both accumulated-error
blocks. A terminal center commutator escaping its predecessor still escapes
the core after two twists by the half-period automorphism. -/
theorem intervalDiagram_half_power_escape (S : Subgroup G) (α : MulAut S) (g : G)
    (w : ℕ) (hw : 0 < w) (Z : Subgroup G)
    (hN : (intervalDiagram (twistedConjugacy S α g) (6*w) (w+1) (5*w-1)).Normal)
    (hQ : (S ⊓ S.map (MulAut.conj g).toMonoidHom).Normal)
    (hNV : ⁅(⊤ : Subgroup G),intervalDiagram (twistedConjugacy S α g) (6*w) (w+1) (5*w-1)⁆ ≤
      intervalDiagram (twistedConjugacy S α g) (6*w) (2*w) (4*w))
    (hQM : ⁅(⊤ : Subgroup G),S ⊓ S.map (MulAut.conj g).toMonoidHom⁆ ≤
      intervalDiagram (twistedConjugacy S α g) (6*w) w (5*w))
    (hZ : Z ≤ intervalDiagram (twistedConjugacy S α g) (6*w) (4*w) (4*w))
    (hescape : ¬ Z ≤ intervalDiagram (twistedConjugacy S α g) (6*w) (4*w-1) (4*w-1)) :
    ¬ (image (twistedConjugacy S (α^w) g))^[2] Z ≤ S ⊓ S.map (MulAut.conj g).toMonoidHom := by
  let φ := twistedConjugacy S α g
  let X := intervalDiagram φ (6*w)
  let Q := S ⊓ S.map (MulAut.conj g).toMonoidHom
  let N := X (w+1) (5*w-1)
  let V := X (2*w) (4*w)
  let M := X w (5*w)
  let _ : N.Normal := hN
  let _ : Q.Normal := hQ
  let E₁ : ℕ → Subgroup G := fun i => if i = 0 then ⊥ else X (2*w) (4*w+i-1)
  let E₂ : ℕ → Subgroup G := fun i => if i = 0 then ⊥ else X w (5*w+i-1)
  have hXQ : X 1 (6*w-1) = Q := by
    simp only [X,intervalDiagram,show 6*w-(6*w-1)=1 by omega,intervalCell_intersection]
    rfl
  have himage {A : Subgroup G} {a b r : ℕ} (ha : A ≤ X a b) (hr : b+r ≤ 6*w) :
      (image φ)^[r] A ≤ X (a+r) (b+r) := by
    have hh := iterate_image_mono φ r ha
    rwa [iterate_image_intervalDiagram φ (6*w) a b r hr] at hh
  have hE₁ : ∀ i ≤ w-1, E₁ i ≤ N := by
    intro i hi
    dsimp only [E₁]
    split_ifs with hz
    · exact bot_le
    · exact intervalDiagram_mono φ (by omega) (by omega)
  have hE₂ : ∀ i ≤ w-1, E₂ i ≤ Q := by
    intro i hi
    rw [←hXQ]
    dsimp only [E₂]
    split_ifs with hz
    · exact bot_le
    · exact intervalDiagram_mono φ (by omega) (by omega)
  have hs₁ : ∀ i < w-1, image φ (E₁ i) ⊔ V ≤ E₁ (i+1) := by
    intro i hi
    by_cases hz : i = 0
    · subst i; simp [E₁,V,X,image]
    · simp only [E₁,hz,if_false,Nat.add_eq_zero_iff,one_ne_zero,and_false]
      rw [image_intervalDiagram φ (by omega)]
      exact sup_le (intervalDiagram_mono φ (by omega) (by omega))
        (intervalDiagram_mono φ le_rfl (by omega))
  have hs₂ : ∀ i < w-1, image φ (E₂ i) ⊔ M ≤ E₂ (i+1) := by
    intro i hi
    by_cases hz : i = 0
    · subst i; simp [E₂,M,X,image]
    · simp only [E₂,hz,if_false,Nat.add_eq_zero_iff,one_ne_zero,and_false]
      rw [image_intervalDiagram φ (by omega)]
      exact sup_le (intervalDiagram_mono φ (by omega) (by omega))
        (intervalDiagram_mono φ le_rfl (by omega))
  have hf₁ : image φ (E₁ (w-1)) ≤ N := by
    dsimp only [E₁]
    split_ifs with hz
    · simp [image]
    · rw [image_intervalDiagram φ (by omega)]
      exact intervalDiagram_mono φ (by omega) (by omega)
  have hf₂ : image φ (E₂ (w-1)) ≤ Q := by
    rw [←hXQ]
    dsimp only [E₂]
    split_ifs with hz
    · simp [image]
    · rw [image_intervalDiagram φ (by omega)]
      exact intervalDiagram_mono φ (by omega) (by omega)
  have hzN : ∀ i ≤ w-1, (image φ)^[i] Z ≤ N := by
    intro i hi
    exact (himage hZ (by omega)).trans (intervalDiagram_mono φ (by omega) (by omega))
  have hbQ : ∀ i ≤ w-1, (image φ)^[i] ((image φ)^[w-1+1] Z) ≤ Q := by
    intro i hi
    have hz := himage hZ (r := w-1+1) (by omega)
    rw [←hXQ]
    exact (himage hz (by omega)).trans (intervalDiagram_mono φ (by omega) (by omega))
  have hnQ : ∀ i ≤ w-1+1, (image φ)^[i] N ≤ Q := by
    intro i hi
    rw [←hXQ]
    exact (himage (A := N) le_rfl (by omega)).trans
      (intervalDiagram_mono φ (by omega) (by omega))
  have hlast : ¬ (image φ)^[w-1+1] ((image φ)^[w-1+1] Z) ≤ Q := by
    intro hh
    have he : w-1+1=w := by omega
    rw [he,←Function.iterate_add_apply,show w+w=2*w by omega] at hh
    have hz := himage hZ (r := 2*w) (by omega)
    rw [show 4*w+2*w=6*w by omega] at hz
    rw [←hXQ] at hh
    have hb := le_inf hz hh
    rw [intervalDiagram_inf,max_eq_left (by omega),min_eq_right (by omega)] at hb
    have hb' : (image φ)^[2*w] Z ≤ (image φ)^[2*w] (X (4*w-1) (4*w-1)) := by
      rw [iterate_image_intervalDiagram φ (6*w) (4*w-1) (4*w-1) (2*w) (by omega)]
      exact hb.trans (intervalDiagram_mono φ (by omega) (by omega))
    exact hescape (iterate_image_reflect_on_intervals φ (6*w) (4*w) (4*w)
      (4*w-1) (4*w-1) (2*w) Z _ hZ le_rfl (by omega) (by omega) hb')
  simp only [φ,twistedConjugacy_eq] at hs₁ hs₂ hf₁ hf₂ hzN hbQ hnQ hlast
  have hh := twice_power_twist_escape S α g Z N Q V M
    (by rw [←hXQ]; exact intervalDiagram_mono φ (by omega) (by omega)) inf_le_left
    hNV hQM E₁ E₂ (by simp [E₁]) (by simp [E₂]) (w-1) hE₁ hE₂ hs₁ hs₂ hf₁ hf₂
    hzN hbQ hnQ hlast
  rw [twistedConjugacy_eq]
  rw [show w-1+1=w by omega] at hh
  exact hh
end Theory.GroupTheory.SubgroupTransport
