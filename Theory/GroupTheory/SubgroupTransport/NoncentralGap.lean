module
public import Theory.GroupTheory.SubgroupTransport.IntervalCentralizers
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupAction.Defs

/-!
# The shortest noncentral gap in a Niles interval

Relative normal generation extends pointwise commutator bounds to a whole
interval. In the depth-3v right Sylow interval, elementary short intervals
and the distance-2v commutator bound make every gap at most 2v central.
If the Sylow commutator is not central, choose the least escaping gap k:
then 2v < k < 3v, and all shorter point commutators are central.

Source: Niles, *Pushing-up in finite groups* (1979), the definition before
Lemma 5.1 and the initial k > u step of Lemma 5.3, pp.49--50.
The actual original-degree construction is in
`Glauberman.PushingUpSL2DegreePoints`.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

/-- A commutator bound for point generators extends to their entire
interval, using only relative normality of its target. -/
theorem intervalDiagram_commutator_le_of_points (φ : S ≃* T) (w : ℕ)
    (hgen : ∀ a b : ℕ, a+b < w →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ w) (C : Subgroup G)
    (hn : intervalDiagram φ w i j ≤ normalizer (C : Set G))
    (hp : ∀ a b : ℕ, i ≤ a → a ≤ j → i ≤ b → b ≤ j →
      ⁅intervalDiagram φ w a a,intervalDiagram φ w b b⁆ ≤ C) :
    ⁅intervalDiagram φ w i j,intervalDiagram φ w i j⁆ ≤ C := by
  let H := intervalDiagram φ w i j
  have hpH (a : ℕ) (ha : i ≤ a) (haj : a ≤ j) : ⁅intervalDiagram φ w a a,H⁆ ≤ C := by
    rw [commutator_comm]
    have hpre : H ≤ commutatorPreimage H (intervalDiagram φ w a a) C := by
      apply intervalDiagram_le_of_points φ w hgen hij hj
      intro b hb hbj
      exact le_commutatorPreimage (intervalDiagram_mono φ hb hbj) (hp b a hb hbj ha haj)
    exact (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hn)
  have hpre : H ≤ commutatorPreimage H H C := by
    apply intervalDiagram_le_of_points φ w hgen hij hj
    intro a ha haj
    exact le_commutatorPreimage (intervalDiagram_mono φ ha haj) (hpH a ha haj)
  exact (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hn)

/-- In the right Sylow interval, commutators separated by at most 2v are
central. Thus a noncentral commutator has a shortest gap strictly above
2v, with all shorter point commutators central. This is the initial
nonabelian selection in Niles 5.3. -/
theorem intervalDiagram_minimal_noncentral_gap (φ : S ≃* T) (v : ℕ) (hv : 0 < v)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3*v → b < a+2*v →
      IsElementaryAbelian 2 (intervalDiagram φ (3*v) a b))
    (hcenter : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (htwice : ∀ i : ℕ, i ≤ v →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) (i+2*v) (i+2*v)⁆ ≤
        intervalDiagram φ (3*v) (i+v) (i+v))
    (hnc : ¬ ⁅T,T⁆ ≤ centerIn T) :
    ∃ k : ℕ, 2*v < k ∧ k < 3*v ∧
      (∃ i : ℕ, 1 ≤ i ∧ i+k ≤ 3*v ∧
        ¬ ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) (i+k) (i+k)⁆ ≤ centerIn T) ∧
      (∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
        ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) j j⁆ ≤ centerIn T) := by
  classical
  let X := intervalDiagram φ (3*v)
  have hT : X 1 (3*v) = T := by
    simp only [X,intervalDiagram,Nat.sub_self,intervalCell_initial_right]
  have hnear (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 3*v) (hgap : j ≤ i+2*v) :
      ⁅X i i,X j j⁆ ≤ centerIn T := by
    by_cases he : j = i+2*v
    · subst j
      exact (htwice i (by omega)).trans (by
        rw [hcenter]
        exact intervalDiagram_mono φ (by omega) (by omega))
    · have hc : X i i ≤ centralizer (X j j : Set G) :=
        intervalDiagram_point_centralizes_of_close φ v i j hshort (by omega) hj (by omega) (by omega)
      exact (commutator_eq_bot_iff_le_centralizer.mpr hc).le.trans bot_le
  have hex : ∃ k : ℕ, ∃ i : ℕ, 1 ≤ i ∧ i+k ≤ 3*v ∧
      ¬ ⁅X i i,X (i+k) (i+k)⁆ ≤ centerIn T := by
    by_contra! h
    apply hnc
    conv_lhs => rw [←hT]
    apply intervalDiagram_commutator_le_of_points φ (3*v) hgen (i := 1) (j := 3*v) (by omega) le_rfl (centerIn T)
      (by change X 1 (3*v) ≤ _; rw [hT]; exact (le_centralizer_iff.mpr (show centerIn T ≤ centralizer (T : Set G) from
        inf_le_right)).trans (centralizer_le_normalizer _))
    intro a b ha haw hb hbw
    rcases le_total a b with hab | hba
    · simpa only [show a+(b-a)=b by omega] using h (b-a) a ha (by omega)
    · rw [commutator_comm]
      simpa only [show b+(a-b)=a by omega] using h (a-b) b hb (by omega)
  let k := Nat.find hex
  obtain ⟨i,hi,hik,hn⟩ := Nat.find_spec hex
  have hk : 2*v < k := by
    by_contra! hh
    apply hn
    exact hnear i (i+k) hi (by omega) hik (by omega)
  refine ⟨k,hk,by omega,⟨i,hi,hik,hn⟩,?_⟩
  intro a b ha hab hb hgap
  by_contra hnot
  have hlt : b-a < k := by omega
  have hh := Nat.find_min hex hlt
  apply hh
  exact ⟨a,ha,by omega,by simpa only [show a+(b-a)=b by omega] using hnot⟩
end Theory.GroupTheory.SubgroupTransport
