module
public import Theory.GroupTheory.SubgroupTransport.NoncentralGap
public import Mathlib.GroupTheory.Nilpotent

/-!
# Central intervals below the first noncentral gap

Pointwise centrality below a gap extends to entire intervals. The two
middle intervals in Niles's argument are consequently normal in the right
Sylow, as are their relative centralizers. Those centralizers bound the
whole derived subgroup, using short-interval commutativity.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas 5.3--5.4,
pp.50--51. Endpoints are shifted up by one from the printed notation.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

/-- Extend a bound on all point pairs to two full intervals. -/
theorem intervalDiagram_cross_commutator_le (φ : S ≃* T) (w : ℕ)
    (hgen : ∀ a b : ℕ, a+b < w →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    {i j k l : ℕ} (hij : i ≤ j) (hkl : k ≤ l) (hj : j ≤ w) (hl : l ≤ w)
    (C : Subgroup G)
    (hn₁ : intervalDiagram φ w i j ≤ normalizer (C : Set G))
    (hn₂ : intervalDiagram φ w k l ≤ normalizer (C : Set G))
    (hp : ∀ a b : ℕ, i ≤ a → a ≤ j → k ≤ b → b ≤ l →
      ⁅intervalDiagram φ w a a,intervalDiagram φ w b b⁆ ≤ C) :
    ⁅intervalDiagram φ w i j,intervalDiagram φ w k l⁆ ≤ C := by
  let A := intervalDiagram φ w i j
  let B := intervalDiagram φ w k l
  have ha (a : ℕ) (hai : i ≤ a) (haj : a ≤ j) :
      ⁅intervalDiagram φ w a a,B⁆ ≤ C := by
    rw [commutator_comm]
    have hpre : B ≤ commutatorPreimage B (intervalDiagram φ w a a) C := by
      apply intervalDiagram_le_of_points φ w hgen hkl hl
      intro b hbk hbl
      apply le_commutatorPreimage (intervalDiagram_mono φ hbk hbl)
      rw [commutator_comm]
      exact hp a b hai haj hbk hbl
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hn₂)
  have hpre : A ≤ commutatorPreimage A B C := by
    apply intervalDiagram_le_of_points φ w hgen hij hj
    intro a hai haj
    exact le_commutatorPreimage (intervalDiagram_mono φ hai haj) (ha a hai haj)
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hn₁)

/-- An interval whose distances from both ends are below k commutes
with the right Sylow modulo its full center. -/
theorem intervalDiagram_gap_central (φ : S ≃* T) (v k : ℕ)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hgap : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) j j⁆ ≤ centerIn T)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3*v)
    (hleft : b < 1+k) (hright : 3*v < a+k) :
    ⁅T,intervalDiagram φ (3*v) a b⁆ ≤ centerIn T := by
  have hT : intervalDiagram φ (3*v) 1 (3*v) = T := by
    simp only [intervalDiagram,Nat.sub_self,intervalCell_initial_right]
  have hn : T ≤ normalizer (centerIn T : Set G) :=
    (le_centralizer_iff.mpr (show centerIn T ≤ centralizer (T : Set G) from inf_le_right)).trans
      (centralizer_le_normalizer _)
  apply (commutator_mono hT.ge le_rfl).trans
  apply intervalDiagram_cross_commutator_le φ (3*v) hgen (by omega) hab le_rfl hb
    (centerIn T) (hT.le.trans hn) ((intervalDiagram_mono φ ha hb).trans (hT.le.trans hn))
  intro i j hi hiw hj hjb
  rcases le_total i j with hij | hji
  · exact hgap i j hi hij (by omega) (by omega)
  · rw [commutator_comm]
    exact hgap j i (by omega) hji hiw (by omega)

/-- Both source middle intervals and their relative centralizers are
normal in T. This uses centrality below k, retaining the full center. -/
theorem intervalDiagram_gap_normalizers (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hz : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (hgap : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) j j⁆ ≤ centerIn T) :
    let X := intervalDiagram φ (3*v)
    (⁅T,X (v+1) k⁆ ≤ centerIn T ∧
      T ≤ normalizer (X (v+1) k : Set G) ∧
      T ≤ normalizer ((T ⊓ centralizer (X (v+1) k : Set G) : Subgroup G) : Set G)) ∧
    (⁅T,X (3*v-k+1) (2*v)⁆ ≤ centerIn T ∧
      T ≤ normalizer (X (3*v-k+1) (2*v) : Set G) ∧
      T ≤ normalizer ((T ⊓ centralizer (X (3*v-k+1) (2*v) : Set G) : Subgroup G) : Set G)) := by
  have key (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3*v)
      (hl : b < 1+k) (hr : 3*v < a+k) (haz : a ≤ v+1) (hzb : 2*v ≤ b) :
      ⁅T,intervalDiagram φ (3*v) a b⁆ ≤ centerIn T ∧
      T ≤ normalizer (intervalDiagram φ (3*v) a b : Set G) ∧
      T ≤ normalizer ((T ⊓ centralizer (intervalDiagram φ (3*v) a b : Set G) : Subgroup G) : Set G) := by
    have hc := intervalDiagram_gap_central φ v k hgen hgap ha hab hb hl hr
    have hn : T ≤ normalizer (intervalDiagram φ (3*v) a b : Set G) := by
      apply le_normalizer_iff_commutator_le_right.mpr
      exact hc.trans (hz ▸ intervalDiagram_mono φ haz hzb)
    exact ⟨hc,hn,(le_inf T.le_normalizer (hn.trans
      ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp inferInstance))).trans inf_normalizer_le_normalizer_inf⟩
  exact ⟨key (v+1) k (by omega) (by omega) (by omega) (by omega) (by omega)
      le_rfl (by omega),
    key (3*v-k+1) (2*v) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) le_rfl⟩

/-- The exact centralizers of the two gap intervals contain every point
commutator, hence the whole derived subgroup. -/
theorem intervalDiagram_derived_gap_bound (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3*v → b < a+2*v →
      IsElementaryAbelian 2 (intervalDiagram φ (3*v) a b))
    (hz : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (hgap : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) j j⁆ ≤ centerIn T)
    (hc₁ : T ⊓ centralizer (intervalDiagram φ (3*v) (v+1) k : Set G) =
      intervalDiagram φ (3*v) (k-2*v+1) (3*v))
    (hc₂ : T ⊓ centralizer (intervalDiagram φ (3*v) (3*v-k+1) (2*v) : Set G) =
      intervalDiagram φ (3*v) 1 (5*v-k)) :
    ⁅T,T⁆ ≤ intervalDiagram φ (3*v) (k-2*v+1) (5*v-k) := by
  let X := intervalDiagram φ (3*v)
  obtain ⟨⟨_,_,hn₁⟩,⟨_,_,hn₂⟩⟩ := intervalDiagram_gap_normalizers φ v k hk hkw hgen hz hgap
  rw [hc₁] at hn₁
  rw [hc₂] at hn₂
  have he : X (k-2*v+1) (3*v) ⊓ X 1 (5*v-k) = X (k-2*v+1) (5*v-k) := by
    rw [intervalDiagram_inf,max_eq_left (by omega),min_eq_right (by omega)]
  have hn : T ≤ normalizer (X (k-2*v+1) (5*v-k) : Set G) := by
    rw [←he]
    exact (le_inf hn₁ hn₂).trans inf_normalizer_le_normalizer_inf
  have hT : X 1 (3*v) = T := by
    simp only [X,intervalDiagram,Nat.sub_self,intervalCell_initial_right]
  have hp (i j : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ 3*v) :
      ⁅X i i,X j j⁆ ≤ X (k-2*v+1) (5*v-k) := by
    by_cases hclose : j < i+2*v
    · have hh := intervalDiagram_point_centralizes_of_close φ v i j hshort
        (by omega) hj (by omega) hclose
      exact (commutator_eq_bot_iff_le_centralizer.mpr hh).le.trans bot_le
    · have hiT : X i i ≤ T := (intervalDiagram_mono φ hi (by omega)).trans hT.le
      have hjT : X j j ≤ T := (intervalDiagram_mono φ (by omega) hj).trans hT.le
      have hjC : X j j ≤ X (k-2*v+1) (3*v) := intervalDiagram_mono φ (by omega) hj
      have hiC : X i i ≤ X 1 (5*v-k) := intervalDiagram_mono φ hi (by omega)
      rw [←he]
      exact le_inf
        ((commutator_mono le_rfl hjC).trans
          (le_normalizer_iff_commutator_le_right.mp (hiT.trans hn₁)))
        ((commutator_mono hiC le_rfl).trans
          (le_normalizer_iff_commutator_le_left.mp (hjT.trans hn₂)))
  apply (commutator_mono hT.ge hT.ge).trans
  apply intervalDiagram_commutator_le_of_points φ (3*v) hgen (by omega) le_rfl
    (X (k-2*v+1) (5*v-k)) (hT.le.trans hn)
  intro i j hi hiw hj hjw
  rcases le_total i j with hij | hji
  · exact hp i j hi hij hjw
  · rw [commutator_comm]
    exact hp j i hj hji hiw
/-- The numerical inequality in Niles 5.3(d) puts the derived subgroup
inside an interval central modulo Z(T), giving the class-three conclusion
of 5.4. The numerical premise is retained explicitly. -/
theorem intervalDiagram_class_three_of_gap_bound (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v) (hsharp : 5*v ≤ 2*k)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hgap : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) j j⁆ ≤ centerIn T)
    (hderived : ⁅T,T⁆ ≤ intervalDiagram φ (3*v) (k-2*v+1) (5*v-k)) :
    ⁅T,T⁆ ≤ intervalDiagram φ (3*v) (3*v-k+1) k ∧
      T.lowerCentralSeries 3 = ⊥ := by
  have hd : ⁅T,T⁆ ≤ intervalDiagram φ (3*v) (3*v-k+1) k :=
    hderived.trans (intervalDiagram_mono φ (by omega) (by omega))
  have hcentral := intervalDiagram_gap_central φ v k hgen hgap
    (a := 3*v-k+1) (b := k) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hthird : ⁅⁅T,T⁆,T⁆ ≤ centerIn T := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hd).trans hcentral
  refine ⟨hd,?_⟩
  rw [show 3=2+1 by omega,Subgroup.lowerCentralSeries_succ,
    show 2=1+1 by omega,Subgroup.lowerCentralSeries_succ,
    show 1=0+1 by omega,Subgroup.lowerCentralSeries_succ,Subgroup.lowerCentralSeries_zero]
  exact commutator_eq_bot_iff_le_centralizer.mpr (hthird.trans inf_le_right)

end Theory.GroupTheory.SubgroupTransport
