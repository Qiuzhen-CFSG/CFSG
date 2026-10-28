module
public import Theory.GroupTheory.SubgroupTransport.GapIntervals
public import Theory.GroupTheory.SubgroupTransport.PointCovering
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.CommutatorPreimage.Membership

/-!
# The commutator at the first noncentral gap

The exact gap centralizer is normal in the right Sylow. Its commutator
with the far endpoint lies in the middle point, and the three-subgroups
lemma places the endpoint commutator centrally modulo that point.
The two central boundaries cannot both contain the first-gap commutator.
Point covering then deletes any left endpoint strictly between k-2v+1
and the center boundary, determining the exact endpoint in that branch.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 5.3(b), p.50.
The full Sylow center is retained; no central quotient is suppressed.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

theorem intervalDiagram_point_not_le_next (φ : S ≃* T) (w : ℕ)
    (hgen : ∀ a b : ℕ, a+b < w →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hne : ¬ S ≤ T) (i : ℕ) (hi : i < w) :
    ¬ intervalDiagram φ w i i ≤ intervalDiagram φ w (i+1) (i+1) := by
  let X := intervalDiagram φ w
  have hS (j : ℕ) (hj : j < w) : X j j ≤ S := by
    have hh : X j j ≤ intervalCell φ 0 1 := intervalCell_antitone φ (by omega) (by omega)
    exact hh.trans (intervalCell_initial_left φ).le
  induction i with
  | zero =>
    intro hh
    have hs := intervalCell_left_supplement φ w (by omega)
      (fun b _ hb => hgen 0 b (by omega))
    have h1T : X 1 1 ≤ T := by
      have hle : X 1 1 ≤ intervalCell φ 1 0 := intervalCell_antitone φ le_rfl (by omega)
      exact hle.trans (intervalCell_initial_right φ).le
    apply hne
    rw [←hs]
    exact sup_le ((show X 0 0 ≤ X 1 1 from hh).trans h1T) inf_le_right
  | succ i ih =>
    intro hh
    apply ih (by omega)
    have hm := image_mono φ.symm hh
    have he (j : ℕ) (hj : j < w) : image φ.symm (X (j+1) (j+1)) = X j j := by
      dsimp only [X]
      rw [←image_intervalDiagram φ (i := j) hj]
      exact image_symm φ _ (hS j hj)
    rw [he i (by omega),he (i+1) (by omega)] at hm
    exact hm

theorem intervalDiagram_point_not_le_previous (φ : S ≃* T) (w : ℕ)
    (hgen : ∀ a b : ℕ, a+b < w →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hne : ¬ T ≤ S) (i : ℕ) (hi : 0 < i) (hiw : i ≤ w) :
    ¬ intervalDiagram φ w i i ≤ intervalDiagram φ w (i-1) (i-1) := by
  have hgenR : ∀ a b : ℕ, a+b < w →
      intervalCell φ.symm a (b+1) ⊔ intervalCell φ.symm (a+1) b = intervalCell φ.symm a b := by
    intro a b hab
    simpa only [intervalCell_symm,sup_comm] using hgen b a (by omega)
  have hh := intervalDiagram_point_not_le_next φ.symm w hgenR hne (w-i) (by omega)
  rw [intervalDiagram_symm φ w (w-i) (w-i) (by omega),
    intervalDiagram_symm φ w (w-i+1) (w-i+1) (by omega)] at hh
  simpa only [show w-(w-i)=i by omega,show w-(w-i+1)=i-1 by omega] using hh

/-- Commuting the first-gap commutator with its normal containing interval
lands in the single middle point. This is the source's estimate (1),
valid for every element of that interval. -/
theorem intervalDiagram_gap_triple_bound (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3*v → b < a+2*v →
      IsElementaryAbelian 2 (intervalDiagram φ (3*v) a b))
    (hz : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (htwice : ∀ i : ℕ, i ≤ v →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) (i+2*v) (i+2*v)⁆ ≤
        intervalDiagram φ (3*v) (i+v) (i+v))
    (hn : T ≤ normalizer (intervalDiagram φ (3*v) (k-2*v+1) (3*v) : Set G)) :
    ⁅⁅intervalDiagram φ (3*v) 1 1,intervalDiagram φ (3*v) (k+1) (k+1)⁆,
      intervalDiagram φ (3*v) (k-2*v+1) (3*v)⁆ ≤
        intervalDiagram φ (3*v) (k-v+1) (k-v+1) := by
  let X := intervalDiagram φ (3*v)
  let C := X (k-2*v+1) (3*v)
  let Y := X (k-v+1) (k-v+1)
  have hT : X 1 (3*v) = T := by
    simp only [X,intervalDiagram,Nat.sub_self,intervalCell_initial_right]
  have hCT : C ≤ T := (intervalDiagram_mono φ (by omega) le_rfl).trans hT.le
  have hYT : Y ≤ centerIn T := by
    rw [hz]
    exact intervalDiagram_mono φ (by omega) (by omega)
  have hTY : T ≤ centralizer (Y : Set G) := le_centralizer_iff.mpr (hYT.trans inf_le_right)
  have hnormY := hTY.trans (centralizer_le_normalizer _)
  have hBT : X (k+1) (k+1) ≤ T := (intervalDiagram_mono φ (by omega) (by omega)).trans hT.le
  have hAT : X 1 1 ≤ T := (intervalDiagram_mono φ le_rfl (by omega)).trans hT.le
  have hCB : ⁅C,X (k+1) (k+1)⁆ ≤ Y := by
    apply intervalDiagram_cross_commutator_le φ (3*v) hgen (by omega) le_rfl le_rfl
      (by omega) Y (hCT.trans hnormY) (hBT.trans hnormY)
    intro a b ha haw hb hbk
    have hb' : b = k+1 := by omega
    subst b
    by_cases he : a = k-2*v+1
    · subst a
      simpa only [show k-2*v+1+2*v=k+1 by omega,show k-2*v+1+v=k-v+1 by omega] using
        htwice (k-2*v+1) (by omega)
    · exact (commutator_eq_bot_iff_le_centralizer.mpr
        (intervalDiagram_point_centralizes_of_close φ v a (k+1) hshort haw (by omega)
          (by omega) (by omega))).le.trans bot_le
  apply commutator_commutator_le_of_rotate_of_le_normalizer
    (hAT.trans hnormY) (hBT.trans hnormY) (hCT.trans hnormY)
  · rw [commutator_comm (X (k+1) (k+1)) C]
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (hCB.trans (hYT.trans inf_le_right |>.trans (centralizer_le hAT)))).le.trans bot_le
  · exact (commutator_mono (le_normalizer_iff_commutator_le_left.mp (hAT.trans hn)) le_rfl).trans hCB
/-- If the first-gap commutator starts strictly after k-2v+1 but before
the Sylow center, covering deletes that first point. Iteration forces
its first endpoint to be k-2v+1 whenever it escapes the center's left edge. -/
theorem intervalDiagram_gap_delete_head (φ : S ≃* T) (v k m : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v) (hm : k-2*v+1 < m) (hmv : m ≤ v)
    (hS : S ≤ normalizer (S ⊓ T : Set G))
    (hT : T ≤ normalizer (S ⊓ T : Set G))
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3*v → b < a+2*v →
      IsElementaryAbelian 2 (intervalDiagram φ (3*v) a b))
    (hz : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (htwice : ∀ i : ℕ, i ≤ v →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) (i+2*v) (i+2*v)⁆ ≤
        intervalDiagram φ (3*v) (i+v) (i+v))
    (hcover : let X := intervalDiagram φ (3*v)
      PointCommutatorCovering (X m m) (X (m+1) (m+1))
        (X (m+2*v) (m+2*v)) (X (m+2*v-1) (m+2*v-1))
        (X (m+v) (m+v)) (X (m+v-1) (m+v-1)))
    (hstrict : ¬ intervalDiagram φ (3*v) (m+v) (m+v) ≤
      intervalDiagram φ (3*v) (m+v-1) (m+v-1))
    (D : Subgroup G)
    (hD : D ≤ intervalDiagram φ (3*v) m (3*v))
    (htriple : ⁅D,intervalDiagram φ (3*v) (k-2*v+1) (3*v)⁆ ≤
      intervalDiagram φ (3*v) (k-v+1) (k-v+1)) :
    D ≤ intervalDiagram φ (3*v) (m+1) (3*v) := by
  classical
  let X := intervalDiagram φ (3*v)
  let B := X (m+2*v) (m+2*v)
  let Y := X (k-v+1) (k-v+1)
  have hXT : X 1 (3*v) = T := by
    simp only [X,intervalDiagram,Nat.sub_self,intervalCell_initial_right]
  have hYT : Y ≤ centerIn T := by
    rw [hz]
    exact intervalDiagram_mono φ (by omega) (by omega)
  have hnY : T ≤ normalizer (Y : Set G) :=
    (le_centralizer_iff.mpr (hYT.trans inf_le_right)).trans (centralizer_le_normalizer _)
  have hB : B ≤ X (k-2*v+1) (3*v) := intervalDiagram_mono φ (by omega) (by omega)
  have htail : X (m+1) (3*v) ≤ centralizer (B : Set G) :=
    intervalDiagram_centralizes_of_close φ v hgen hshort (by omega) le_rfl le_rfl
      (by omega) (by omega) (by omega)
  have hjoin := intervalDiagram_head_sup_tail φ (3*v) hgen (i := m) (j := 3*v) (by omega) le_rfl
  have hnorm := (intervalDiagram_normalizes_trim φ hS hT (3*v) (i := m) (j := 3*v)
    (by omega) le_rfl (by omega)).2
  intro x hx
  by_contra hx'
  have hxprod : x ∈ (X m m : Set G) * (X (m+1) (3*v) : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _
      ((intervalDiagram_mono φ le_rfl (show m ≤ 3*v by omega)).trans hnorm),hjoin]
    exact hD hx
  obtain ⟨a,ha,b,hb,hab⟩ := hxprod
  have ha' : a ∉ X (m+1) (m+1) := by
    intro hh
    apply hx'
    rw [←hab]
    exact mul_mem (intervalDiagram_mono φ le_rfl (show m+1 ≤ 3*v by omega) hh) hb
  have hac : ∀ z ∈ B, ⁅a,z⁆ ∈ Y := by
    intro z hzB
    have hc : ⁅b,z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr ((htail hb) z hzB).symm
    have hh := htriple (commutator_mem_commutator hx (hB hzB))
    rw [←hab,commutatorElement_mul_left_eq_conj_mul,hc,mul_one,mul_inv_cancel,one_mul] at hh
    exact hh
  have hnA : X m m ≤ normalizer (Y : Set G) :=
    ((intervalDiagram_mono φ (show 1 ≤ m by omega) (show m ≤ 3*v by omega)).trans hXT.le).trans hnY
  have hpre : zpowers a ≤ commutatorPreimage (X m m) B Y :=
    zpowers_le.mpr ((mem_commutatorPreimage_iff _ _ _ hnA a).mpr ⟨ha,hac⟩)
  have hrowY : ⁅zpowers a,B⁆ ≤ Y :=
    (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hnA)
  have hrowM : ⁅zpowers a,B⁆ ≤ X (m+v) (m+v) :=
    (commutator_mono (zpowers_le.mpr ha) le_rfl).trans (htwice m hmv)
  have hYleft : Y ≤ X 1 (m+v-1) := intervalDiagram_mono φ (by omega) (by omega)
  have hrowPrev : ⁅zpowers a,B⁆ ≤ X (m+v-1) (m+v-1) := by
    have hh := le_inf hrowM (hrowY.trans hYleft)
    rw [intervalDiagram_inf,max_eq_left (show 1 ≤ m+v by omega),
      min_eq_right (show m+v-1 ≤ m+v by omega)] at hh
    exact hh.trans (intervalDiagram_mono φ (by omega) le_rfl)
  have hc := hcover.2.1 a ha ha'
  apply hstrict
  exact hc.symm.le.trans (sup_le hrowPrev inf_le_right)

/-- Exactness of the left endpoint in the branch escaping the Sylow
center's left boundary. This is Niles 5.3(b) in natural coordinates. -/
theorem intervalDiagram_gap_left_endpoint (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v)
    (hS : S ≤ normalizer (S ⊓ T : Set G))
    (hT : T ≤ normalizer (S ⊓ T : Set G))
    (hne : ¬ T ≤ S)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3*v → b < a+2*v →
      IsElementaryAbelian 2 (intervalDiagram φ (3*v) a b))
    (hz : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (htwice : ∀ i : ℕ, i ≤ v →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) (i+2*v) (i+2*v)⁆ ≤
        intervalDiagram φ (3*v) (i+v) (i+v))
    (hcover : ∀ m : ℕ, m ≤ v →
      let X := intervalDiagram φ (3*v)
      PointCommutatorCovering (X m m) (X (m+1) (m+1))
        (X (m+2*v) (m+2*v)) (X (m+2*v-1) (m+2*v-1))
        (X (m+v) (m+v)) (X (m+v-1) (m+v-1)))
    (D : Subgroup G)
    (htriple : ⁅D,intervalDiagram φ (3*v) (k-2*v+1) (3*v)⁆ ≤
      intervalDiagram φ (3*v) (k-v+1) (k-v+1))
    (hescape : ¬ D ≤ intervalDiagram φ (3*v) (v+1) (3*v)) :
    ¬ D ≤ intervalDiagram φ (3*v) (k-2*v+2) (3*v) := by
  intro hh
  have hsteps : ∀ m : ℕ, k-2*v+2 ≤ m → m ≤ v+1 →
      D ≤ intervalDiagram φ (3*v) m (3*v) := by
    intro m hm
    induction m,hm using Nat.le_induction with
    | base => intro _; exact hh
    | succ m hm ih =>
      intro hmv
      apply intervalDiagram_gap_delete_head φ v k m hk hkw (by omega) (by omega)
        hS hT hgen hshort hz htwice (hcover m (by omega))
        (intervalDiagram_point_not_le_previous φ (3*v) hgen hne (m+v) (by omega) (by omega))
        D (ih (by omega)) htriple
  exact hescape (hsteps (v+1) (by omega) le_rfl)

/-- The first-gap commutator must escape at least one central boundary.
Otherwise literal shifts make every commutator at that gap central,
contradicting the selected witness. This is Niles 5.3(a). -/
theorem intervalDiagram_gap_endpoint_escape (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v)
    (hz : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (hex : ∃ i : ℕ, 1 ≤ i ∧ i+k ≤ 3*v ∧
      ¬ ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) (i+k) (i+k)⁆ ≤ centerIn T) :
    let X := intervalDiagram φ (3*v)
    ¬ ⁅X 1 1,X (k+1) (k+1)⁆ ≤ X (v+1) (3*v) ∨
      ¬ ⁅X 1 1,X (k+1) (k+1)⁆ ≤ X 1 (k-v+1) := by
  classical
  dsimp only
  by_contra! hh
  obtain ⟨i,hi,hiw,hnot⟩ := hex
  have hb := le_inf hh.1 hh.2
  rw [intervalDiagram_inf,max_eq_left (show 1 ≤ v+1 by omega),
    min_eq_right (show k-v+1 ≤ 3*v by omega)] at hb
  have hs := intervalCell_commutator_shift φ (i-1) 1 (3*v-i)
    (k+1) (3*v-i-k) (v+1) (3*v-i-k+v) (by
      simpa only [intervalDiagram,show 3*v-i+(i-1)=3*v-1 by omega,
        show 3*v-i-k+(i-1)=3*v-(k+1) by omega,
        show 3*v-i-k+v+(i-1)=3*v-(k-v+1) by omega] using hb)
  apply hnot
  rw [hz]
  have hs' : ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) (i+k) (i+k)⁆ ≤
      intervalDiagram φ (3*v) (v+i) (k-v+i) := by
    simpa only [intervalDiagram,show 1+(i-1)=i by omega,
      show k+1+(i-1)=i+k by omega,show 3*v-i-k=3*v-(i+k) by omega,
      show v+1+(i-1)=v+i by omega,show 3*v-(i+k)+v=3*v-(k-v+i) by omega] using hs
  exact hs'.trans (intervalDiagram_mono φ (by omega) (by omega))

end Theory.GroupTheory.SubgroupTransport
