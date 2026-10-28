module
public import Theory.GroupTheory.SubgroupTransport.GapFixedHalves
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# A surviving terminal triple commutator in the Niles diagram

The exact action kernel on M/N forces the first-gap commutator to escape
its left boundary. The equality 5v = 2k shifts it to the interval starting
at v. Elementwise point covering then makes its commutator with the final
point cover the last core-center point modulo its predecessor. All
intervals and full centers are retained.

Source: Niles, *Pushing-up in finite groups* (1979), Lemmas 5.7 and 6.4,
pp.52--54. The original-degree application is in
`Glauberman.PushingUpSL2DegreeReduction`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise commutatorElement
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

/-- The first commutator escapes the smaller normal layer on its left.
The exact action kernel prevents the original left Sylow from fixing M/N. -/
theorem intervalDiagram_gap_initial_escape (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v)
    (hne : ¬ S ≤ T)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hN : (intervalDiagram φ (3*v) (3*v-k+1) (k-1)).Normal)
    (hhalf : ⁅S,intervalDiagram φ (3*v) (3*v-k) (k-1)⁆ ≤
      intervalDiagram φ (3*v) (3*v-k+1) (k-1))
    (hkernel : commutatorPreimage ⊤
      (intervalDiagram φ (3*v) (3*v-k) k)
      (intervalDiagram φ (3*v) (3*v-k+1) (k-1)) = S ⊓ T)
    (hd : ⁅T,T⁆ ≤ intervalDiagram φ (3*v) (3*v-k+1) k) :
    let X := intervalDiagram φ (3*v)
    ⁅X 0 0,X k k⁆ ≤ X (3*v-k) (k-1) ∧
      ¬ ⁅X 0 0,X k k⁆ ≤ X (3*v-k+1) (3*v) := by
  let X := intervalDiagram φ (3*v)
  let N := X (3*v-k+1) (k-1)
  let M := X (3*v-k) k
  let _ : N.Normal := hN
  have hXS : X 0 0 ≤ S := (intervalCell_antitone φ le_rfl (by omega)).trans
    (intervalCell_initial_left φ).le
  have hkS : X k k ≤ S := (intervalCell_antitone φ (by omega) (by omega)).trans
    (intervalCell_initial_left φ).le
  have hSS : ⁅S,S⁆ ≤ X (3*v-k) (k-1) := by
    have hh := image_mono φ.symm hd
    rw [image_commutator φ.symm T T le_rfl le_rfl,image_self φ.symm] at hh
    have he : image φ.symm (X (3*v-k+1) k) = X (3*v-k) (k-1) := by
      dsimp only [X,intervalDiagram]
      rw [image_symm_intervalCell]
      congr 1
      omega
    rwa [he] at hh
  have hD := (commutator_mono hXS hkS).trans hSS
  refine ⟨hD,?_⟩
  intro hbad
  have hDN : ⁅X 0 0,X k k⁆ ≤ N := by
    have hi := le_inf hD hbad
    rw [intervalDiagram_inf,max_eq_right (by omega),min_eq_left (by omega)] at hi
    exact hi
  have hMQ : M ≤ S ⊓ T := by
    have hh : X 1 (3*v-1) = S ⊓ T := by
      simp only [X,intervalDiagram,show 3*v-(3*v-1)=1 by omega,intervalCell_intersection]
    exact (intervalDiagram_mono φ (by omega) (by omega)).trans hh.le
  have hQM : ⁅S ⊓ T,M⁆ ≤ N := by
    rw [←hkernel]
    exact commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal
  have hQk : ⁅S ⊓ T,X k k⁆ ≤ N :=
    (commutator_mono le_rfl (intervalDiagram_mono φ (by omega) le_rfl)).trans hQM
  have hSgen : X 0 0 ⊔ (S ⊓ T) = S := by
    simpa only [X,intervalDiagram,Nat.sub_zero] using
      intervalCell_left_supplement φ (3*v) (by omega)
        (fun b _ hb => hgen 0 b (by omega))
  have hSk : ⁅S,X k k⁆ ≤ N := by
    rw [←hSgen]
    exact commutator_sup_le_of_relative_normal (⊤ : Subgroup G) _ _ _ N
      le_normalizer_of_normal le_top le_top hDN hQk
  have hMgen : X (3*v-k) (k-1) ⊔ X k k = M := by
    apply le_antisymm (sup_le (intervalDiagram_mono φ le_rfl (by omega))
      (intervalDiagram_mono φ (by omega) le_rfl))
    apply intervalDiagram_le_of_points φ (3*v) hgen (by omega) (by omega)
    intro j hj hjk
    by_cases he : j = k
    · subst j; exact le_sup_right
    · exact (intervalDiagram_mono φ hj (by omega)).trans le_sup_left
  have hSM : ⁅S,M⁆ ≤ N := by
    rw [commutator_comm,←hMgen]
    exact commutator_sup_le_of_relative_normal (⊤ : Subgroup G) _ _ _ N
      le_normalizer_of_normal le_top le_top (by rwa [commutator_comm])
      (by rwa [commutator_comm])
  have hh := le_commutatorPreimage (show S ≤ (⊤ : Subgroup G) from le_top) hSM
  rw [hkernel] at hh
  exact hne (hh.trans inf_le_right)

/-- Exact gap parameters shift the first escaping commutator to the
right boundary. Its left endpoint is precisely v. -/
theorem intervalDiagram_gap_terminal_escape (φ : S ≃* T) (v k : ℕ)
    (_hk : 2*v < k) (hkw : k < 3*v) (hparam : 5*v = 2*k)
    (hbound : ⁅intervalDiagram φ (3*v) 0 0,intervalDiagram φ (3*v) k k⁆ ≤
      intervalDiagram φ (3*v) (3*v-k) (k-1))
    (hescape : ¬ ⁅intervalDiagram φ (3*v) 0 0,intervalDiagram φ (3*v) k k⁆ ≤
      intervalDiagram φ (3*v) (3*v-k+1) (3*v)) :
    let X := intervalDiagram φ (3*v)
    ⁅X (3*v-k) (3*v-k),X (3*v) (3*v)⁆ ≤ X v (3*v-1) ∧
      ¬ ⁅X (3*v-k) (3*v-k),X (3*v) (3*v)⁆ ≤ X (v+1) (3*v) := by
  let X := intervalDiagram φ (3*v)
  have hh := intervalCell_commutator_shift φ (3*v-k) 0 k k 0 (3*v-k) 1 (by
    simpa only [X,intervalDiagram,Nat.sub_zero,Nat.zero_add,show k+(3*v-k)=3*v by omega,
      show 3*v-(k-1)=1+(3*v-k) by omega] using hbound)
  have hb : ⁅X (3*v-k) (3*v-k),X (3*v) (3*v)⁆ ≤ X v (3*v-1) := by
    simpa only [X,intervalDiagram,Nat.zero_add,show k+(3*v-k)=3*v by omega,
      show 3*v-k+(3*v-k)=v by omega,show 3*v-(3*v-k)=k by omega,
      Nat.sub_self,show 3*v-(3*v-1)=1 by omega] using hh
  refine ⟨hb,?_⟩
  intro hbad
  have hb' := intervalCell_commutator_shift_back φ (3*v-k) 0 k k 0 (3*v-k+1) 0 (by
    simpa only [X,intervalDiagram,Nat.zero_add,show k+(3*v-k)=3*v by omega,
      show 3*v-k+1+(3*v-k)=v+1 by omega,show 3*v-(3*v-k)=k by omega,
      Nat.sub_self] using hbad)
  apply hescape
  have hb'' : ⁅X 0 0,X k k⁆ ≤ X (3*v-k+1) k := by
    simpa only [X,intervalDiagram,Nat.sub_zero,Nat.zero_add,
      show k+(3*v-k)=3*v by omega] using hb'
  exact hb''.trans (intervalDiagram_mono φ le_rfl (show k ≤ 3*v by omega))

/-- A subgroup reaching the left endpoint v has a commutator with the
last point which covers the last core-center point modulo its predecessor. -/
theorem intervalDiagram_terminal_triple_cover (φ : S ≃* T) (v : ℕ) (hv : 0 < v)
    (hS : S ≤ normalizer (S ⊓ T : Set G))
    (hT : T ≤ normalizer (S ⊓ T : Set G))
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3*v → b < a+2*v →
      IsElementaryAbelian 2 (intervalDiagram φ (3*v) a b))
    (hz : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (htwice : ⁅intervalDiagram φ (3*v) v v,intervalDiagram φ (3*v) (3*v) (3*v)⁆ ≤
      intervalDiagram φ (3*v) (2*v) (2*v))
    (hcover : let X := intervalDiagram φ (3*v)
      PointCommutatorCovering (X v v) (X (v+1) (v+1))
        (X (3*v) (3*v)) (X (3*v-1) (3*v-1)) (X (2*v) (2*v)) (X (2*v-1) (2*v-1)))
    (D : Subgroup G) (hD : D ≤ intervalDiagram φ (3*v) v (3*v-1))
    (hescape : ¬ D ≤ intervalDiagram φ (3*v) (v+1) (3*v)) :
    let X := intervalDiagram φ (3*v)
    ⁅D,X (3*v) (3*v)⁆ ≤ X (2*v) (2*v) ∧
      ⁅D,X (3*v) (3*v)⁆ ⊔ (X (2*v) (2*v) ⊓ X (2*v-1) (2*v-1)) = X (2*v) (2*v) := by
  let X := intervalDiagram φ (3*v)
  let B := X (3*v) (3*v)
  let C := X (2*v) (2*v)
  let L := X (v+1) (3*v-1)
  let Z := ⁅D,B⁆
  have hXT : X 1 (3*v) = T := by
    simp only [X,intervalDiagram,Nat.sub_self,intervalCell_initial_right]
  have hCT : C ≤ centerIn T := by
    rw [hz]
    exact intervalDiagram_mono φ (by omega) le_rfl
  have hc : L ≤ centralizer (B : Set G) := intervalDiagram_centralizes_of_close φ v hgen hshort
    (by omega) le_rfl (by omega) le_rfl (by omega) (by omega)
  have hjoin : X v v ⊔ L = X v (3*v-1) :=
    intervalDiagram_head_sup_tail φ (3*v) hgen (by omega) (by omega)
  have hZT : Z ≤ C := by
    apply (commutator_mono hD le_rfl).trans
    change ⁅X v (3*v-1),B⁆ ≤ C
    rw [←hjoin]
    exact commutator_sup_le_of_relative_normal T _ _ _ C
      ((le_centralizer_iff.mpr (hCT.trans inf_le_right)).trans (centralizer_le_normalizer _))
      ((intervalDiagram_mono φ (by omega) (by omega)).trans hXT.le)
      ((intervalDiagram_mono φ (by omega) (by omega)).trans hXT.le)
      htwice ((commutator_eq_bot_iff_le_centralizer.mpr hc).le.trans bot_le)
  refine ⟨hZT,le_antisymm (sup_le hZT inf_le_left) ?_⟩
  obtain ⟨x,hx,hxn⟩ := SetLike.not_le_iff_exists.mp hescape
  have hn : X v v ≤ normalizer (L : Set G) :=
    (intervalDiagram_mono φ le_rfl (show v ≤ 3*v-1 by omega)).trans
      (intervalDiagram_normalizes_trim φ hS hT (3*v) (by omega) (by omega) (by omega)).2
  have hp : x ∈ (X v v : Set G) * (L : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hn,hjoin]
    exact hD hx
  obtain ⟨a,ha,b,hb,hab⟩ := hp
  have han : a ∉ X (v+1) (v+1) := by
    intro hh
    apply hxn
    rw [←hab]
    exact mul_mem (intervalDiagram_mono φ le_rfl (show v+1 ≤ 3*v by omega) hh)
      (intervalDiagram_mono φ le_rfl (show 3*v-1 ≤ 3*v by omega) hb)
  have hnorm : X v v ≤ normalizer (Z : Set G) :=
    ((intervalDiagram_mono φ (by omega) (by omega)).trans hXT.le).trans
      ((le_centralizer_iff.mpr ((hZT.trans hCT).trans inf_le_right)).trans
        (centralizer_le_normalizer _))
  have hpre : zpowers a ≤ commutatorPreimage (X v v) B Z := by
    apply zpowers_le.mpr
    apply (mem_commutatorPreimage_iff _ _ _ hnorm a).mpr
    refine ⟨ha,?_⟩
    intro y hy
    have hh := commutator_mem_commutator hx hy
    have hby : ⁅b,y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr ((hc hb) y hy).symm
    rw [←hab,commutatorElement_mul_left_eq_conj_mul,hby,mul_one,mul_inv_cancel,one_mul] at hh
    exact hh
  have hrow : ⁅zpowers a,B⁆ ≤ Z := (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hnorm)
  exact (hcover.2.1 a ha han).symm.le.trans (sup_le_sup_right hrow _)

end Theory.GroupTheory.SubgroupTransport
