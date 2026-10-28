module
public import Theory.GroupTheory.SubgroupTransport.GapEndpoints
public import Theory.GroupTheory.SubgroupTransport.ReflectedCentralizers

/-!
# The sharp gap bound from an escaping endpoint

Backward transport through the literal partial isomorphism preserves an
escaping subgroup and its commutator bound. If subgroups escaping the
opposite Sylow generate the ambient group with it, the first-gap endpoint
forces 5v ≤ 2k. The full normal middle cell is retained. Reflection of
short-gap centrality supplies the other orientation used by the source.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 5.3(d), p.50.
-/

public section
open Subgroup
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

theorem image_symm_intervalCell (φ : S ≃* T) (a b : ℕ) :
    image φ.symm (intervalCell φ (a+1) b) = intervalCell φ a (b+1) := by
  simpa only [intervalCell_symm] using image_intervalCell φ.symm b a

/-- Backward transport preserves a specified commutator bound and the
failure of containment in the next cell. All maps remain in their domains. -/
theorem intervalCell_backward_escape (φ : S ≃* T) (r a b c d e f : ℕ)
    (D : Subgroup G) (hD : D ≤ intervalCell φ (a+r) b)
    (hnot : ¬ D ≤ intervalCell φ (a+r+1) b)
    (hcomm : ⁅D,intervalCell φ (c+r) d⁆ ≤ intervalCell φ (e+r) f) :
    ∃ U : Subgroup G, U ≤ intervalCell φ a (b+r) ∧
      ¬ U ≤ intervalCell φ (a+1) (b+r) ∧
      ⁅U,intervalCell φ c (d+r)⁆ ≤ intervalCell φ e (f+r) := by
  induction r generalizing b d f D with
  | zero => simpa only [Nat.add_zero] using And.intro hD (And.intro hnot hcomm) |> fun h => ⟨D,h⟩
  | succ r ih =>
    have hDT : D ≤ T := hD.trans (by
      simpa only [Nat.add_succ] using intervalCell_le_range φ (a+r) b)
    have hD' := image_mono φ.symm hD
    simp only [Nat.add_succ,image_symm_intervalCell] at hD'
    have hn' : ¬ image φ.symm D ≤ intervalCell φ (a+r+1) (b+1) := by
      intro hh
      have hm := image_mono φ hh
      rw [image_inverse_image φ D,inf_eq_left.mpr hDT,image_intervalCell] at hm
      exact hnot (by simpa only [Nat.add_succ] using hm)
    have hc' := image_mono φ.symm hcomm
    rw [image_commutator φ.symm _ _ hDT (by
      simpa only [Nat.add_succ] using intervalCell_le_range φ (c+r) d)] at hc'
    simp only [Nat.add_succ,image_symm_intervalCell] at hc'
    obtain ⟨U,hU,hn,hc⟩ := ih (b+1) (d+1) (f+1) _ hD' hn' hc'
    exact ⟨U,by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hU,
      by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hn,
      by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hc⟩
/-- An escaping first-gap commutator forces the sharp bound. The generating
property is used only for the actual backward-translated subgroup. -/
theorem intervalDiagram_gap_bound_of_left_escape (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hz : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (hgap : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) j j⁆ ≤ centerIn T)
    (hnV : (⊤ : Subgroup G) ≤ normalizer (intervalDiagram φ (3*v) v (2*v) : Set G))
    (hgenerate : ∀ U : Subgroup G, U ≤ S → ¬ U ≤ T → U ⊔ T = ⊤)
    (hD : ⁅intervalDiagram φ (3*v) 1 1,intervalDiagram φ (3*v) (k+1) (k+1)⁆ ≤
      intervalDiagram φ (3*v) (k-2*v+1) (3*v))
    (hnot : ¬ ⁅intervalDiagram φ (3*v) 1 1,intervalDiagram φ (3*v) (k+1) (k+1)⁆ ≤
      intervalDiagram φ (3*v) (k-2*v+2) (3*v))
    (htriple : ⁅⁅intervalDiagram φ (3*v) 1 1,intervalDiagram φ (3*v) (k+1) (k+1)⁆,
      intervalDiagram φ (3*v) (k-2*v+1) (3*v)⁆ ≤
      intervalDiagram φ (3*v) (k-v+1) (k-v+1))
    (hescape : ¬ ⁅intervalDiagram φ (3*v) 1 1,intervalDiagram φ (3*v) (k+1) (k+1)⁆ ≤
      intervalDiagram φ (3*v) (v+1) (3*v)) : 5*v ≤ 2*k := by
  by_contra hbad
  let X := intervalDiagram φ (3*v)
  let D := ⁅X 1 1,X (k+1) (k+1)⁆
  let m := k-2*v+1
  have hmk : m+k ≤ 3*v := by dsimp [m]; omega
  have ht : ⁅D,intervalCell φ (k+m) (3*v-(k+m))⁆ ≤
      intervalCell φ (v+m) (3*v-(k-v+1)) := by
    have hb : X (k+m) (k+m) ≤ X m (3*v) := intervalDiagram_mono φ (by omega) (by omega)
    simpa only [D,X,m,intervalDiagram,show v+(k-2*v+1)=k-v+1 by omega] using
      (commutator_mono le_rfl hb).trans htriple
  obtain ⟨U,hU,hnU,hcU⟩ := intervalCell_backward_escape φ m 0 0 k
    (3*v-(k+m)) v (3*v-(k-v+1)) D
    (by simpa only [D,X,m,intervalDiagram,Nat.sub_self,Nat.zero_add] using hD)
    (by simpa only [D,X,m,intervalDiagram,Nat.sub_self,Nat.zero_add,
      show k-2*v+1+1=k-2*v+2 by omega] using hnot) ht
  simp only [Nat.zero_add] at hU hnU
  have hUS : U ≤ S := hU.trans (by
    have hh : intervalCell φ 0 m ≤ intervalCell φ 0 1 :=
      intervalCell_antitone φ le_rfl (by dsimp [m]; omega)
    exact hh.trans (intervalCell_initial_left φ).le)
  have hUT : ¬ U ≤ T := by
    intro hh
    apply hnU
    change U ≤ forwardChain φ 1 ⊓ forwardChain φ.symm m
    exact le_inf (by simpa only [forwardChain_one] using hh)
      (by simpa only [intervalCell_zero_left] using hU)
  have htop := hgenerate U hUS hUT
  have hcU' : ⁅U,X k k⁆ ≤ X v v := by
    simpa only [D,X,m,intervalDiagram,show 3*v-(k+m)+m=3*v-k by omega,
      show 3*v-(k-v+1)+m=3*v-v by dsimp [m]; omega] using hcU
  have hcT : ⁅T,X k k⁆ ≤ X v (2*v) := by
    have hh := intervalDiagram_gap_central φ v k hgen hgap
      (a := k) (b := k) (by omega) le_rfl (by omega) (by omega) (by omega)
    rw [hz] at hh
    exact hh.trans (intervalDiagram_mono φ (by omega) le_rfl)
  have hp : U ⊔ T ≤ commutatorPreimage ⊤ (X k k) (X v (2*v)) :=
    sup_le (le_commutatorPreimage le_top (hcU'.trans (intervalDiagram_mono φ le_rfl (by omega))))
      (le_commutatorPreimage le_top hcT)
  rw [htop] at hp
  have hall : ⁅(⊤ : Subgroup G),X k k⁆ ≤ X v (2*v) :=
    (commutator_mono hp le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hnV)
  have hh : ⁅X 0 0,X k k⁆ ≤ X v (2*v) := (commutator_mono le_top le_rfl).trans hall
  have hs (j : ℕ) (hj : j < 3*v) : X j j ≤ S :=
    (intervalCell_antitone φ (by omega) (by omega)).trans (intervalCell_initial_left φ).le
  have hm := image_mono φ hh
  rw [image_commutator φ _ _ (hs 0 (by omega)) (hs k hkw),
    image_intervalDiagram φ (show 0 < 3*v by omega),image_intervalDiagram φ hkw,
    image_intervalDiagram φ (show 2*v < 3*v by omega)] at hm
  exact hescape (hm.trans (intervalDiagram_mono φ le_rfl (by omega)))
/-- Short-gap centrality passes to the reversed diagram by shifting once
into the right Sylow before reversing the endpoints. -/
theorem intervalDiagram_gap_central_symm (φ : S ≃* T) (v k : ℕ) (hv : 0 < v)
    (hzS : centerIn S = intervalDiagram φ (3*v) v (2*v-1))
    (hzT : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (hgap : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) j j⁆ ≤ centerIn T) :
    ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
      ⁅intervalDiagram φ.symm (3*v) i i,intervalDiagram φ.symm (3*v) j j⁆ ≤ centerIn S := by
  intro i j hi hij hj hdist
  have hh := hgap (3*v-j+1) (3*v-i+1) (by omega) (by omega) (by omega) (by omega)
  rw [hzT] at hh
  have hs := intervalCell_commutator_shift_back φ 1 (3*v-j) (j-1)
    (3*v-i) (i-1) v v (by
      simpa only [intervalDiagram,show 3*v-(3*v-j+1)=j-1 by omega,
        show 3*v-(3*v-i+1)=i-1 by omega,show 3*v-2*v=v by omega] using hh)
  rw [intervalDiagram_symm φ (3*v) i i (by omega),
    intervalDiagram_symm φ (3*v) j j hj,commutator_comm,hzS]
  simpa only [intervalDiagram,show j-1+1=j by omega,show i-1+1=i by omega,
    show 3*v-(3*v-j)=j by omega,show 3*v-(3*v-i)=i by omega,
    show 3*v-(2*v-1)=v+1 by omega] using hs

/-- The bound in the left-escaping branch, with its endpoint and normal
centralizer premises discharged by the actual point diagram. -/
theorem intervalDiagram_gap_left_bound (φ : S ≃* T) (v k : ℕ)
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
    (hgap : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) j j⁆ ≤ centerIn T)
    (hkernel : S ⊓ centralizer (intervalDiagram φ (3*v) v (2*v) : Set G) ≤ S ⊓ T)
    (hnV : (⊤ : Subgroup G) ≤ normalizer (intervalDiagram φ (3*v) v (2*v) : Set G))
    (hgenerate : ∀ U : Subgroup G, U ≤ S → ¬ U ≤ T → U ⊔ T = ⊤)
    (hescape : ¬ ⁅intervalDiagram φ (3*v) 1 1,intervalDiagram φ (3*v) (k+1) (k+1)⁆ ≤
      intervalDiagram φ (3*v) (v+1) (3*v)) : 5*v ≤ 2*k := by
  let X := intervalDiagram φ (3*v)
  have hp := intervalDiagram_opposite_point_kernel φ v (by omega) hgen hshort hkernel
  have hc := intervalDiagram_right_centralizer_eq φ v hS hT hgen hshort
    (fun r _ hr => hp r hr) (j := k) (by omega) (by omega)
  have hn := (intervalDiagram_gap_normalizers φ v k hk hkw hgen hz hgap).1.2.2
  rw [hc] at hn
  have hXT : X 1 (3*v) = T := by
    simp only [X,intervalDiagram,Nat.sub_self,intervalCell_initial_right]
  have hA : X 1 1 ≤ T := (intervalDiagram_mono φ le_rfl (by omega)).trans hXT.le
  have hB : X (k+1) (k+1) ≤ X (k-2*v+1) (3*v) :=
    intervalDiagram_mono φ (by omega) (by omega)
  have hD := (commutator_mono le_rfl hB).trans
    (le_normalizer_iff_commutator_le_right.mp (hA.trans hn))
  have ht := intervalDiagram_gap_triple_bound φ v k hk hkw hgen hshort hz htwice hn
  have hl := intervalDiagram_gap_left_endpoint φ v k hk hkw hS hT hne
    hgen hshort hz htwice hcover _ ht hescape
  exact intervalDiagram_gap_bound_of_left_escape φ v k hk hkw hgen hz hgap hnV
    hgenerate hD hl ht hescape

/-- A left boundary in the reversed diagram becomes the right boundary
of the original first-gap commutator, after the permitted backward shift. -/
theorem intervalDiagram_reflected_gap_right_bound (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k+2 ≤ 3*v)
    (h : ⁅intervalDiagram φ.symm (3*v) 1 1,
      intervalDiagram φ.symm (3*v) (k+1) (k+1)⁆ ≤
        intervalDiagram φ.symm (3*v) (v+1) (3*v)) :
    ⁅intervalDiagram φ (3*v) 1 1,intervalDiagram φ (3*v) (k+1) (k+1)⁆ ≤
      intervalDiagram φ (3*v) 1 (k-v+1) := by
  let X := intervalDiagram φ (3*v)
  have hh : ⁅X (3*v-k-1) (3*v-k-1),X (3*v-1) (3*v-1)⁆ ≤ X 0 (2*v-1) := by
    rw [intervalDiagram_symm φ (3*v) 1 1 (by omega),
      intervalDiagram_symm φ (3*v) (k+1) (k+1) (by omega),
      intervalDiagram_symm φ (3*v) (v+1) (3*v) (by omega),commutator_comm] at h
    simpa only [Nat.sub_self,show 3*v-(v+1)=2*v-1 by omega,
      show 3*v-(k+1)=3*v-k-1 by omega] using h
  have hi : ⁅X (3*v-k-1) (3*v-k-1),X (3*v-1) (3*v-1)⁆ ≤ X (3*v-k-1) (3*v-1) :=
    (Subgroup.commutator_le_sup _ _).trans (sup_le
      (intervalDiagram_mono φ le_rfl (by omega)) (intervalDiagram_mono φ (by omega) le_rfl))
  have hb := le_inf hi hh
  rw [intervalDiagram_inf,max_eq_left (by omega),min_eq_right (by omega)] at hb
  have hs := intervalCell_commutator_shift_back φ (3*v-k-2) 1 (k+1) (k+1) 1 1 (v+1) (by
    simpa only [X,intervalDiagram,show 1+(3*v-k-2)=3*v-k-1 by omega,
      show k+1+(3*v-k-2)=3*v-1 by omega,
      show 3*v-(3*v-k-1)=k+1 by omega,show 3*v-(3*v-1)=1 by omega,
      show 3*v-(2*v-1)=v+1 by omega] using hb)
  simpa only [intervalDiagram,show k+1+(3*v-k-2)=3*v-1 by omega,
    show 1+(3*v-k-2)=3*v-(k+1) by omega,
    show v+1+(3*v-k-2)=3*v-(k-v+1) by omega] using hs

end Theory.GroupTheory.SubgroupTransport
