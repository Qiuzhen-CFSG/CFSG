module
public import Theory.GroupTheory.SubgroupTransport.SharpGap
public import Theory.ThreeSubgroups
public import Theory.ElementaryAbelian.CommutingFamily
/-!
# Normal layers at the first noncentral gap

The smaller middle interval is central modulo the full core center; the
larger contains both Sylow derived subgroups. Generation by the two Sylows
makes both intervals ambient normal. Point generation proves that their
abelian factors are elementary, and the existing depth-2v indices give
order q² for the middle factor. If the ambient group is perfect modulo
the Sylow intersection, trivial action on that factor contradicts the
first-gap endpoint escape.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 5.5,
pp.51--52. Interval endpoints are the printed endpoints plus one.
The full core and Sylow centers are retained throughout.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

/-- Short-gap bounds extend to any two intervals of the right member. -/
theorem intervalDiagram_cross_gap_central (φ : S ≃* T) (v k : ℕ)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hgap : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) j j⁆ ≤ centerIn T)
    {a b c d : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3*v)
    (hc : 1 ≤ c) (hcd : c ≤ d) (hd : d ≤ 3*v)
    (hleft : b < c+k) (hright : d < a+k) :
    ⁅intervalDiagram φ (3*v) a b,intervalDiagram φ (3*v) c d⁆ ≤ centerIn T := by
  have hT : intervalDiagram φ (3*v) 1 (3*v) = T := by
    simp only [intervalDiagram,Nat.sub_self,intervalCell_initial_right]
  have hn : T ≤ normalizer (centerIn T : Set G) :=
    (le_centralizer_iff.mpr (show centerIn T ≤ centralizer (T : Set G) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  apply intervalDiagram_cross_commutator_le φ (3*v) hgen hab hcd hb hd (centerIn T)
    ((intervalDiagram_mono φ ha hb).trans (hT.le.trans hn))
    ((intervalDiagram_mono φ hc hd).trans (hT.le.trans hn))
  intro i j hi hib hj hjd
  rcases le_total i j with hij | hji
  · exact hgap i j (by omega) hij (by omega) (by omega)
  · rw [commutator_comm]
    exact hgap j i (by omega) hji (by omega) (by omega)

/-- The smaller gap interval is central modulo the full core center.
The larger contains both derived subgroups and is normal in the generated group. -/
theorem intervalDiagram_gap_layers (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v) (hgenST : S ⊔ T = ⊤)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hzS : centerIn S = intervalDiagram φ (3*v) v (2*v-1))
    (hzT : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (hgap : ∀ i j : ℕ, 1 ≤ i → i ≤ j → j ≤ 3*v → j < i+k →
      ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) j j⁆ ≤ centerIn T)
    (hVn : (intervalDiagram φ (3*v) v (2*v)).Normal)
    (hderived : ⁅T,T⁆ ≤ intervalDiagram φ (3*v) (3*v-k+1) k) :
    let X := intervalDiagram φ (3*v)
    let N := X (3*v-k+1) (k-1)
    let M := X (3*v-k) k
    X v (2*v) ≤ N ∧ N ≤ M ∧ M ≤ S ⊓ T ∧
      N.Normal ∧ M.Normal ∧
      ⁅(⊤ : Subgroup G),N⁆ ≤ X v (2*v) ∧
      ⁅(⊤ : Subgroup G),S ⊓ T⁆ ≤ M ∧
      ⁅S ⊓ T,M⁆ ≤ centerIn T := by
  let X := intervalDiagram φ (3*v)
  let V := X v (2*v)
  let N := X (3*v-k+1) (k-1)
  let M := X (3*v-k) k
  let _ : V.Normal := hVn
  have hS : X 0 (3*v-1) = S := by
    simp only [X,intervalDiagram,show 3*v-(3*v-1)=1 by omega,
      intervalCell_initial_left]
  have hT : X 1 (3*v) = T := by
    simp only [X,intervalDiagram,Nat.sub_self,intervalCell_initial_right]
  have hQ : X 1 (3*v-1) = S ⊓ T := by
    simp only [X,intervalDiagram,show 3*v-(3*v-1)=1 by omega,intervalCell_intersection]
  have hVN : V ≤ N := intervalDiagram_mono φ (by omega) (by omega)
  have hNM : N ≤ M := intervalDiagram_mono φ (by omega) (by omega)
  have hMQ : M ≤ S ⊓ T := (intervalDiagram_mono φ (by omega) (by omega)).trans hQ.le
  have hgenR : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ.symm a (b+1) ⊔ intervalCell φ.symm (a+1) b = intervalCell φ.symm a b := by
    intro a b hab
    simpa only [intervalCell_symm,sup_comm] using hgen b a (by omega)
  have hgapR := intervalDiagram_gap_central_symm φ v k (by omega) hzS hzT hgap
  have hNR : intervalDiagram φ.symm (3*v) (3*v-k+1) (k-1) = N := by
    rw [intervalDiagram_symm φ (3*v) (3*v-k+1) (k-1) (by omega)]
    simp only [N,X,show 3*v-(k-1)=3*v-k+1 by omega,
      show 3*v-(3*v-k+1)=k-1 by omega]
  have hTN : ⁅T,N⁆ ≤ centerIn T := intervalDiagram_gap_central φ v k hgen hgap
    (by omega) (by omega) (by omega) (by omega) (by omega)
  have hSN : ⁅S,N⁆ ≤ centerIn S := by
    rw [←hNR]
    exact intervalDiagram_gap_central φ.symm v k hgenR hgapR
      (by omega) (by omega) (by omega) (by omega) (by omega)
  have hNV : ⁅(⊤ : Subgroup G),N⁆ ≤ V := by
    have hpre : S ⊔ T ≤ commutatorPreimage ⊤ N V := sup_le
      (le_commutatorPreimage le_top (hSN.trans (hzS ▸ intervalDiagram_mono φ le_rfl (by omega))))
      (le_commutatorPreimage le_top (hTN.trans (hzT ▸ intervalDiagram_mono φ (by omega) le_rfl)))
    rw [hgenST] at hpre
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)
  have hnN : N.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp
    (le_normalizer_iff_commutator_le_right.mpr (hNV.trans hVN)))
  have hSS : ⁅S,S⁆ ≤ M := by
    have hh := image_mono φ.symm hderived
    rw [image_commutator φ.symm T T le_rfl le_rfl,image_self φ.symm] at hh
    have he : image φ.symm (X (3*v-k+1) k) = X (3*v-k) (k-1) := by
      dsimp only [X,intervalDiagram]
      rw [image_symm_intervalCell]
      congr 1
      omega
    rw [he] at hh
    exact hh.trans (intervalDiagram_mono φ le_rfl (by omega))
  have hTT : ⁅T,T⁆ ≤ M := hderived.trans (intervalDiagram_mono φ (by omega) le_rfl)
  have hnM : M.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [←hgenST]
    exact sup_le
      (le_normalizer_iff_commutator_le_right.mpr ((commutator_mono le_rfl (hMQ.trans inf_le_left)).trans hSS))
      (le_normalizer_iff_commutator_le_right.mpr ((commutator_mono le_rfl (hMQ.trans inf_le_right)).trans hTT))
  let _ := hnM
  have hQM : ⁅(⊤ : Subgroup G),S ⊓ T⁆ ≤ M := by
    have hpre : S ⊔ T ≤ commutatorPreimage ⊤ (S ⊓ T) M := sup_le
      (le_commutatorPreimage le_top ((commutator_mono le_rfl inf_le_left).trans hSS))
      (le_commutatorPreimage le_top ((commutator_mono le_rfl inf_le_right).trans hTT))
    rw [hgenST] at hpre
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)
  refine ⟨hVN,hNM,hMQ,hnN,hnM,hNV,hQM,?_⟩
  rw [←hQ]
  exact intervalDiagram_cross_gap_central φ v k hgen hgap
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- Every abelian image of a reconstructed interval generated by elementary
points is elementary abelian. This applies to the actual normal factors. -/
theorem intervalDiagram_elementary_image {G' : Type*} [Group G']
    (φ : S ≃* T) (v : ℕ) (hv : 0 < v)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3*v → b < a+2*v →
      IsElementaryAbelian 2 (intervalDiagram φ (3*v) a b))
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 3*v) (f : G →* G')
    (hcomm : ⁅intervalDiagram φ (3*v) i j,intervalDiagram φ (3*v) i j⁆ ≤ f.ker) :
    IsElementaryAbelian 2 ((intervalDiagram φ (3*v) i j).map f) := by
  let X := intervalDiagram φ (3*v)
  have hA : (X i j).map f ≤ centralizer ((X i j).map f : Set G') := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [←map_commutator,Subgroup.map_eq_bot_iff]
    exact hcomm
  have hle (a : Set.Icc i j) : (X a a).map f ≤ (X i j).map f :=
    map_mono (intervalDiagram_mono φ a.property.1 a.property.2)
  let (a : Set.Icc i j) : IsElementaryAbelian 2 (X a a) := hshort a a (a.property.2.trans hj) (by omega)
  let (a : Set.Icc i j) : IsElementaryAbelian 2 ((X a a).map f) := IsElementaryAbelian.map f
  have he : X i j = ⨆ a : Set.Icc i j, X a a := by
    rw [iSup_subtype]
    exact intervalDiagram_eq_iSup_points φ (3*v) hgen hij hj
  change IsElementaryAbelian 2 ((X i j).map f)
  rw [he,Subgroup.map_iSup]
  exact IsElementaryAbelian.iSup_of_le_centralizer _ (fun a b =>
    (hle a).trans (hA.trans (centralizer_le (hle b))))

/-- The two endpoint cells of the second normal section have index q each.
The indices needed here are all in the already reconstructed depth-2v range. -/
theorem intervalDiagram_gap_layer_index [Finite G] (φ : S ≃* T) (v k q : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v) (hsharp : 5*v ≤ 2*k)
    (hindex : ∀ a : ℕ, 1 ≤ a → a ≤ 2*v → rectangleStepIndex φ a = q) :
    (intervalDiagram φ (3*v) (3*v-k+1) (k-1)).relIndex
      (intervalDiagram φ (3*v) (3*v-k) k) = q^2 := by
  let X := intervalDiagram φ (3*v)
  have hleft : (X (3*v-k+1) (k-1)).relIndex (X (3*v-k+1) k) = q := by
    dsimp only [X,intervalDiagram]
    rw [intervalCell_relIndex φ _ _ _ _ le_rfl (by omega) (by omega)]
    exact hindex _ (by omega) (by omega)
  have hright : (X (3*v-k+1) k).relIndex (X (3*v-k) k) = q := by
    dsimp only [X,intervalDiagram]
    rw [intervalCell_relIndex φ _ _ _ _ (by omega) le_rfl (by omega)]
    exact hindex _ (by omega) (by omega)
  have he := relIndex_mul_relIndex (X (3*v-k+1) (k-1)) (X (3*v-k+1) k)
    (X (3*v-k) k) (intervalDiagram_mono φ le_rfl (by omega))
    (intervalDiagram_mono φ (by omega) le_rfl)
  rw [hleft,hright] at he
  exact he.symm.trans (pow_two q).symm

/-- All three factors used in the second-gap filtration are elementary.
They are the literal images under the three ambient quotient maps. -/
theorem intervalDiagram_gap_elementary_sections (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v)
    (hgen : ∀ a b : ℕ, a+b < 3*v →
      intervalCell φ a (b+1) ⊔ intervalCell φ (a+1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3*v → b < a+2*v →
      IsElementaryAbelian 2 (intervalDiagram φ (3*v) a b))
    (V N M : Subgroup G) [V.Normal] [N.Normal] [M.Normal]
    (hN : N = intervalDiagram φ (3*v) (3*v-k+1) (k-1))
    (hM : M = intervalDiagram φ (3*v) (3*v-k) k)
    (hVN : V ≤ N) (hMQ : M ≤ S ⊓ T)
    (hNV : ⁅(⊤ : Subgroup G),N⁆ ≤ V)
    (hQM : ⁅(⊤ : Subgroup G),S ⊓ T⁆ ≤ M)
    (hMQV : ⁅S ⊓ T,M⁆ ≤ V) :
    IsElementaryAbelian 2 ((S ⊓ T).map (QuotientGroup.mk' M)) ∧
      IsElementaryAbelian 2 (N.map (QuotientGroup.mk' V)) ∧
      IsElementaryAbelian 2 (M.map (QuotientGroup.mk' N)) := by
  have hQ : intervalDiagram φ (3*v) 1 (3*v-1) = S ⊓ T := by
    simp only [intervalDiagram,show 3*v-(3*v-1)=1 by omega,intervalCell_intersection]
  have helem {U : Subgroup G} (i j : ℕ) (hij : i ≤ j) (hj : j ≤ 3*v)
      (he : U = intervalDiagram φ (3*v) i j) (L : Subgroup G) [L.Normal]
      (hc : ⁅U,U⁆ ≤ L) : IsElementaryAbelian 2 (U.map (QuotientGroup.mk' L)) := by
    have hh : ⁅U,U⁆ ≤ (QuotientGroup.mk' L).ker := by rwa [QuotientGroup.ker_mk']
    rw [he] at hh ⊢
    exact intervalDiagram_elementary_image φ v (by omega) hgen hshort hij hj _ hh
  refine ⟨helem 1 (3*v-1) (by omega) (by omega) hQ.symm M
    ((commutator_mono le_top le_rfl).trans hQM),
    helem (3*v-k+1) (k-1) (by omega) (by omega) hN V
      ((commutator_mono le_top le_rfl).trans hNV),
    helem (3*v-k) k (by omega) (by omega) hM N
      (((commutator_mono hMQ le_rfl).trans hMQV).trans hVN)⟩

/-- In the class-two branch the whole group centralizes the core modulo
its full center, before any representation recognition. -/
theorem intervalDiagram_class_two_core (φ : S ≃* T) (v : ℕ) (hv : 0 < v)
    (hgenST : S ⊔ T = ⊤)
    (hzS : centerIn S = intervalDiagram φ (3*v) v (2*v-1))
    (hzT : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (hVn : (intervalDiagram φ (3*v) v (2*v)).Normal)
    (hderived : ⁅T,T⁆ ≤ centerIn T) :
    ⁅(⊤ : Subgroup G),S ⊓ T⁆ ≤ intervalDiagram φ (3*v) v (2*v) := by
  let V := intervalDiagram φ (3*v) v (2*v)
  let _ : V.Normal := hVn
  have hSS : ⁅S,S⁆ ≤ centerIn S := by
    have hh := image_mono φ.symm hderived
    rw [image_commutator φ.symm T T le_rfl le_rfl,image_self φ.symm,hzT] at hh
    have he : image φ.symm (intervalDiagram φ (3*v) (v+1) (2*v)) =
        intervalDiagram φ (3*v) v (2*v-1) := by
      unfold intervalDiagram
      rw [image_symm_intervalCell]
      congr 1
      omega
    rwa [he,←hzS] at hh
  have hpre : S ⊔ T ≤ commutatorPreimage ⊤ (S ⊓ T) V := sup_le
    (le_commutatorPreimage le_top (((commutator_mono le_rfl inf_le_left).trans hSS).trans
      (hzS ▸ intervalDiagram_mono φ le_rfl (by omega))))
    (le_commutatorPreimage le_top (((commutator_mono le_rfl inf_le_right).trans hderived).trans
      (hzT ▸ intervalDiagram_mono φ (by omega) le_rfl)))
  rw [hgenST] at hpre
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)

/-- The second normal factor has a nontrivial ambient action. If its action
were trivial, perfectness modulo the intersection would centralize the larger
layer modulo the core center. Both first-gap endpoints would then be central. -/
theorem intervalDiagram_gap_action_nontrivial (φ : S ≃* T) (v k : ℕ)
    (hk : 2*v < k) (hkw : k < 3*v)
    (hperfect : ⁅(⊤ : Subgroup G),(⊤ : Subgroup G)⁆ ⊔ (S ⊓ T) = ⊤)
    (hzT : centerIn T = intervalDiagram φ (3*v) (v+1) (2*v))
    (hex : ∃ i : ℕ, 1 ≤ i ∧ i+k ≤ 3*v ∧
      ¬ ⁅intervalDiagram φ (3*v) i i,intervalDiagram φ (3*v) (i+k) (i+k)⁆ ≤ centerIn T)
    (hVn : (intervalDiagram φ (3*v) v (2*v)).Normal)
    (hNV : ⁅(⊤ : Subgroup G),intervalDiagram φ (3*v) (3*v-k+1) (k-1)⁆ ≤
      intervalDiagram φ (3*v) v (2*v))
    (hQM : ⁅S ⊓ T,intervalDiagram φ (3*v) (3*v-k) k⁆ ≤
      intervalDiagram φ (3*v) v (2*v)) :
    ¬ ⁅(⊤ : Subgroup G),intervalDiagram φ (3*v) (3*v-k) k⁆ ≤
      intervalDiagram φ (3*v) (3*v-k+1) (k-1) := by
  let X := intervalDiagram φ (3*v)
  let V := X v (2*v)
  let N := X (3*v-k+1) (k-1)
  let M := X (3*v-k) k
  let _ : V.Normal := hVn
  intro htrivial
  have htriple : ⁅⁅(⊤ : Subgroup G),M⁆,⊤⁆ ≤ V := by
    rw [commutator_comm _ (⊤ : Subgroup G)]
    exact (commutator_mono le_rfl htrivial).trans hNV
  have hder : ⁅⁅(⊤ : Subgroup G),(⊤ : Subgroup G)⁆,M⁆ ≤ V := by
    apply commutator_commutator_le_of_rotate_of_le_normalizer
      (show (⊤ : Subgroup G) ≤ normalizer (V : Set G) from le_normalizer_of_normal)
      (show (⊤ : Subgroup G) ≤ normalizer (V : Set G) from le_normalizer_of_normal)
      (show M ≤ normalizer (V : Set G) from le_normalizer_of_normal)
    · exact htriple
    · rwa [commutator_comm M ⊤]
  have hpre : ⁅(⊤ : Subgroup G),(⊤ : Subgroup G)⁆ ⊔ (S ⊓ T) ≤ commutatorPreimage ⊤ M V :=
    sup_le (le_commutatorPreimage le_top hder) (le_commutatorPreimage le_top hQM)
  rw [hperfect] at hpre
  have hall : ⁅(⊤ : Subgroup G),M⁆ ≤ V := (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ le_normalizer_of_normal)
  have hs (i : ℕ) (hi : i < 3*v) : X i i ≤ S :=
    (intervalCell_antitone φ (by omega) (by omega)).trans (intervalCell_initial_left φ).le
  have hleft : ⁅X 1 1,X (k+1) (k+1)⁆ ≤ X (v+1) (3*v) := by
    have hh : ⁅X 0 0,X k k⁆ ≤ V :=
      (commutator_mono le_top (intervalDiagram_mono φ (by omega) le_rfl)).trans hall
    have hm := image_mono φ hh
    rw [image_commutator φ _ _ (hs 0 (by omega)) (hs k hkw),
      image_intervalDiagram φ (show 0 < 3*v by omega),image_intervalDiagram φ hkw,
      image_intervalDiagram φ (show 2*v < 3*v by omega)] at hm
    exact hm.trans (intervalDiagram_mono φ le_rfl (by omega))
  have hright : ⁅X 1 1,X (k+1) (k+1)⁆ ≤ X 1 (k-v+1) := by
    have hh : ⁅X (3*v-k) (3*v-k),X (3*v) (3*v)⁆ ≤ V := by
      rw [commutator_comm]
      exact (commutator_mono le_top (intervalDiagram_mono φ le_rfl (by omega))).trans hall
    have hb := intervalCell_commutator_shift_back φ (3*v-k-1) 1 k (k+1) 0 (k-2*v+1) v (by
      simpa only [X,V,intervalDiagram,show 1+(3*v-k-1)=3*v-k by omega,
        show k+1+(3*v-k-1)=3*v by omega,show k-2*v+1+(3*v-k-1)=v by omega,
        show 3*v-(3*v-k)=k by omega,show 3*v-2*v=v by omega,Nat.sub_self] using hh)
    have hb' : ⁅X 1 1,X (k+1) (k+1)⁆ ≤ X (k-2*v+1) (k-v+1) := by
      simpa only [X,intervalDiagram,show k+(3*v-(k+1))=3*v-1 by omega,
        show 3*v-k-1=3*v-(k+1) by omega,
        show v+(3*v-(k+1))=3*v-(k-v+1) by omega,Nat.zero_add] using hb
    exact hb'.trans (intervalDiagram_mono φ (by omega) le_rfl)
  exact (intervalDiagram_gap_endpoint_escape φ v k hk hkw hzT hex).elim
    (fun hh => hh hleft) (fun hh => hh hright)

end Theory.GroupTheory.SubgroupTransport
