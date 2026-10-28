module
public import Theory.GroupTheory.SubgroupTransport.IntersectionNormality

/-!
# Centralizers of right intervals

Singleton generation and short-interval abelianness let us delete the
leftmost point of any right interval centralizing a given middle interval.
The point-kernel premise itself follows from the original centralizer of
the middle interval: all other middle points already commute, and literal
partial-isomorphism transport supplies the subsequent point kernels.

Source: Niles, *Pushing-up in finite groups* (1979), Lemma 5.2, printed p.49.
The proof retains the actual interval subgroups and allows central fixed
attachments; no quotient splitting or pointwise covering is required.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.SubgroupTransport
variable {G : Type*} [Group G] {S T : Subgroup G}

theorem intervalDiagram_head_sup_tail (φ : S ≃* T) (w : ℕ)
    (hgen : ∀ a b : ℕ, a + b < w →
      intervalCell φ a (b + 1) ⊔ intervalCell φ (a + 1) b = intervalCell φ a b)
    {i j : ℕ} (hij : i < j) (hjw : j ≤ w) :
    intervalDiagram φ w i i ⊔ intervalDiagram φ w (i + 1) j = intervalDiagram φ w i j := by
  apply le_antisymm
  · exact sup_le (intervalDiagram_mono φ le_rfl hij.le)
      (intervalDiagram_mono φ (Nat.le_succ i) le_rfl)
  · apply intervalDiagram_le_of_points φ w hgen hij.le hjw
    intro k hik hkj
    by_cases he : k = i
    · subst k
      exact le_sup_left
    · exact (intervalDiagram_mono φ (by omega) hkj).trans le_sup_right

theorem intervalDiagram_point_centralizes_of_close (φ : S ≃* T) (v i j : ℕ)
    (hshort : ∀ a b : ℕ, b ≤ 3 * v → b < a + 2 * v →
      IsElementaryAbelian 2 (intervalDiagram φ (3 * v) a b))
    (hiw : i ≤ 3 * v) (hjw : j ≤ 3 * v)
    (hij : i < j + 2 * v) (hji : j < i + 2 * v) :
    intervalDiagram φ (3 * v) i i ≤ centralizer (intervalDiagram φ (3 * v) j j : Set G) := by
  let C := intervalDiagram φ (3 * v) (min i j) (max i j)
  let _ : IsElementaryAbelian 2 C := hshort _ _ (by omega) (by omega)
  have hI : intervalDiagram φ (3 * v) i i ≤ C := intervalDiagram_mono φ (by omega) (by omega)
  have hJ : intervalDiagram φ (3 * v) j j ≤ C := intervalDiagram_mono φ (by omega) (by omega)
  exact (hI.trans C.le_centralizer).trans (centralizer_le hJ)

/-- Two intervals centralize one another if both cross-endpoint distances
are shorter than the elementary-abelian length bound. -/
theorem intervalDiagram_centralizes_of_close (φ : S ≃* T) (v : ℕ)
    (hgen : ∀ a b : ℕ, a + b < 3 * v →
      intervalCell φ a (b + 1) ⊔ intervalCell φ (a + 1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3 * v → b < a + 2 * v →
      IsElementaryAbelian 2 (intervalDiagram φ (3 * v) a b))
    {i j k l : ℕ} (hij : i ≤ j) (hkl : k ≤ l) (hjw : j ≤ 3 * v) (hlw : l ≤ 3 * v)
    (hjk : j < k + 2 * v) (hli : l < i + 2 * v) :
    intervalDiagram φ (3 * v) i j ≤ centralizer (intervalDiagram φ (3 * v) k l : Set G) := by
  apply intervalDiagram_le_of_points φ (3 * v) hgen hij hjw
  intro a hia haj
  apply le_centralizer_iff.mpr
  apply intervalDiagram_le_of_points φ (3 * v) hgen hkl hlw
  intro b hkb hbl
  exact intervalDiagram_point_centralizes_of_close φ v b a hshort (by omega) (by omega)
    (by omega) (by omega)

/-- The local point-centralizer kernel determines the full right-interval
centralizer. This is the deletion argument of Niles Lemma 5.2. -/
theorem intervalDiagram_right_centralizer_eq (φ : S ≃* T) (v : ℕ)
    (hS : S ≤ normalizer (S ⊓ T : Set G))
    (hT : T ≤ normalizer (S ⊓ T : Set G))
    (hgen : ∀ a b : ℕ, a + b < 3 * v →
      intervalCell φ a (b + 1) ⊔ intervalCell φ (a + 1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3 * v → b < a + 2 * v →
      IsElementaryAbelian 2 (intervalDiagram φ (3 * v) a b))
    (hpoint : ∀ r : ℕ, 1 ≤ r → r ≤ v →
      intervalDiagram φ (3 * v) r r ⊓
        centralizer (intervalDiagram φ (3 * v) (r + 2 * v) (r + 2 * v) : Set G) ≤
      intervalDiagram φ (3 * v) (r + 1) (r + 1))
    {j : ℕ} (hjlo : 2 * v + 1 ≤ j) (hjhi : j ≤ 3 * v) :
    T ⊓ centralizer (intervalDiagram φ (3 * v) (v + 1) j : Set G) =
      intervalDiagram φ (3 * v) (j - 2 * v + 1) (3 * v) := by
  let X := intervalDiagram φ (3 * v)
  have hXT : X 1 (3 * v) = T := by simp only [X, intervalDiagram, Nat.sub_self, intervalCell_initial_right]
  apply le_antisymm
  · intro x hx
    have hdelete : ∀ r : ℕ, 1 ≤ r → r ≤ j - 2 * v → x ∈ X r (3 * v) →
        x ∈ X (r + 1) (3 * v) := by
      intro r hr hrj hxr
      have hrv : r ≤ v := by omega
      have hhead : X r r ≤ normalizer (X (r + 1) (3 * v) : Set G) :=
        (intervalDiagram_mono φ le_rfl (show r ≤ 3 * v by omega)).trans
          (intervalDiagram_normalizes_trim φ hS hT (3 * v) (show r < 3 * v by omega)
            le_rfl (by omega)).2
      have hjoin : X r r ⊔ X (r + 1) (3 * v) = X r (3 * v) :=
        intervalDiagram_head_sup_tail φ (3 * v) hgen (by omega) le_rfl
      have hmul : x ∈ (X r r : Set G) * (X (r + 1) (3 * v) : Set G) := by
        rw [← coe_mul_of_left_le_normalizer_right _ _ hhead, hjoin]
        exact hxr
      obtain ⟨a, ha, b, hb, hab⟩ := hmul
      have hbC : b ∈ centralizer (X (r + 2 * v) (r + 2 * v) : Set G) :=
        intervalDiagram_centralizes_of_close φ v hgen hshort (show r + 1 ≤ 3 * v by omega)
          le_rfl le_rfl (show r + 2 * v ≤ 3 * v by omega) (by omega) (by omega) hb
      have hxC : x ∈ centralizer (X (r + 2 * v) (r + 2 * v) : Set G) :=
        centralizer_le (intervalDiagram_mono φ (show v + 1 ≤ r + 2 * v by omega)
          (show r + 2 * v ≤ j by omega)) hx.2
      have haC : a ∈ centralizer (X (r + 2 * v) (r + 2 * v) : Set G) := by
        have hc := mul_mem hxC (inv_mem hbC)
        rw [← hab, mul_inv_cancel_right] at hc
        exact hc
      have ha' : a ∈ X (r + 1) (3 * v) :=
        intervalDiagram_mono φ le_rfl (show r + 1 ≤ 3 * v by omega) (hpoint r hr hrv ⟨ha, haC⟩)
      exact hab ▸ mul_mem ha' hb
    have hstep : ∀ n : ℕ, n ≤ j - 2 * v → x ∈ X (n + 1) (3 * v) := by
      intro n
      induction n with
      | zero => intro _; exact hXT.symm ▸ hx.1
      | succ n ih =>
        intro hn
        exact hdelete (n + 1) (by omega) (by omega) (ih (by omega))
    exact hstep (j - 2 * v) le_rfl
  · refine le_inf ?_ ?_
    · exact (intervalDiagram_mono φ (show 1 ≤ j - 2 * v + 1 by omega) le_rfl).trans hXT.le
    · exact intervalDiagram_centralizes_of_close φ v hgen hshort (by omega) (by omega)
        le_rfl hjhi (by omega) (by omega)

private theorem image_centralizer_intersection (φ : S ≃* T) (A B : Subgroup G)
    (hBS : B ≤ S) :
    image φ (A ⊓ centralizer (B : Set G)) = image φ A ⊓ centralizer (image φ B : Set G) := by
  apply le_antisymm
  · rintro x ⟨a, ha, rfl⟩
    exact ⟨(mem_image_iff φ A a).mpr ha.1, (centralizes_iff φ B hBS a).mp ha.2⟩
  · rintro x ⟨⟨a, ha, rfl⟩, hc⟩
    exact ⟨a, ⟨ha, (centralizes_iff φ B hBS a).mpr hc⟩, rfl⟩

/-- Centralization with the opposite point detects the next point kernel,
provided the original Sylow centralizer of the middle interval is the
common intersection. The conclusion transports along the literal map. -/
theorem intervalDiagram_opposite_point_kernel (φ : S ≃* T) (v : ℕ) (hv : 0 < v)
    (hgen : ∀ a b : ℕ, a + b < 3 * v →
      intervalCell φ a (b + 1) ⊔ intervalCell φ (a + 1) b = intervalCell φ a b)
    (hshort : ∀ a b : ℕ, b ≤ 3 * v → b < a + 2 * v →
      IsElementaryAbelian 2 (intervalDiagram φ (3 * v) a b))
    (hkernel : S ⊓ centralizer (intervalDiagram φ (3 * v) v (2 * v) : Set G) ≤ S ⊓ T)
    (r : ℕ) (hr : r ≤ v) :
    intervalDiagram φ (3 * v) r r ⊓
      centralizer (intervalDiagram φ (3 * v) (r + 2 * v) (r + 2 * v) : Set G) ≤
      intervalDiagram φ (3 * v) (r + 1) (r + 1) := by
  let X := intervalDiagram φ (3 * v)
  induction r with
  | zero =>
    intro x hx
    have hxV : x ∈ centralizer (X v (2 * v) : Set G) := by
      have hcentral : X v (2 * v) ≤ centralizer (zpowers x : Set G) := by
        apply intervalDiagram_le_of_points φ (3 * v) hgen (by omega) (by omega)
        intro k hvk hk
        apply le_centralizer_iff.mpr
        apply zpowers_le.mpr
        by_cases he : k = 2 * v
        · subst k
          have hc := hx.2
          simp only [Nat.zero_add] at hc
          exact hc
        · exact intervalDiagram_point_centralizes_of_close φ v 0 k hshort (by omega)
            (by omega) (by omega) (by omega) hx.1
      exact le_centralizer_iff.mp hcentral (mem_zpowers x)
    have hxS : x ∈ S := by
      have hle : X 0 0 ≤ intervalCell φ 0 1 := intervalCell_antitone φ le_rfl (by omega)
      exact intervalCell_initial_left φ ▸ hle hx.1
    have hxT : x ∈ T := (hkernel ⟨hxS, hxV⟩).2
    have hxt : x ∈ X 0 0 ⊓ T := ⟨hx.1, hxT⟩
    have he : X 0 0 ⊓ T = intervalCell φ 1 (3 * v) := by
      change intervalCell φ 0 (3 * v - 0) ⊓ T = _
      conv_lhs => arg 2; rw [← intervalCell_initial_right φ]
      rw [Nat.sub_zero, intervalCell_inf,
        max_eq_right (show 0 ≤ 1 by omega), max_eq_left (Nat.zero_le _)]
    have hle : intervalCell φ 1 (3 * v) ≤ X 1 1 :=
      intervalCell_antitone φ le_rfl (by omega)
    exact hle (he ▸ hxt)
  | succ r ih =>
    have hm := image_mono φ (ih (by omega))
    have hB : X (r + 2 * v) (r + 2 * v) ≤ S := by
      have hle : X (r + 2 * v) (r + 2 * v) ≤ intervalCell φ 0 1 :=
        intervalCell_antitone φ (by omega) (by omega)
      exact hle.trans (intervalCell_initial_left φ).le
    rw [image_centralizer_intersection φ _ _ hB] at hm
    change image φ (X r r) ⊓ centralizer (image φ (X (r + 2 * v) (r + 2 * v)) : Set G) ≤
      image φ (X (r + 1) (r + 1)) at hm
    dsimp only [X] at hm
    rw [image_intervalDiagram φ (show r < 3 * v by omega),
      image_intervalDiagram φ (show r + 2 * v < 3 * v by omega),
      image_intervalDiagram φ (show r + 1 < 3 * v by omega)] at hm
    simpa only [Nat.succ_eq_add_one, show r + 2 * v + 1 = r + 1 + 2 * v by omega] using hm

end Theory.GroupTheory.SubgroupTransport
