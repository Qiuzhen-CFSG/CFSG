module

public import Theory.GroupAction.CubicTree.TrackFixer
public import Theory.GroupAction.CubicTree.ArcRegularity

/-!
# Finite arcs in translation tracks

An integer track interval is a nonbacktracking based walk. Its pointwise
fixer is exactly the interval subgroup already used by the finite track
filtration. One-step extensions intersect with the new vertex stabilizer,
and translating the track conjugates the interval subgroup. Finite local
stabilizers therefore provide a last even interval whose fixer is larger
than the whole track fixer.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the maximal
subarc in (5.1), printed p.394, and the interval counts in Section 6.
-/

@[expose] public section
open Subgroup SimpleGraph
namespace Theory.GroupAction.CubicTree.Track
variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
variable (t : Track Γ G)

def arc (a : ℤ) (n : ℕ) : BasedWalk Γ n (t.vertex a) :=
  sequenceWalk t.vertex t.adjacent a n

@[simp] theorem arc_endpoint (a : ℤ) (n : ℕ) :
    (t.arc a n).endpoint = t.vertex (a+n) :=
  sequenceWalk_endpoint _ _ _ _

theorem arc_nonbacktracking (a : ℤ) (n : ℕ) : (t.arc a n).Nonbacktracking :=
  sequenceWalk_nonbacktracking _ _ (fun i he => by have := t.injective he; omega) a n

@[simp] theorem arc_penultimate (a : ℤ) (n : ℕ) :
    (t.arc a (n+1)).penultimate = t.vertex (a+n) := by
  induction n generalizing a with
  | zero => simp only [Nat.cast_zero, add_zero]; rfl
  | succ n ih =>
    change (t.arc (a+1) (n+1)).penultimate = _
    rw [ih]
    congr 1
    omega

theorem arc_forward (a : ℤ) (n : ℕ) :
    Forward (t.arc a n) (t.vertex (a+n+1)) := by
  cases n with
  | zero =>
    change Γ.Adj (t.vertex a) (t.vertex (a+(0:ℕ)+1))
    simpa only [Nat.cast_zero, add_zero] using t.adjacent a
  | succ n =>
    rw [Forward, t.arc_endpoint, t.arc_penultimate]
    exact ⟨t.adjacent _, fun he => by have := t.injective he; omega⟩

theorem arc_backward (a : ℤ) (n : ℕ) :
    Backward (t.arc a n) (t.vertex (a-1)) := by
  have hadj : Γ.Adj (t.vertex a) (t.vertex (a-1)) := by
    simpa only [sub_add_cancel] using (t.adjacent (a-1)).symm
  cases n with
  | zero => exact hadj
  | succ n => exact ⟨hadj, fun he => by have := t.injective he; omega⟩

theorem fixes_arc_iff (a : ℤ) (n : ℕ) (g : G) :
    (∀ v ∈ (t.arc a n).vertices, g • v = v) ↔ g ∈ t.segmentFixer a n := by
  induction n generalizing a with
  | zero =>
    simp only [BasedWalk.vertices, List.mem_singleton,
      forall_eq, t.segmentFixer_zero, MulAction.mem_stabilizer_iff]
  | succ n ih =>
    change (∀ v ∈ t.vertex a :: (t.arc (a+1) n).vertices, g • v = v) ↔ _
    rw [List.forall_mem_cons, ih, t.mem_segmentFixer, t.mem_segmentFixer]
    constructor
    · rintro ⟨ha, hg⟩ i hai hin
      by_cases hi : i = a
      · simpa only [hi] using ha
      · exact hg i (by omega) (by omega)
    · intro hg
      exact ⟨hg a le_rfl (by omega), fun i hai hin => hg i (by omega) (by omega)⟩

theorem segmentFixer_succ (a : ℤ) (n : ℕ) :
    t.segmentFixer a (n+1) =
      t.segmentFixer a n ⊓ MulAction.stabilizer G (t.vertex (a+n+1)) := by
  ext g
  simp only [mem_inf, mem_segmentFixer, MulAction.mem_stabilizer_iff]
  constructor
  · intro hg
    exact ⟨fun i hai hin => hg i hai (by omega), hg _ (by omega) (by omega)⟩
  · rintro ⟨hg, he⟩ i hai hin
    by_cases hi : i ≤ a+n
    · exact hg i hai hi
    · have : i = a+n+1 := by omega
      simpa only [this] using he

theorem segmentFixer_prepend (a : ℤ) (n : ℕ) :
    t.segmentFixer (a-1) (n+1) =
      t.segmentFixer a n ⊓ MulAction.stabilizer G (t.vertex (a-1)) := by
  ext g
  simp only [mem_inf, mem_segmentFixer, MulAction.mem_stabilizer_iff]
  constructor
  · intro hg
    exact ⟨fun i hai hin => hg i (by omega) (by omega), hg _ le_rfl (by omega)⟩
  · rintro ⟨hg, he⟩ i hai hin
    by_cases hi : a ≤ i
    · exact hg i hi (by omega)
    · have : i = a-1 := by omega
      simpa only [this] using he

theorem segmentFixer_translate (a : ℤ) (n : ℕ) :
    (t.segmentFixer a n).map (MulAut.conj t.translation).toMonoidHom =
      t.segmentFixer (a+2) n := by
  ext g
  constructor
  · rintro ⟨g, hg, rfl⟩
    apply t.mem_segmentFixer.mpr
    intro i hai hin
    change (t.translation * g * t.translation⁻¹) • t.vertex i = t.vertex i
    rw [mul_smul, mul_smul, t.inverse_translate,
      t.mem_segmentFixer.mp hg (i-2) (by omega) (by omega), t.translate]
    congr 1
    omega
  · intro hg
    refine ⟨t.translation⁻¹*g*t.translation, ?_, ?_⟩
    · apply t.mem_segmentFixer.mpr
      intro i hai hin
      rw [mul_smul, mul_smul, t.translate,
        t.mem_segmentFixer.mp hg (i+2) (by omega) (by omega), t.inverse_translate]
      congr 1
      omega
    · change t.translation * (t.translation⁻¹*g*t.translation) * t.translation⁻¹ = g
      simp only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left]

theorem segmentFixer_eq_fixer_of_le {a : ℤ} {m n : ℕ} (hmn : m ≤ n)
    (hm : t.segmentFixer a m = t.fixer) : t.segmentFixer a n = t.fixer :=
  le_antisymm (hm ▸ t.segmentFixer_antitone a hmn) (t.fixer_le_segmentFixer a n)

theorem exists_last_even_segment
    (hfin : ∀ i, Finite (MulAction.stabilizer G (t.vertex i))) (a : ℤ)
    (hne : t.segmentFixer a 0 ≠ t.fixer) :
    ∃ m : ℕ, t.segmentFixer a (2*m) ≠ t.fixer ∧
      ∀ k, m < k → t.segmentFixer a (2*k) = t.fixer := by
  classical
  obtain ⟨N, hN⟩ := t.segmentFixer_stabilizes hfin a
  have hex : ∃ n : ℕ, t.segmentFixer a (2*n) = t.fixer := ⟨N, hN _ (by omega)⟩
  have hpos : 0 < Nat.find hex := by
    by_contra hn
    have he : Nat.find hex = 0 := by omega
    exact hne (by simpa only [he, mul_zero] using Nat.find_spec hex)
  refine ⟨Nat.find hex - 1, Nat.find_min hex (by omega), ?_⟩
  intro k hk
  exact t.segmentFixer_eq_fixer_of_le (by omega) (Nat.find_spec hex)

end Theory.GroupAction.CubicTree.Track
