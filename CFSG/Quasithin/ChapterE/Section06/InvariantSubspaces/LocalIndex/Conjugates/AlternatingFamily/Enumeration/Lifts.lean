module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration.Counting
public import Theory.ElementaryAbelian.UniqueLift
public import Stellmacher.MaxElementaryOffenderEquality

/-!
# The four maximum elementary lifts of the commuting-transposition actor

Let an action on five letters have elementary kernel `V` and image generated
by the two disjoint transpositions. Given the fixed-centralizer profile and an
elementary full-image subgroup `W` of order `|V|`, the maximum elementary
family consists of `V`, `W`, and one lift of each transposition line.

Choose each transposition lift `w` in `W` and form `C_V(w) ⟨w⟩`. Its order
is `|V|` by the fixed profile and kernel–image counting. For uniqueness,
maximum elementary subgroups contain their fixed subgroup in `V`. A generator
of a cyclic image detects its entire fixed subgroup; the full actor is detected
by a lift of the double transposition. The elementary-kernel uniqueness lemma
then applies directly, without a self-centralizing-kernel assumption. The
counting module excludes the remaining, diagonal image.

This is a conditional finite-group result. Constructing `FixedProfile` and
proving the order of the source's opposite subgroup belong to the ambient
assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.21,
printed pp.82–83, and the proof of C.5.6, printed pp.157–158.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
variable {T : Type*} [Group T] [Finite T]

omit [Finite T] in
private theorem fixed_eq_singleton_of_line (σ : T →* Perm) (V B : Subgroup T)
    [IsElementaryAbelian 2 V] (hk : σ.ker = V) (i : Fin 2)
    (hB : B.map σ = line i) (b : T) (hb : b ∈ B) (hbi : σ b = transposition i) :
    V ⊓ centralizer (B : Set T) = V ⊓ centralizer ({b} : Set T) := by
  apply le_antisymm
  · exact inf_le_inf_left V (centralizer_le (Set.singleton_subset_iff.mpr hb))
  · rintro v ⟨hvV, hvb⟩
    refine ⟨hvV, mem_centralizer_iff.mpr ?_⟩
    intro x hx
    have hxi : σ x ∈ zpowers (σ b) := by
      rw [hbi]
      change σ x ∈ line i
      rw [← hB]
      exact mem_map_of_mem σ hx
    obtain ⟨k, hkx⟩ := mem_zpowers_iff.mp hxi
    have hd : (b ^ k)⁻¹ * x ∈ V := by
      rw [← hk, MonoidHom.mem_ker]
      simp [hkx]
    have hcomm : Commute b v := mem_centralizer_iff.mp hvb b rfl
    have hdiff : Commute ((b ^ k)⁻¹ * x) v := setLike_mul_comm hd hvV
    simpa using ((hcomm.zpow_left k).mul_left hdiff).eq

private theorem maxFamily_unique_of_detector (σ : T →* Perm) (V A B : Subgroup T)
    [IsElementaryAbelian 2 V] (hk : σ.ker = V)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (hB : B ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
    (he : A.map σ = B.map σ) (a : T) (ha : a ∈ A)
    (hfix : V ⊓ centralizer (A : Set T) = V ⊓ centralizer ({a} : Set T)) : B = A := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 B := hB.2.1
  have hf (E : Subgroup T)
      (hE : E ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T)) :
      V ⊓ centralizer (E : Set T) ≤ E := by
    let _ : IsElementaryAbelian 2 (V ⊓ centralizer (E : Set T) : Subgroup T) :=
      IsElementaryAbelian.of_le inf_le_left
    exact Stellmacher.maxElementary_contains_elementary_centralizer ⊤ E _ hE
      le_top inf_le_right
  exact eq_of_le_of_card_ge
    (IsElementaryAbelian.le_of_same_image_of_centralizer_singleton σ V A B hk
      (hf A hA) (hf B hB) he a ha hfix)
    (hB.2.2 A le_top hA.2.1)

private theorem line_lift (σ : T →* Perm) (V W : Subgroup T)
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W]
    (hk : σ.ker = V) (hr : σ.range = ChapterB.Offenders.D 5)
    (hW : W.map σ = ChapterB.Offenders.D 5) (hp : FixedProfile σ V) (i : Fin 2) :
    ∃ B : Subgroup T,
      B ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T) ∧
      B.map σ = line i := by
  have hi : transposition i ∈ W.map σ := by
    rw [hW]
    exact ChapterB.Offenders.pairSwap_mem (n := 5) i i.isLt
  obtain ⟨w, hw, hwi⟩ := hi
  let C : Subgroup T := V ⊓ centralizer ({w} : Set T)
  let B : Subgroup T := C ⊔ zpowers w
  let _ : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  let _ : IsElementaryAbelian 2 (zpowers w) :=
    IsElementaryAbelian.of_le (zpowers_le.mpr hw)
  have hCW : C ≤ centralizer (zpowers w : Set T) := by
    rw [zpowers_eq_closure, centralizer_closure]
    exact inf_le_right
  have hBe : IsElementaryAbelian 2 B :=
    IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hCW)
  have hCmap : C.map σ = ⊥ := by
    apply (map_eq_bot_iff C).mpr
    rw [hk]
    exact inf_le_left
  have hBmap : B.map σ = line i := by
    change (C ⊔ zpowers w).map σ = line i
    rw [Subgroup.map_sup, hCmap, bot_sup_eq, MonoidHom.map_zpowers, hwi, line]
  have hCfixed : V ⊓ centralizer (zpowers w : Set T) = C := by
    rw [zpowers_eq_closure, centralizer_closure]
  have hCcard : Nat.card C * 2 = Nat.card V := by
    have h := hp.card_fixed (zpowers w)
    rw [hCfixed, MonoidHom.map_zpowers, hwi, ← line, fixedIndex_line] at h
    exact h
  have hprod : Nat.card (V ⊓ B : Subgroup T) * 2 = Nat.card B := by
    have h := relIndex_mul_relIndex (⊥ : Subgroup T) (σ.ker ⊓ B) B bot_le inf_le_right
    have h' : Nat.card (σ.ker ⊓ B : Subgroup T) * σ.ker.relIndex B = Nat.card B := by
      simpa only [relIndex_bot_left, inf_relIndex_right] using h
    rw [relIndex_ker, hk, hBmap, line_card] at h'
    exact h'
  have hcard : Nat.card B = Nat.card V := by
    apply le_antisymm (elementary_card_le_core σ V hk hr hp B hBe)
    calc
      Nat.card V = Nat.card C * 2 := hCcard.symm
      _ ≤ Nat.card (V ⊓ B : Subgroup T) * 2 :=
        Nat.mul_le_mul_right _ (card_le_of_le (le_inf inf_le_left le_sup_left))
      _ = Nat.card B := hprod
  exact ⟨B, mem_maxFamily_of_card_eq σ V hk hr hp B hBe hcard, hBmap⟩

/-- The maximum elementary order is exactly the order of the elementary kernel. -/
theorem maxOrder_eq_card_core (σ : T →* Perm) (V : Subgroup T)
    (hVe : IsElementaryAbelian 2 V) (hk : σ.ker = V)
    (hr : σ.range = ChapterB.Offenders.D 5) (hp : FixedProfile σ V) :
    Stellmacher.elementaryAbelianMaxOrder (⊤ : Subgroup T) = Nat.card V :=
  Stellmacher.maxOrder_eq_card_of_mem ⊤ V (core_mem_maxFamily σ V hVe hk hr hp)

/-- The four possible maximum elementary lifts exhaust the family. The two new
members have the specified transposition images. The fixed profile and the order
of the given full-image member are explicit inputs to this conditional result. -/
theorem exists_maxFamily_eq_four (σ : T →* Perm) (V W : Subgroup T)
    (hVe : IsElementaryAbelian 2 V) (hWe : IsElementaryAbelian 2 W)
    (hk : σ.ker = V) (hr : σ.range = ChapterB.Offenders.D 5)
    (hWmap : W.map σ = ChapterB.Offenders.D 5) (hWcard : Nat.card W = Nat.card V)
    (hp : FixedProfile σ V) :
    ∃ B₀ B₁ : Subgroup T,
      Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T) = {V, W, B₀, B₁} ∧
      B₀.map σ = line 0 ∧ B₁.map σ = line 1 := by
  let _ : IsElementaryAbelian 2 V := hVe
  let _ : IsElementaryAbelian 2 W := hWe
  have hV := core_mem_maxFamily σ V hVe hk hr hp
  have hW := mem_maxFamily_of_card_eq σ V hk hr hp W hWe hWcard
  obtain ⟨B₀, hB₀, h₀⟩ := line_lift σ V W hk hr hWmap hp 0
  obtain ⟨B₁, hB₁, h₁⟩ := line_lift σ V W hk hr hWmap hp 1
  have hline (i : Fin 2) (A B : Subgroup T)
      (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
      (hB : B ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
      (hAi : A.map σ = line i) (hBi : B.map σ = line i) : B = A := by
    have hai : transposition i ∈ A.map σ := by
      rw [hAi]
      exact mem_zpowers _
    obtain ⟨a, ha, hai⟩ := hai
    exact maxFamily_unique_of_detector σ V A B hk hA hB (hAi.trans hBi.symm) a ha
      (fixed_eq_singleton_of_line σ V A hk i hAi a ha hai)
  have hfull (B : Subgroup T)
      (hB : B ∈ Stellmacher.elementaryAbelianMaxSubgroups (⊤ : Subgroup T))
      (hBi : B.map σ = ChapterB.Offenders.D 5) : B = W := by
    have hwd : doubleSwap ∈ W.map σ := by
      rw [hWmap]
      exact (mem_actor _).mpr (Or.inr (Or.inr (Or.inr rfl)))
    obtain ⟨w, hw, hwd⟩ := hwd
    exact maxFamily_unique_of_detector σ V W B hk hW hB (hWmap.trans hBi.symm) w hw
      (hp.full_detect W w hw hWmap hwd)
  refine ⟨B₀, B₁, ?_, h₀, h₁⟩
  ext B
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hB
    rcases maxFamily_image_cases σ V hVe hk hr hp B hB with hi | hi | hi | hi
    · left
      have hBV : B ≤ V := by
        rw [← hk]
        exact (map_eq_bot_iff B).mp hi
      exact eq_of_le_of_card_ge hBV (hB.2.2 V le_top hVe)
    · exact Or.inr (Or.inr (Or.inl (hline 0 B₀ B hB₀ hB h₀ hi)))
    · exact Or.inr (Or.inr (Or.inr (hline 1 B₁ B hB₁ hB h₁ hi)))
    · exact Or.inr (Or.inl (hfull B hB hi))
  · rintro (rfl | rfl | rfl | rfl)
    · exact hV
    · exact hW
    · exact hB₀
    · exact hB₁

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily.Enumeration
end
