module
public import Theory.GroupTheory.DihedralCentralProductThree.Splitting
public import Theory.GroupTheory.DihedralCentralProductSix.Model

/-!
# Iterated dihedral splitting

The maximal elementary subgroup loses exactly one binary dimension at each
dihedral split, by the extraspecial elementary-subgroup bound. Iteration ends
in a dihedral group of order eight. Composing the inclusions produces faithful,
pairwise commuting factor maps which generate the group; their central
involutions agree because the ambient center has order two.

This is the intrinsic plus-type argument used in Aschbacher–Smith 8.2.12,
printed p.722 (PDF p.739). It extends the three-factor splitting construction.
-/

namespace DihedralCentralProductFourSix
open Subgroup DihedralGroup

private theorem prepend_factor_maps
    {P : Type*} [Group P] (n : ℕ)
    (D : Subgroup P) (e : D ≃* DihedralGroup 4)
    (hgen : D ⊔ centralizer (D : Set P) = ⊤)
    (f : Fin n → DihedralGroup 4 →* centralizer (D : Set P))
    (hinj : ∀ i, Function.Injective (f i))
    (hc : Pairwise fun i j => ∀ x y, Commute (f i x) (f j y))
    (hg : (⨆ i, (f i).range) = ⊤) :
    ∃ g : Fin (n + 1) → DihedralGroup 4 →* P,
      (∀ i, Function.Injective (g i)) ∧
      (Pairwise fun i j => ∀ x y, Commute (g i x) (g j y)) ∧
      (⨆ i, (g i).range) = ⊤ := by
  let C := centralizer (D : Set P)
  let g₀ : DihedralGroup 4 →* P := D.subtype.comp e.symm.toMonoidHom
  let gs (i : Fin n) : DihedralGroup 4 →* P := C.subtype.comp (f i)
  let g : Fin (n + 1) → DihedralGroup 4 →* P := Fin.cases g₀ gs
  have hcross (i : Fin n) (x y : DihedralGroup 4) : Commute (g₀ x) (gs i y) :=
    (f i y).property _ (e.symm x).property
  refine ⟨g, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact D.subtype_injective.comp e.symm.injective
    · exact C.subtype_injective.comp (hinj j)
  · intro i j
    refine Fin.cases ?_ (fun a => ?_) i
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro h; exact (h rfl).elim
      · intro _ x y; exact hcross b x y
    · refine Fin.cases ?_ (fun b => ?_) j
      · intro _ x y; exact (hcross a y x).symm
      · intro h x y
        exact congrArg Subtype.val (hc (fun hab => h (congrArg Fin.succ hab)) x y)
  · have hr₀ : g₀.range = D := by
      simp [g₀, MonoidHom.range_comp, ← MonoidHom.range_eq_map]
    have hrs : (⨆ i, (gs i).range) = C := by
      simp only [gs, MonoidHom.range_comp, ← Subgroup.map_iSup, hg,
        ← MonoidHom.range_eq_map, C.range_subtype]
    have hh : (⨆ i, (g i).range) = g₀.range ⊔ ⨆ i, (gs i).range := by
      apply le_antisymm
      · apply iSup_le
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact le_sup_left
        · exact (le_iSup (fun j => (gs j).range) j).trans le_sup_right
      · apply sup_le
        · exact le_iSup (fun i => (g i).range) 0
        · apply iSup_le
          intro i
          exact le_iSup (fun i => (g i).range) i.succ
    rw [hh, hr₀, hrs]
    exact hgen

private theorem aligned_central_rotations
    {P : Type*} [Group P] [IsExtraspecial 2 P] (n : ℕ)
    (f : Fin (n + 1) → DihedralGroup 4 →* P)
    (hinj : ∀ i, Function.Injective (f i))
    (hc : Pairwise fun i j => ∀ x y, Commute (f i x) (f j y))
    (hg : (⨆ i, (f i).range) = ⊤) :
    ∀ i, f i (r 2) = f 0 (r 2) := by
  have hcent (i : Fin (n + 1)) : f i (r 2) ∈ center P := by
    have hle : (⨆ j, (f j).range) ≤ centralizer ({f i (r 2)} : Set P) := by
      apply iSup_le
      intro j x hx
      obtain ⟨y, rfl⟩ := hx
      apply mem_centralizer_singleton_iff.mpr
      by_cases hij : j = i
      · subst j
        simpa only [map_mul] using congrArg (f i)
          (Subgroup.mem_center_iff.mp DihedralCentralProductSix.r_two_central y)
      · exact hc hij y (r 2)
    rw [hg] at hle
    exact mem_center_iff.mpr (fun x => mem_centralizer_singleton_iff.mp (hle (mem_top x)))
  have hne (i : Fin (n + 1)) : f i (r 2) ≠ 1 := by
    intro h
    exact (by decide : (r 2 : DihedralGroup 4) ≠ 1)
      (hinj i (h.trans (map_one (f i)).symm))
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : center P)).mp
    (IsExtraspecial.center_order_p 2 P)
  intro i
  exact congrArg Subtype.val ((hz ⟨_, hcent i⟩ (fun h => hne i (congrArg Subtype.val h))).trans
    (hz ⟨_, hcent 0⟩ (fun h => hne 0 (congrArg Subtype.val h))).symm)

private theorem exists_factor_maps_aux (n : ℕ)
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hP : Nat.card P = 2 * (2 ^ (n + 1)) ^ 2)
    (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2 * 2 ^ (n + 1)) (hZA : center P ≤ A) :
    ∃ f : Fin (n + 1) → DihedralGroup 4 →* P,
      (∀ i, Function.Injective (f i)) ∧
      (Pairwise fun i j => ∀ x y, Commute (f i x) (f j y)) ∧
      (⨆ i, (f i).range) = ⊤ := by
  induction n generalizing P with
  | zero =>
    obtain ⟨e⟩ := DihedralCentralProductThree.dihedral_of_elementary_four
      (by simpa using hP) A (by simpa using hA)
    refine ⟨fun _ => e.symm.toMonoidHom, fun _ => e.symm.injective, ?_, ?_⟩
    · intro i j h
      exact (h (Fin.ext (by omega))).elim
    · simp
  | succ n ih =>
    have ht : 2 ≤ 2 ^ (n + 1) := by
      calc
        2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hp : Nat.card P = 8 * (2 ^ (n + 1)) ^ 2 := by
      rw [hP, pow_succ]
      ring
    have ha : Nat.card A = 4 * 2 ^ (n + 1) := by
      rw [hA, pow_succ]
      ring
    obtain ⟨D, ⟨e⟩, hg, hC, hAC, hZAC, hc, hac⟩ :=
      DihedralCentralProductThree.exists_dihedral_split A hZA
        (by nlinarith) (by nlinarith)
    let C := centralizer (D : Set P)
    let AC := A.subgroupOf C
    let : IsExtraspecial 2 C := hC
    let : IsElementaryAbelian 2 AC := hAC
    have hCcard : Nat.card C = 2 * (2 ^ (n + 1)) ^ 2 := by
      change Nat.card P = 4 * Nat.card C at hc
      omega
    have hACcard : Nat.card AC = 2 * 2 ^ (n + 1) := by
      have hb := extraspecial_two_elementary_card_sq_le AC hZAC
      rw [hCcard] at hb
      change Nat.card A ≤ 2 * Nat.card AC at hac
      rw [ha] at hac
      nlinarith
    obtain ⟨f, hi, hcomm, hgen⟩ := ih hCcard AC hACcard hZAC
    exact prepend_factor_maps (n + 1) D e hg f hi hcomm hgen

/-- A maximal elementary subgroup constructs all the dihedral factors. There
is no assumed hyperbolic basis or generation premise. The parameter `n + 1`
is the number of factors. -/
public theorem exists_dihedral_factor_maps (n : ℕ)
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]
    (hP : Nat.card P = 2 ^ (1 + 2 * (n + 1)))
    (A : Subgroup P) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 2 ^ (n + 2)) (hZA : center P ≤ A) :
    ∃ f : Fin (n + 1) → DihedralGroup 4 →* P,
      (∀ i, Function.Injective (f i)) ∧
      (Pairwise fun i j => ∀ x y, Commute (f i x) (f j y)) ∧
      (∀ i, f i (r 2) = f 0 (r 2)) ∧ (⨆ i, (f i).range) = ⊤ := by
  have hp : Nat.card P = 2 * (2 ^ (n + 1)) ^ 2 := by
    rw [hP, pow_add, pow_one, Nat.mul_comm 2 (n + 1), pow_mul]
  have ha : Nat.card A = 2 * 2 ^ (n + 1) := by
    rw [hA, pow_succ, Nat.mul_comm]
  obtain ⟨f, hi, hc, hg⟩ := exists_factor_maps_aux n hp A ha hZA
  exact ⟨f, hi, hc, aligned_central_rotations n f hi hc hg, hg⟩

end DihedralCentralProductFourSix
