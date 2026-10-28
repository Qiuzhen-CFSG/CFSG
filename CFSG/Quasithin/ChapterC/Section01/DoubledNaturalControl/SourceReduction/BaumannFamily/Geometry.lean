module

public import CFSG.Quasithin.ChapterC.Section01.DoubledNaturalControl.SourceReduction.Contracts
import Mathlib.Tactic.FinCases

/-!
# Three coordinate radicals and their doubled fixed spaces

The shear radical fixes the plane v₂ = 0. Two coordinate swaps give three
radicals containing all six elementary transvections, hence generating SL₃(2).
Every nonidentity shear has this same fixed plane, so every nontrivial subgroup
of a conjugate radical fixes exactly sixteen vectors in the doubled module.

These are the concrete calculations in Aschbacher--Smith C.1.37, printed
pp.142--143, used to verify B.2.18(c),(d). All conjugations act on the original
column-vector module; no graph automorphism changes its marking.
-/

@[expose] public section
open Matrix Subgroup
namespace CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction.BaumannGeometry

def modelFixed (A : Subgroup SL) :=
  {v : DoubleSpace // ∀ g ∈ A, ∀ i, g • v i = v i}

def coordinateConjugator : Fin 3 → SL :=
  ![1, ⟨!![0,0,1; 0,1,0; 1,0,0], by decide⟩,
    ⟨!![1,0,0; 0,0,1; 0,1,0], by decide⟩]

theorem transvection_witness : ∀ (i j : Fin 3) (h : i ≠ j) (c : ZMod 2),
    ∃ (k : Fin 3) (a : ZMod 2 × ZMod 2),
      MulAut.conj (coordinateConjugator k) (BinaryLinearThree.shear (Multiplicative.ofAdd a)) =
        SpecialLinearGroup.transvection h c := by
  intro i j h c
  fin_cases i <;> fin_cases j
  · exact (h rfl).elim
  · refine ⟨2, (c, 0), ?_⟩
    revert h c
    decide +kernel
  · refine ⟨0, (c, 0), ?_⟩
    revert h c
    decide +kernel
  · refine ⟨1, (0, c), ?_⟩
    revert h c
    decide +kernel
  · exact (h rfl).elim
  · refine ⟨0, (0, c), ?_⟩
    revert h c
    decide +kernel
  · refine ⟨1, (c, 0), ?_⟩
    revert h c
    decide +kernel
  · refine ⟨2, (0, c), ?_⟩
    revert h c
    decide +kernel
  · exact (h rfl).elim

theorem coordinate_generation :
    (⨆ i, BinaryLinearThree.R.map (MulAut.conj (coordinateConjugator i)).toMonoidHom) = ⊤ := by
  apply eq_top_iff.mpr
  intro g _
  apply Representation.OneCohomology.SLHigherNatural.transvection_induction
    (fun g => g ∈ ⨆ i, BinaryLinearThree.R.map
      (MulAut.conj (coordinateConjugator i)).toMonoidHom) ?_ ?_ g
  · intro i j h c
    obtain ⟨k, a, ha⟩ := transvection_witness i j h c
    exact (le_iSup (fun k => BinaryLinearThree.R.map
      (MulAut.conj (coordinateConjugator k)).toMonoidHom) k)
      ⟨_, ⟨Multiplicative.ofAdd a, rfl⟩, ha⟩
  · intro a b ha hb
    exact mul_mem ha hb

theorem shear_fixes_iff (a : ZMod 2 × ZMod 2) (ha : a ≠ 0)
    (v : Fin 3 → ZMod 2) :
    BinaryLinearThree.shear (Multiplicative.ofAdd a) • v = v ↔ v 2 = 0 := by
  revert v ha a
  decide +kernel

theorem shear_fixes_of_plane (a : ZMod 2 × ZMod 2) (v : Fin 3 → ZMod 2)
    (hv : v 2 = 0) : BinaryLinearThree.shear (Multiplicative.ofAdd a) • v = v := by
  change !![1,0,a.1; 0,1,a.2; 0,0,1].mulVec v = v
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv]

def planeEquiv : {v : DoubleSpace // ∀ i, v i 2 = 0} ≃ (Fin 2 → Fin 2 → ZMod 2) where
  toFun v i j := v.val i j.castSucc
  invFun w := ⟨fun i => ![w i 0, w i 1, 0], by simp⟩
  left_inv v := by
    apply Subtype.ext
    funext i j
    fin_cases j <;> simp [v.property]
  right_inv w := by
    funext i j
    fin_cases j <;> rfl

theorem fixed_iff_plane (E : Subgroup SL) (hE : E ≤ BinaryLinearThree.R)
    (hne : E ≠ ⊥) (v : DoubleSpace) :
    (∀ g ∈ E, ∀ i, g • v i = v i) ↔ ∀ i, v i 2 = 0 := by
  have hex : ∃ g ∈ E, g ≠ 1 := by
    by_contra! h
    apply hne
    exact eq_bot_iff.mpr (fun g hg => h g hg)
  obtain ⟨g, hg, hg1⟩ := hex
  obtain ⟨a, rfl⟩ := hE hg
  have ha : a.toAdd ≠ 0 := by
    intro hz
    have ha1 : a = 1 := hz
    simp [ha1] at hg1
  constructor
  · intro hv i
    exact (shear_fixes_iff a.toAdd ha (v i)).mp (hv _ hg i)
  · intro hv g hg i
    obtain ⟨a, rfl⟩ := hE hg
    exact shear_fixes_of_plane a.toAdd (v i) (hv i)

theorem card_fixed (E : Subgroup SL) (hE : E ≤ BinaryLinearThree.R)
    (hne : E ≠ ⊥) : Nat.card (modelFixed E) = 16 := by
  let e : modelFixed E ≃ (Fin 2 → Fin 2 → ZMod 2) :=
    (Equiv.subtypeEquivRight (fixed_iff_plane E hE hne)).trans planeEquiv
  rw [Nat.card_congr e]
  simp

/-- Matrix multiplication transports fixed vectors under inner conjugation. -/
def conjugateFixedEquiv (E : Subgroup SL) (g : SL) :
    modelFixed E ≃ modelFixed (E.map (MulAut.conj g).toMonoidHom) where
  toFun v := ⟨fun i => g • v.val i, by
    rintro _ ⟨a, ha, rfl⟩ i
    change (g * a * g⁻¹) • (g • v.val i) = g • v.val i
    simp only [mul_smul, inv_smul_smul, v.property a ha]⟩
  invFun v := ⟨fun i => g⁻¹ • v.val i, by
    intro a ha i
    have h := congrArg (fun w : Fin 3 → ZMod 2 => g⁻¹ • w)
      (v.property (MulAut.conj g a) (mem_map_of_mem _ ha) i)
    change g⁻¹ • ((g * a * g⁻¹) • v.val i) = g⁻¹ • v.val i at h
    simpa only [mul_smul, inv_smul_smul] using h⟩
  left_inv v := by apply Subtype.ext; funext i; simp
  right_inv v := by apply Subtype.ext; funext i; simp

theorem card_fixed_conjugate (E : Subgroup SL) (g : SL) :
    Nat.card (modelFixed (E.map (MulAut.conj g).toMonoidHom)) =
      Nat.card (modelFixed E) := (Nat.card_congr (conjugateFixedEquiv E g)).symm

theorem map_conj_mul {G : Type*} [Group G] (A : Subgroup G) (g h : G) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one {G : Type*} [Group G] (A : Subgroup G) :
    A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  have hf : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [hf, Subgroup.map_id]

theorem map_conj_cancel {G : Type*} [Group G] (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = A := by
  rw [map_conj_mul, mul_inv_cancel]
  exact map_conj_one A

theorem map_conjugate {G H : Type*} [Group G] [Group H]
    (f : G →* H) (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map f =
      (A.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem card_fixed_of_le_conjugate (E : Subgroup SL) (g : SL)
    (hE : E ≤ BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom)
    (hne : E ≠ ⊥) : Nat.card (modelFixed E) = 16 := by
  let E' := E.map (MulAut.conj g⁻¹).toMonoidHom
  have hc : E'.map (MulAut.conj g).toMonoidHom = E := map_conj_cancel E g
  have hle : E' ≤ BinaryLinearThree.R := by
    have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hE
    rwa [map_conj_mul, inv_mul_cancel, map_conj_one] at h
  have hn : E' ≠ ⊥ := by
    intro he
    apply hne
    rw [← hc, he, Subgroup.map_bot]
  rw [← hc, card_fixed_conjugate]
  exact card_fixed E' hle hn

theorem card_le_four_of_le_conjugate (E : Subgroup SL) (g : SL)
    (hE : E ≤ BinaryLinearThree.R.map (MulAut.conj g).toMonoidHom) : Nat.card E ≤ 4 := by
  have h := card_le_of_le hE
  rwa [card_map_of_injective (MulAut.conj g).injective, BinaryLinearThree.card_R] at h

theorem conjugate_coordinate_generation (g : SL) :
    (⨆ i, BinaryLinearThree.R.map (MulAut.conj (g * coordinateConjugator i)).toMonoidHom) = ⊤ := by
  simp_rw [← map_conj_mul]
  rw [← Subgroup.map_iSup, coordinate_generation, map_top_of_surjective _ (MulAut.conj g).surjective]

end CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction.BaumannGeometry
