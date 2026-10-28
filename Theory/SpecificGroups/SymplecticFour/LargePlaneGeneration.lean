module
public import Theory.SpecificGroups.SymplecticFour.SelectedPositioning

/-!
# Large plane actors and an opposite radical generate Sp₄

An additive subgroup of singular symmetric two-by-two matrices injects into
one field coordinate. Thus a plane actor larger than the field contains
an invertible shear B. Together with the full opposite radical, the word
u(B) l(B⁻¹) u(B) exchanges the two planes. It recovers every upper shear
from the lower radical, and the four root axes generate the whole group.

The final theorem transports this construction to the original plane
radical and its contained actor. The full-kernel consumer is
Sp4Four.SourceComparison.OriginalLargePlaneGeneration, used to exclude the
equal-mover large-distance branch of the original tensor geometry.
Source: the symplectic generation step in MS93 (5.5)--(5.11), pp.915--924.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Matrix Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.LargePlaneGeneration
open Plane CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private theorem symmetric_singular_card_bound
    (A : AddSubgroup (symmetricMatrices F))
    (hdet : ∀ B ∈ A, B.val.det = 0) : Nat.card A ≤ Nat.card F := by
  classical
  have hsym (B : symmetricMatrices F) : B.val 1 0 = B.val 0 1 :=
    congrArg (fun X : Matrix (Fin 2) (Fin 2) F => X 0 1) B.property
  have hd (B : symmetricMatrices F) (hB : B ∈ A) :
      B.val 0 0 * B.val 1 1 = (B.val 0 1)^2 := by
    have h := hdet B hB
    rw [Matrix.det_fin_two,hsym] at h
    exact (sub_eq_zero.mp h).trans (pow_two _).symm
  have hp (B C : symmetricMatrices F) (hB : B ∈ A) (hC : C ∈ A) :
      B.val 0 0 * C.val 1 1 + C.val 0 0 * B.val 1 1 = 0 := by
    have h := hd (B+C) (A.add_mem hB hC)
    change (B.val 0 0+C.val 0 0)*(B.val 1 1+C.val 1 1) =
      (B.val 0 1+C.val 0 1)^2 at h
    have hsq : (B.val 0 1+C.val 0 1)^2 = (B.val 0 1)^2+(C.val 0 1)^2 := by
      ring_nf
      simp [CharTwo.two_eq_zero]
    rw [hsq,←hd B hB,←hd C hC] at h
    linear_combination h
  have hz (B : symmetricMatrices F) (hB : B ∈ A)
      (h00 : B.val 0 0=0) (h11 : B.val 1 1=0) : B=0 := by
    have h01 : B.val 0 1=0 := (sq_eq_zero_iff).mp (by simpa [h00] using (hd B hB).symm)
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00,h11,h01,hsym]
  by_cases hex : ∃ B ∈ A, B.val 0 0 ≠ 0
  · obtain ⟨B,hB,hB0⟩ := hex
    let f : A →+ F :=
      { toFun := fun C => C.val.val 0 0
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hinj : Function.Injective f := by
      apply (AddMonoidHom.ker_eq_bot_iff f).mp
      apply _root_.eq_bot_iff.mpr
      intro C hC
      have hc0 : C.val.val 0 0=0 := hC
      have hc1 : C.val.val 1 1=0 := by
        have h := hp B C.val hB C.property
        rw [hc0,zero_mul,add_zero] at h
        exact (mul_eq_zero.mp h).resolve_left hB0
      exact Subtype.ext (hz C.val C.property hc0 hc1)
    exact Nat.card_le_card_of_injective f hinj
  · push Not at hex
    let f : A →+ F :=
      { toFun := fun C => C.val.val 1 1
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hinj : Function.Injective f := by
      apply (AddMonoidHom.ker_eq_bot_iff f).mp
      apply _root_.eq_bot_iff.mpr
      intro C hC
      exact Subtype.ext (hz C.val C.property (hex C.val C.property) hC)
    exact Nat.card_le_card_of_injective f hinj

private def lowerShear (B : symmetricMatrices F) : Sp F :=
  TwoConjugate.opposition * shearSp B * TwoConjugate.opposition⁻¹

omit [Finite F] in
private theorem lowerShear_matrix (B : symmetricMatrices F) :
    (lowerShear B).val = fromBlocks 1 0 B.val 1 := by
  change (TwoConjugate.opposition (F := F)).val * (shearSp B).val *
    (TwoConjugate.opposition⁻¹).val = _
  rw [TwoConjugate.opposition_inv]
  simp [TwoConjugate.opposition,shearSp,Matrix.fromBlocks_multiply]

private theorem upper_lower_generate (H : Subgroup (Sp F))
    (hu : ∀ B : symmetricMatrices F, shearSp B ∈ H)
    (hl : ∀ B : symmetricMatrices F, lowerShear B ∈ H) : H = ⊤ := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have h0 (t : F) : rootElement 0 t ∈ H := by
    let B : symmetricMatrices F := ⟨!![t,0;0,0], by
      ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
    convert hu B using 1
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootElement,rootMatrix,shearSp,B,Matrix.fromBlocks,Matrix.single,Matrix.one_apply]
  have h4 (t : F) : rootElement 4 t ∈ H := by
    let B : symmetricMatrices F := ⟨!![0,t;t,0], by
      ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
    convert hu B using 1
    apply Subtype.ext
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [rootElement,rootMatrix,shearSp,B,Matrix.fromBlocks,Matrix.single,Matrix.one_apply]
  have hneg (r : Fin 8) (t : F) (h : rootElement r t ∈ SymplecticConjugatePair.planeRadical) :
      TwoConjugate.opposition * rootElement r t * TwoConjugate.opposition⁻¹ ∈ H := by
    obtain ⟨B,hB⟩ := SymplecticConjugatePair.mem_planeRadical_iff _ |>.mp h
    rw [←hB]
    exact hl B
  have hm (r : Fin 8) (t : F) (hr : r=0 ∨ r=4) :
      rootElement r t ∈ SymplecticConjugatePair.planeRadical := by
    rw [SymplecticConjugatePair.planeRadical_eq_wing]
    rcases hr with rfl | rfl
    · refine ⟨element 0 t 0 0,(element_mem_wing _ _ _ _ _).mpr rfl,?_⟩
      simp [element,RootSubgroup.element_zero]
    · refine ⟨element 0 0 t 0,(element_mem_wing _ _ _ _ _).mpr rfl,?_⟩
      simp [element,RootSubgroup.element_zero]
  refine TwoConjugate.eq_top_of_four_axes H h0 ?_ h4 ?_
  · intro t
    rw [←(TwoConjugate.opposition_central_axes t).1]
    exact hneg 0 t (hm 0 t (Or.inl rfl))
  · intro t
    rw [←(TwoConjugate.opposition_central_axes t).2]
    exact hneg 4 t (hm 4 t (Or.inr rfl))

/-- An invertible plane shear and the full opposite radical generate Sp₄.
The Weyl word has off-diagonal blocks B and B⁻¹. -/
private theorem eq_top_of_lower_and_invertible_shear (H : Subgroup (Sp F))
    (B : symmetricMatrices F) (hB : B.val.det ≠ 0) (hu : shearSp B ∈ H)
    (hl : ∀ C : symmetricMatrices F, lowerShear C ∈ H) : H = ⊤ := by
  let C : symmetricMatrices F := ⟨B.val⁻¹,B.property.inv⟩
  have hBC : B.val*C.val=1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hB)
  have hCB : C.val*B.val=1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hB)
  let w := shearSp B * lowerShear C * shearSp B
  have hw : w ∈ H := H.mul_mem (H.mul_mem hu (hl C)) hu
  have h11 : (1+1 : Matrix (Fin 2) (Fin 2) F)=0 := by
    ext i j
    simp [Matrix.one_apply,CharTwo.add_self_eq_zero]
  have hwm : w.val = fromBlocks 0 B.val C.val 0 := by
    change (shearSp B).val * (lowerShear C).val * (shearSp B).val = _
    rw [lowerShear_matrix]
    simp only [shearSp,Matrix.fromBlocks_multiply,mul_one,one_mul,mul_zero,zero_mul,
      add_zero,zero_add,hBC,hCB,h11]
  apply upper_lower_generate H _ hl
  intro D
  let E : symmetricMatrices F := ⟨C.val*D.val*C.val, by
    change (C.val*D.val*C.val)ᵀ=C.val*D.val*C.val
    rw [Matrix.transpose_mul,Matrix.transpose_mul,C.property,D.property]
    exact (Matrix.mul_assoc _ _ _).symm⟩
  have he : w * lowerShear E * w = shearSp D := by
    apply Subtype.ext
    change w.val * (lowerShear E).val * w.val = _
    rw [hwm,lowerShear_matrix]
    simp only [shearSp,Matrix.fromBlocks_multiply,mul_one,one_mul,mul_zero,zero_mul,
      add_zero,zero_add,hBC,hCB]
    congr 1
    change B.val * (C.val*D.val*C.val) * B.val = D.val
    simp only [←Matrix.mul_assoc,hBC,one_mul]
    rw [Matrix.mul_assoc,hCB,mul_one]
  rw [←he]
  exact H.mul_mem (H.mul_mem hw (hl E)) hw

/-- A subgroup larger than the field inside a plane radical contains an
invertible shear. Otherwise singular symmetric matrices inject into one field coordinate. -/
theorem exists_invertible_shear (A : Subgroup (Sp F))
    (hA : A ≤ SymplecticConjugatePair.planeRadical)
    (hc : Nat.card F < Nat.card A) :
    ∃ B : symmetricMatrices F, shearSp B ∈ A ∧ B.val.det ≠ 0 := by
  classical
  let N : AddSubgroup (symmetricMatrices F) :=
    { carrier := {B | shearSp B ∈ A}
      zero_mem' := by
        change shearSp (0 : symmetricMatrices F) ∈ A
        have he : shearSp (0 : symmetricMatrices F)=1 := congrArg Subtype.val shear_zero
        rw [he]
        exact A.one_mem
      add_mem' := by
        intro B C hB hC
        have h : shearSp (B+C) = shearSp B*shearSp C := congrArg Subtype.val (shear_add B C)
        change shearSp (B+C) ∈ A
        rw [h]
        exact A.mul_mem hB hC
      neg_mem' := by
        intro B hB
        have hn : -B=B := by
          apply Subtype.ext
          ext i j
          exact CharTwo.neg_eq _
        rwa [hn] }
  let f : N → A := fun B => ⟨shearSp B.val,B.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro B C he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun g : A => g.val.val.toBlocks₁₂) he
    · intro a
      obtain ⟨B,hB⟩ := SymplecticConjugatePair.mem_planeRadical_iff a.val |>.mp (hA a.property)
      exact ⟨⟨B,show shearSp B ∈ A from hB.symm ▸ a.property⟩,Subtype.ext hB⟩
  by_contra! h
  have hb := symmetric_singular_card_bound N (fun B hB => h B hB)
  have he := Nat.card_congr (Equiv.ofBijective f hf)
  omega

/-- The opposite radical generates with every contained actor larger than
the field. This includes the order-sixteen critical image over GF(4). -/
theorem opposite_plane_large_subactor_generate (A : Subgroup (Sp F))
    (hA : A ≤ SymplecticConjugatePair.planeRadical)
    (hc : Nat.card F < Nat.card A) :
    (SymplecticConjugatePair.planeRadical.map
      (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom) ⊔ A = ⊤ := by
  obtain ⟨B,hBA,hB⟩ := exists_invertible_shear A hA hc
  apply eq_top_of_lower_and_invertible_shear _ B hB (mem_sup_right hBA)
  intro C
  apply mem_sup_left
  exact mem_map_of_mem _ (SymplecticConjugatePair.mem_planeRadical_iff _ |>.mpr ⟨C,rfl⟩)

/-- Position the original plane radical relative to its large contained
actor, retaining a literal symplectic conjugator. -/
theorem exists_plane_large_subactor_generator
    (E A : Subgroup (Sp F))
    (hE : ∃ k : Sp F, E.map (MulAut.conj k).toMonoidHom =
      (wing true).map (unipotent (F := F)).subtype)
    (hAE : A ≤ E) (hc : Nat.card F < Nat.card A) :
    ∃ g : Sp F, E.map (MulAut.conj g).toMonoidHom ⊔ A = ⊤ := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨k,hk⟩ := hE
  rw [←SymplecticConjugatePair.planeRadical_eq_wing] at hk
  let o := TwoConjugate.opposition (F := F)
  have hh := opposite_plane_large_subactor_generate (A.map (MulAut.conj k).toMonoidHom)
    (hk ▸ map_mono hAE) (by rw [card_map_of_injective (MulAut.conj k).injective]; exact hc)
  refine ⟨k⁻¹*o*k,?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective
  rw [Subgroup.map_sup]
  have hm : (E.map (MulAut.conj (k⁻¹*o*k)).toMonoidHom).map (MulAut.conj k).toMonoidHom =
      (E.map (MulAut.conj k).toMonoidHom).map (MulAut.conj o).toMonoidHom := by
    rw [Subgroup.map_map,Subgroup.map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change k*((k⁻¹*o*k)*x*(k⁻¹*o*k)⁻¹)*k⁻¹=o*(k*x*k⁻¹)*o⁻¹
    group
  rw [hm,hk,hh,←MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr (MulAut.conj k).surjective]

end Theory.SpecificGroups.SymplecticFour.LargePlaneGeneration
