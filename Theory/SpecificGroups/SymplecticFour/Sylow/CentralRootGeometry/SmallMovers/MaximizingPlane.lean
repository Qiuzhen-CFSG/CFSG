module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.LargeQuadratic
public import Theory.SpecificGroups.SymplecticFour.QuadraticSmallMovers

/-!
# A plane radical maximizing the small-mover intersection

Explicit inner root matrices align every maximum small mover with the
standard plane radical while keeping the entire two-subgroup unipotent.
The quadratic fixed-space bound then controls its intersection with every
other conjugate plane radical. The choice applies at every binary field
degree and does not assume the given two-subgroup is Sylow.

Source: MS93 (5.0), printed p.912. The full-kernel replacement application
is NonbinarySymplectic.CriticalReduction.MaximizingParabolic.
-/
public noncomputable section
set_option linter.unusedSimpArgs false
open Subgroup Matrix
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private def planeSelector (l : F) : Sp F :=
  rootElement 2 1 * rootElement 3 1 * rootElement 2 1 * rootElement 2 l

omit [Finite F] in
private theorem planeSelector_element (l b u w : F) :
    planeSelector l * (element b u w 0).val * (planeSelector l)⁻¹ =
      (element (w+l*b) u b 0).val := by
  have hmat : (planeSelector l).val = fromBlocks !![1,0;0,0]
      !![0,0;0,1] !![0,0;0,1] !![1,0;0,l] := by
    change rootMatrix 2 1 * rootMatrix 3 1 * rootMatrix 2 1 * rootMatrix 2 l = _
    change fromBlocks 1 (single 1 1 (1:F)) 0 1 * fromBlocks 1 0 (single 1 1 (1:F)) 1 *
      fromBlocks 1 (single 1 1 (1:F)) 0 1 * fromBlocks 1 (single 1 1 l) 0 1 = _
    simp only [Matrix.fromBlocks_multiply]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.fromBlocks,Matrix.mul_apply,Fin.sum_univ_two,Matrix.single,
        CharTwo.neg_eq,CharTwo.add_self_eq_zero,CharTwo.two_eq_zero]
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (planeSelector l).val * (element b u w 0).val.val =
    (element (w+l*b) u b 0).val.val * (planeSelector l).val
  rw [hmat,element_matrix,element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix,Matrix.fromBlocks,Matrix.mul_apply,Fintype.sum_sum_type,
      Fin.sum_univ_two,Matrix.single]
  ring_nf
  simp [CharTwo.two_eq_zero,sub_eq_add_neg,CharTwo.neg_eq]

private theorem planeSelector_point (l : F) :
    ((wing false).map (unipotent (F := F)).subtype).map
      (MulAut.conj (planeSelector l)).toMonoidHom = (wing false).map unipotent.subtype := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    dsimp only at hx ⊢
    have hv : v=0 := (element_mem_wing false _ _ _ _).mp hx
    subst v
    change planeSelector l * (element _ _ _ 0).val * (planeSelector l)⁻¹ ∈ _
    rw [planeSelector_element]
    exact mem_map_of_mem unipotent.subtype ((element_mem_wing false _ _ _ _).mpr rfl)
  · exact (card_map_of_injective (MulAut.conj (planeSelector l)).injective).ge

private theorem planeSelector_plane (l : F) :
    ((finitePlane l).map (unipotent (F := F)).subtype).map
      (MulAut.conj (planeSelector l)).toMonoidHom ≤ (wing true).map unipotent.subtype := by
  rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  dsimp only at hx ⊢
  obtain ⟨rfl,rfl⟩ := (element_mem_finitePlane l _ _ _ _).mp hx
  change planeSelector l * (element _ _ _ 0).val * (planeSelector l)⁻¹ ∈ _
  rw [planeSelector_element,CharTwo.add_self_eq_zero]
  exact mem_map_of_mem unipotent.subtype ((element_mem_wing true _ _ _ _).mpr rfl)

/-- A maximum can be placed in the plane radical without losing the
containing Sylow coordinates of the entire two-subgroup. -/
private theorem maximal_plane_alignment (T A : Subgroup (unipotent (F := F)))
    (hA : A ∈ Maximal T) :
    ∃ g : Sp F,
      (T.map unipotent.subtype).map (MulAut.conj g).toMonoidHom ≤ unipotent ∧
      (A.map unipotent.subtype).map (MulAut.conj g).toMonoidHom ≤
        (wing true).map unipotent.subtype := by
  rcases small_classification_nonstandard A hA.2.1 with hwing | ⟨l,rfl⟩
  · refine ⟨1,?_,?_⟩
    all_goals rw [show (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ by ext x; simp,
      Subgroup.map_id]
    · exact map_le_range _ _ |>.trans_eq (range_subtype _)
    · exact map_mono hwing
  · refine ⟨planeSelector l,?_,planeSelector_plane l⟩
    have ht := map_mono (f := (MulAut.conj (planeSelector l)).toMonoidHom)
      (map_mono (f := (unipotent (F := F)).subtype) (le_point_wing_of_maximal_finitePlane T l hA))
    rw [planeSelector_point] at ht
    exact ht.trans ((map_le_range _ _).trans_eq (range_subtype _))

variable [Algebra (ZMod 2) F]
open Representation Representation.BinaryOffender

omit [CharP F 2] in
private theorem quadratic_movingIndex_le (B : Subgroup (unipotent (F := F)))
    (hq : ∀ x ∈ B.map unipotent.subtype, ∀ y ∈ B.map unipotent.subtype,
      ∀ v : Theory.SpecificGroups.SymplecticFour.Vector F,
        x • (y • v-v)=y • v-v) : movingIndex B ≤ Nat.card F^2 := by
  have hh := quadratic_natural_fixed_index_le_square (B.map unipotent.subtype) hq
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
  rw [←binary_movingIndex]
  change 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
    (symplecticNatural (k := F) 2)).comp unipotent.subtype) B ≤ _
  rw [fixedCodim,Representation.BinaryOffender.fixedSpace_comp_map]
  exact hh

omit [CharP F 2] [Finite F] [Algebra (ZMod 2) F] in
/-- Inner conjugation preserves quadratic action in the literal natural module. -/
theorem quadratic_conjugate (B : Subgroup (Sp F)) (g : Sp F)
    (hq : ∀ x ∈ B, ∀ y ∈ B, ∀ v : Theory.SpecificGroups.SymplecticFour.Vector F,
      x • (y • v-v)=y • v-v) :
    ∀ x ∈ B.map (MulAut.conj g).toMonoidHom,
      ∀ y ∈ B.map (MulAut.conj g).toMonoidHom,
        ∀ v : Theory.SpecificGroups.SymplecticFour.Vector F,
          x • (y • v-v)=y • v-v := by
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ v
  have hh := congrArg (fun w : Theory.SpecificGroups.SymplecticFour.Vector F => g • w)
    (hq x hx y hy (g⁻¹ • v))
  simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,mul_smul,
    smul_sub,inv_smul_smul,smul_inv_smul] using hh

omit [CharP F 2] in
private theorem quadratic_card_le_maximal (T A : Subgroup (unipotent (F := F)))
    (hA : A ∈ Maximal T) (hlarge : Nat.card F^2 ≤ Nat.card A)
    (C : Subgroup (Sp F)) (hCT : C ≤ T.map unipotent.subtype)
    (hq : ∀ x ∈ C, ∀ y ∈ C, ∀ v : Theory.SpecificGroups.SymplecticFour.Vector F,
      x • (y • v-v)=y • v-v) : Nat.card C ≤ Nat.card A := by
  let B := C.subgroupOf unipotent
  have hCU : C ≤ unipotent := hCT.trans ((map_le_range _ _).trans_eq (range_subtype _))
  have hBm : B.map (unipotent (F := F)).subtype = C := map_subgroupOf_eq_of_le hCU
  have hc : Nat.card B = Nat.card C := by
    rw [←card_map_of_injective (K := B) (unipotent (F := F)).subtype_injective,hBm]
  by_cases hbig : Nat.card F^2 ≤ Nat.card B
  · have hm := quadratic_movingIndex_le B (hBm.symm ▸ hq)
    have hBT : B ≤ T := by
      apply (map_le_map_iff_of_injective (unipotent (F := F)).subtype_injective).mp
      rwa [hBm]
    have hh := hA.2.2 B hBT ⟨hm.trans hbig,hm⟩
    rwa [hc] at hh
  · rw [hc] at hbig
    exact (le_of_lt (lt_of_not_ge hbig)).trans hlarge

omit [CharP F 2] [Finite F] [Algebra (ZMod 2) F] in
private theorem conjugate_back (B : Subgroup (Sp F)) (g : Sp F) :
    (B.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = B := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (Sp F) := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [he,Subgroup.map_id]

omit [Algebra (ZMod 2) F] in
/-- The full plane radical acts quadratically on the natural four-space. -/
theorem plane_radical_quadratic :
    ∀ x : Sp F, x ∈ (wing true).map (unipotent (F := F)).subtype →
      ∀ y : Sp F, y ∈ (wing true).map unipotent.subtype →
        ∀ v : Theory.SpecificGroups.SymplecticFour.Vector F,
          x • (y • v-v)=y • v-v :=
  small_quadratic (wing true) (small_of_le_wing_of_large _ le_rfl
    (by rw [card_wing]; exact Nat.pow_le_pow_right Nat.card_pos (by decide)))

/-- A maximizing plane radical exists in coordinates containing the entire
edge image. Every other conjugate plane radical has no larger intersection
with the full small-mover join. -/
theorem exists_maximizing_plane (T : Subgroup (unipotent (F := F)))
    (hlarge : Nat.card F^2 ≤ Nat.card (join T)) :
    ∃ g : Sp F,
      (T.map unipotent.subtype).map (MulAut.conj g).toMonoidHom ≤ unipotent ∧
      ∀ x : Sp F,
        Nat.card (((join T).map unipotent.subtype).map (MulAut.conj g).toMonoidHom ⊓
          ((wing true).map unipotent.subtype).map (MulAut.conj x).toMonoidHom : Subgroup (Sp F)) ≤
        Nat.card (((join T).map unipotent.subtype).map (MulAut.conj g).toMonoidHom ⊓
          (wing true).map unipotent.subtype : Subgroup (Sp F)) := by
  obtain ⟨A,hA,hcard,_⟩ := exists_large_quadratic_maximal T hlarge
  obtain ⟨g,hT,hP⟩ := maximal_plane_alignment T A hA
  refine ⟨g,hT,?_⟩
  let J := ((join T).map unipotent.subtype).map (MulAut.conj g).toMonoidHom
  let P := (wing (F := F) true).map unipotent.subtype
  have hAP : Nat.card A ≤ Nat.card (J ⊓ P : Subgroup (Sp F)) := by
    have hAJ := map_mono (f := (MulAut.conj g).toMonoidHom)
      (map_mono (f := (unipotent (F := F)).subtype) (le_sSup hA))
    have hc := card_le_of_le (le_inf hAJ hP)
    simpa only [J,P,join,card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,
      card_map_of_injective (unipotent (F := F)).subtype_injective] using hc
  have hquad : ∀ x ∈ P, ∀ y ∈ P, ∀ v : Theory.SpecificGroups.SymplecticFour.Vector F,
      x • (y • v-v)=y • v-v :=
    plane_radical_quadratic
  have hJT : join T ≤ T := sSup_le fun _ h => h.1
  intro x
  let C := J ⊓ P.map (MulAut.conj x).toMonoidHom
  let D := C.map (MulAut.conj g⁻¹).toMonoidHom
  have hCq : ∀ a ∈ C, ∀ b ∈ C, ∀ v : Theory.SpecificGroups.SymplecticFour.Vector F,
      a • (b • v-v)=b • v-v :=
    fun a ha b hb v => quadratic_conjugate P x hquad a ha.2 b hb.2 v
  have hDT : D ≤ T.map unipotent.subtype := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (show C ≤ J from inf_le_left)
    change D ≤ (((join T).map unipotent.subtype).map
      (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom at hh
    rw [conjugate_back] at hh
    exact hh.trans (map_mono hJT)
  have hbound := quadratic_card_le_maximal T A hA hcard D hDT
    (quadratic_conjugate C g⁻¹ hCq)
  rw [show Nat.card D = Nat.card C from card_map_of_injective (MulAut.conj g⁻¹).injective] at hbound
  exact hbound.trans hAP

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.Degree
