module
public import Theory.SpecificGroups.SymplecticFour.PrescribedLargePlaneGeneration
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairMarking
import all Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairMarking

/-!
# A large opposite-plane actor and two prescribed distinct roots

The root6 and root7 conjugations placing a distinct pair of full roots on
standard axes preserve both opposite plane radicals. Conjugation by opposition
then puts the same large actor in the upper plane and the same full roots on
the two lower axes, where PrescribedLargePlaneGeneration applies.

Source: MS93 (5.6)(a), printed p.917, as used in (5.12)(3), p.927.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Subgroup Matrix
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.PrescribedRootPairPlaneGeneration
open CentralRootGeometry CentralRootGeometry.SmallMovers
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private abbrev upperPlane : Subgroup (Sp F) := (wing true).map unipotent.subtype
private abbrev lowerPlane : Subgroup (Sp F) :=
  (upperPlane (F := F)).map (MulAut.conj TwoConjugate.opposition).toMonoidHom

omit [Finite F] [CharP F 2] in
private theorem map_conj_mul (A : Subgroup (Sp F)) (g h : Sp F) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*h)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply,mul_assoc]

omit [Finite F] [CharP F 2] in
private theorem map_conj_one (A : Subgroup (Sp F)) :
    A.map (MulAut.conj (1 : Sp F)).toMonoidHom = A := by
  rw [show (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ by ext x; simp]
  exact map_id A

private theorem upper_shift (b : F) :
    (upperPlane (F := F)).map (MulAut.conj (rootElement 6 b)).toMonoidHom = upperPlane := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_,⟨y,hy,rfl⟩,rfl⟩
    obtain ⟨⟨c,u,w,v⟩,rfl⟩ := element_surjective y
    have hc : c = 0 := by
      simpa only [↓reduceIte] using (element_mem_wing true c u w v).mp hy
    subst c
    change rootElement 6 b * (element 0 u w v).val * (rootElement 6 b)⁻¹ ∈ _
    rw [SmallMovers.shift_element]
    exact mem_map_of_mem unipotent.subtype ((element_mem_wing true _ _ _ _).mpr rfl)
  · exact le_of_eq (Subgroup.card_map_of_injective
      (f := (MulAut.conj (rootElement 6 b)).toMonoidHom) (MulAut.conj _).injective).symm

private theorem upper_lower (b : F) :
    (upperPlane (F := F)).map (MulAut.conj (rootElement 7 b)).toMonoidHom = upperPlane := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_,⟨y,hy,rfl⟩,rfl⟩
    obtain ⟨⟨c,u,w,v⟩,rfl⟩ := element_surjective y
    have hc : c = 0 := by
      simpa only [↓reduceIte] using (element_mem_wing true c u w v).mp hy
    subst c
    change rootElement 7 b * (element 0 u w v).val * (rootElement 7 b)⁻¹ ∈ _
    rw [SmallMovers.lower_element]
    exact mem_map_of_mem unipotent.subtype ((element_mem_wing true _ _ _ _).mpr rfl)
  · exact le_of_eq (Subgroup.card_map_of_injective
      (f := (MulAut.conj (rootElement 7 b)).toMonoidHom) (MulAut.conj _).injective).symm

omit [Finite F] in
private theorem opposition_short (b : F) :
    TwoConjugate.opposition * rootElement 6 b * TwoConjugate.opposition⁻¹ = rootElement 7 b ∧
    TwoConjugate.opposition * rootElement 7 b * TwoConjugate.opposition⁻¹ = rootElement 6 b := by
  rw [TwoConjugate.opposition_inv]
  constructor <;> apply Subtype.ext <;>
    change (TwoConjugate.opposition (F := F)).val * _ *
      (TwoConjugate.opposition (F := F)).val = _
  all_goals
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [TwoConjugate.opposition,rootElement,rootMatrix,Matrix.mul_apply,
        Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.single,Matrix.fromBlocks,CharTwo.neg_eq]

private theorem lower_normalizes (g : Sp F)
    (h : (upperPlane (F := F)).map
      (MulAut.conj (TwoConjugate.opposition*g*TwoConjugate.opposition⁻¹)).toMonoidHom = upperPlane) :
    (lowerPlane (F := F)).map (MulAut.conj g).toMonoidHom = lowerPlane := by
  apply Subgroup.map_injective (f := (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom)
    (MulAut.conj _).injective
  change (((upperPlane (F := F)).map (MulAut.conj TwoConjugate.opposition).toMonoidHom).map
    (MulAut.conj g).toMonoidHom).map (MulAut.conj TwoConjugate.opposition).toMonoidHom =
      ((upperPlane (F := F)).map (MulAut.conj TwoConjugate.opposition).toMonoidHom).map
        (MulAut.conj TwoConjugate.opposition).toMonoidHom
  rw [map_conj_mul,map_conj_mul,map_conj_mul]
  have hoo : TwoConjugate.opposition (F := F)*TwoConjugate.opposition=1 := by
    nth_rw 1 [←TwoConjugate.opposition_inv]
    exact inv_mul_cancel _
  simpa only [TwoConjugate.opposition_inv,hoo,map_conj_one] using h

private theorem lower_shift (b : F) :
    (lowerPlane (F := F)).map (MulAut.conj (rootElement 6 b)).toMonoidHom = lowerPlane := by
  apply lower_normalizes
  rw [(opposition_short b).1]
  exact upper_lower b

private theorem lower_lower (b : F) :
    (lowerPlane (F := F)).map (MulAut.conj (rootElement 7 b)).toMonoidHom = lowerPlane := by
  apply lower_normalizes
  rw [(opposition_short b).2]
  exact upper_shift b

private theorem distinct_pair_standard (s t : Option F) (hst : s ≠ t) :
    ∃ g : Sp F,
      (upperPlane (F := F)).map (MulAut.conj g).toMonoidHom = upperPlane ∧
      (lowerPlane (F := F)).map (MulAut.conj g).toMonoidHom = lowerPlane ∧
      (rootImage s ⊔ rootImage t).map (MulAut.conj g).toMonoidHom =
        rootImage none ⊔ rootImage (some 0) := by
  cases s with
  | none =>
    cases t with
    | none => exact (hst rfl).elim
    | some t =>
      refine ⟨rootElement 6 t,upper_shift t,lower_shift t,?_⟩
      rw [Subgroup.map_sup,rootImage_none_shift,rootImage_shift,CharTwo.add_self_eq_zero]
  | some s =>
    cases t with
    | none =>
      refine ⟨rootElement 6 s,upper_shift s,lower_shift s,?_⟩
      rw [Subgroup.map_sup,rootImage_none_shift,rootImage_shift,CharTwo.add_self_eq_zero,sup_comm]
    | some t =>
      have hr : t+s ≠ 0 := by
        intro hh
        exact hst (congrArg some (CharTwo.add_eq_zero.mp hh).symm)
      refine ⟨rootElement 7 (t+s)⁻¹ * rootElement 6 s,?_,?_,?_⟩
      · rw [←map_conj_mul,upper_shift,upper_lower]
      · rw [←map_conj_mul,lower_shift,lower_lower]
      · rw [←map_conj_mul,Subgroup.map_sup,rootImage_shift,rootImage_shift,
          CharTwo.add_self_eq_zero,Subgroup.map_sup,rootImage_zero_lower,
          rootImage_inverse_lower _ hr,sup_comm]

private theorem first_root_opposition :
    (rootImage (none : Option F)).map (MulAut.conj TwoConjugate.opposition).toMonoidHom =
      RootSubgroup.group 1 := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨u,rfl⟩ := (SmallMovers.mem_rootImage_none z).mp hz
    have he : (element (0:F) u 0 0).val = rootElement 0 u := by
      simp [element,RootSubgroup.element_zero]
    change TwoConjugate.opposition * _ * TwoConjugate.opposition⁻¹ ∈ _
    rw [he,(TwoConjugate.opposition_central_axes u).1]
    exact subset_closure ⟨u,rfl⟩
  · intro hy
    obtain ⟨u,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hy
    refine ⟨(element 0 u 0 0).val,(SmallMovers.mem_rootImage_none _).mpr ⟨u,rfl⟩,?_⟩
    have he : (element (0:F) u 0 0).val = rootElement 0 u := by
      simp [element,RootSubgroup.element_zero]
    change TwoConjugate.opposition * _ * TwoConjugate.opposition⁻¹ = _
    rw [he,(TwoConjugate.opposition_central_axes u).1]

omit [Finite F] in
private theorem opposition_second (u : F) :
    TwoConjugate.opposition * rootElement 2 u * TwoConjugate.opposition⁻¹ = rootElement 3 u := by
  rw [TwoConjugate.opposition_inv]
  apply Subtype.ext
  change (TwoConjugate.opposition (F := F)).val * rootMatrix 2 u *
    (TwoConjugate.opposition (F := F)).val = rootMatrix 3 u
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [TwoConjugate.opposition,rootMatrix,Matrix.mul_apply,Fintype.sum_sum_type,
      Fin.sum_univ_two,Matrix.single,Matrix.fromBlocks]

omit [Finite F] in
private theorem second_root_opposition :
    (rootImage (some (0:F))).map (MulAut.conj TwoConjugate.opposition).toMonoidHom =
      RootSubgroup.group 3 := by
  ext y
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨u,rfl⟩ := (SmallMovers.mem_rootImage_some 0 z).mp hz
    have he : (element (0:F) (0^2*u) (0*u) u).val = rootElement 2 u := by
      simp [element,RootSubgroup.element_zero]
    change TwoConjugate.opposition * _ * TwoConjugate.opposition⁻¹ ∈ _
    rw [he,opposition_second]
    exact subset_closure ⟨u,rfl⟩
  · intro hy
    obtain ⟨u,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hy
    refine ⟨(element 0 (0^2*u) (0*u) u).val,(SmallMovers.mem_rootImage_some 0 _).mpr ⟨u,rfl⟩,?_⟩
    have he : (element (0:F) (0^2*u) (0*u) u).val = rootElement 2 u := by
      simp [element,RootSubgroup.element_zero]
    change TwoConjugate.opposition * _ * TwoConjugate.opposition⁻¹ = _
    rw [he,opposition_second]

private theorem lower_opposition :
    (lowerPlane (F := F)).map (MulAut.conj TwoConjugate.opposition).toMonoidHom = upperPlane := by
  change ((upperPlane (F := F)).map (MulAut.conj TwoConjugate.opposition).toMonoidHom).map
    (MulAut.conj TwoConjugate.opposition).toMonoidHom = _
  have hoo : TwoConjugate.opposition (F := F) * TwoConjugate.opposition = 1 := by
    nth_rw 1 [←TwoConjugate.opposition_inv]
    exact inv_mul_cancel _
  rw [map_conj_mul,hoo,map_conj_one]

/-- Every subgroup above q² in the opposite plane generates with the two
literal prescribed distinct full roots in the original upper plane. -/
theorem large_opposite_plane_and_prescribed_root_pair_generate
    (hq : 2 < Nat.card F) (A : Subgroup (Sp F))
    (hAP : A ≤ ((wing true).map (unipotent (F := F)).subtype).map
      (MulAut.conj TwoConjugate.opposition).toMonoidHom)
    (hcard : Nat.card F^2 < Nat.card A) (s t : Option F) (hst : s ≠ t) :
    (A ⊔ rootImage s) ⊔ rootImage t = ⊤ := by
  obtain ⟨g,hupper,hlower,hroots⟩ := distinct_pair_standard s t hst
  let o := TwoConjugate.opposition (F := F)
  let c := o*g
  have hplane : (lowerPlane (F := F)).map (MulAut.conj c).toMonoidHom = upperPlane := by
    rw [show c=o*g from rfl,←map_conj_mul,hlower]
    exact lower_opposition
  have hA : A.map (MulAut.conj c).toMonoidHom ≤ upperPlane := hplane ▸ map_mono hAP
  have hc : Nat.card F^2 < Nat.card (A.map (MulAut.conj c).toMonoidHom) := by
    rwa [card_map_of_injective (MulAut.conj c).injective]
  have hr : (rootImage s ⊔ rootImage t).map (MulAut.conj c).toMonoidHom =
      RootSubgroup.group 1 ⊔ RootSubgroup.group 3 := by
    rw [show c=o*g from rfl,←map_conj_mul,hroots,Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) first_root_opposition second_root_opposition
  apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
  rw [sup_assoc,Subgroup.map_sup,hr,map_top_of_surjective _ (MulAut.conj c).surjective,←sup_assoc]
  exact PrescribedLargePlaneGeneration.large_plane_and_prescribed_roots_generate hq _ hA hc

end Theory.SpecificGroups.SymplecticFour.PrescribedRootPairPlaneGeneration
