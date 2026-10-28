module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.NonrootCentralizer
public import Theory.SpecificGroups.SymplecticFour.InvolutionCentralizers.NormalForms
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent
public import Theory.SpecificGroups.SymplecticFour.Sylow.Normalizer

/-!
# Aligning a coefficient symplectic subgroup with the original flag

A conjugate of Sp4(K) containing a central upper-root product with two nonzero
parameters can be conjugated into coefficient position by an element of the
original Borel. The marked element descends to type c2 over K: the other two
involution normal forms remain root types after coefficient inclusion. Its
intrinsic c2 conjugacy then corrects the original conjugator, and the literal
ambient centralizer calculation forces the correction to normalize U.

The inverse images of U and B are their exact coefficient counterparts. This
works for binary and proper coefficient fields, and applies to the same
opposite pair used by Aschbacher--Smith E.2.7, printed p.220. Recognition of
that pair as a coefficient copy is a separate input.
-/

public noncomputable section
open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.TwoConjugate
open InvolutionTypes InvolutionCentralizers
open DiagramAutomorphisms.FieldFixedResidual
variable {F : Type*} [Field F]
local notation "a" => (Sum.inl (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "b" => (Sum.inl (1 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "c" => (Sum.inr (0 : Fin 2) : Fin 2 ⊕ Fin 2)
local notation "d" => (Sum.inr (1 : Fin 2) : Fin 2 ⊕ Fin 2)

private theorem coefficient_root (K : Subfield F) (r : Fin 8) (t : K) :
    coefficientInclusion K (rootElement r t) = rootElement r (t : F) := by
  apply Subtype.ext
  ext i j
  rw [coefficientInclusion_apply]
  change ((rootMatrix r t i j : K) : F) = rootMatrix r (t : F) i j
  fin_cases r <;> rcases i with i | i <;> rcases j with j | j <;>
    fin_cases i <;> fin_cases j <;> simp [rootMatrix, Matrix.fromBlocks, Matrix.single]

private theorem coefficient_upper [CharP F 2] (K : Subfield F) (s t : K) :
    coefficientInclusion K (upper s t) = upper (s : F) (t : F) := by
  simp only [upper, map_mul, coefficient_root]

private theorem upper_isC2 [CharP F 2] (s t : F) (hs : s ≠ 0) (ht : t ≠ 0) :
    IsC2 (upper s t) := by
  have hm : movedSpace (upper s t) = plane F := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      intro i
      fin_cases i <;> simp [upper_apply]
    · intro hx
      refine ⟨Sum.elim ![0,0] ![x b / t,(x a - s * (x b / t)) / t],?_⟩
      change upper s t • _ - _ = x
      rw [upper_apply]
      ext i
      rcases i with i | i <;> fin_cases i <;>
        simp [hx 0,hx 1] <;> field_simp
      all_goals ring
  refine ⟨upper_orderOf s t hs, ?_, ?_⟩
  · rw [hm,finrank_plane]
  · refine ⟨Pi.single c 1, ?_⟩
    simpa [form_apply,upper_apply,Fin.sum_univ_two,Pi.single_apply,CharTwo.neg_eq] using hs

private theorem isC2_of_coefficient [CharP F 2] (K : Subfield F)
    (g : Sp K) (hg : IsC2 (coefficientInclusion K g)) : IsC2 g := by
  have ho : orderOf g = 2 :=
    (orderOf_injective (coefficientInclusion K) (coefficientInclusion_injective K) g).symm.trans hg.1
  rcases involution_types g ho with hb | ha | hc
  · obtain ⟨h,t,ht,he⟩ := isB1_conjugate_root0 g hb
    have htF : (t : F) ≠ 0 := fun he => ht (Subtype.ext he)
    have hbF : IsB1 (coefficientInclusion K g) := by
      rw [he,map_mul,map_mul,map_inv,coefficient_root]
      exact (isB1_conj_iff _ _).mpr (root0_isB1 htF)
    have := hbF.2
    have := hg.2.1
    omega
  · obtain ⟨h,t,ht,he⟩ := isA2_conjugate_root4 g ha
    have htF : (t : F) ≠ 0 := fun he => ht (Subtype.ext he)
    have haF : IsA2 (coefficientInclusion K g) := by
      rw [he,map_mul,map_mul,map_inv,coefficient_root]
      exact (isA2_conj_iff _ _).mpr (root4_isA2 htF)
    obtain ⟨v,hv⟩ := hg.2.2
    exact (hv (haF.2.2 v)).elim
  · exact hc

private theorem conjugate_upper_one [Finite F] [CharP F 2]
    (g : Sp F) (hg : IsC2 g) :
    ∃ h : Sp F, g = h * upper (1:F) 1 * h⁻¹ := by
  obtain ⟨h,hh⟩ := isC2_conjugate_c2 g hg
  obtain ⟨k,hk⟩ := isC2_conjugate_c2 (upper (1:F) 1)
    (upper_isC2 1 1 one_ne_zero one_ne_zero)
  refine ⟨h*k⁻¹,?_⟩
  rw [hk,hh]
  group

private theorem centralizer_map_conj (g x : Sp F) :
    (centralizer ({x} : Set (Sp F))).map (MulAut.conj g).toMonoidHom =
      centralizer ({g*x*g⁻¹} : Set (Sp F)) := by
  let e := MulAut.conj g
  apply le_antisymm
  · simpa only [Set.image_singleton,MulEquiv.coe_toMonoidHom,e,MulAut.conj_apply] using
      map_centralizer_le_centralizer_image ({x} : Set (Sp F)) e.toMonoidHom
  · intro y hy
    refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simp only [map_mul,e.apply_symm_apply]
    exact mem_centralizer_singleton_iff.mp hy

/-- Correct a recognized coefficient copy to the original Borel using its
marked nonroot central involution. -/
theorem exists_borel_coefficient_alignment [Finite F] [CharP F 2]
    (K : Subfield F) (g : Sp F) (s t : F) (hs : s ≠ 0) (ht : t ≠ 0)
    (hz : upper s t ∈ (coefficientInclusion K).range.map (MulAut.conj g).toMonoidHom) :
    ∃ h : Sp F, h ∈ borel ∧
      (coefficientInclusion K).range.map (MulAut.conj g).toMonoidHom =
      (coefficientInclusion K).range.map (MulAut.conj h).toMonoidHom := by
  obtain ⟨_,⟨x,rfl⟩,hx⟩ := hz
  change g * coefficientInclusion K x * g⁻¹ = upper s t at hx
  have hc : IsC2 (coefficientInclusion K x) :=
    (isC2_conj_iff g _).mp (by rw [hx]; exact upper_isC2 s t hs ht)
  obtain ⟨k,hk⟩ := conjugate_upper_one x (isC2_of_coefficient K x hc)
  let h := g * coefficientInclusion K k
  have he : h * upper (1:F) 1 * h⁻¹ = upper s t := by
    rw [←hx,hk,map_mul,map_mul,map_inv,coefficient_upper]
    simp only [Subfield.coe_one]
    dsimp [h]
    group
  have hn : h ∈ normalizer (unipotent (F := F) : Set (Sp F)) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (unipotent (F := F)).map (MulAut.conj h).toMonoidHom = unipotent
    rw [←centralizer_upper_eq_unipotent 1 1 one_ne_zero one_ne_zero,
      centralizer_map_conj,he,centralizer_upper_eq_unipotent s t hs ht,
      centralizer_upper_eq_unipotent 1 1 one_ne_zero one_ne_zero]
  refine ⟨h,normalizer_unipotent_le_borel hn,?_⟩
  have hkN : coefficientInclusion K k ∈
      normalizer ((coefficientInclusion K).range : Set (Sp F)) :=
    le_normalizer ⟨k,rfl⟩
  have hm : (coefficientInclusion K).range.map
      (MulAut.conj (coefficientInclusion K k)).toMonoidHom =
      (coefficientInclusion K).range := mem_normalizer_iff_map_conj_eq.mp hkN
  have hcomp : (MulAut.conj g).toMonoidHom.comp
      (MulAut.conj (coefficientInclusion K k)).toMonoidHom =
      (MulAut.conj h).toMonoidHom := by
    ext y : 1
    change g * (coefficientInclusion K k * y * (coefficientInclusion K k)⁻¹) * g⁻¹ = h*y*h⁻¹
    dsimp [h]
    group
  conv_lhs => rw [←hm]
  rw [Subgroup.map_map,hcomp]

/-- Apply the alignment to the literal original opposite pair and its marked
nonroot central element. -/
theorem oppositePair_borel_coefficient_alignment [Finite F] [CharP F 2]
    (V : Subgroup (Sp F)) (K : Subfield F) (g : Sp F) (s t : F)
    (hs : s ≠ 0) (ht : t ≠ 0) (hz : upper s t ∈ V)
    (he : oppositePair V = (coefficientInclusion K).range.map (MulAut.conj g).toMonoidHom) :
    ∃ h : Sp F, h ∈ borel ∧
      oppositePair V = (coefficientInclusion K).range.map (MulAut.conj h).toMonoidHom := by
  have hz' : upper s t ∈ (coefficientInclusion K).range.map (MulAut.conj g).toMonoidHom :=
    he ▸ (show upper s t ∈ oppositePair V from
      (show V ≤ oppositePair V from le_sup_left) hz)
  obtain ⟨h,hh,hcopy⟩ := exists_borel_coefficient_alignment K g s t hs ht hz'
  exact ⟨h,hh,he.trans hcopy⟩

/-- The literal Borel conditions descend through coefficient inclusion. -/
theorem coefficient_comap_borel (K : Subfield F) :
    (borel (F := F)).comap (coefficientInclusion K) = borel (F := K) := by
  ext g
  simp only [mem_comap,mem_borel_iff,coefficientInclusion_apply]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨Subtype.ext ha,fun i j => Subtype.ext (hb i j)⟩
  · rintro ⟨ha,hb⟩
    exact ⟨congrArg (fun x : K => (x : F)) ha,
      fun i j => congrArg (fun x : K => (x : F)) (hb i j)⟩

/-- The literal unipotent conditions descend through coefficient inclusion. -/
theorem coefficient_comap_unipotent (K : Subfield F) :
    (unipotent (F := F)).comap (coefficientInclusion K) = unipotent (F := K) := by
  ext g
  change coefficientInclusion K g ∈ unipotent ↔ g ∈ unipotent
  rw [mem_unipotent_iff,mem_unipotent_iff]
  have hb : coefficientInclusion K g ∈ borel ↔ g ∈ borel :=
    SetLike.ext_iff.mp (coefficient_comap_borel K) g
  simp only [hb,coefficientInclusion_apply]
  constructor
  · rintro ⟨ha,hb,hc⟩
    exact ⟨ha,Subtype.ext hb,Subtype.ext hc⟩
  · rintro ⟨ha,hb,hc⟩
    exact ⟨ha,congrArg (fun x : K => (x : F)) hb,
      congrArg (fun x : K => (x : F)) hc⟩

/-- A Borel-aligned coefficient copy retains the original unipotent intersection. -/
theorem coefficient_conj_comap_unipotent (K : Subfield F)
    (h : Sp F) (hh : h ∈ borel) :
    (unipotent (F := F)).comap
      ((MulAut.conj h).toMonoidHom.comp (coefficientInclusion K)) = unipotent (F := K) := by
  have hn : h ∈ normalizer (unipotent (F := F) : Set (Sp F)) :=
    borel_le_normalizer_unipotent hh
  ext g
  change h * coefficientInclusion K g * h⁻¹ ∈ unipotent ↔ g ∈ unipotent
  rw [←mem_normalizer_iff.mp hn]
  exact SetLike.ext_iff.mp (coefficient_comap_unipotent K) g

/-- A Borel-aligned coefficient copy retains the original Borel intersection. -/
theorem coefficient_conj_comap_borel (K : Subfield F)
    (h : Sp F) (hh : h ∈ borel) :
    (borel (F := F)).comap
      ((MulAut.conj h).toMonoidHom.comp (coefficientInclusion K)) = borel (F := K) := by
  have hn : h ∈ normalizer (borel (F := F) : Set (Sp F)) := le_normalizer hh
  ext g
  change h * coefficientInclusion K g * h⁻¹ ∈ borel ↔ g ∈ borel
  rw [←mem_normalizer_iff.mp hn]
  exact SetLike.ext_iff.mp (coefficient_comap_borel K) g

end Theory.SpecificGroups.SymplecticFour.TwoConjugate
