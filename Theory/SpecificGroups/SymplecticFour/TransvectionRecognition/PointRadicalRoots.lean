module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.TransvectionProducts
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.FixedQuotient

/-!
# Transvections in the actual point radical

A transvection in the kernel of the point-local SL₂ quotient has moved
space equal to the fixed point. In radical coordinates (u,v,z), a nonzero
u or v already puts that point in the displacement image, while the opposite
basis vector has nonzero middle displacement. Rank one therefore forces
u=v=0, so the transvection is a central root. Conversely every nonzero central
coordinate is an actual b₁ transvection.

In particular a noncommuting pair cannot lose either transvection in the
literal quotient. These facts supply the radical/root step of the
three-center argument in Aschbacher--Smith G.4.9, printed p.341.
-/

public noncomputable section

open Subgroup Module
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes InvolutionCentralizers
variable {F : Type*} [Field F] [CharP F 2]

private theorem radical_move_e_one (u v z : F) :
    (pointRadicalElement u v z).val • e (F:=F) 1-e 1=v • e 0 := by
  ext i
  fin_cases i <;>
    simp [pointRadicalElement,pointRadicalMatrix,e,Matrix.mulVec_single]

private theorem radical_move_f_one (u v z : F) :
    (pointRadicalElement u v z).val • (Pi.single (.inr 1) (1:F) : Vector F)-Pi.single (.inr 1) 1=
      u • e 0 := by
  ext i
  fin_cases i <;>
    simp [pointRadicalElement,pointRadicalMatrix,e,Matrix.mulVec_single]

private theorem radical_move_f_zero (u v z : F) :
    (pointRadicalElement u v z).val • (Pi.single (.inr 0) (1:F) : Vector F)-Pi.single (.inr 0) 1=
      Sum.elim ![z,u] ![0,v] := by
  ext i
  fin_cases i <;>
    simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec_single]

/-- A rank-one element of the actual point radical is a central root. -/
theorem pointRadicalElement_coordinates_of_isB1 (u v z : F)
    (ht : IsB1 (pointRadicalElement u v z).val) : u=0 ∧ v=0 := by
  by_contra hn
  have hep : e (F:=F) 0∈movedSpace (pointRadicalElement u v z).val := by
    by_cases hu : u=0
    · have hv : v≠0 := by tauto
      have hm : v • e (F:=F) 0∈movedSpace (pointRadicalElement u v z).val :=
        ⟨e 1,radical_move_e_one u v z⟩
      exact (Submodule.smul_mem_iff _ hv).mp hm
    · have hm : u • e (F:=F) 0∈movedSpace (pointRadicalElement u v z).val :=
        ⟨Pi.single (.inr 1) 1,radical_move_f_one u v z⟩
      exact (Submodule.smul_mem_iff _ hu).mp hm
  have hpoint : point F=movedSpace (pointRadicalElement u v z).val := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      intro w hw
      have hw : w=e (F:=F) 0 := Set.mem_singleton_iff.mp hw
      rwa [hw]
    · exact finrank_point.trans ht.2.symm
  have hw : Sum.elim ![z,u] ![0,v]∈point F := by
    rw [hpoint]
    exact ⟨Pi.single (.inr 0) 1,radical_move_f_zero u v z⟩
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw
  have hu := congrFun hc (.inl 1)
  have hv := congrFun hc (.inr 1)
  exact hn ⟨by simpa [e] using hu.symm,by simpa [e] using hv.symm⟩

/-- Every actual radical transvection has the fixed point as moved line. -/
theorem pointRadical_movedSpace_of_isB1 (t : pointLocal (F:=F))
    (htQ : t∈pointRadical) (ht : IsB1 t.val) : movedSpace t.val=point F := by
  have he := pointRadical_eq_element t htQ
  rw [he] at ht ⊢
  obtain ⟨hu,hv⟩ := pointRadicalElement_coordinates_of_isB1 _ _ _ ht
  rw [hu,hv] at ht ⊢
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro w ⟨x,rfl⟩
    change (pointRadicalElement (F:=F) 0 0 _).val • x-x∈point F
    apply Submodule.mem_span_singleton.mpr
    refine ⟨t.val.val (.inl 0) (.inr 0) * x (.inr 0),?_⟩
    ext i
    fin_cases i <;>
      simp [pointRadicalElement,pointRadicalMatrix,Matrix.mulVec,
        dotProduct,Fintype.sum_sum_type,Fin.sum_univ_two,e]
  · exact ht.2.trans finrank_point.symm

/-- A transvection in the point radical centralizes the whole point-local group. -/
theorem pointRadical_transvection_central (t : pointLocal (F:=F))
    (htQ : t∈pointRadical) (ht : IsB1 t.val) : t∈Subgroup.center (pointLocal (F:=F)) := by
  have he := pointRadical_eq_element t htQ
  rw [he] at ht ⊢
  obtain ⟨hu,hv⟩ := pointRadicalElement_coordinates_of_isB1 _ _ _ ht
  rw [hu,hv]
  exact pointRadicalElement_central _

/-- The noncommuting first pair in G.4.9 survives in the literal SL₂ quotient. -/
theorem pointQuotient_ne_one_of_isB1_noncommuting (a b : pointLocal (F:=F))
    (ha : IsB1 a.val) (hab : ¬Commute a b) : pointQuotient a≠1 := by
  intro hq
  have haQ : a∈pointRadical := hq
  have hc := pointRadical_transvection_central a haQ ha
  exact hab ((Subgroup.mem_center_iff.mp hc) b).symm

/-- Every nonidentity element of the central radical coordinate is a transvection. -/
theorem pointRadicalElement_isB1 {z : F} (hz : z≠0) :
    IsB1 (pointRadicalElement (F:=F) 0 0 z).val := by
  have he : (pointRadicalElement (F:=F) 0 0 z).val=
      Representation.OneCohomology.SymplecticFour.rootElement 0 z := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pointRadicalElement,pointRadicalMatrix,
        Representation.OneCohomology.SymplecticFour.rootElement,
        Representation.OneCohomology.SymplecticFour.rootMatrix,Matrix.single]
  rw [he]
  exact root0_isB1 hz

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
