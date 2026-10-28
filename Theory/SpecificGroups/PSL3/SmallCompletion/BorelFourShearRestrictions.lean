module

public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourEndpointInclusions

/-!
# Genuine whole-Borel restrictions of the two endpoint shears

The two endpoint automorphisms preserve the complete original Borel,
including its cubic torus. Their actual restrictions therefore extend
through the corresponding literal endpoint inclusions.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.LinearAmbientGeometry Matrix.PSL3Even.UnipotentGeometry
open Representation.SL2FourNatural Theory.GroupTheory.RankTwoAmalgam

private theorem restrict_of_range {B L : Type*} [Group B] [Group L] [Finite B]
    (i : B →* L) (hi : Function.Injective i) (a : MulAut L)
    (ha : ∀ b : B, ∃ c : B, a (i b)=i c) :
    ∃ d : MulAut B, ∀ b : B, a (i b)=i (d b) := by
  let e := MonoidHom.ofInjective hi
  have hm : i.range.map a.toMonoidHom=i.range := by
    let : Finite i.range := Finite.of_equiv B e.toEquiv
    apply eq_of_le_of_card_ge
    · rintro _ ⟨_,⟨b,rfl⟩,rfl⟩
      obtain ⟨c,hc⟩ := ha b
      exact ⟨c,hc.symm⟩
    · rw [←Nat.card_congr (i.range.equivMapOfInjective a.toMonoidHom a.injective).toEquiv]
  let d : MulAut B := e.trans ((a.subgroupMap i.range).trans ((MulEquiv.subgroupCongr hm).trans e.symm))
  refine ⟨d,fun b => ?_⟩
  change a (i b)=((e (e.symm _)) : L)
  rw [e.apply_symm_apply]
  rfl

private theorem line_inclusion_unipotent (u : U F) :
    lineBorelInclusion (borelUnipotent F u)=lineUnipotent u := Subtype.ext rfl
private theorem point_inclusion_unipotent (u : U F) :
    pointBorelInclusion (borelUnipotent F u)=pointUnipotent u := Subtype.ext rfl
private theorem line_inclusion_torus (t : Fˣ) :
    lineBorelInclusion (simultaneousTorus F t)=lineTorus t :=
  Subtype.ext (lineTorus_val t).symm
private theorem point_inclusion_torus (t : Fˣ) :
    pointBorelInclusion (simultaneousTorus F t)=pointTorus t :=
  Subtype.ext (pointTorus_val t).symm

/-- The first shear is an actual restriction from the entire line endpoint. -/
theorem exists_line_shear_restriction (k : F) :
    ∃ d : MulAut (borel F), ExtendsAcross lineBorelInclusion d ∧
      (∀ u : U F, d (borelUnipotent F u)=borelUnipotent F ⟨u.x,u.y,u.c+k*u.x^2⟩) ∧
      ∀ t : Fˣ, d (simultaneousTorus F t)=simultaneousTorus F t := by
  have he : ∀ b : borel F, ∃ c : borel F,
      lineCentralCorrection k (lineBorelInclusion b)=lineBorelInclusion c := by
    intro b
    obtain ⟨u,t,rfl⟩ := borel_four_factorization b
    refine ⟨borelUnipotent F ⟨u.x,u.y,u.c+k*u.x^2⟩*simultaneousTorus F t,?_⟩
    simp only [map_mul,line_inclusion_unipotent,line_inclusion_torus,
      lineCentralCorrection_unipotent,lineCentralCorrection_torus]
  obtain ⟨d,hd⟩ := restrict_of_range lineBorelInclusion (inclusion_injective _)
    (lineCentralCorrection k) he
  refine ⟨d,⟨lineCentralCorrection k,hd⟩,?_,?_⟩
  · intro u
    apply (show Function.Injective lineBorelInclusion from inclusion_injective _)
    rw [←hd,line_inclusion_unipotent,lineCentralCorrection_unipotent,line_inclusion_unipotent]
  · intro t
    apply (show Function.Injective lineBorelInclusion from inclusion_injective _)
    rw [←hd,line_inclusion_torus,lineCentralCorrection_torus]

/-- The second shear is an actual restriction from the entire point endpoint. -/
theorem exists_point_shear_restriction (k : F) :
    ∃ d : MulAut (borel F), ExtendsAcross pointBorelInclusion d ∧
      (∀ u : U F, d (borelUnipotent F u)=borelUnipotent F ⟨u.x,u.y,u.c+k*u.y^2⟩) ∧
      ∀ t : Fˣ, d (simultaneousTorus F t)=simultaneousTorus F t := by
  have he : ∀ b : borel F, ∃ c : borel F,
      pointCentralCorrection k (pointBorelInclusion b)=pointBorelInclusion c := by
    intro b
    obtain ⟨u,t,rfl⟩ := borel_four_factorization b
    refine ⟨borelUnipotent F ⟨u.x,u.y,u.c+k*u.y^2⟩*simultaneousTorus F t,?_⟩
    simp only [map_mul,point_inclusion_unipotent,point_inclusion_torus,
      pointCentralCorrection_unipotent,pointCentralCorrection_torus]
  obtain ⟨d,hd⟩ := restrict_of_range pointBorelInclusion (inclusion_injective _)
    (pointCentralCorrection k) he
  refine ⟨d,⟨pointCentralCorrection k,hd⟩,?_,?_⟩
  · intro u
    apply (show Function.Injective pointBorelInclusion from inclusion_injective _)
    rw [←hd,point_inclusion_unipotent,pointCentralCorrection_unipotent,point_inclusion_unipotent]
  · intro t
    apply (show Function.Injective pointBorelInclusion from inclusion_injective _)
    rw [←hd,point_inclusion_torus,pointCentralCorrection_torus]

end Matrix.PSL3.SmallCompletion
