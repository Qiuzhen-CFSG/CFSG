module

public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelFourShearRestrictions
public import Theory.SpecificGroups.PSL3.SmallCompletion.BorelSemilinearExtension

/-!
# Whole-Borel twist factorization for the native PSL₃(4) amalgam

Every automorphism of the literal Borel preserving its two ordered elementary
radicals factors through automorphisms of the actual point and line endpoints.
The proof aligns the full cubic torus, derives the original coordinate normal
form, and realizes each factor by a genuine endpoint automorphism.
No factorization or compatibility premise is assumed. This result concerns
the amalgam; it asserts no mixed-word relation in an arbitrary completion.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.LinearAmbientGeometry Matrix.PSL3Even.UnipotentGeometry
open Representation.SL2FourNatural Theory.GroupTheory.RankTwoAmalgam

private theorem semilinear_restriction (r s : Fˣ) (σ : F ≃+* F) :
    ∃ d : MulAut (borel F), ExtendsAcross pointBorelInclusion d ∧
      ExtendsAcross lineBorelInclusion d ∧
      (∀ u : U F, d (borelUnipotent F u)=
        borelUnipotent F ⟨r*σ u.x,s*σ u.y,(r:F)*s*σ u.c⟩) ∧
      ∀ t : Fˣ, d (simultaneousTorus F t)=
        simultaneousTorus F (Units.map σ.toMonoidHom t) := by
  let A := rootSemilinearActor F r s σ
  obtain ⟨hP,hL,hB⟩ := rootSemilinearActor_endpoints F r s σ
  let d : MulAut (borel F) := (A.subgroupMap (borel F)).trans (MulEquiv.subgroupCongr hB)
  let p : MulAut (pointLocal F) :=
    (A.subgroupMap (pointLocal F)).trans (MulEquiv.subgroupCongr hP)
  let l : MulAut (lineLocal F) :=
    (A.subgroupMap (lineLocal F)).trans (MulEquiv.subgroupCongr hL)
  refine ⟨d,⟨p,fun _ => Subtype.ext rfl⟩,⟨l,fun _ => Subtype.ext rfl⟩,?_,?_⟩
  · intro u
    apply Subtype.ext
    exact rootSemilinearActor_unipotent F r s σ u
  · intro t
    apply Subtype.ext
    exact rootSemilinearActor_torus F r s σ t

private theorem aligned_factorization (a : MulAut (borel F))
    (h₁ : ∀ u∈V₁ F,a (borelUnipotent F u)∈(V₁ F).map (borelUnipotent F))
    (h₂ : ∀ u∈V₂ F,a (borelUnipotent F u)∈(V₂ F).map (borelUnipotent F))
    (hT : ∀ t∈borelTorus F,a t∈borelTorus F) :
    FactorsThrough fieldFourBorelAmalgam a := by
  obtain ⟨r,s,k,l,σ,hr,hs,haU,haT⟩ := borel_four_torus_normal_form F
    (by rw [Nat.card_eq_fintype_card,card_field]) a h₁ h₂ hT
  obtain ⟨H,hHP,hHL,hHU,hHT⟩ := semilinear_restriction (Units.mk0 r hr) (Units.mk0 s hs) σ
  obtain ⟨L,hL,hLU,hLT⟩ := exists_line_shear_restriction (k/r^2)
  obtain ⟨P,hP,hPU,hPT⟩ := exists_point_shear_restriction (l/s^2)
  have hU (u : U F) : a (borelUnipotent F u)=(L*(P*H)) (borelUnipotent F u) := by
    rw [haU,MulAut.mul_apply,MulAut.mul_apply,hHU,hPU,hLU]
    apply congrArg (borelUnipotent F)
    apply U.ext
    · rfl
    · rfl
    · change r*s*σ u.c+k*(σ u.x)^2+l*(σ u.y)^2=
        r*s*σ u.c+(l/s^2)*(s*σ u.y)^2+(k/r^2)*(r*σ u.x)^2
      field_simp
      ring
  have hT' (t : Fˣ) : a (simultaneousTorus F t)=(L*(P*H)) (simultaneousTorus F t) := by
    rw [haT,MulAut.mul_apply,MulAut.mul_apply,hHT,hPT,hLT]
  have he : a=L*(P*H) := by
    ext b
    obtain ⟨u,t,rfl⟩ := borel_four_factorization b
    rw [map_mul,map_mul,hU,hT']
  refine ⟨P*H,L.symm,?_,?_,?_⟩
  · exact (extensionSubgroup pointBorelInclusion).mul_mem hP hHP
  · exact (extensionSubgroup lineBorelInclusion).inv_mem hL
  · change a=L*(P*H)
    exact he

private theorem inner_preserves_planes (b : borel F) :
    (∀ u∈V₁ F, b*borelUnipotent F u*b⁻¹∈(V₁ F).map (borelUnipotent F)) ∧
    (∀ u∈V₂ F, b*borelUnipotent F u*b⁻¹∈(V₂ F).map (borelUnipotent F)) := by
  obtain ⟨v,t,rfl⟩ := borel_four_factorization b
  have he (u : U F) :
      (borelUnipotent F v*simultaneousTorus F t)*borelUnipotent F u*
        (borelUnipotent F v*simultaneousTorus F t)⁻¹ =
      borelUnipotent F (v*⟨t*u.x,t*u.y,(t:F)^2*u.c⟩*v⁻¹) := by
    rw [map_mul,map_mul,map_inv,←simultaneousTorus_conj]
    group
  constructor
  · intro u hu
    rw [he]
    apply mem_map_of_mem
    rw [mem_V₁] at hu ⊢
    simp [mul_y,hu,show (v⁻¹).y = -v.y from rfl]
  · intro u hu
    rw [he]
    apply mem_map_of_mem
    rw [mem_V₂] at hu ⊢
    simp [mul_x,hu,show (v⁻¹).x = -v.x from rfl]

private theorem inner_extends {L : Type*} [Group L] (i : borel F →* L) (b : borel F) :
    ExtendsAcross i (MulAut.conj b) :=
  ⟨MulAut.conj (i b),fun x => by simp only [MulAut.conj_apply,map_mul,map_inv]⟩

/-- Every ordered-radical-preserving twist of the original whole Borel is
removed by actual endpoint automorphisms, including the complete cubic torus. -/
theorem ordered_borel_twist_factors (a : MulAut (borel F))
    (h₁ : ∀ u∈V₁ F,a (borelUnipotent F u)∈(V₁ F).map (borelUnipotent F))
    (h₂ : ∀ u∈V₂ F,a (borelUnipotent F u)∈(V₂ F).map (borelUnipotent F)) :
    FactorsThrough fieldFourBorelAmalgam a := by
  obtain ⟨b,hb⟩ := exists_borel_torus_alignment F (n:=2)
    (by rw [Nat.card_eq_fintype_card,card_field]; norm_num) a
  let c := MulAut.conj b
  let d := c*a
  have hd₁ (u : U F) (hu : u∈V₁ F) : d (borelUnipotent F u)∈(V₁ F).map (borelUnipotent F) := by
    obtain ⟨v,hv,hv'⟩ := h₁ u hu
    change b*a (borelUnipotent F u)*b⁻¹∈_
    rw [←hv']
    exact (inner_preserves_planes b).1 v hv
  have hd₂ (u : U F) (hu : u∈V₂ F) : d (borelUnipotent F u)∈(V₂ F).map (borelUnipotent F) := by
    obtain ⟨v,hv,hv'⟩ := h₂ u hu
    change b*a (borelUnipotent F u)*b⁻¹∈_
    rw [←hv']
    exact (inner_preserves_planes b).2 v hv
  have hdT (t : borel F) (ht : t∈borelTorus F) : d t∈borelTorus F := by
    rw [←hb]
    exact mem_map_of_mem c.toMonoidHom (mem_map_of_mem a.toMonoidHom ht)
  obtain ⟨l,r,hl,hr,hd⟩ := aligned_factorization d hd₁ hd₂ hdT
  refine ⟨l,r*c,hl,(extensionSubgroup lineBorelInclusion).mul_mem hr
    (inner_extends lineBorelInclusion b),?_⟩
  have he : c*a=r⁻¹*l := hd
  change a=(r*c)⁻¹*l
  calc
    a=c⁻¹*(c*a) := by group
    _=c⁻¹*(r⁻¹*l) := by rw [he]
    _=(r*c)⁻¹*l := by group

end Matrix.PSL3.SmallCompletion
