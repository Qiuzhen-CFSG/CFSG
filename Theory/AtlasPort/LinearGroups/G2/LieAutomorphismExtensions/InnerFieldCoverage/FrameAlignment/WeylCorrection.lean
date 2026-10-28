module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.RootFrame
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.SylowAlignment

/-!
# Simultaneous correction of the two Weyl reflections

The Weyl matrices normalize the actual split torus. If an abstract
automorphism sends each to its own torus coset, their order-two relations
force the forms `torus 1 r * R` and `torus s s⁻¹ * S`. Conjugating by
`torus (r⁻¹*s⁻¹^2) (r⁻¹*s⁻¹)` fixes both at once. This calculation works
over every field and requires no extraction of roots.

`RankOneTorusNormalizerCover` states the remaining concrete normalizer
calculation used by the frame-alignment assembly. It is a property to prove
for each labelled parabolic, not an assumed property of the G₂ model.

Source context: the G₂ automorphism input in Aschbacher--Smith F.1.12,
printed pp.263--264. The torus and Weyl matrices are from the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Atlas.SplitOctonion Atlas.G2.Explicit Subgroup
namespace Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
variable {F : Type*} [Field F]

/-- Inside a specified parabolic, the torus normalizer has just the torus
and the coset of its specified Weyl reflection. -/
@[expose] def RankOneTorusNormalizerCover (P : Subgroup (Model F)) (w : Model F) : Prop :=
  ∀ g : Model F, g ∈ P → g ∈ normalizer (splitTorus (K := F) : Set (Model F)) →
    g ∈ splitTorus ∨ ∃ l m : Fˣ, g = torus l m * w

private theorem weylR_torus (l m : Fˣ) :
    weylR * torus l m * weylR⁻¹ = torus l (l*m⁻¹) := by
  rw [weylR_inverse]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,
      weylR,weylREquiv,weylRLinear,weylRApply]
  field_simp
  simp

private theorem weylS_torus (l m : Fˣ) :
    weylS * torus l m * weylS⁻¹ = torus m l := by
  rw [weylS_inverse]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [torus,torusEquiv,torusLinear,torusWeights,
      weylS,weylSEquiv,weylSLinear,weylSApply] <;> field_simp
  all_goals simp

theorem weylR_mem_torusNormalizer : (weylR : Model F) ∈ normalizer (splitTorus (K := F) : Set (Model F)) := by
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨⟨l,m⟩,rfl⟩
    exact ⟨(l,l*m⁻¹), (weylR_torus l m).symm⟩
  · intro hx
    have hRR : (weylR : Model F)*weylR = 1 := by rw [← pow_two, weylR_sq]
    obtain ⟨⟨l,m⟩,he⟩ := hx
    have hh : weylR * (weylR * x * weylR⁻¹) * weylR⁻¹ = x := by
      calc
        _ = (weylR*weylR)*x*(weylR*weylR)⁻¹ := by group
        _ = x := by rw [hRR]; simp
    rw [← he] at hh
    change weylR * torus l m * weylR⁻¹ = x at hh
    rw [weylR_torus] at hh
    exact ⟨(l,l*m⁻¹), hh⟩

theorem weylS_mem_torusNormalizer : (weylS : Model F) ∈ normalizer (splitTorus (K := F) : Set (Model F)) := by
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨⟨l,m⟩,rfl⟩
    exact ⟨(m,l), (weylS_torus l m).symm⟩
  · intro hx
    have hSS : (weylS : Model F)*weylS = 1 := by rw [← pow_two, weylS_sq]
    obtain ⟨⟨l,m⟩,he⟩ := hx
    have hh : weylS * (weylS * x * weylS⁻¹) * weylS⁻¹ = x := by
      calc
        _ = (weylS*weylS)*x*(weylS*weylS)⁻¹ := by group
        _ = x := by rw [hSS]; simp
    rw [← he] at hh
    change weylS * torus l m * weylS⁻¹ = x at hh
    rw [weylS_torus] at hh
    exact ⟨(m,l), hh⟩

theorem weylR_not_mem_torus : (weylR : Model F) ∉ splitTorus := by
  rintro ⟨⟨l,m⟩,h⟩
  have he := congrArg (fun g : Model F => g.val (basisVector 1) 2) h
  simp [torusHom,torus,torusEquiv,torusLinear,torusWeights,
    weylR,weylREquiv,weylRLinear,weylRApply,basisVector] at he

theorem weylS_not_mem_torus : (weylS : Model F) ∉ splitTorus := by
  rintro ⟨⟨l,m⟩,h⟩
  have he := congrArg (fun g : Model F => g.val (basisVector 0) 1) h
  simp [torusHom,torus,torusEquiv,torusLinear,torusWeights,
    weylS,weylSEquiv,weylSLinear,weylSApply,basisVector] at he

private theorem torus_weylR_square (l m : Fˣ) :
    (torus l m * weylR)^2 = torus (l*l) l := by
  have hRR : (weylR : Model F)*weylR = 1 := by rw [← pow_two, weylR_sq]
  calc
    _ = torus l m * (weylR*torus l m*weylR⁻¹) * (weylR*weylR) := by rw [pow_two]; group
    _ = torus (l*l) l := by
      rw [weylR_torus,hRR,mul_one,torus_product]
      congr 1
      simp [mul_left_comm]

private theorem torus_weylS_square (l m : Fˣ) :
    (torus l m * weylS)^2 = torus (l*m) (m*l) := by
  have hSS : (weylS : Model F)*weylS = 1 := by rw [← pow_two, weylS_sq]
  calc
    _ = torus l m * (weylS*torus l m*weylS⁻¹) * (weylS*weylS) := by rw [pow_two]; group
    _ = torus (l*m) (m*l) := by rw [weylS_torus,hSS,mul_one,torus_product]

private theorem correct_weylR (r s : Fˣ) :
    MulAut.conj (torus (r⁻¹*s⁻¹^2) (r⁻¹*s⁻¹)) (torus 1 r * weylR) = weylR := by
  calc
    _ = torus (r⁻¹*s⁻¹^2) (r⁻¹*s⁻¹) * torus 1 r *
        (weylR * (torus (r⁻¹*s⁻¹^2) (r⁻¹*s⁻¹))⁻¹ * weylR⁻¹) * weylR := by
      simp only [MulAut.conj_apply]
      group
    _ = weylR := by
      rw [torus_inverse, weylR_torus, torus_product, torus_product]
      have h1 : (r⁻¹*s⁻¹^2) * 1 * (r⁻¹*s⁻¹^2)⁻¹ = 1 := by group
      have h2 : (r⁻¹*s⁻¹) * r * ((r⁻¹*s⁻¹^2)⁻¹ * (r⁻¹*s⁻¹)⁻¹⁻¹) = 1 := by
        group
        simp [mul_right_comm]
      rw [h1,h2]
      change torusHom (1,1) * weylR = weylR
      rw [show (1,1) = (1 : Fˣ × Fˣ) from rfl, map_one, one_mul]

private theorem correct_weylS (r s : Fˣ) :
    MulAut.conj (torus (r⁻¹*s⁻¹^2) (r⁻¹*s⁻¹)) (torus s s⁻¹ * weylS) = weylS := by
  calc
    _ = torus (r⁻¹*s⁻¹^2) (r⁻¹*s⁻¹) * torus s s⁻¹ *
        (weylS * (torus (r⁻¹*s⁻¹^2) (r⁻¹*s⁻¹))⁻¹ * weylS⁻¹) * weylS := by
      simp only [MulAut.conj_apply]
      group
    _ = weylS := by
      rw [torus_inverse, weylS_torus, torus_product, torus_product]
      have h1 : (r⁻¹*s⁻¹^2) * s * (r⁻¹*s⁻¹)⁻¹ = 1 := by group
      have h2 : (r⁻¹*s⁻¹) * s⁻¹ * (r⁻¹*s⁻¹^2)⁻¹ = 1 := by group
      rw [h1,h2]
      change torusHom (1,1) * weylS = weylS
      rw [show (1,1) = (1 : Fˣ × Fˣ) from rfl, map_one, one_mul]

/-- The two actual Weyl images can be corrected simultaneously by one split-torus element. -/
theorem exists_torus_weyl_correction (a : MulAut (Model F))
    (hR : ∃ l m : Fˣ, a weylR = torus l m * weylR)
    (hS : ∃ l m : Fˣ, a weylS = torus l m * weylS) :
    ∃ t : Model F, t ∈ splitTorus ∧
      (MulAut.conj t * a) weylR = weylR ∧ (MulAut.conj t * a) weylS = weylS := by
  obtain ⟨l,r,hR⟩ := hR
  obtain ⟨s,m,hS⟩ := hS
  have hl : l = 1 := by
    have he : torus (l*l) l = 1 := by
      rw [← torus_weylR_square, ← hR, ← map_pow, weylR_sq, map_one]
    have hh : torusHom (l*l,l) = torusHom (1,1) := he.trans (torusHom.map_one).symm
    exact congrArg Prod.snd (torusHom_injective hh)
  have hm : m = s⁻¹ := by
    have he : torus (s*m) (m*s) = 1 := by
      rw [← torus_weylS_square, ← hS, ← map_pow, weylS_sq, map_one]
    have hh : torusHom (s*m,m*s) = torusHom (1,1) := he.trans (torusHom.map_one).symm
    exact eq_inv_of_mul_eq_one_right (congrArg Prod.fst (torusHom_injective hh))
  refine ⟨torus (r⁻¹*s⁻¹^2) (r⁻¹*s⁻¹), ⟨(r⁻¹*s⁻¹^2, r⁻¹*s⁻¹),rfl⟩, ?_, ?_⟩
  · change MulAut.conj _ (a weylR) = weylR
    rw [hR,hl]
    exact correct_weylR r s
  · change MulAut.conj _ (a weylS) = weylS
    rw [hS,hm]
    exact correct_weylS r s
end Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
