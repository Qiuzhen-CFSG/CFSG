module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Factors
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Internal
public import Theory.Representation.BinaryOffender.Stability

/-!
# Ambient conjugation of the solvable FF factors

The actual factors in `SolvableFFFactors` are permuted by ambient conjugation.
Their product is the normal offender subgroup. In coordinates, a normal copy
of SL₂(2) in a product of copies of SL₂(2) is one coordinate factor: every
coordinate image is normal, and an endomorphism of SL₂(2) with normal image is
trivial or bijective. A faithful coordinate then makes all other coordinates
central, hence trivial. The elementary SL₂(2) facts are checked on its six
elements. Transport through the specified internal product gives equality of
actual subgroups, and their distinctness gives the permutation homomorphism.

This is conditional on the concrete B.1.8(1)–(2) witness, independently of the
B.1.8(4) offender-product classification. It supplies the assertion that the
ambient group permutes those factors in the proof of B.1.12.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.1.8,
printed p. 70 (PDF p. 81), and B.1.12, printed p. 73 (PDF p. 84).
-/

public section

open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors

private abbrev SL := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private theorem involution_words : ∀ t : SL, t ≠ 1 → t ^ 2 = 1 →
    ∃ g : SL, ∀ x : SL,
      let u := g * t * g⁻¹
      x = 1 ∨ x = t ∨ x = u ∨ x = t * u ∨ x = u * t ∨ x = t * u * t := by
  decide

private theorem exists_involution : ∃ t : SL, t ≠ 1 ∧ t ^ 2 = 1 := by decide

private theorem centerless : ∀ x : SL, (∀ y : SL, y * x = x * y) → x = 1 := by
  decide

private theorem normal_contains_involution (K : Subgroup SL) (hn : K.Normal)
    {t : SL} (ht : t ∈ K) (hne : t ≠ 1) (htwo : t ^ 2 = 1) : K = ⊤ := by
  obtain ⟨g, hg⟩ := involution_words t hne htwo
  have hu : g * t * g⁻¹ ∈ K := hn.conj_mem t ht g
  apply top_unique
  intro x _
  rcases hg x with h | h | h | h | h | h
  · exact h ▸ K.one_mem
  · exact h ▸ ht
  · exact h ▸ hu
  · exact h ▸ K.mul_mem ht hu
  · exact h ▸ K.mul_mem hu ht
  · exact h ▸ K.mul_mem (K.mul_mem ht hu) ht

private theorem normal_endomorphism (f : SL →* SL) (hn : f.range.Normal) :
    (∀ x, f x = 1) ∨ Function.Bijective f := by
  obtain ⟨t, ht, ht2⟩ := exists_involution
  by_cases hft : f t = 1
  · left
    have hk : f.ker = ⊤ := normal_contains_involution f.ker inferInstance hft ht ht2
    intro x
    exact show x ∈ f.ker from hk ▸ Subgroup.mem_top x
  · right
    have hr : f.range = ⊤ := normal_contains_involution f.range hn
      ⟨t, rfl⟩ hft (by rw [← map_pow, ht2, map_one])
    have hs : Function.Surjective f := MonoidHom.range_eq_top.mp hr
    exact ⟨Finite.injective_iff_surjective.mpr hs, hs⟩

private theorem normal_embedding_coordinate {I : Type*} [DecidableEq I]
    (f : SL →* (I → SL)) (hf : Function.Injective f) (hn : f.range.Normal) :
    ∃ i : I, f.range = (MonoidHom.mulSingle (fun _ : I => SL) i).range := by
  classical
  obtain ⟨t, ht, _⟩ := exists_involution
  obtain ⟨i, hi⟩ : ∃ i, f t i ≠ 1 := by
    by_contra h
    push Not at h
    apply ht
    apply hf
    rw [map_one]
    exact funext h
  let p (j : I) : SL →* SL := (Pi.evalMonoidHom (fun _ : I => SL) j).comp f
  have hn' : (p i).range.Normal := by
    rw [MonoidHom.range_comp]
    exact hn.map _ (fun x => ⟨fun _ => x, rfl⟩)
  obtain htriv | hp := normal_endomorphism (p i) hn'
  · exact (hi (htriv t)).elim
  have hs : ∀ x, f x = Pi.mulSingle i (f x i) := by
    intro x
    have hz : ∀ j, j ≠ i → f x j = 1 := by
      intro j hji
      apply centerless
      intro y
      have hm := hn.conj_mem (f x) ⟨x, rfl⟩ (Pi.mulSingle j y)
      obtain ⟨u, hu⟩ := hm
      have hui : u = x := by
        apply hp.1
        change f u i = f x i
        simpa [Ne.symm hji] using congrFun hu i
      subst u
      have he : y * f x j * y⁻¹ = f x j := by
        simpa using (congrFun hu j).symm
      exact mul_inv_eq_iff_eq_mul.mp he
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji, hz j hji]
  refine ⟨i, ?_⟩
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨f a i, (hs a).symm⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hp.2 a
    exact ⟨b, (hs b).trans (congrArg (Pi.mulSingle i) hb)⟩

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

private noncomputable def modelProduct : (Fin d.count → SL) ≃* offenderSubgroup ρ :=
  (MulEquiv.piCongrRight d.factorModel).symm.trans d.groupProduct

private theorem modelProduct_single (i : Fin d.count) (x : SL) :
    (d.modelProduct (Pi.mulSingle i x) : G) = ((d.factorModel i).symm x : G) := by
  change (d.groupProduct ((MulEquiv.piCongrRight d.factorModel).symm
    (Pi.mulSingle i x)) : G) = _
  have he : (MulEquiv.piCongrRight d.factorModel).symm (Pi.mulSingle i x) =
      Pi.mulSingle i ((d.factorModel i).symm x) := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  rw [he, d.groupProduct_single]

/-- Ambient conjugation sends each actual internal factor to another factor.
The recognition uses only the concrete internal product, and does not assume
an offender classification or ambient normality of any individual factor. -/
theorem exists_factor_map_conj (g : G) (i : Fin d.count) :
    ∃ j : Fin d.count, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j := by
  classical
  let := offenderSubgroup_normal ρ
  let e := d.modelProduct
  let c : MulAut (Fin d.count → SL) := e.trans ((MulAut.conjNormal g).trans e.symm)
  let s := MonoidHom.mulSingle (fun _ : Fin d.count => SL)
  have hn (k : Fin d.count) : (s k).range.Normal := by
    refine ⟨?_⟩
    rintro x ⟨a, rfl⟩ y
    refine ⟨y k * a * (y k)⁻¹, ?_⟩
    ext j
    by_cases hj : j = k
    · subst j
      simp [s]
    · simp [s, hj]
  let f := c.toMonoidHom.comp (s i)
  have hfn : f.range.Normal := by
    rw [MonoidHom.range_comp]
    exact (hn i).map _ c.surjective
  obtain ⟨j, hj⟩ := normal_embedding_coordinate f
    (c.injective.comp (Pi.mulSingle_injective (M := fun _ : Fin d.count => SL) i)) hfn
  let inc : (Fin d.count → SL) →* G := (offenderSubgroup ρ).subtype.comp e.toMonoidHom
  have hi (k : Fin d.count) : (s k).range.map inc = d.factor k := by
    ext x
    constructor
    · rintro ⟨a, ⟨b, rfl⟩, rfl⟩
      change (d.modelProduct (Pi.mulSingle k b) : G) ∈ d.factor k
      rw [d.modelProduct_single]
      exact Subtype.property _
    · intro hx
      refine ⟨s k (d.factorModel k ⟨x, hx⟩), ⟨_, rfl⟩, ?_⟩
      change (d.modelProduct (Pi.mulSingle k (d.factorModel k ⟨x, hx⟩)) : G) = x
      rw [d.modelProduct_single, MulEquiv.symm_apply_apply]
  have hc : inc.comp c.toMonoidHom = (MulAut.conj g).toMonoidHom.comp inc := by
    ext x
    simp [inc, c, MulAut.conjNormal_apply, MulAut.conj_apply]
  refine ⟨j, ?_⟩
  rw [← hi i, Subgroup.map_map, ← hc, ← Subgroup.map_map, ← MonoidHom.range_comp]
  change f.range.map inc = d.factor j
  rw [hj]
  exact hi j

private noncomputable def conjugateIndex (g : G) (i : Fin d.count) : Fin d.count :=
  Classical.choose (d.exists_factor_map_conj g i)

private theorem conjugateIndex_spec (g : G) (i : Fin d.count) :
    (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor (d.conjugateIndex g i) :=
  Classical.choose_spec (d.exists_factor_map_conj g i)

private theorem conjugateIndex_one (i : Fin d.count) : d.conjugateIndex 1 i = i := by
  apply d.factor_injective
  rw [← d.conjugateIndex_spec]
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private theorem conjugateIndex_mul (g h : G) (i : Fin d.count) :
    d.conjugateIndex (g * h) i = d.conjugateIndex g (d.conjugateIndex h i) := by
  apply d.factor_injective
  rw [← d.conjugateIndex_spec, ← d.conjugateIndex_spec, ← d.conjugateIndex_spec,
    Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem conjugateIndex_inv (g : G) (i : Fin d.count) :
    d.conjugateIndex g⁻¹ (d.conjugateIndex g i) = i := by
  rw [← d.conjugateIndex_mul, inv_mul_cancel, d.conjugateIndex_one]

/-- The ambient conjugation action on the indices of the actual factors.
Here conjugation by `g` means `x ↦ g * x * g⁻¹`. -/
noncomputable def factorConjugation : G →* Equiv.Perm (Fin d.count) where
  toFun g :=
    { toFun := d.conjugateIndex g
      invFun := d.conjugateIndex g⁻¹
      left_inv := d.conjugateIndex_inv g
      right_inv := fun i => by simpa using d.conjugateIndex_inv g⁻¹ i }
  map_one' := Equiv.ext (d.conjugateIndex_one)
  map_mul' g h := Equiv.ext (d.conjugateIndex_mul g h)

/-- The permutation action transports the actual subgroups. This supplies
the factor-permutation step used in the proof of B.1.12. -/
theorem factor_map_conj (g : G) (i : Fin d.count) :
    (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor (d.factorConjugation g i) :=
  d.conjugateIndex_spec g i

end CFSG.Quasithin.ChapterB.SolvableFFFactors
