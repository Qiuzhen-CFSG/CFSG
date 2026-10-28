module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.FactorArgument.Product
public import Mathlib.GroupTheory.Index

/-!
# Orbits of the normal S₃ product in 13.6.13

Conjugation permutes the actual factors of the specified internal product.
The coordinate recognition adapts the proof in Chapter B's
`SolvableStructure/OffenderProducts/Conjugation.lean` to S₃. Orbit–stabilizer
bounds each factor normalizer's index by the number of factors, hence by two.

The cubic residuals generate X. If a Sylow two-subgroup fixes both factors,
the index bound makes them ambient normal. At least one cubic residual is
moved by the literal Thompson actor, so it is an X-family member. Minimality
then forces one factor. This proves transitivity of the actual T_v* action.
No support irreducibility or identification of L_v* is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 13.6.13, printed p.929.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.NormalS3Decomposition
private abbrev S3 := Equiv.Perm (Fin 3)

private theorem involution_words : ∀ t : S3, t ≠ 1 → t ^ 2 = 1 →
    ∃ g : S3, ∀ x : S3,
      let u := g * t * g⁻¹
      x = 1 ∨ x = t ∨ x = u ∨ x = t * u ∨ x = u * t ∨ x = t * u * t := by
  decide +kernel

private theorem exists_involution : ∃ t : S3, t ≠ 1 ∧ t ^ 2 = 1 := by decide +kernel

private theorem centerless : ∀ x : S3, (∀ y : S3, y * x = x * y) → x = 1 := by
  decide +kernel

private theorem normal_contains_involution (K : Subgroup S3) (hn : K.Normal)
    {t : S3} (ht : t ∈ K) (hne : t ≠ 1) (htwo : t ^ 2 = 1) : K = ⊤ := by
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

private theorem normal_endomorphism (f : S3 →* S3) (hn : f.range.Normal) :
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
    (f : S3 →* (I → S3)) (hf : Function.Injective f) (hn : f.range.Normal) :
    ∃ i : I, f.range = (MonoidHom.mulSingle (fun _ : I => S3) i).range := by
  classical
  obtain ⟨t, ht, _⟩ := exists_involution
  obtain ⟨i, hi⟩ : ∃ i, f t i ≠ 1 := by
    by_contra h
    push Not at h
    apply ht
    apply hf
    rw [map_one]
    exact funext h
  let p (j : I) : S3 →* S3 := (Pi.evalMonoidHom (fun _ : I => S3) j).comp f
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

variable {G : Type*} [Group G] {z v : G} {X : Subgroup (Gstar z v)}
variable (d : NormalS3Decomposition z v X)

private noncomputable def modelProduct : (Fin d.count → S3) ≃* d.H :=
  (MulEquiv.piCongrRight d.model).symm.trans d.product

private theorem modelProduct_single (i : Fin d.count) (x : S3) :
    (d.modelProduct (Pi.mulSingle i x) : Gstar z v) = ((d.model i).symm x : Gstar z v) := by
  change (d.product ((MulEquiv.piCongrRight d.model).symm
    (Pi.mulSingle i x)) : Gstar z v) = _
  have he : (MulEquiv.piCongrRight d.model).symm (Pi.mulSingle i x) =
      Pi.mulSingle i ((d.model i).symm x) := by
    ext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  rw [he, d.product_single]

/-- Ambient conjugation sends each actual internal factor to another factor.
The recognition uses only the concrete internal product, and does not assume
an offender classification or ambient normality of any individual factor. -/
theorem exists_factor_map_conj (g : Gstar z v) (i : Fin d.count) :
    ∃ j : Fin d.count, (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor j := by
  classical
  let := d.normal
  let e := d.modelProduct
  let c : MulAut (Fin d.count → S3) := e.trans ((MulAut.conjNormal g).trans e.symm)
  let s := MonoidHom.mulSingle (fun _ : Fin d.count => S3)
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
    (c.injective.comp (Pi.mulSingle_injective (M := fun _ : Fin d.count => S3) i)) hfn
  let inc : (Fin d.count → S3) →* Gstar z v := (d.H).subtype.comp e.toMonoidHom
  have hi (k : Fin d.count) : (s k).range.map inc = d.factor k := by
    ext x
    constructor
    · rintro ⟨a, ⟨b, rfl⟩, rfl⟩
      change (d.modelProduct (Pi.mulSingle k b) : Gstar z v) ∈ d.factor k
      rw [d.modelProduct_single]
      exact Subtype.property _
    · intro hx
      refine ⟨s k (d.model k ⟨x, hx⟩), ⟨_, rfl⟩, ?_⟩
      change (d.modelProduct (Pi.mulSingle k (d.model k ⟨x, hx⟩)) : Gstar z v) = x
      rw [d.modelProduct_single, MulEquiv.symm_apply_apply]
  have hc : inc.comp c.toMonoidHom = (MulAut.conj g).toMonoidHom.comp inc := by
    ext x
    simp [inc, c, MulAut.conjNormal_apply, MulAut.conj_apply]
  refine ⟨j, ?_⟩
  rw [← hi i, Subgroup.map_map, ← hc, ← Subgroup.map_map, ← MonoidHom.range_comp]
  change f.range.map inc = d.factor j
  rw [hj]
  exact hi j


theorem factor_injective : Function.Injective d.factor := by
  intro i j h
  apply d.factorResidual_injective
  change (pResidual 2 (d.factor i)).map (d.factor i).subtype =
    (pResidual 2 (d.factor j)).map (d.factor j).subtype
  rw [h]

private noncomputable def conjugateIndex (g : Gstar z v) (i : Fin d.count) : Fin d.count :=
  Classical.choose (d.exists_factor_map_conj g i)

private theorem conjugateIndex_spec (g : Gstar z v) (i : Fin d.count) :
    (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor (d.conjugateIndex g i) :=
  Classical.choose_spec (d.exists_factor_map_conj g i)

private theorem conjugateIndex_one (i : Fin d.count) : d.conjugateIndex 1 i = i := by
  apply d.factor_injective
  rw [← d.conjugateIndex_spec]
  have h : (MulAut.conj (1 : Gstar z v)).toMonoidHom = MonoidHom.id (Gstar z v) := by
    ext x
    simp
  rw [h, Subgroup.map_id]

private theorem conjugateIndex_mul (g h : Gstar z v) (i : Fin d.count) :
    d.conjugateIndex (g * h) i = d.conjugateIndex g (d.conjugateIndex h i) := by
  apply d.factor_injective
  rw [← d.conjugateIndex_spec, ← d.conjugateIndex_spec, ← d.conjugateIndex_spec,
    Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem conjugateIndex_inv (g : Gstar z v) (i : Fin d.count) :
    d.conjugateIndex g⁻¹ (d.conjugateIndex g i) = i := by
  rw [← d.conjugateIndex_mul, inv_mul_cancel, d.conjugateIndex_one]

/-- The ambient conjugation action on the indices of the actual factors.
Here conjugation by `g` means `x ↦ g * x * g⁻¹`. -/
noncomputable def factorConjugation : Gstar z v →* Equiv.Perm (Fin d.count) where
  toFun g :=
    { toFun := d.conjugateIndex g
      invFun := d.conjugateIndex g⁻¹
      left_inv := d.conjugateIndex_inv g
      right_inv := fun i => by simpa using d.conjugateIndex_inv g⁻¹ i }
  map_one' := Equiv.ext (d.conjugateIndex_one)
  map_mul' g h := Equiv.ext (d.conjugateIndex_mul g h)

/-- The permutation action transports the actual subgroups. This supplies
the factor-permutation step used in the proof of B.1.12. -/
theorem factor_map_conj (g : Gstar z v) (i : Fin d.count) :
    (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor (d.factorConjugation g i) :=
  d.conjugateIndex_spec g i


/-- The normalizer index is bounded by the number of actual factors. -/
theorem factor_normalizer_index_le_count [Finite G] (i : Fin d.count) :
    (normalizer (d.factor i : Set (Gstar z v))).index ≤ d.count := by
  let : MulAction (Gstar z v) (Fin d.count) :=
    MulAction.compHom (Fin d.count) d.factorConjugation
  have hs : MulAction.stabilizer (Gstar z v) i =
      normalizer (d.factor i : Set (Gstar z v)) := by
    ext g
    change d.factorConjugation g i = i ↔ _
    rw [mem_normalizer_iff_map_conj_eq]
    change d.factorConjugation g i = i ↔
      (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor i
    rw [d.factor_map_conj]
    exact d.factor_injective.eq_iff.symm
  rw [← hs, MulAction.index_stabilizer]
  exact (Set.ncard_le_card _).trans_eq (Nat.card_fin _)

/-- Each S₃ factor has at most two ambient conjugates. -/
theorem factor_normalizer_index_le_two [Finite G] (i : Fin d.count) :
    (normalizer (d.factor i : Set (Gstar z v))).index ≤ 2 :=
  (d.factor_normalizer_index_le_count i).trans d.count_le_two


/-- The embedded cubic residuals generate precisely X. -/
theorem iSup_factorResidual : (⨆ i, d.factorResidual i) = X := by
  classical
  apply le_antisymm (iSup_le d.factorResidual_le_X)
  let R (i : Fin d.count) := pResidual 2 (d.factor i)
  let f (i : Fin d.count) : R i →* Gstar z v :=
    (d.factor i).subtype.comp (R i).subtype
  have hc : Pairwise fun i j => ∀ (a : R i) (b : R j), Commute (f i a) (f j b) :=
    fun _ _ hij a b => d.factor_commute hij a.val b.val
  let q := MonoidHom.noncommPiCoprod f hc
  let inc : (∀ i, R i) →* (∀ i, d.factor i) :=
    MonoidHom.pi fun i => (R i).subtype.comp (Pi.evalMonoidHom (fun i => R i) i)
  have hq : q = d.factorProductMap.comp inc := by
    apply MonoidHom.pi_ext
    intro i a
    rw [MonoidHom.noncommPiCoprod_mulSingle]
    change f i a = d.factorProductMap (inc (Pi.mulSingle i a))
    have he : inc (Pi.mulSingle i a) = Pi.mulSingle i a.val := by
      ext j
      by_cases hj : j = i
      · subst j; simp [inc]
      · simp [inc, hj]
    rw [he, d.factorProductMap_single]
    rfl
  have hr : q.range = ⨆ i, d.factorResidual i := by
    rw [MonoidHom.noncommPiCoprod_range]
    congr 1
    funext i
    change ((d.factor i).subtype.comp (R i).subtype).range = _
    rw [MonoidHom.range_comp, range_subtype]
  intro x hx
  rw [← d.residual_eq] at hx
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
  let c := d.product.symm a
  have hci (i : Fin d.count) : c i ∈ R i := by
    let e := (Pi.evalMonoidHom (fun i => d.factor i) i).comp d.product.symm.toMonoidHom
    exact map_pResidual_le 2 e (mem_map.mpr ⟨a, ha, rfl⟩)
  rw [← hr]
  refine ⟨fun i => ⟨c i, hci i⟩, ?_⟩
  rw [hq]
  change (d.product c : Gstar z v) = (a : Gstar z v)
  exact congrArg Subtype.val (d.product.apply_symm_apply a)

/-- A Sylow-fixed factor is ambient normal, since its orbit has size at most two. -/
theorem factor_normal_of_sylow_normalizes [Finite G]
    (P : Sylow 2 (Gstar z v)) (i : Fin d.count)
    (hP : (P : Subgroup (Gstar z v)) ≤ normalizer (d.factor i : Set (Gstar z v))) :
    (d.factor i).Normal := by
  apply normalizer_eq_top_iff.mp
  apply index_eq_one.mp
  have hb := d.factor_normalizer_index_le_two i
  have hp := P.not_dvd_index
  have hd := index_dvd_of_le hP
  have hn := (normalizer (d.factor i : Set (Gstar z v))).index_ne_zero_of_finite
  have hne : (normalizer (d.factor i : Set (Gstar z v))).index ≠ 2 := by
    intro he
    rw [he] at hd
    exact hp hd
  omega


/-- A normal cubic coordinate moved by J(T_v)* is a member of the literal X-family. -/
theorem factorResidual_mem_XFamily [Finite G] (L T : Subgroup G) (i : Fin d.count)
    (hn : (d.factor i).Normal)
    (hc : ⁅d.factorResidual i,
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ ≠ ⊥) :
    d.factorResidual i ∈ XFamily L T z v := by
  let := hn
  let R := d.factorResidual i
  let J := starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))
  have hle : ⁅R, J⁆ ≤ R := commutator_le_left R J
  have he : ⁅R, J⁆ = R := by
    apply le_antisymm hle
    by_contra hh
    have hz := Theory.GroupTheory.NormalSymmetricThreeMarked.inf_eq_bot_of_not_le
      (d.factorResidual_card i) hh
    rw [inf_eq_right.mpr hle] at hz
    exact hc hz
  have hne : R ≠ ⊥ := by
    intro hz
    have hcard := d.factorResidual_card i
    change Nat.card R = 3 at hcard
    rw [hz, card_bot] at hcard
    omega
  refine ⟨⟨le_normalizer_of_normal, ?_, hne, he⟩, inferInstance⟩
  rw [(pResidual_eq_top_iff 2 R).mpr (isPPerfect_embedded_pResidual 2 (d.factor i)),
    ← MonoidHom.range_eq_map, range_subtype]

/-- If every factor is normal, at least one cubic coordinate is moved by the
literal Thompson actor, since that actor generates X by commutators. -/
theorem exists_factorResidual_mem_XFamily_of_normal [Finite G]
    (L T : Subgroup G) (hX : X ∈ XFamily L T z v)
    (hn : ∀ i, (d.factor i).Normal) :
    ∃ i, d.factorResidual i ∈ XFamily L T z v := by
  obtain ⟨i, hi⟩ : ∃ i, ⁅d.factorResidual i,
      starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v))⁆ ≠ ⊥ := by
    by_contra! hh
    have hc : X ≤ centralizer
        (starImage z v (Stellmacher.elementaryAbelianMaxJ (Tv T v)) : Set _) := by
      rw [← d.iSup_factorResidual]
      exact iSup_le fun i => commutator_eq_bot_iff_le_centralizer.mp (hh i)
    have hz := commutator_eq_bot_iff_le_centralizer.mpr hc
    rw [hX.1.2.2.2] at hz
    exact hX.1.2.2.1 hz
  exact ⟨i, d.factorResidual_mem_XFamily L T i (hn i) hi⟩

/-- Minimality rules out two individually normal factors. -/
theorem count_eq_one_of_normal [Finite G] (L T : Subgroup G)
    (hX : MinimalSolvable L T z v X) (hn : ∀ i, (d.factor i).Normal) :
    d.count = 1 := by
  obtain ⟨i, hi⟩ := d.exists_factorResidual_mem_XFamily_of_normal L T hX.1 hn
  have he := hX.2.2 (d.factorResidual i) hi (d.factorResidual_le_X i)
  have hji (j : Fin d.count) : j = i := by
    by_contra hij
    have hd : Disjoint (d.factorResidual j) (d.factorResidual i) :=
      (d.factor_disjoint hij).mono (map_subtype_le _) (map_subtype_le _)
    have hle : d.factorResidual j ≤ d.factorResidual i := he.symm ▸ d.factorResidual_le_X j
    have hz : d.factorResidual j = ⊥ := by
      have hh := hd.eq_bot
      rwa [inf_eq_left.mpr hle] at hh
    have hcard := d.factorResidual_card j
    rw [hz, card_bot] at hcard
    omega
  have hpos := d.count_pos
  by_contra hcount
  have htwo : 2 ≤ d.count := by omega
  have hh := (hji ⟨0, by omega⟩).trans (hji ⟨1, by omega⟩).symm
  have hh' := congrArg Fin.val hh
  norm_num at hh'


/-- The actual Sylow actor is transitive on the S₃ factors. A failed orbit
would fix both factors; their cubic residuals would then violate minimality. -/
theorem factorsTransitive [Finite G] (L T : Subgroup G)
    (hX : MinimalSolvable L T z v X) (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v) :
    d.FactorsTransitive T := by
  intro i j
  by_cases hij : i = j
  · subst j
    refine ⟨1, one_mem _, ?_⟩
    simpa only [map_one, Equiv.Perm.one_apply] using d.factor_map_conj 1 i
  by_contra! hfail
  have hcases (k : Fin d.count) : k = i ∨ k = j := by
    have hi := i.isLt
    have hj := j.isLt
    have hk := k.isLt
    have hb := d.count_le_two
    have hne : i.val ≠ j.val := fun he => hij (Fin.ext he)
    have he : k.val = i.val ∨ k.val = j.val := by omega
    exact he.imp Fin.ext Fin.ext
  have hfixi (t : Gstar z v) (ht : t ∈ starImage z v (Tv T v)) :
      d.factorConjugation t i = i := by
    rcases hcases (d.factorConjugation t i) with hi | hj
    · exact hi
    · exact (hfail t ht ((d.factor_map_conj t i).trans (congrArg d.factor hj))).elim
  have hfix (t : Gstar z v) (ht : t ∈ starImage z v (Tv T v)) (k : Fin d.count) :
      d.factorConjugation t k = k := by
    rcases hcases k with hk | hk
    · simpa only [hk] using hfixi t ht
    rw [hk]
    rcases hcases (d.factorConjugation t j) with hji | hj
    · have he := (d.factorConjugation t).injective (hji.trans (hfixi t ht).symm)
      exact (hij he.symm).elim
    · exact hj
  obtain ⟨P, hP⟩ := FactorArgument.exists_starSylow T z v S hS
  have hn (k : Fin d.count) : (d.factor k).Normal := by
    apply d.factor_normal_of_sylow_normalizes P k
    rw [hP]
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (d.factor_map_conj t k).trans (congrArg d.factor (hfix t ht k))
  have hone := d.count_eq_one_of_normal L T hX hn
  apply hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  omega

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.NormalS3Decomposition
end
