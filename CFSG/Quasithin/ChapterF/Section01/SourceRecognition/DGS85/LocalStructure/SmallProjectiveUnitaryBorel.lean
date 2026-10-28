module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalEnlargement
public import Theory.SpecificGroups.SU3.FixedFieldTwoNormalizer

/-!
# The original Borel when the local quotient is PSU₃(2)

The actual quotient Sylow is self-normalizing. Pulling it back through
O₂(Lᵢ), then applying the original marked inclusion, proves Bᵢ=S∩Lᵢ.
Thus the full common Borel is BⱼS and the opposite parabolic is LⱼS.
The same argument for the starred factor identifies its intersection
with the original full Borel with the original starred Sylow, preserving
the literal quotient equivalence from F.1.9.

The module also transports the explicit outer involution to any original
PSU₃(2) marking. This shows that the large-unitary normalizer-displacement
detector does not extend to the small projective quotient, even with an
actual Sylow and two-power actor. The counterexample concerns that local
detector; it is not an exclusion or a counterexample under all F.1.1
ambient hypotheses. The unrestricted enlargement and 6.5 obstruction
for both small unitary rows remain open.

Source: Aschbacher--Smith F.1.1, F.1.3(1), F.1.9, pp.259--262;
DGS, Groups and Graphs (1985), Hypothesis A p.94, the explicitly retained
small rows on p.104, and 6.1 pp.118--119.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {H : Type*} [Group H]

/-- Every actual PSU₃(2) marking has self-normalizing Sylow two-subgroups. -/
theorem isPSU_two_sylow_normalizer_eq
    (hm : ClassicalGroup.IsPSU H 3 2) (T : Sylow 2 H) :
    normalizer (T : Set H) = (T : Subgroup H) := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let : Finite H := Finite.of_injective e e.injective
  change normalizer ((T : Subgroup H) : Set H) = (T : Subgroup H)
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [map_equiv_normalizer_eq]
  exact HermitianForm.FixedFieldTwoNormalizer.sylow_normalizer_eq J hcard hconj
    (T.mapSurjective (f := e.toMonoidHom) e.surjective)

/-- The failed local detector transports to the actual original quotient carrier. -/
theorem isPSU_two_outer_normalizer_actor (hm : ClassicalGroup.IsPSU H 3 2) :
    ∃ (T : Sylow 2 H) (a : MulAut H),
      a^2=1 ∧ (T : Subgroup H).map a.toMonoidHom = T ∧
      (∀ x ∈ normalizer (T : Set H), x⁻¹*a x ∈ T) ∧
      a ∉ MulAut.innerSubgroup H := by
  have hmodel := hm
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
  let := hF
  let := hfin
  have hf : Nat.card {x : F // J.conj x = x} = 2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1
      (by decide) (by simpa using hcard) (by simpa using hconj)
  obtain ⟨e₀⟩ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.exists_projectiveEquiv J 2 hcard hf
  let J₀ := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let f := (e.trans e₀).symm
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) :=
    Finite.of_surjective J₀.specialToProjective J₀.specialToProjective_surjective
  obtain ⟨R,b,hb2,hbR,_,hbout⟩ :=
    HermitianForm.FixedFieldTwoNormalizer.outer_involution_with_trivial_normalizer_displacements
      J₀ rfl hcard hconj
  let T := R.mapSurjective (f := f.toMonoidHom) f.surjective
  let a := MulAut.congr f b
  have he : a.toMonoidHom.comp f.toMonoidHom = f.toMonoidHom.comp b.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact congrArg f (congrArg b (f.symm_apply_apply x))
  have hT : (T : Subgroup H).map a.toMonoidHom = T := by
    change ((R : Subgroup _).map f.toMonoidHom).map a.toMonoidHom = _
    rw [Subgroup.map_map,he,←Subgroup.map_map,hbR]
    rfl
  refine ⟨T,a,?_,hT,?_,?_⟩
  · change MulAut.congr f b ^ 2=1
    rw [←map_pow,hb2,map_one]
  · intro x hx
    have hn := isPSU_two_sylow_normalizer_eq hmodel T
    change normalizer ((T : Subgroup H) : Set H) = (T : Subgroup H) at hn
    change x ∈ normalizer ((T : Subgroup H) : Set H) at hx
    have hxT : x ∈ (T : Subgroup H) := hn ▸ hx
    have hax : a x ∈ (T : Subgroup H) := by
      rw [←hT]
      exact mem_map_of_mem a.toMonoidHom hxT
    exact (T : Subgroup H).mul_mem ((T : Subgroup H).inv_mem hxT) hax
  · rintro ⟨g,hg⟩
    apply hbout
    refine ⟨f.symm g,?_⟩
    apply MulEquiv.ext
    intro x
    apply f.injective
    change f (f.symm g*x*(f.symm g)⁻¹)=f (b x)
    rw [map_mul,map_mul,map_inv,f.apply_symm_apply]
    have hh := congrArg (fun k : MulAut H => k (f x)) hg
    change g*f x*g⁻¹=f (b (f.symm (f x))) at hh
    rwa [f.symm_apply_apply] at hh

/-- Pullback through the original two-core preserves the self-normalizing Sylow. -/
theorem sylow_normalizer_eq_of_small_projective_quotient [Finite H]
    (hm : ClassicalGroup.IsPSU (H ⧸ pCore 2 H) 3 2) (T : Sylow 2 H) :
    normalizer (T : Set H) = (T : Subgroup H) := by
  have hn := isPSU_two_sylow_normalizer_eq hm (quotientSylow T)
  change normalizer ((quotientSylow T : Subgroup (H ⧸ pCore 2 H)) : Set (H ⧸ pCore 2 H)) =
    (quotientSylow T : Subgroup (H ⧸ pCore 2 H)) at hn
  change normalizer ((T : Subgroup H) : Set H) = (T : Subgroup H)
  rw [←quotientSylow_normalizer_comap T,hn,quotientSylow_comap]

variable {G : Type*} [Group G] {P B : Subgroup G}

/-- The starred Borel is its marked Sylow in the small projective row. -/
theorem source_star_borel_eq_sylow_of_small_projective_unitary
    (d : LocalRankOneData P B)
    (hm : ClassicalGroup.IsPSU (d.Pstar ⧸ pCore 2 d.Pstar) 3 2) :
    d.Pstar ⊓ B = (d.sylow : Subgroup d.Pstar).map d.Pstar.subtype := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  have hh := congrArg (Subgroup.map d.Pstar.subtype) (source_star_borel d)
  rw [sylow_normalizer_eq_of_small_projective_quotient hm d.sylow,
    subgroupOf_map_subtype] at hh
  simpa only [inf_comm] using hh

variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The literal F.1.1 Borel equals the originally specified local Sylow. -/
theorem original_borel_eq_sylow_of_small_projective_unitary
    (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2) :
    borel (L i) S = S ⊓ L i := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hh := congrArg (Subgroup.map (L i).subtype)
    (borel_subgroupOf_eq_sylowNormalizer (L i) S T hT)
  change ((borel (L i) S).subgroupOf (L i)).map (L i).subtype =
    (normalizer (T : Set (L i))).map (L i).subtype at hh
  rwa [map_subgroupOf_eq_of_le (borel_le _ _),
    sylow_normalizer_eq_of_small_projective_quotient hm T,hT] at hh

/-- The full source Borel retains just the opposite local Borel and original S. -/
theorem original_commonBorel_of_small_projective_unitary
    (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2) :
    commonBorel L S = borel (L (other i)) S ⊔ S := by
  have hb := original_borel_eq_sylow_of_small_projective_unitary h i hm
  fin_cases i
  · change borel (L 0) S = S ⊓ L 0 at hb
    change borel (L 0) S ⊔ borel (L 1) S ⊔ S = borel (L 1) S ⊔ S
    rw [hb,sup_assoc]
    exact sup_eq_right.mpr (inf_le_left.trans le_sup_right)
  · change borel (L 1) S = S ⊓ L 1 at hb
    change borel (L 0) S ⊔ borel (L 1) S ⊔ S = borel (L 0) S ⊔ S
    rw [hb,sup_assoc,show (S ⊓ L 1) ⊔ S = S from sup_eq_right.mpr inf_le_left]

/-- The opposite original parabolic is exactly LⱼS, with its original embeddings. -/
theorem original_opposite_parabolic_of_small_projective_unitary
    (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2) :
    parabolic L S (other i) = L (other i) ⊔ S := by
  rw [parabolic,other_other,original_borel_eq_sylow_of_small_projective_unitary h i hm]
  exact sup_eq_left.mpr (inf_le_left.trans le_sup_right)

/-- The F.1.9 starred Borel is the actual original starred Sylow. -/
theorem original_star_borel_of_small_projective_unitary
    (h : HypothesisF11 L S) (i : Fin 2)
    (hm : ClassicalGroup.IsPSU (L i ⧸ pCore 2 (L i)) 3 2) :
    starredParabolic L S i ⊓ commonBorel L S = starredSylow L S i := by
  have hstar : ClassicalGroup.IsPSU
      ((h.starredLocalRankOneData i).Pstar ⧸ pCore 2 (h.starredLocalRankOneData i).Pstar) 3 2 := by
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨e⟩⟩ := hm
    exact ⟨F,hF,hfin,J,hcard,hconj,⟨(h.starredQuotientEquiv i).symm.trans e⟩⟩
  have hh := source_star_borel_eq_sylow_of_small_projective_unitary (h.starredLocalRankOneData i) hstar
  exact hh.trans (h.starredLocalRankOneData_sylow_image i)

end CFSG.Quasithin.ChapterF.Source.DGS85
