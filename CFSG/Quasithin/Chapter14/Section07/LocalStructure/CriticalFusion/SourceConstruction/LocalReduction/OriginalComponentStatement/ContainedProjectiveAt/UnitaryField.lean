module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt.Borel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ProjectiveNormalityAt
public import Theory.SpecificGroups.SU3.LargeBorelCubicAction
public import Theory.SpecificGroups.Classical.SignedThreeCubicRank
public import Theory.GroupTheory.NormalizedSupConsequences
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree.Borel.Geometry

/-!
# Field eight in the original contained projective unitary-three row

For an actual C-component C of any original local I with C/O₂(C) ≃ PSU₃(2ⁿ),
n ≥ 2, containment of the original L₁ forces n = 3. The rank-one geometry
places L₁ in the normalizer of the original Sylow intersection. Source 14.7.29
puts that normalizer in N_G(L) and makes it normalize L₁. Its literal
quotient by its two-core is abelian of odd order.

The original inverter in T∩L inverts the cubic image of L₁ and fixes the
source action-kernel supplement, so every quotient displacement has cube one.
Transport to the full Hermitian Borel retains its projective scalar kernel.
Cubic rigidity makes the displacement trivial in degree two and in every
degree above three, contradicting the original cubic inversion.

The projective exclusion assembly combines this with odd-degree containment
and the field-eight module obstruction. All structural and previous-theorem
inputs here are for the original group and Sylow subgroup.
Source: Aschbacher–Smith 14.7.40–41, printed p.1061, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt
open AlternatingSevenSource
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
open Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.UnitaryThree
universe u
variable {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]

private theorem unitary_normalizer_displacement_of_cube
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n) (hn3 : n ≠ 3)
    (hcard : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (q : G →* ProjectiveSpecialUnitaryMatrixGroup J) (hq : Function.Surjective q)
    (P : Sylow 2 G) (hk : q.ker ≤ (P : Subgroup G))
    (α : MulAut G) (β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (he : ∀ x, q (α x) = β (q x))
    (hP : (P : Subgroup G).map α.toMonoidHom = P)
    (hc : ∀ x ∈ normalizer (P : Set G), (α x * x⁻¹)^3 ∈ (P : Subgroup G)) :
    ∀ x ∈ normalizer (P : Set G), α x * x⁻¹ ∈ (P : Subgroup G) := by
  let R := P.mapSurjective hq
  obtain ⟨e,hR,hN⟩ := psu_borel_model J n (by omega) hcard hconj R
  let J₀ := ChapterF.Source.Unitary.FormTransport.standardForm J
  let : Group (ProjectiveSpecialUnitaryMatrixGroup J₀) := inferInstance
  let : DivisionMonoid (ProjectiveSpecialUnitaryMatrixGroup J₀) := Group.toDivisionMonoid
  let q' := e.toMonoidHom.comp q
  let β' := MulAut.congr e β
  have hq' : Function.Surjective q' := e.surjective.comp hq
  have hk' : q'.ker ≤ (P : Subgroup G) := by
    intro x hx
    exact hk (e.map_eq_one_iff.mp hx)
  have hPq : (P : Subgroup G).map q' = projectiveRoot J₀ rfl := by
    rw [show q' = e.toMonoidHom.comp q from rfl,←Subgroup.map_map]
    exact hR
  have hNq : (normalizer (P : Set G)).map q' = projectiveBorel J₀ rfl := by
    rw [show q' = e.toMonoidHom.comp q from rfl,←Subgroup.map_map,
      P.normalizer_map_surjective q hq]
    exact hN
  have he' (x : G) : q' (α x) = β' (q' x) := by
    change e (q (α x)) = e (β (e.symm (e (q x))))
    rw [he,e.symm_apply_apply]
  have hr : (projectiveRoot J₀ rfl).map β'.toMonoidHom = projectiveRoot J₀ rfl := by
    have heq : β'.toMonoidHom.comp q' = q'.comp α.toMonoidHom :=
      MonoidHom.ext (fun x => (he' x).symm)
    rw [←hPq,Subgroup.map_map,heq,←Subgroup.map_map,hP]
  have hcube : ∀ x ∈ projectiveBorel J₀ rfl,
      (β' x * x⁻¹)^3 ∈ projectiveRoot J₀ rfl := by
    intro x hx
    rw [←hNq] at hx
    obtain ⟨y,hy,rfl⟩ := hx
    have hh := mem_map_of_mem q' (hc y hy)
    rw [hPq] at hh
    simpa only [map_pow,map_mul,map_inv,he'] using hh
  have hstep : ∀ x ∈ projectiveBorel J₀ rfl,
      β' x * x⁻¹ ∈ projectiveRoot J₀ rfl := by
    by_cases hlarge : 3 < n
    · exact (large_standard_borel_rigidity J₀ rfl hlarge hcard hconj
        (projectiveBorel_twoCore J₀ n (by omega) hcard hconj rfl) β' hr hcube).1
    · have hn2 : n = 2 := by omega
      exact standard_borel_displacement_mem_of_cube J₀ rfl hn (hn2 ▸ by decide) hcard hconj
        (projectiveBorel_twoCore J₀ n (by omega) hcard hconj rfl) β' hr hcube
  intro x hx
  have hm : q' x ∈ projectiveBorel J₀ rfl := hNq ▸ mem_map_of_mem q' hx
  have hh := hstep (q' x) hm
  rw [←hPq,←he',←map_inv,←map_mul] at hh
  change α x * x⁻¹ ∈ ((P : Subgroup G).map q').comap q' at hh
  rwa [comap_map_eq_self hk'] at hh

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- An actual binary projective U₃ component containing the original point has field eight. -/
theorem local_unitaryThree_contained_field_eight_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) (hin : F.Li L 1 ≤ C.map I.subtype)
    {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (e : (C ⧸ pCore 2 C) ≃* ProjectiveSpecialUnitaryMatrixGroup J) : n = 3 := by
  let : C.Normal := local_projective_unitaryThree_normal_at d h hab structural previous faithful earlier
    I hI C hC J (by omega) hE hconj e
  let : Group.IsPerfect C := hC.perfect
  let j : C →* G := I.subtype.comp C.subtype
  have hj : Function.Injective j := I.subtype_injective.comp C.subtype_injective
  let S := T.subtype (F.sylow_le_of_mem_Hz hI)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal C
  let N : Subgroup C := normalizer (P : Set C)
  let B₀ : Subgroup G := N.map j
  let A : Subgroup C := (F.Li L 1).comap j
  have hArange : F.Li L 1 ≤ j.range := by
    rw [MonoidHom.range_comp,range_subtype]
    exact hin
  have hAm : A.map j = F.Li L 1 := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hArange
  let ea : A ≃* F.Li L 1 :=
    (equivMapOfInjective A j hj).trans (MulEquiv.subgroupCongr hAm)
  let : Group.IsSolvable (F.Li L 1) := by
    let : Group.IsNilpotent (pCore 2 (F.Li L 1)) := pCore_isPGroup.isNilpotent
    have hp : IsPGroup 3 (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) :=
      IsPGroup.of_card (n := 1) (by simpa using pointResidual_core_quotient_card_at h structural)
    let := hp.isNilpotent
    exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 (F.Li L 1))).mpr
      ⟨inferInstance,inferInstance⟩
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective (f := ea.toMonoidHom) ea.injective
  have hPA : (P : Subgroup C) ≤ normalizer (A : Set C) := by
    intro x hx
    rw [hP] at hx
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp
      (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) hx) (j a)
  let q : C →* ProjectiveSpecialUnitaryMatrixGroup J := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker ≤ (P : Subgroup C) := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup.le_sylow_of_normal P
  have hFacts : ChapterF.Source.RankOneSylowFacts P := by
    apply ChapterF.Source.rankOneSylowFacts_of_quotient
    apply ChapterF.Source.rankOneSylowFacts_of_equiv _ e
    exact ChapterF.Source.rankOneSylowFacts_psu3 J n (by omega) hE hconj _
  have hAN : A ≤ N := by
    let := P.isPGroup'.isNilpotent
    let : Group.IsSolvable (A ⊔ (P : Subgroup C) : Subgroup C) :=
      Group.isSolvable_sup_of_normalizes A P hPA
    have hproper : A ⊔ (P : Subgroup C) < ⊤ := by
      apply lt_top_iff_ne_top.mpr
      intro hh
      let : Group.IsSolvable (⊤ : Subgroup C) := hh ▸ inferInstanceAs
        (Group.IsSolvable (A ⊔ (P : Subgroup C) : Subgroup C))
      exact hC.not_isSolvable (Group.isSolvable_of_surjective
        (f := (topEquiv (G := C)).toMonoidHom) (topEquiv (G := C)).surjective)
    exact le_sup_left.trans (hFacts.unique_maximal _ le_sup_right hproper)
  have hAB : F.Li L 1 ≤ B₀ := hAm ▸ map_mono (f := j) hAN
  have hPpres (t : I) (ht : (t : G) ∈ T) :
      (P : Subgroup C).map (MulAut.conjNormal t).toMonoidHom = P := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x,hx,rfl⟩
      rw [hP] at hx ⊢
      exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hx)
        ((T : Subgroup G).inv_mem ht)
    · rw [card_map_of_injective (f := (MulAut.conjNormal t : MulAut C).toMonoidHom)
        (K := (P : Subgroup C)) (MulAut.conjNormal t : MulAut C).injective]
  have hTB : (T : Subgroup G) ≤ normalizer (B₀ : Set G) := by
    intro t ht
    let t' : I := ⟨t,F.sylow_le_of_mem_Hz hI ht⟩
    let α : MulAut C := MulAut.conjNormal t'
    have hN : N.map α.toMonoidHom = N := by
      change (normalizer (P : Set C)).map α.toMonoidHom = normalizer (P : Set C)
      have hh := map_normalizer_eq_of_bijective (f := α.toMonoidHom)
        (P : Subgroup C) α.bijective
      rw [show (P : Subgroup C).map α.toMonoidHom = P from hPpres t' ht] at hh
      simpa only [Sylow.coe_coe] using hh
    have he : (MulAut.conj t).toMonoidHom.comp j = j.comp α.toMonoidHom := rfl
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (N.map j).map (MulAut.conj t).toMonoidHom = N.map j
    rw [Subgroup.map_map,he,←Subgroup.map_map,hN]
  have hnB : F.Li L 1 ⊔ (T : Subgroup G) ≤ normalizer (B₀ : Set G) :=
    sup_le (hAB.trans B₀.le_normalizer) hTB
  have hBH : B₀ ≤ F.H :=
    (map_mono (show N ≤ ⊤ from le_top)).trans (by
      rw [←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype]
      exact (map_subtype_le _).trans hI.2.1)
  let : Group.IsSolvable N := hFacts.solvable
  have hsol : Group.IsSolvable B₀ :=
    Group.isSolvable_of_surjective (j.subgroupMap_surjective N)
  have hBM := WholeResidualAssembly.GuardedSource.point_normalized_solvable_le_normalizer d h hab structural previous faithful
    earlier B₀ hBH hsol hnB
  have hBA := WholeResidualAssembly.GuardedSource.point_normalized_solvable_normalizes_point d h hab structural previous faithful
    earlier B₀ hBH hsol hnB
  have hAres : F.Li L 1 ≤ (pResidual 2 B₀).map B₀.subtype := by
    have hh := embedded_pResidual_mono 2 hAB
    have hpA : IsPPerfect 2 (F.Li L 1) := isPPerfect_embedded_pResidual 2 _
    rw [(pResidual_eq_top_iff 2 _).mpr hpA,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  obtain ⟨t,hti⟩ := AlternatingSevenSource.exists_point_core_inverter_at (F := F) h structural
  let t' : I := ⟨t,F.sylow_le_of_mem_Hz hI t.property.1⟩
  let α : MulAut C := MulAut.conjNormal t'
  let β : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) := MulAut.congr e ((pCore 2 C).quotientAut α)
  have hact (x : C) : q (α x) = β (q x) := by
    change e (QuotientGroup.mk' _ (α x)) =
      e ((pCore 2 C).quotientAut α (e.symm (e (QuotientGroup.mk' _ x))))
    rw [e.symm_apply_apply,quotientAut_apply_mk]
  have hcore : pCore 2 N = (P : Subgroup C).subgroupOf N := by
    have hh := congrArg (subgroupOf · N) (sylowNormalizer_twoCore P)
    rw [show (N.pCoreIn 2).subgroupOf N = pCore 2 N from
      comap_map_eq_self_of_injective N.subtype_injective _] at hh
    exact hh
  let Z := N ⧸ pCore 2 N
  let : IsMulCommutative Z := by
    let : ((P : Subgroup C).subgroupOf N).Normal :=
      normal_subgroupOf_of_le_normalizer le_rfl
    let := hFacts.quotient_commutative P
    let ez := QuotientGroup.quotientMulEquivOfEq hcore
    exact ⟨⟨fun x y => ez.injective (by simp only [map_mul]; exact mul_comm' _ _)⟩⟩
  let f₀ := QuotientGroup.mk' (pCore 2 N)
  have hf₀ : Function.Surjective f₀ := QuotientGroup.mk'_surjective _
  have hk₀ (x : N) : f₀ x = 1 ↔ (x : C) ∈ P := by
    change (QuotientGroup.mk x : N ⧸ pCore 2 N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff,hcore]
    rfl
  have hαN : N.map α.toMonoidHom = N := by
    change (normalizer (P : Set C)).map α.toMonoidHom = normalizer (P : Set C)
    have hh := map_normalizer_eq_of_bijective (f := α.toMonoidHom)
      (P : Subgroup C) α.bijective
    rw [show (P : Subgroup C).map α.toMonoidHom = P from hPpres t' t.property.1] at hh
    exact hh
  let αN := (α.subgroupMap N).trans (MulEquiv.subgroupCongr hαN)
  let τ := (pCore 2 N).quotientAut αN
  have he₀ (x y : N) (hxy : α x = y) : f₀ y = τ (f₀ x) := by
    rw [quotientAut_apply_mk]
    congr 1
    exact Subtype.ext hxy.symm
  let eb : N ≃* B₀ := equivMapOfInjective N j hj
  let f : B₀ →* Z := f₀.comp eb.symm.toMonoidHom
  have hf : Function.Surjective f := hf₀.comp eb.symm.surjective
  have hk : IsPGroup 2 f.ker := by
    have hker : f₀.ker = (P : Subgroup C).subgroupOf N := by
      ext x
      exact hk₀ x
    have hk' : IsPGroup 2 f₀.ker := by
      rw [hker]
      exact P.isPGroup'.comap_of_injective N.subtype N.subtype_injective
    exact hk'.comap_of_injective eb.symm.toMonoidHom eb.symm.injective
  have ho : Odd (Nat.card Z) := by
    change Odd (Nat.card (N ⧸ pCore 2 N))
    rw [←index_eq_card,hcore]
    exact Nat.not_even_iff_odd.mp (fun heven =>
      (P.subtype (P : Subgroup C).le_normalizer).not_dvd_index
        (even_iff_two_dvd.mp heven))
  have he (b : B₀) : τ (f b) = f (B₀.normalizerMonoidHom ⟨t,hTB t.property.1⟩ b) := by
    apply (he₀ (eb.symm b)
      (eb.symm (B₀.normalizerMonoidHom ⟨t,hTB t.property.1⟩ b)) ?_).symm
    apply hj
    have heb (c : B₀) : j (eb.symm c) = c := congrArg Subtype.val (eb.apply_symm_apply c)
    change (t : G) * j (eb.symm b) * (t : G)⁻¹ = _
    rw [heb,heb]
    rfl
  let X := SourceActions.Markings.image B₀ (F.Li L 1) f
  have hX : Nat.card X = 3 :=
    (SourceActions.Markings.image_card B₀ (F.Li L 1) hAB f hk ho).trans
      (pointResidual_core_quotient_card_at h structural)
  obtain ⟨hgen,hfix⟩ := point_borel_torus_supplement_at h structural B₀ hBM hAres hBA f hf hk ho
    t t.property.2 (hTB t.property.1) τ he
  have hinv := SourceActions.Markings.image_inverted B₀ (F.Li L 1) hAB f hk ho
    ⟨t,hTB t.property.1⟩
    (ResidualNormalizer.T_normalizes_Li (h.sylow_normalizes_at structural) t.property.1) τ he hti
  have hτne : τ ≠ 1 := by
    intro htau
    have hbot : X = ⊥ := eq_bot_iff.mpr fun x hx => by
      have hi := hinv x hx
      rw [htau] at hi
      change x = x⁻¹ at hi
      have htwo : x^2 = 1 := by
        rw [pow_two]
        exact (congrArg (x * ·) hi).trans (mul_inv_cancel _)
      have hthree : x^3 = 1 := by
        have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : X))
        rw [hX] at hh
        exact congrArg Subtype.val hh
      simpa [pow_succ,htwo] using hthree
    have hh := X.eq_bot_iff_card.mp hbot
    omega
  by_contra hn3
  apply hτne
  have hcube : ∀ z : Z, (τ z * z⁻¹)^3 = 1 := by
    intro z
    let δ : Z →* Z := τ.toMonoidHom * (MonoidHom.id _)⁻¹
    have hd (x : Z) : δ x = τ x * x⁻¹ := rfl
    have hle : δ.range ≤ X := by
      rintro _ ⟨x,rfl⟩
      have hx : x ∈ X ⊔ _ := hgen ▸ mem_top x
      obtain ⟨p,hp,c,hc,rfl⟩ := mem_sup_of_normal_right.mp hx
      rw [map_mul,hd,hd,hinv p hp,hfix c hc,mul_inv_cancel,mul_one]
      exact X.mul_mem (X.inv_mem hp) (X.inv_mem hp)
    have hh := pow_card_eq_one' (x := (⟨δ z,hle ⟨z,rfl⟩⟩ : X))
    rw [hX] at hh
    exact congrArg Subtype.val hh
  have hdisp : ∀ x ∈ normalizer (P : Set C), (α x * x⁻¹)^3 ∈ (P : Subgroup C) := by
    intro x hx
    let b : N := ⟨x,hx⟩
    have hh := hcube (f₀ b)
    rw [quotientAut_apply_mk,←map_inv,←map_mul,←map_pow] at hh
    exact (hk₀ _).mp hh
  have hfixN := unitary_normalizer_displacement_of_cube J hn hn3 hE hconj
    q hq P hqk α β hact (hPpres t' t.property.1) hdisp
  apply MulEquiv.ext
  intro z
  obtain ⟨b,rfl⟩ := hf₀ z
  change τ (f₀ b) = f₀ b
  rw [quotientAut_apply_mk]
  apply mul_inv_eq_one.mp
  rw [←map_inv,←map_mul]
  exact (hk₀ _).mpr (hfixN b b.property)


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt
