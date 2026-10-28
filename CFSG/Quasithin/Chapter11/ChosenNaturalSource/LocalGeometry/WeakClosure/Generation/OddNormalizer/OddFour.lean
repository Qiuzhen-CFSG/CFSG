module
public import Theory.SpecificGroups.OddFourProjectiveRank
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OddG2
public import Theory.Representation.RankThreeAbelianAutomizer
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients

/-!
# Excluding every remaining placed odd four-dimensional component

Lift an elementary subgroup of a central quotient to a Sylow two-subgroup P
of the full matrix cover. A normal abelian self-centralizer A contains the
central kernel, so P/A is elementary abelian. Its faithful action on the at
most four character weights embeds P/A in S₄, bounding its order by four.
The determinant-one action bounds the first omega subgroup of A by eight.
The Frattini index inequality therefore bounds the original elementary
quotient by 32, giving projective two-rank at most five.

This applies to the actual PSL₄, PSU₄ and PSp₄ conventions in odd
characteristic, retaining their full covering kernels. The original natural
cover image has rank at least six, excluding all three remaining odd rows.
The complete placed B-catalogue thus reduces to J₄ and Ru. Source applies
this to the literal Hall kernel; those two local exclusions and the outer
sections remain with qt-d-1222-natural-odd-kernel-normalizer.

Source: Aschbacher--Smith, the rank inspection in 4.4.3, printed p.622;
the character-weight automizer argument is A.3.21(c), printed pp.55--56.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

private theorem elementary_symmetric_four_card {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (j : E →* Equiv.Perm (Fin 4)) (hj : Function.Injective j) :
    Nat.card E ≤ 4 := by
  let k := Equiv.Perm.viaEmbeddingHom ⟨Fin.castSucc, Fin.castSucc_injective 4⟩
  have hk : Function.Injective k := Equiv.Perm.viaEmbeddingHom_injective _
  let i := k.comp j
  have hr : primeRank 2 E ≤ 2 := (_root_.primeRank_le_of_injective 2 i (hk.comp hj)).trans
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
  let : IsElementaryAbelian 2 (⊤ : Subgroup E) :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (fun a =>
        Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 E) a.val)) }
  have h := (primeRank_le_iff_elementary_card_le E).mp hr ⊤ inferInstance
  simpa only [Nat.card_congr (topEquiv : (⊤ : Subgroup E) ≃* E).toEquiv, Nat.reducePow] using h

private theorem elementary_quotient_card_le_thirtytwo
    {F P E : Type*} [Field F] [Group P] [Finite P] [Group E]
    [IsElementaryAbelian 2 E] (hP : IsPGroup 2 P)
    (f : P →* E) (hf : Function.Surjective f) (hc : f.ker ≤ center P)
    (ρ : P →* GL (Fin 4) F) (hρ : Function.Injective ρ)
    (h2 : (2 : F) ≠ 0) (hdet : ∀ p, Matrix.GeneralLinearGroup.det (ρ p) = 1) :
    Nat.card E ≤ 32 := by
  classical
  obtain ⟨A,hAn,hAc,hCA⟩ := exists_normal_abelian_selfCentralizing hP
  let := hAn
  let := hAc
  have hZA : center P ≤ A := (center_le_centralizer (A : Set P)).trans hCA
  have hkerA : f.ker ≤ A := hc.trans hZA
  have hq2 (x : P ⧸ A) : x ^ 2 = 1 := by
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective A x
    rw [←map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply hkerA
    rw [MonoidHom.mem_ker,map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) _
  let : IsMulCommutative (P ⧸ A) := IsMulCommutative.of_comm fun x y => by
    have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hq2 x)
    have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hq2 y)
    have hxy : (x*y)⁻¹ = x*y := inv_eq_of_mul_eq_one_left
      (by simpa only [pow_two] using hq2 (x*y))
    simpa only [mul_inv_rev,hx,hy] using hxy.symm
  let : IsElementaryAbelian 2 (P ⧸ A) :=
    ⟨Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hq2⟩
  let K := AlgebraicClosure F
  let τ : Representation F P (Fin 4 → F) := (generalLinearNatural (F := F) 4).comp ρ
  let σ := τ.extendScalars K
  have hσ : Function.Injective σ := (extendScalars_faithful_iff K _).mp
    ((generalLinearNatural_injective 4).comp hρ)
  have hord : (Nat.card A : K) ≠ 0 := by
    obtain ⟨n,hn⟩ := (hP.to_subgroup A).exists_card_eq
    rw [hn,Nat.cast_pow]
    apply pow_ne_zero
    intro h
    apply h2
    apply (algebraMap F K).injective
    simpa only [map_ofNat, map_zero, Nat.cast_ofNat] using h
  obtain ⟨j,hj⟩ := automizer_embeds_perm_of_abelian σ A hσ hord 4 (by
    simp only [Module.finrank_baseChange,Module.finrank_pi,Fintype.card_fin,le_refl])
  let n : P →* normalizer (A : Set P) := (MonoidHom.id P).codRestrict _
    (fun x => A.normalizer_eq_top ▸ mem_top x)
  let g := j.comp (A.normalizerMonoidHom.rangeRestrict.comp n)
  have hg : g.ker = A := by
    ext x
    change j (A.normalizerMonoidHom.rangeRestrict (n x)) = 1 ↔ x ∈ A
    rw [←j.map_one,hj.eq_iff]
    rw [Subtype.ext_iff]
    change A.normalizerMonoidHom (n x) = 1 ↔ x ∈ A
    rw [←MonoidHom.mem_ker,A.normalizerMonoidHom_ker]
    change x ∈ centralizer (A : Set P) ↔ x ∈ A
    exact ⟨fun hx => hCA hx,fun hx => le_centralizer A hx⟩
  let gbar := QuotientGroup.lift A g hg.ge
  have hgb : Function.Injective gbar := (QuotientGroup.injective_lift_iff A g hg.ge).mpr hg.symm
  have hindex : A.index ≤ 4 := elementary_symmetric_four_card gbar hgb
  let : IsElementaryAbelian 2 (omega₁ A (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative A
  have hr : primeRank 2 A ≤ 3 := Theory.SpecificGroups.OddFourRank.twoRank_le_three
    (ρ.comp A.subtype) (hρ.comp A.subtype_injective) h2 (fun a => hdet a.val)
  have ho : Nat.card (omega₁ A (p := 2)) ≤ 8 :=
    (primeRank_le_iff_elementary_card_le A).mp hr _ inferInstance
  have hb := hP.card_frattini_quotient_le_index_mul_omega_one A
  let fbar := QuotientGroup.lift (frattini P) f
    (Theory.GroupTheory.frattini_le_ker_of_square_image f (fun a =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) (f a)))
  have hfb : Function.Surjective fbar := by
    intro x
    obtain ⟨a,rfl⟩ := hf x
    exact ⟨QuotientGroup.mk' (frattini P) a,rfl⟩
  exact (Nat.card_le_card_of_surjective fbar hfb).trans
    (hb.trans ((Nat.mul_le_mul hindex ho).trans (by norm_num)))


/-- A central quotient of an odd-characteristic special four-dimensional
matrix group has two-rank at most five. -/
theorem central_quotient_twoRank_le_five
    {F G H : Type*} [Field F] [Group G] [Finite G] [Group H] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (hc : f.ker ≤ center G)
    (ρ : G →* GL (Fin 4) F) (hρ : Function.Injective ρ)
    (h2 : (2 : F) ≠ 0) (hdet : ∀ g, Matrix.GeneralLinearGroup.det (ρ g) = 1) :
    primeRank 2 H ≤ 5 := by
  apply (primeRank_le_iff_elementary_card_le H).mpr
  intro E hE
  let : IsElementaryAbelian 2 E := hE
  let L := E.comap f
  let q : L →* E := f.subgroupComap E
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective E hf
  let P : Sylow 2 L := Sylow.nonempty.some
  have hPtop : (P : Subgroup L).map q = ⊤ := by
    change (P.mapSurjective hq : Subgroup E) = ⊤
    apply top_unique
    exact ((IsElementaryAbelian.isPGroup 2 E).to_subgroup ⊤).le_sylow_of_normal _
  let g : P →* E := q.comp (P : Subgroup L).subtype
  have hg : Function.Surjective g := by
    intro e
    have he : e ∈ (P : Subgroup L).map q := hPtop.symm ▸ mem_top e
    obtain ⟨x, hx, he⟩ := he
    exact ⟨⟨x, hx⟩, he⟩
  let j : P →* G := L.subtype.comp (P : Subgroup L).subtype
  have hj : Function.Injective j := L.subtype_injective.comp (P : Subgroup L).subtype_injective
  have hker (x : g.ker) : j x.val ∈ f.ker :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp x.property)
  have hgc : g.ker ≤ center P := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply hj
    exact mem_center_iff.mp (hc (hker ⟨x, hx⟩)) (j y)
  exact elementary_quotient_card_le_thirtytwo P.isPGroup' g hg hgc
    (ρ.comp j) (hρ.comp hj) h2 (fun p => hdet (j p))


variable {F : Type*} [Field F] [Finite F]

/-- PSL₄ in odd characteristic has two-rank at most five. -/
theorem psl_four_twoRank_le_five (h2 : (2 : F) ≠ 0) : primeRank 2 PSL(4,F) ≤ 5 :=
  central_quotient_twoRank_le_five (QuotientGroup.mk' (center SL(4,F)))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective h2
    Matrix.SpecialLinearGroup.coeToGL_det

/-- The projective image of every odd special unitary four-space has two-rank at most five. -/
theorem psu_four_twoRank_le_five (J : BenderSuzuki.MatrixGroups.HermitianForm 4 F)
    (h2 : (2 : F) ≠ 0) :
    primeRank 2 (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) ≤ 5 := by
  let f := Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup
  have hf : Function.Surjective f := Matrix.ProjGenLinGroup.mk.subgroupMap_surjective J.specialSubgroup
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective f hf
  have hc : f.ker ≤ center J.specialSubgroup := by
    intro x hx
    have hs : x.val ∈ center (GL (Fin 4) F) := by
      apply Matrix.ProjGenLinGroup.mk_eq_one.mp
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp hs y.val)
  exact central_quotient_twoRank_le_five f hf hc J.specialSubgroup.subtype
    J.specialSubgroup.subtype_injective h2 (fun s => s.property.2)

open Theory.SpecificGroups.SymplecticFour

private def symplecticToGL : Sp F →* GL (Fin 2 ⊕ Fin 2) F where
  toFun g := Matrix.GeneralLinearGroup.mk'' g.val (SymplecticGroup.symplectic_det g.property)
  map_one' := by apply Units.ext; rfl
  map_mul' _ _ := by apply Units.ext; rfl

omit [Finite F] in
private theorem symplecticToGL_injective : Function.Injective (symplecticToGL (F := F)) := by
  intro x y h
  exact Subtype.ext (congrArg Units.val h)

/-- The odd symplectic four-space central quotient has two-rank at most five. -/
theorem psp_four_twoRank_le_five (h2 : (2 : F) ≠ 0) :
    primeRank 2 (Sp F ⧸ center (Sp F)) ≤ 5 := by
  let e : (Fin 2 ⊕ Fin 2) ≃ Fin 4 := finSumFinEquiv
  let r : GL (Fin 2 ⊕ Fin 2) F ≃* GL (Fin 4) F :=
    Units.mapEquiv (Matrix.reindexRingEquiv F e).toMulEquiv
  let ρ := r.toMonoidHom.comp symplecticToGL
  have hρ : Function.Injective ρ := r.injective.comp symplecticToGL_injective
  have hdet (g : Sp F) : Matrix.GeneralLinearGroup.det (ρ g) = 1 := by
    apply Units.ext
    change Matrix.det (Matrix.reindex e e g.val) = 1
    rw [Matrix.det_reindex_self]
    exact SymplecticGroup.det_eq_one g.property
  exact central_quotient_twoRank_le_five (QuotientGroup.mk' (center (Sp F)))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']) ρ hρ h2 hdet

/-- Transport the degree-four bound to the actual PSL₄ model convention. -/
theorem odd_psl_four_twoRank_le_five {Q : Type*} [Group Q] [Finite Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSL Q 4 q) : primeRank 2 Q ≤ 5 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [primeRank_congr 2 e]
  exact psl_four_twoRank_le_five
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hF))

/-- Transport the degree-four bound to the actual PSU₄ model convention. -/
theorem odd_psu_four_twoRank_le_five {Q : Type*} [Group Q] [Finite Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSU Q 4 q) : primeRank 2 Q ≤ 5 := by
  obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv Q e.toEquiv
  rw [primeRank_congr 2 e]
  exact psu_four_twoRank_le_five J
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hF)

/-- Transport the degree-four bound to the actual PSp₄ model convention. -/
theorem odd_psp_four_twoRank_le_five {Q : Type*} [Group Q] [Finite Q]
    {q : ℕ} (ho : Odd q) (hm : ClassicalGroup.IsPSp Q 2 q) : primeRank 2 Q ≤ 5 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rw [primeRank_congr 2 e]
  exact psp_four_twoRank_le_five
    (Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho (by simpa using hF))


open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {Q : Type*} [Group Q] [Finite Q]
include D S

/-- The elementary image of the original module excludes all three remaining
odd four-dimensional models, with their actual projective conventions. -/
theorem NaturalCoverImage.not_odd_four (h : NaturalCoverImage D Q) {q : ℕ}
    (ho : Odd q) :
    ¬ ClassicalGroup.IsPSL Q 4 q ∧ ¬ ClassicalGroup.IsPSU Q 4 q ∧
      ¬ ClassicalGroup.IsPSp Q 2 q := by
  have hlo := h.twoRank_ge_six D S
  refine ⟨fun hm => ?_,fun hm => ?_,fun hm => ?_⟩
  · have hup := odd_psl_four_twoRank_le_five ho hm
    omega
  · have hup := odd_psu_four_twoRank_le_five ho hm
    omega
  · have hup := odd_psp_four_twoRank_le_five ho hm
    omega

/-- Once the genuine residual is placed in a B-component, its central quotient
is J₄ or Ru. This discharges every additional placed B-model row. -/
theorem NaturalCoverImage.theoremB_models_sporadic (h : NaturalCoverImage D Q)
    (hm : ChapterA.Section02.IsTheoremBModel Q) :
    Nonempty (Q ≃* Janko4.Model) ∨ Nonempty (Q ≃* Rudvalis.Model) := by
  rcases h.theoremB_models_without_g2 D S hm with hs | ⟨p,_,ho,hp⟩ | hl | hu
  · exact hs
  · exact ((h.not_odd_four D S ho).2.2 hp).elim
  · obtain ⟨r,_,⟨k,hk⟩,hm⟩ := hl
    have ho : Odd r := by
      rw [hk]
      exact (even_two.pow_of_ne_zero (by positivity)).add_one
    exact ((h.not_odd_four D S ho).1 hm).elim
  · obtain ⟨s,hs,⟨b,hb⟩,hm⟩ := hu
    have ho : Odd s := by
      have hb0 : b ≠ 0 := by
        intro he
        simp only [he,pow_zero] at hb
        have := hs.two_le
        omega
      have heven : Even (s + 1) := hb.symm ▸ even_two.pow_of_ne_zero hb0
      exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp heven)
    exact ((h.not_odd_four D S ho).2.1 hm).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
