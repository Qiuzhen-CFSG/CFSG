module

public import Stellmacher.SectionOne.OffenderSelectedProduct
public import Stellmacher.SectionOne.OneSevenIdentification
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Sylow normal closure of a supplementing offender

An offender whose ambient normal closure supplements a Sylow two-subgroup
generates the full offender join under Sylow conjugation. Thus every subgroup
normal in the Sylow and containing that offender contains the full join.
The normal-closure supplement is essential: an offender confined to one
coordinate of a product need not generate the remaining coordinates.

Conjugation preserves offender size by transporting both the actor and its
fixed subgroup through the original action. The join of Sylow conjugates lies
in every Sylow-normal overgroup. Its selected product from
`OffenderSelectedProduct` is normal under the global product and under the
Sylow. Since the global product is ambient normal and contains the offender,
the supplement makes the selected product ambient normal as well. Its quotient
is a two-group. An omitted global factor centralizes the selected product;
centerlessness would embed that order-six factor in the two-group quotient,
which is impossible. The two Sylow-intersection identities then identify the
Sylow conjugate join with the full offender join.

This is the Section One selected-product argument needed in the opening of
Stellmacher (8.4), Journal of Algebra 190 (1997), p.38, using the factors and
identifications of (1.7), pp.19–20. Source: the full scan corresponding to
`refs/latex/stellmacher-n-group.tex`; the local transcription abbreviates the
opening of (8.4). No later numbered lemma is used here.
-/

namespace Stellmacher.SectionOne
universe u

set_option maxHeartbeats 1200000

private theorem fixedPoints_conjugate
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (A : Subgroup G) (g : G) :
    FixedPoints.subgroup (A.conjBy g) V =
      (FixedPoints.subgroup A V).map
        (MulDistribMulAction.toMulAut G V g).toMonoidHom := by
  ext vector
  constructor
  · intro hvector
    refine ⟨g⁻¹ • vector, ?_, by simp⟩
    change g⁻¹ • vector ∈ FixedPoints.subgroup A V
    rw [FixedPoints.mem_subgroup]
    intro actor
    change (actor : G) • (g⁻¹ • vector) = g⁻¹ • vector
    have hfix := (FixedPoints.mem_subgroup (M := A.conjBy g) (a := vector)).mp hvector
      ⟨g * (actor : G) * g⁻¹, Subgroup.mem_map_of_mem
        (MulAut.conj g).toMonoidHom actor.property⟩
    change (g * (actor : G) * g⁻¹) • vector = vector at hfix
    have := congrArg (fun value : V => g⁻¹ • value) hfix
    simpa [mul_smul] using this
  · rintro ⟨vector, hvector, rfl⟩
    rw [FixedPoints.mem_subgroup]
    rintro ⟨actor, source, hsource, rfl⟩
    have hfix := (FixedPoints.mem_subgroup (M := A) (a := vector)).mp hvector
      ⟨source, hsource⟩
    change (g * source * g⁻¹) • (g • vector) = g • vector
    simpa [mul_smul] using congrArg (fun value : V => g • value) hfix

private theorem oneA_conjugate
    {G V : Type u} [Group G] [Group V] [Finite V]
    [MulDistribMulAction G V] (S A : Subgroup G)
    (hA : oneA (V := V) S A) (g : S) :
    oneA (V := V) S (A.conjBy (g : G)) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  refine ⟨?_, IsElementaryAbelian.map (MulAut.conj (g : G)).toMonoidHom, ?_⟩
  · rintro element ⟨actor, hactor, rfl⟩
    exact S.mul_mem (S.mul_mem g.property (hA.1 hactor)) (S.inv_mem g.property)
  · unfold m
    rw [fixedPoints_conjugate, Subgroup.card_map_of_injective
      (f := (MulDistribMulAction.toMulAut G V (g : G)).toMonoidHom)
      (MulDistribMulAction.toMulAut G V (g : G)).injective]
    change (Nat.card V : ℚ) / ((Nat.card (FixedPoints.subgroup A V) : ℚ) *
      (Nat.card (A.map (MulAut.conj (g : G)).toMonoidHom) : ℚ)) ≤ 1
    rw [Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective]
    exact hA.2.2

private theorem selected_product_exhaustion
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (E : Subgroup G) (hE : E.Normal)
    (hsupp : E ⊔ (S : Subgroup G) = ⊤)
    (hselected : ∃ F : Finset (Subgroup G), IsInternalDirectProduct E F ∧
      ∀ D ∈ F, IsOneSevenFactor (V := V) D) :
    E = oneSevenGenerated (G := G) (V := V) := by
  classical
  let : E.Normal := hE
  obtain ⟨F, hprod, hF⟩ := hselected
  have hquot : IsPGroup 2 (G ⧸ E) := by
    apply S.isPGroup'.of_surjective ((QuotientGroup.mk' E).comp (S : Subgroup G).subtype)
    intro element
    obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective E element
    have hlift : lift ∈ E ⊔ (S : Subgroup G) := hsupp ▸ Subgroup.mem_top lift
    obtain ⟨normal, hnormal, sylow, hsylow, rfl⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hlift
    refine ⟨⟨sylow, hsylow⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul]
    have hnormalImage : (QuotientGroup.mk' E) normal = 1 :=
      (QuotientGroup.eq_one_iff normal).mpr hnormal
    rw [hnormalImage, one_mul]
  apply le_antisymm
  · rw [hprod.1]
    exact iSup_le fun factor => le_sSup (hF factor.val factor.property)
  · apply sSup_le
    intro D hD
    by_contra hnot
    have hED : E ≤ Subgroup.centralizer (D : Set G) := by
      rw [hprod.1]
      apply iSup_le
      intro factor member hmember other hother
      have hne : D ≠ factor.val := by
        intro heq
        apply hnot
        rw [heq, hprod.1]
        exact le_iSup (fun factor : {factor // factor ∈ F} => factor.val) factor
      exact ((oneSevenFactor_eq_or_commute h D factor.val hD
        (hF factor.val factor.property)).resolve_left hne) other hother member hmember
    have hdisj : Disjoint D E := by
      rw [disjoint_iff_inf_le]
      intro member hmember
      have hcentral : (⟨member, hmember.1⟩ : D) ∈ Subgroup.center D := by
        rw [Subgroup.mem_center_iff]
        intro other
        apply Subtype.ext
        exact hED hmember.2 other.val other.property
      rw [RankOneThreeGroupAssembly.center_eq_bot_of_isSL2Two hD.1] at hcentral
      exact congrArg Subtype.val hcentral
    let inclusion : D →* G ⧸ E := (QuotientGroup.mk' E).comp D.subtype
    have hinjective : Function.Injective inclusion := by
      apply inclusion.ker_eq_bot_iff.mp
      apply bot_unique
      intro member hmember
      have hmemE : (member : G) ∈ E :=
        (QuotientGroup.eq_one_iff (member : G)).mp hmember
      apply Subtype.ext
      exact hdisj.le_bot ⟨member.property, hmemE⟩
    obtain ⟨exponent, hcard⟩ := (hquot.of_injective inclusion hinjective).exists_card_eq
    have hthree : 3 ∣ 2 ^ exponent := by
      rw [← hcard, RankOneThreeGroupAssembly.isSL2Two_card hD.1]
      decide
    have hdiv : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide) hthree
    norm_num at hdiv

public theorem oneJ_le_of_offender_normalClosure_supplement
    {X V : Type u} [Group X] [Group V] [Finite X] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction X V]
    (h : Hypotheses X V) (U : Sylow 2 X) (A T : Subgroup X)
    (hA : oneA (V := V) (U : Subgroup X) A)
    (hTU : T ≤ (U : Subgroup X))
    (hTnormal : (T.subgroupOf (U : Subgroup X)).Normal)
    (hAT : A ≤ T)
    (hsupp : Subgroup.normalClosure (A : Set X) ⊔ (U : Subgroup X) = ⊤) :
    oneJ (V := V) (U : Subgroup X) ≤ T := by
  let conjugates : U → Subgroup X := fun actor => A.conjBy (actor : X)
  let J : Subgroup X := ⨆ actor, conjugates actor
  let E : Subgroup X := ⁅oddCore X, J⁆ ⊔ J
  let N : Subgroup X := oneSevenGenerated (G := X) (V := V)
  have hgenerators : ∀ actor, oneA (V := V) (U : Subgroup X) (conjugates actor) :=
    fun actor => oneA_conjugate (U : Subgroup X) A hA actor
  have hAJ : A ≤ J := by
    simpa only [conjugates, OneMemClass.coe_one, Subgroup.conjBy_one] using
      (le_iSup conjugates (1 : U))
  have hUT : (U : Subgroup X) ≤ Subgroup.normalizer (T : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTU).mp hTnormal
  have hJT : J ≤ T := by
    apply iSup_le
    intro actor element helement
    obtain ⟨source, hsource, rfl⟩ := helement
    exact (Subgroup.mem_normalizer_iff.mp (hUT actor.property) source).mp (hAT hsource)
  have hJU : J ≤ (U : Subgroup X) := hJT.trans hTU
  have hUJ : (U : Subgroup X) ≤ Subgroup.normalizer (J : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro actor hactor element helement
    have hle : J ≤ J.comap (MulAut.conj actor).toMonoidHom := by
      apply iSup_le
      intro conjugator source hsource
      have hmem : source ∈ A.conjBy (conjugator : X) := hsource
      obtain ⟨original, horiginal, rfl⟩ := hmem
      have htarget : A.conjBy (actor * (conjugator : X)) ≤ J :=
        le_iSup conjugates (⟨actor, hactor⟩ * conjugator)
      apply htarget
      refine ⟨original, horiginal, ?_⟩
      change (actor * (conjugator : X)) * original * (actor * (conjugator : X))⁻¹ =
        actor * ((conjugator : X) * original * (conjugator : X)⁻¹) * actor⁻¹
      group
    exact hle helement
  obtain ⟨hEN, hEnormal, hproduct⟩ :=
    offender_selected_finite_product h U conjugates hgenerators J rfl
  have hNE : N ≤ Subgroup.normalizer (E : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEN).mp hEnormal
  have hUE : (U : Subgroup X) ≤ Subgroup.normalizer (E : Set X) := by
    let W := oddCore X
    let : W.Normal := pPrimeCore_normal
    intro actor hactor
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hW : W.map (MulAut.conj actor).toMonoidHom = W :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (show actor ∈ Subgroup.normalizer (W : Set X) by
          rw [Subgroup.normalizer_eq_top]; trivial)
    have hJ : J.map (MulAut.conj actor).toMonoidHom = J :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hUJ hactor)
    change (⁅W, J⁆ ⊔ J).map (MulAut.conj actor).toMonoidHom = ⁅W, J⁆ ⊔ J
    rw [Subgroup.map_sup, Subgroup.map_commutator, hW, hJ]
  have hAN : A ≤ N := hAJ.trans (le_sup_right.trans hEN)
  let : N.Normal := (oneSeven_global_product h U).1
  have hNU : N ⊔ (U : Subgroup X) = ⊤ := by
    apply top_le_iff.mp
    rw [← hsupp]
    exact sup_le_sup (Subgroup.normalClosure_le_normal hAN) le_rfl
  have hE : E.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [← hNU]
    exact sup_le hNE hUE
  let : E.Normal := hE
  have hEU : E ⊔ (U : Subgroup X) = ⊤ := by
    apply top_le_iff.mp
    rw [← hsupp]
    exact sup_le_sup (Subgroup.normalClosure_le_normal (hAJ.trans le_sup_right)) le_rfl
  have hfull : E = N := selected_product_exhaustion h U E hE hEU hproduct
  rw [(oneSeven_global_identification h U).1]
  change (U : Subgroup X) ⊓ N ≤ T
  rw [← hfull, ← oddCore_commutator_join_sylow_inf U J hJU]
  exact hJT

end Stellmacher.SectionOne
