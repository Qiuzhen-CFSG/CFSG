module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryReduced
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete
public import Theory.Representation.BinaryOffender.RankOneNormalClosure
public import Theory.Representation.ElementaryAbelianAction

/-!
# Classification of the reduced transvection closure

Under the contrary abelian-closure assumption in 6.1.19, the checked
reduced action on W/Z_S has trivial two-core. Each nonidentity element of
the moving actor has displacement rank one: its displacement embeds in the
order-two commutator line, and faithfulness rules out rank zero. Its cyclic
subgroup is consequently a best offender. Conjugating these cyclic subgroups
and restricting to the literal normal closure proves the FF generation
hypothesis for that whole image.

The original closure subgroup lies in C_G(z), so the ambient QTKE hypotheses
supply a genuine finite SQTK cover. The complete B.5 classification now applies
to this particular action, with its quotient, maps and transvections retained.
This uses W/Z_S throughout and does not assert core vanishing on W/<z>.
The component sieve, amalgam contradiction and initial naturalness remain
with qt-d-1222-rankone-recognition-natural, which owns unconditional 6.1.27.
Source: Aschbacher–Smith, 6.1.19, printed pp.674–675, and B.5.3–6, pp.104–105.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u

private theorem transvection_rank_bound
    {X : Type*} [Group X] [Finite X] [IsElementaryAbelian 2 X]
    (A : Subgroup (MulAut X)) (hc : Nat.card (commutatorAction A X) = 2)
    (a : MulAut X) (ha : a ∈ A) :
    Module.finrank (ZMod 2)
      (LinearMap.range (Representation.ofElementaryAbelianAction
        (A := MulAut X) (G := X) (p := 2) a - LinearMap.id)) ≤ 1 := by
  let ρ := Representation.ofElementaryAbelianAction (A := MulAut X) (G := X) (p := 2)
  let D := LinearMap.range (ρ a - LinearMap.id)
  have hmem (v : D) : v.val.toMul ∈ commutatorAction A X := by
    obtain ⟨w,hw⟩ := v.property
    rw [←hw]
    change (a w.toMul) / w.toMul ∈ commutatorAction A X
    have hh : w.toMul⁻¹ * (⟨a,ha⟩ : A) • w.toMul ∈ commutatorAction A X :=
      subset_closure ⟨⟨a,ha⟩,w.toMul,mem_top _,rfl⟩
    change w.toMul⁻¹ * a w.toMul ∈ commutatorAction A X at hh
    simpa only [div_eq_mul_inv,mul_comm] using hh
  let f : D → commutatorAction A X := fun v => ⟨v.val.toMul,hmem v⟩
  have hf : Function.Injective f := by
    intro v w h
    exact Subtype.ext (Additive.toMul.injective (congrArg (fun z : commutatorAction A X => z.val) h))
  have hcard : Nat.card D ≤ 2 := (Nat.card_le_card_of_injective f hf).trans_eq hc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hcard
  change Module.finrank (ZMod 2) D ≤ 1
  by_contra hn
  have hh : 2^2 ≤ 2 ^ Module.finrank (ZMod 2) D := Nat.pow_le_pow_right (by decide) (by omega)
  omega

private theorem transvection_span_generated
    {X : Type*} [Group X] [Finite X] [IsElementaryAbelian 2 X]
    (A B : Subgroup (MulAut X)) [IsElementaryAbelian 2 A]
    (hc : Nat.card (commutatorAction A X) = 2) :
    let J := conjugateSpanBy A B
    offenderSubgroup (Representation.ofElementaryAbelianAction
      (A := J) (G := X) (p := 2)) = ⊤ := by
  let ρ := Representation.ofElementaryAbelianAction (A := MulAut X) (G := X) (p := 2)
  let J := conjugateSpanBy A B
  let θ := Representation.ofElementaryAbelianAction (A := J) (G := X) (p := 2)
  have heq : θ = ρ.comp J.subtype := rfl
  let O := offenderSubgroup θ
  have hJO : J ≤ O.map J.subtype := by
    change conjugateSpanBy A B ≤ _
    rw [conjugateSpanBy_eq_iSup_conj]
    apply iSup_le
    intro b
    rintro x ⟨a,ha,rfl⟩
    by_cases ha1 : a = 1
    · simp only [ha1,map_one,one_mem]
    have hpow : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
    have hbest := bestOffender_of_involution_displacement_le_one ρ a hpow ha1
      (transvection_rank_bound A hc a ha)
    have hconj := hbest.map_conj ρ (b : MulAut X)
    have hle : (zpowers a).map (MulAut.conj (b : MulAut X)).toMonoidHom ≤ J := by
      intro x hx
      exact (le_iSup (fun b : B => A.map (MulAut.conj (b : MulAut X)).toMonoidHom) b)
        (map_mono (zpowers_le.mpr ha) hx) |> (conjugateSpanBy_eq_iSup_conj A B).symm.le
    have hrestrict := hconj.subgroupOf ρ hle
    have hm : MulAut.conj (b : MulAut X) a ∈
        (zpowers a).map (MulAut.conj (b : MulAut X)).toMonoidHom :=
      mem_map_of_mem _ (mem_zpowers a)
    refine mem_map.mpr ⟨⟨_,hle hm⟩,?_,rfl⟩
    change _ ∈ offenderSubgroup θ
    rw [heq]
    exact hrestrict.le_offenderSubgroup _ hm
  apply top_unique
  intro j _
  obtain ⟨k,hk,he⟩ := hJO j.property
  exact (show k = j from Subtype.ext he) ▸ hk

private theorem reduced_image_classification
    {I X : Type u} [Group I] [Finite I] [Group X] [Finite X]
    [IsElementaryAbelian 2 X]
    (σ : I →* MulAut X) (E P : Subgroup I)
    (hsq : IsSQTK KnownSimple.IsKnownSimple I)
    (hA : IsElementaryAbelian 2 (E.map σ))
    (hpos : 1 < Nat.card (E.map σ))
    (hline : Nat.card (commutatorAction (E.map σ) X) = 2)
    (hspan : P.map σ = conjugateSpanBy (E.map σ) σ.range)
    (hcore : pCore 2 (P.map σ) = ⊥) :
    let J := P.map σ
    let θ := Representation.ofElementaryAbelianAction (A := J) (G := X) (p := 2)
    ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple θ ∧
      ChapterB.SourceInduction.NontrivialAdequateAlternative θ ∧
      ∀ t : J, (t : MulAut X) ∈ E.map σ → t ≠ 1 →
        Module.finrank (ZMod 2) (LinearMap.range (θ t - LinearMap.id)) = 1 := by
  let J := P.map σ
  let θ := Representation.ofElementaryAbelianAction (A := J) (G := X) (p := 2)
  have hf : Function.Injective θ := by
    intro j k he
    apply Subtype.ext
    ext x
    exact Additive.ofMul.injective (congrArg (fun f => f (Additive.ofMul x)) he)
  have hgen : offenderSubgroup θ = ⊤ := by
    change offenderSubgroup (Representation.ofElementaryAbelianAction
      (A := P.map σ) (G := X) (p := 2)) = ⊤
    rw [hspan]
    let := hA
    exact transvection_span_generated (E.map σ) σ.range hline
  let q := σ.subgroupMap P
  let cover : ChapterB.SourceInduction.SQTKQuotient KnownSimple.IsKnownSimple J := {
    Cover := P
    kernel := q.ker
    sqtk := hsq.subgroup P
    equiv := QuotientGroup.quotientKerEquivOfSurjective q (σ.subgroupMap_surjective P) }
  have hff : ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple θ :=
    ⟨inferInstance,hf,hcore,hgen,⟨cover⟩⟩
  have hAJ : E.map σ ≤ J :=
    (le_conjugateSpanBy (E.map σ) σ.range).trans hspan.symm.le
  have hJne : J ≠ ⊥ := by
    intro hz
    have hzA : E.map σ = ⊥ := bot_unique (hz ▸ hAJ)
    rw [hzA,card_bot] at hpos
    omega
  let : Nontrivial J := (nontrivial_iff_ne_bot J).mpr hJne
  refine ⟨hff,ChapterB.SourceInduction.nontrivialAdequateAlternative_knownSimple θ hff,?_⟩
  intro t ht hn
  change Module.finrank (ZMod 2) (LinearMap.range (θ t - LinearMap.id)) = 1
  have hle := transvection_rank_bound (E.map σ) hline (t : MulAut X) ht
  change Module.finrank (ZMod 2) (LinearMap.range (θ t - LinearMap.id)) ≤ 1 at hle
  have hne : Module.finrank (ZMod 2) (LinearMap.range (θ t - LinearMap.id)) ≠ 0 := by
    intro hz
    have hz' : θ t - LinearMap.id = 0 :=
      LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
    apply hn
    apply hf
    rw [map_one]
    change θ t = LinearMap.id
    exact sub_eq_zero.mp hz'
  exact Nat.le_antisymm hle (Nat.one_le_iff_ne_zero.mpr hne)

open CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)

/-- The actual reduced action satisfies B.5.3 and its proved nontrivial
classification. Every surviving element of the moving actor is a transvection.
The source naturalness and the subsequent component/amalgam analysis remain
with the owner of the unconditional 6.1.27 theorem. -/
theorem exists_reduced_ff_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧ Z' ≤ W ∧ E ⊓ W = Z' ∧
      ∃ (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hN : (Z.subgroupOf W).Normal),
      letI := hN
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := hX
        let A := (E.subgroupOf I).map σ
        let J := (P.subgroupOf I).map σ
        let θ : Representation (ZMod 2) J (Additive (W ⧸ Z.subgroupOf W)) :=
          Representation.ofElementaryAbelianAction
          (A := J) (G := W ⧸ Z.subgroupOf W) (p := 2)
        IsElementaryAbelian 2 A ∧ 1 < Nat.card A ∧ Nat.card A ≤ 4 ∧
        commutatorAction A (W ⧸ Z.subgroupOf W) =
          (Z'.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)) ∧
        Nat.card ((Z'.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W))) = 2 ∧
        commutatorAction₂ A (W ⧸ Z.subgroupOf W) = ⊥ ∧
        σ.ker = (commutatorPreimage I W Z).subgroupOf I ∧
        J = conjugateSpanBy A σ.range ∧ pCore 2 J = ⊥ ∧
        ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple θ ∧
        ChapterB.SourceInduction.NontrivialAdequateAlternative θ ∧
        ∀ t : J, (t : MulAut (W ⧸ Z.subgroupOf W)) ∈ A → t ≠ 1 →
          Module.finrank (ZMod 2) (LinearMap.range
            (θ t - LinearMap.id (R := ZMod 2) (M := Additive (W ⧸ Z.subgroupOf W)))) = 1 := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hZ'W,hEW,hIW,hN,σ,hσ,hX,hA,hpos,hsize,
      hdisp,hcard,hquad,hker,hspan,hcore,_⟩ :=
    d.exists_reduced_transvection_action h hnat hE hs hNS hab
  let I := Escape.I (T : Subgroup G) L R
  let Z := ZS (T : Subgroup G) L R
  let W := Escape.U (T : Subgroup G) L R ⊓
    conjugateSpanBy Z (centralizer ({z} : Set G))
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let P := conjugateSpanBy E I
  let := hN
  let := hX
  have hIC : I ≤ centralizer ({z} : Set G) := by
    intro i hi
    exact mem_centralizer_singleton_iff.mpr (hi z hz).symm
  have hsqI : IsSQTK KnownSimple.IsKnownSimple I :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hIC)).mp
      ((h.simpleQTKE.involution_centralizer_sqtk ho).subgroup
        (I.subgroupOf (centralizer ({z} : Set G))))
  have hline : Nat.card (commutatorAction ((E.subgroupOf I).map σ)
      (W ⧸ Z.subgroupOf W)) = 2 := hdisp ▸ hcard
  have hclass := reduced_image_classification σ (E.subgroupOf I) (P.subgroupOf I)
    hsqI hA hpos hline hspan hcore
  exact ⟨hn,z,a,hz,ho,hEI,hZW,hZ'W,hEW,hIW,hN,σ,hσ,hX,hA,hpos,hsize,
    hdisp,hcard,hquad,hker,hspan,hcore,hclass⟩

end NaturalEscapeGraph.OddConfiguration

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
