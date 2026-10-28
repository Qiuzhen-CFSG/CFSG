module
public import Stellmacher.SectionEight.EightTwoBackwardNativeQuotient
public import Stellmacher.SectionEight.EightTwoBackwardHallOrbitReduction
public import Stellmacher.SectionTwo.OddNormalizerTranslate
public import Stellmacher.SectionTwo.LemmaTwoFive
public import Theory.GroupTheory.Hall.OddSylowComplement

/-!
# The initial core intersection in the backward case of (8.2)

First-step noncentrality and a critical path of length greater than one
exclude normality of the first core intersection in the initial stabilizer.
The normal supplement L = Ea Qfirst supplies the native Sylow and (2.5)
quotient hypotheses. Let W be the odd-complement orbit closure of its native
module. Result (2.5) makes W normal in L; its definition makes it normal
under the complement U, and W lies in Qfirst, hence in the common Sylow S.
The further closure X = ⟨W^S⟩ is normalized by both stabilizers, using their
literal products S L and S U. It is a two-group, so generation and the
trivial ambient two-core force X to vanish, contrary to criticality.

This implements the normal-subgroup contradiction in Stellmacher (8.2),
first containment case, printed pp.37–38, refs/latex/stellmacher-n-group.tex.
It keeps the native orbit closure without identifying it with the graph's
neighbor module; no Thompson-noncontainment or omega-center upper bound is
needed. The two-stage closure argument also occurs in the proof of (6.1).
-/

open scoped Pointwise
namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u

private theorem le_left_of_set_product
    {G : Type*} [Group G] (P S L : Subgroup G)
    (hprod : (P : Set G) = (S : Set G) * (L : Set G)) : S ≤ P := by
  intro s hs
  change s ∈ (P : Set G)
  rw [hprod]
  exact Set.mem_mul.mpr ⟨s, hs, 1, L.one_mem, by simp⟩

private theorem product_le_normalizer_conjugateClosure
    {G : Type*} [Group G] (P S L W : Subgroup G)
    (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hprod : (P : Set G) = (S : Set G) * (L : Set G)) :
    P ≤ Subgroup.normalizer (conjugateClosure W S : Set G) := by
  have hSP : S ≤ P := le_left_of_set_product P S L hprod
  rw [Subgroup.le_normalizer_iff]
  intro g hg x hx
  change x ∈ conjugateClosure W S at hx
  rw [conjugateClosure] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨s, w, rfl⟩ := hx
    have hgs : g * (s : G) ∈ P := P.mul_mem hg (hSP s.property)
    change g * (s : G) ∈ (P : Set G) at hgs
    rw [hprod] at hgs
    obtain ⟨t, ht, l, hl, htl⟩ := Set.mem_mul.mp hgs
    have hlw : l * (w : G) * l⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (hLW hl) (w : G)).mp w.property
    apply Subgroup.subset_closure
    refine ⟨⟨t, ht⟩, ⟨l * (w : G) * l⁻¹, hlw⟩, ?_⟩
    change g * ((s : G) * (w : G) * (s : G)⁻¹) * g⁻¹ =
      t * (l * (w : G) * l⁻¹) * t⁻¹
    calc
      g * ((s : G) * (w : G) * (s : G)⁻¹) * g⁻¹ =
          (g * (s : G)) * (w : G) * (g * (s : G))⁻¹ := by group
      _ = (t * l) * (w : G) * (t * l)⁻¹ := by rw [← htl]
      _ = t * (l * (w : G) * l⁻¹) * t⁻¹ := by group
  | one => simp
  | mul x y hx hy ihx ihy =>
    convert Subgroup.mul_mem _ ihx ihy using 1 ; group
  | inv x hx ih =>
    convert Subgroup.inv_mem _ ih using 1 ; group


public theorem eight_two_backward_core_intersection_obstruction_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (hlen : 1 < ctx.criticalPath.length)
    (hnormal : NormalIn
      (QAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
      (GAt ctx.Γ ctx.criticalPath.a)) : False := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let Pa := GAt Γ cp.a
  let Pb := GAt Γ cp.firstStep
  let L := EAt Γ cp.a ⊔ QAt Γ cp.firstStep
  let B := QAt Γ cp.firstStep
  obtain ⟨hLN, hgen, T, hT, hchar⟩ :=
    eight_two_local_setup_of_core_intersection_normal_local ctx hnormal
  obtain ⟨hsec, hunique, projection, hsurj, hker⟩ :=
    eight_two_backward_native_quotient_local ctx hcenter hlen hnormal T hT
  obtain ⟨hSPb, R, hR⟩ := (SevenSix.edge_sylow_data h Γ cp).2
  obtain ⟨U, hodd, hcomp⟩ := Subgroup.exists_odd_complement_sylow_two
    (SevenSix.edge_local_data h Γ cp).2.2 R
  let actors := U.map Pb.subtype
  have hactorsOdd : Odd (Nat.card actors) := by
    rw [show actors = U.map Pb.subtype from rfl,
      Subgroup.card_map_of_injective Pb.subtype_injective]
    exact hodd
  have hactorsN : actors ≤ Subgroup.normalizer (B : Set H) :=
    (Subgroup.map_subtype_le U).trans (SevenSix.stabilizer_le_normalizer_q Γ cp.firstStep)
  let action := SectionTwo.sylowImageNormalizerAction T L.subtype
    L.subtype_injective B hT actors hactorsN
  have hactionOdd : Odd (Nat.card action.range) :=
    SectionTwo.sylowImageNormalizerAction_range_odd T L.subtype
      L.subtype_injective B hT actors hactorsN hactorsOdd
  have hVT : SectionTwo.vSubgroup T ≤ (T : Subgroup L) :=
    (SectionTwo.vSubgroup_le_twoCore_and_elementaryAbelian hsec T).1.trans
      (fitting_pCore_le_sylow T)
  let A := (SectionTwo.vSubgroup T).map L.subtype
  let W := conjugateClosure A actors
  have htranslate : (⨆ actor : action.range,
      SectionTwo.automorphismTranslateV T (actor : MulAut T)).map L.subtype = W :=
    SectionTwo.map_sylowImageNormalizerAction_translate_join T L.subtype
      L.subtype_injective B hT actors hactorsN hVT
  obtain ⟨K, hK, hKN, _⟩ := SectionTwo.lemma_two_five hsec T hchar hunique
    projection hsurj hker ⟨MulEquiv.ulift⟩ action.range hactionOdd
  have hKW : K.map L.subtype = W := by rw [hK]; exact htranslate
  have hLW : L ≤ Subgroup.normalizer (W : Set H) := by
    let _ : K.Normal := hKN
    have hm := Subgroup.le_normalizer_map (H := K) L.subtype
    rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hKW] at hm
  have hUW : actors ≤ Subgroup.normalizer (W : Set H) := by
    rw [show W = conjugateClosure A actors from rfl,
      conjugateClosure, Subgroup.le_normalizer_closure_iff]
    intro a ha x hx
    obtain ⟨b, w, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨⟨a * (b : H), actors.mul_mem ha b.property⟩, w, ?_⟩
    change a * ((b : H) * (w : H) * (b : H)⁻¹) * a⁻¹ =
      (a * (b : H)) * (w : H) * (a * (b : H))⁻¹
    group
  have hAB : A ≤ B := by
    exact (Subgroup.map_mono hVT).trans_eq hT
  have hWB : W ≤ B := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨a, w, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hactorsN a.property) (w : H)).mp (hAB w.property)
  have hBS : B ≤ S := (SevenSix.local_cores_le_edge_sylow h Γ cp).2
  have hP1prod : (Pa : Set H) = (S : Set H) * (L : Set H) := by
    have hLP : L ≤ Pa := hLN.1
    have hSP : S ≤ Pa := (SevenSix.edge_sylow_data h Γ cp).1.1
    have hSL : S ≤ Subgroup.normalizer (L : Set H) :=
      hSP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hLP).mp hLN.2)
    rw [← show L ⊔ S = Pa from hgen, sup_comm]
    exact Subgroup.coe_mul_of_left_le_normalizer_right S L hSL
  have hP2prod : (Pb : Set H) = (S : Set H) * (actors : Set H) := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨s, a⟩, he⟩ := hcomp.2 (⟨x, hx⟩ : Pb)
      exact Set.mem_mul.mpr ⟨s, hR.le (Subgroup.mem_map_of_mem _ s.property),
        a, Subgroup.mem_map_of_mem Pb.subtype a.property, congrArg Subtype.val he⟩
    · rintro ⟨s, hs, a, ha, rfl⟩
      exact Pb.mul_mem (hSPb hs) (Subgroup.map_subtype_le U ha)
  let X := conjugateClosure W S
  have hWX : W ≤ X := by
    intro w hw
    exact Subgroup.subset_closure ⟨1, ⟨w, hw⟩, by simp⟩
  have hXS : X ≤ S := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨s, w, rfl⟩
    exact S.mul_mem (S.mul_mem s.property (hBS (hWB w.property))) (S.inv_mem s.property)
  have hPaX : Pa ≤ Subgroup.normalizer (X : Set H) :=
    product_le_normalizer_conjugateClosure Pa S L W hLW hP1prod
  have hPbX : Pb ≤ Subgroup.normalizer (X : Set H) :=
    product_le_normalizer_conjugateClosure Pb S actors W hUW hP2prod
  have hgenerated : Pa ⊔ Pb = ⊤ := by
    change stabilizer ctx.Γ ctx.criticalPath.a ⊔ stabilizer ctx.Γ ctx.criticalPath.firstStep = ⊤
    rcases ctx.criticalPath.edge_stabilizers_are_P with hedge | hedge
    · rw [hedge.1, hedge.2]
      exact h.generated
    · rw [hedge.1, hedge.2, sup_comm]
      exact h.generated
  have hXnormal : X.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgenerated]
    exact sup_le hPaX hPbX
  have hSp : IsPGroup 2 S := by
    rw [← hR]
    exact R.isPGroup'.map Pb.subtype
  have hXbot : X = ⊥ := by
    apply le_bot_iff.mp
    exact (show X ≤ pCore 2 H from le_sSup ⟨hXnormal, hSp.to_le hXS⟩).trans_eq h.twoCore_eq_bot
  have hAW : A ≤ W := by
    intro w hw
    exact Subgroup.subset_closure ⟨1, ⟨w, hw⟩, by simp⟩
  have hZaA : z Γ cp.a ≤ A :=
    eight_two_backward_vertex_le_native_module_local ctx hnormal T hT
  have hZaBot : z Γ cp.a = ⊥ := le_bot_iff.mp ((hZaA.trans (hAW.trans hWX)).trans_eq hXbot)
  apply ctx.commutator_ne
  change ⁅z Γ cp.a, z Γ cp.a'⁆ = ⊥
  rw [hZaBot, Subgroup.commutator_bot_left]

end Stellmacher.SectionEight
