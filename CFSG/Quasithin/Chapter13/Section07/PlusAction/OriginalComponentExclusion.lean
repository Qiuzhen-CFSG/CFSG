module
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalLocal
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.OrdinaryParabolic
public import Theory.GroupTheory.PResidual.SimpleQuotientNormalGeneration

public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalParabolicTerminal
public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalComponentRows

/-!
# The original primitive component kernel contradiction

A doubled natural kernel actor supplies a subgroup K₀ in its Baumann
normalizer whose order is divisible by three. Under the actual Baumann
bound K₀ lies in M. The source theta identity places an element of order
three in the point residual L₁. Since the primitive kernel is normal in H,
the simple cubic quotient and two-perfectness of L₁ then force L₁ into that
kernel, contradicting its original escape selection.

The literal reduced-action consumer connects this argument to B.5.6. The
last theorem constructs the source minimal subgroup and excludes the binary
PSL₃ component row: its order makes the A₅ marking premise vacuous. The
Baumann bound and centralization of L₁ modulo the component core remain
genuine earlier-source inputs.

Source: Aschbacher--Smith, 13.7.4(1), printed pp.937--938, with 13.2.2(7).
-/

set_option backward.isDefEq.respectTransparency false
public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
open Stellmacher ChapterB.QuasisimpleSource ChapterB.SourceInduction ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- A normal primitive kernel not containing L₁ has no subgroup of order
divisible by three lying in the original M. -/
theorem source_kernel_no_cubic_overlap
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    {K : Subgroup G} (hKH : K ≤ H)
    (hKn : H ≤ normalizer (K : Set G))
    (hnot : ¬ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ≤ K)
    (K₀ : Subgroup G) (hK₀K : K₀ ≤ K) (hK₀M : K₀ ≤ M)
    (hcard : 3 ∣ Nat.card K₀) : False := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := K₀) 3 hcard
  have hxG : orderOf (x : G) = 3 := (K₀.orderOf_coe x).trans hx
  have htheta := d.source_theta_normalizer h1221
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hxL : (x : G) ∈ L := htheta ▸ subset_closure ⟨hK₀M x.property,hxG⟩
  have hxGz : (x : G) ∈ F.Gz := h.H_centralizes (hKH (hK₀K x.property))
  let y : ↥(F.L ⊓ F.Gz) := ⟨x,hxL,hxGz⟩
  have hy : orderOf y = 3 := ((F.L ⊓ F.Gz).orderOf_coe y).symm.trans hxG
  have hxB : (x : G) ∈ F.L₁ := by
    exact ⟨y,mem_pResidual_of_orderOf_coprime (by rw [hy];decide),rfl⟩
  let b : F.L₁ := ⟨x,hxB⟩
  let N := K.subgroupOf F.L₁
  let : N.Normal := normal_subgroupOf_of_le_normalizer (le_sup_left.trans h.local_le |>.trans hKn)
  let f := QuotientGroup.mk' (pCore 2 F.L₁)
  have hc : Nat.card (F.L₁ ⧸ pCore 2 F.L₁) = 3 := by
    rw [source_local_residual_eq d h]
    exact Section03.Noncentrality.ordinary_point_residual_quotient_card d eL
  let : IsSimpleGroup (F.L₁ ⧸ pCore 2 F.L₁) := isSimpleGroup_of_prime_card hc
  have hb : orderOf b = 3 := (F.L₁.orderOf_coe b).symm.trans hxG
  have hker : IsPGroup 2 f.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hbimage : f b ≠ 1 := by
    intro he
    have hm : b ∈ pCore 2 F.L₁ := (QuotientGroup.eq_one_iff b).mp he
    have ho := (pCore_isPGroup (p := 2) (G := F.L₁)).orderOf_coprime
      (by decide : Nat.Coprime 2 3) (⟨b,hm⟩ : pCore 2 F.L₁)
    have hh : orderOf (⟨b,hm⟩ : pCore 2 F.L₁) = 3 :=
      ((pCore 2 F.L₁).orderOf_coe _).symm.trans hb
    rw [hh] at ho
    norm_num at ho
  have hNimage : N.map f ≠ ⊥ := by
    intro he
    have hm : f b ∈ N.map f := mem_map_of_mem f (hK₀K x.property)
    rw [he,mem_bot] at hm
    exact hbimage hm
  have hp : IsPPerfect 2 F.L₁ := isPPerfect_embedded_pResidual 2 _
  have hgen : normalClosure (N : Set F.L₁) = ⊤ :=
    normalClosure_eq_top_of_pPerfect_simple_image hp f
      (QuotientGroup.mk'_surjective (pCore 2 F.L₁)) hker N hNimage
  have hn : N = ⊤ := by
    apply top_unique
    rw [←hgen]
    exact normalClosure_le_normal (fun _ hx => hx)
  apply hnot
  intro z hz
  exact (show (⟨z,hz⟩ : F.L₁) ∈ N from hn ▸ mem_top _) 

/-- The actual doubled reduced component action contradicts the original
primitive kernel selection through the source Baumann bound. -/
theorem source_component_reduced_false
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hKC : (J.map H.subtype) ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer ((J.map H.subtype) : Set G))
    (hnot : ¬ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ≤ J.map H.subtype)
    (hcomm : ⁅(J.map H.subtype),(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤ (J.map H.subtype).pCoreIn 2)
    (U : Subgroup ↥((J.map H.subtype) ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hred : IsPReduced 2 U)
    (hU0 : U ≤ (fixedLayer (ConjugateIntersections.sourceSetup T L V V₃ V₁ H)).subgroupOf
      ((J.map H.subtype) ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))))
    (hout : ¬ J.map H.subtype ≤ M)
    (hB : normalizer (baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (hne : U ≠ ⊥)
    (hmove : ⁅U,(J.map H.subtype).subgroupOf (J.map H.subtype ⊔
      ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G)))⁆ = U)
    (hdouble : let X := (J.map H.subtype) ⊔ ((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔ (T : Subgroup G))
      letI := hred.normal
      letI := hred.elementary
      let q := QuotientGroup.mk' (centralizer (U : Set X))
      let C := ((J.map H.subtype).subgroupOf X).map q
      let ρ := NormalElementaryQuotient.representation U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      Nonempty (ActionEquiv (V := Additive U) (ρ.comp C.subtype)
        (repeated (linearNatural BinaryField.two 3) 2))) : False := by
  obtain ⟨K₀,hK₀K,hK₀B,_,hc⟩ := source_component_doubled_baumann_terminal h J hJ hs
    hKC hKn hcomm U hred hU0 hout hB hne hmove hdouble
  exact source_kernel_no_cubic_overlap d h1221 h eL
    (hKC.trans (kernel_le_H (D := ConjugateIntersections.sourceSetup T L V V₃ V₁ H)))
    hKn hnot K₀ hK₀K (hK₀B.trans hB) hc

/-- The PSL₃(2) component row is excluded without any A₅ module marking. -/
theorem source_primitive_linearThree_false
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h1221 : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hm : ⁅(normalizer (V₁ : Set G)).pCoreIn 2,V₂⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hJn : H ≤ normalizer (J.map H.subtype : Set G))
    (hp : IsPPerfect 2 (J.map H.subtype)) (hout : ¬ J.map H.subtype ≤ M)
    (hnot : ¬ (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ≤ J.map H.subtype)
    (hcomm : ⁅J.map H.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤
      (J.map H.subtype).pCoreIn 2)
    (hB : normalizer (baumann
      (((ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁ ⊔
        (T : Subgroup G)).pCoreIn 2) : Set G) ≤ M)
    (hl : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 2) : False := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let K := J.map H.subtype
  let P := F.L₁ ⊔ (T : Subgroup G)
  let X := K ⊔ P
  obtain ⟨U,hUD,hUU₂,hr,hne,hUK,hUL,hmin,hn,hff⟩ :=
    source_primitive_component_minimal_doubleThree d h1221 h hU eL hm J hJ hs
      hJC hJn hp hout hcomm hB (Or.inr hl)
  let := hr.normal
  let := hr.elementary
  let q := QuotientGroup.mk' (centralizer (U : Set X))
  let C := (K.subgroupOf X).map q
  let E := C ⊔ ((P.pCoreIn 2).subgroupOf X).map q
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let := hn
  obtain ⟨e⟩ := source_primitive_reduced_actor_equiv h J hJC hJn U hr hne hUK hs
  have hc : Nat.card C = 168 := by
    obtain ⟨F₀,hF,hfin,hcard,⟨a⟩⟩ := hl
    let := hF
    let := hfin
    let := Fintype.ofFinite F₀
    let f : F₀ ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F₀ Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
    let ea := (e.symm.trans a).trans
      ((Atlas.fieldEquivPSL 3 f).trans Matrix.PSL3Two.equiv.symm)
    exact (Nat.card_congr ea.toEquiv).trans
      Matrix.PSL3Two.card_SL
  have hA5 : Nat.card C = 60 → Nonempty (ActionEquiv
      ((MovedSection.ofNormal (ρ.comp E.subtype) (C.subgroupOf E)).action.comp
        (C.subgroupOf E).subtype) (alternatingNatural 5)) := by
    intro h60
    have hf : (168 : ℕ) = 60 := hc.symm.trans h60
    norm_num at hf
  have hU0 : U ≤ (fixedLayer F).subgroupOf X :=
    hUU₂.trans (comap_mono (source_kernel_mixed_geometry d h hJC hJn hp hcomm).2.2.1)
  exact source_component_reduced_false d h1221 h eL J hJ hs hJC hJn hnot hcomm
    U hr hU0 hout hB hne hUK (hff hA5)

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
