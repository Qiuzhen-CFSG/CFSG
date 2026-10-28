module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.AlternatingResidual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.PointResidual
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# The actual common Borel in the remaining field-four case

For an outside H of generation greater than one, the preceding reduction
constructs a faithful cubic B inside L and K. Since K centralizes the
original field line, the natural point-fixer lift puts B in L₁T, with the
full component two-core retained. The literal product BT has index five
in H. Its maximality therefore identifies it with H ∩ M and H ∩ L₁T.

The original field-four marking also identifies the two-core quotient of
L₁T with A₅ or S₅. Counting the common Sylow subgroup proves index five
on this side too. The normal core of the intersection in each original
side is exactly R₁, so their join lies in N_G(R₁). These identities supply
actual subgroup and kernel markings for the remaining ambient exclusion;
they do not assert uniqueness of abstract A₅ Sylow overgroups.

The field-four exclusion and universal 11.4.4 remain unfinished. Earlier
geometry, the surviving list, full 11.3.2 and Kz=K retain the producers
listed in AlternatingResidual. OddKernelNormalizer remains with
qt-d-1222-natural-odd-kernel-normalizer; the parent
qt-d-1222-shadow-components owns final discharge of those source inputs.
Source: Aschbacher–Smith 11.4.4, printed p.778 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation

private theorem sylow_index_fifteen
    {J : Type*} [Group J] [Finite J]
    (hm : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 5))) (U : Sylow 2 J) :
    (U : Subgroup J).index = 15 := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let W := U.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  have hi : (W : Subgroup (J ⧸ pCore 2 J)).index = (U : Subgroup J).index :=
    index_map_eq _ (QuotientGroup.mk'_surjective _) (by
      rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal U)
  have hc := (W : Subgroup (J ⧸ pCore 2 J)).card_mul_index
  have hs := W.card_eq_multiplicity
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    have hcard : Nat.card (J ⧸ pCore 2 J) = 60 := by
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hcard] at hs hc
    have hs4 : Nat.card W = 4 := hs.trans (by decide +kernel)
    rw [hs4,hi] at hc
    omega
  · obtain ⟨e⟩ := hm
    have hcard : Nat.card (J ⧸ pCore 2 J) = 120 := by
      rw [Nat.card_congr e.toEquiv]
      norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
    rw [hcard] at hs hc
    have hs8 : Nat.card W = 8 := hs.trans (by decide +kernel)
    rw [hs8,hi] at hc
    omega

private theorem cubic_product_index
    {J : Type*} [Group J] [Finite J] (U : Sylow 2 J) (B : Subgroup J)
    (hB : Nat.card B = 3)
    (hp : (B : Set J) * (U : Set J) = (U : Set J) * (B : Set J))
    (hi : (U : Subgroup J).index = 15) :
    (B ⊔ (U : Subgroup J)).index = 5 ∧
      (U : Subgroup J).relIndex (B ⊔ (U : Subgroup J)) = 3 := by
  have hd : Disjoint B (U : Subgroup J) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k,hk⟩ := U.isPGroup'.exists_card_eq
    rw [hB,hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hc := card_set_mul_mul_card_inf B (U : Subgroup J)
  rw [hd.eq_bot,card_bot,mul_one,←coe_sup_of_set_mul_comm B (U : Subgroup J) hp,hB] at hc
  change Nat.card (B ⊔ (U : Subgroup J) : Subgroup J) = 3 * Nat.card U at hc
  have hidx := (B ⊔ (U : Subgroup J)).card_mul_index
  have hu := (U : Subgroup J).card_mul_index
  rw [hi] at hu
  rw [hc] at hidx
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hfive : (B ⊔ (U : Subgroup J)).index = 5 := by nlinarith
  refine ⟨hfive,?_⟩
  have hmul := relIndex_mul_index (show (U : Subgroup J) ≤ B ⊔ (U : Subgroup J) from le_sup_right)
  rw [hfive,hi] at hmul
  omega

private theorem coatom_of_index_five {J : Type*} [Group J] [Finite J]
    (B : Subgroup J) (hi : B.index = 5) : IsCoatom B := by
  refine ⟨fun hh => by simp [hh] at hi,?_⟩
  intro C hBC
  have hd := index_dvd_of_le hBC.le
  rw [hi] at hd
  rcases (Nat.dvd_prime Nat.prime_five).mp hd with hc | hc
  · exact index_eq_one.mp hc
  · have hh := index_strictAnti hBC
    omega

private theorem normalCore_eq_twoCore_of_five_models
    {J : Type*} [Group J] [Finite J]
    (hm : Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 5)))
    (U : Sylow 2 J) (B : Subgroup J) (hUB : (U : Subgroup J) ≤ B)
    (hi : B.index = 5) : B.normalCore = pCore 2 J := by
  have hOB : pCore 2 J ≤ B := (pCore_isPGroup.le_sylow_of_normal U).trans hUB
  apply le_antisymm ?_ (normal_le_normalCore.mpr hOB)
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : q.ker = pCore 2 J := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    let N := B.normalCore.map q
    let : N.Normal := Normal.map inferInstance q hq
    have hn : N = ⊥ := by
      rcases (inferInstance : N.Normal).eq_bot_or_eq_top with hn | hn
      · exact hn
      have ht : B.map q = ⊤ := top_unique (hn ▸ map_mono B.normalCore_le)
      have hidx := index_map_eq B hq (hk ▸ hOB)
      rw [ht,hi,index_top] at hidx
      omega
    rw [←hk]
    exact (Subgroup.map_eq_bot_iff _).mp hn
  · obtain ⟨e⟩ := hm
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
    have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : q.ker = pCore 2 J := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    let N := B.normalCore.map q
    let : N.Normal := Normal.map inferInstance q hq
    have hn : N = ⊥ := by
      by_contra hn
      have hA := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 5) (by simp)
        ((nontrivial_iff_ne_bot N).mpr hn)
      have hd := index_dvd_of_le (hA.trans (map_mono B.normalCore_le))
      rw [alternatingGroup.index_eq_two,index_map_eq B hq (hk ▸ hOB),hi] at hd
      norm_num at hd
    rw [←hk]
    exact (Subgroup.map_eq_bot_iff _).mp hn

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- The full original point fixer lies in L₁T, retaining the component two-core. -/
theorem ofFlag_component_point_fixer_le_first_join :
    L ⊓ centralizer (f.Vi 0 : Set G) ≤ f.Li 0 ⊔ (T : Subgroup G) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L
    D.sylow_normalizes_component
  have hcoreT : pCore 2 L ≤ (T : Subgroup G).subgroupOf L :=
    hP ▸ pCore_isPGroup.le_sylow_of_normal P
  rintro a ⟨ha,hfix⟩
  let a' : L := ⟨a,ha⟩
  have hmodel : ∀ v ∈ f.space 0, c.modelAction (c.quotientMap a') v = v := by
    intro v hv
    obtain ⟨w,hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
    have hwp : (w : G) ∈ f.Vi 0 := by
      apply (c.mem_preimage _ w).mpr
      change (c.projection w).toAdd ∈ f.space 0
      rw [hw]
      exact hv
    have he : V.normalizerMonoidHom (inclusion D.normalizes a') w = w := by
      apply Subtype.ext
      change a * w * a⁻¹ = w
      rw [←hfix w hwp,mul_inv_cancel_right]
    have hh := c.projection_component_conjugation a' w
    rw [he,hw] at hh
    exact hh.symm
  obtain ⟨l,hl⟩ := LocalGeometry.Components.point_model_fixer_lifts_to_residual D S f
    (c.quotientMap a') hmodel
  let l' : L := ⟨l,(LocalGeometry.localResidual_le _ l.property).1⟩
  have hk : a' * l'⁻¹ ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply c.groupEquiv.injective
    change c.quotientMap (a' * l'⁻¹) = c.groupEquiv 1
    rw [map_mul,map_inv,hl,map_one,mul_inv_cancel]
  have hmem := (f.Li 0 ⊔ (T : Subgroup G)).mul_mem
    (mem_sup_right (hcoreT hk)) (mem_sup_left l.property)
  change a * (l : G)⁻¹ * (l : G) ∈ _ at hmem
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hmem

/-- The actual cubic in a hypothetical larger-generation H gives the common
maximal overgroup of T. Both its index and its normal core are literal. -/
theorem ofFlag_large_generation_common_borel
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H) :
    ∃ B : Subgroup G, Nat.card B = 3 ∧ B ≤ L ⊓ (ofFlag S f X z H).K ∧
      B ⊓ centralizer (V : Set G) = ⊥ ∧
      (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) ∧
      B ⊔ (T : Subgroup G) = H ⊓ normalizer (L : Set G) ∧
      H ⊓ (f.Li 0 ⊔ (T : Subgroup G)) = H ⊓ normalizer (L : Set G) ∧
      (H ⊓ normalizer (L : Set G)).relIndex H = 5 ∧
      (T : Subgroup G).relIndex (H ⊓ normalizer (L : Set G)) = 3 ∧
      (((H ⊓ normalizer (L : Set G)).subgroupOf H).normalCore).map H.subtype = f.Ri 0 := by
  obtain ⟨hfour,hcore,hn2,hm,hr⟩ := ofFlag_large_generation_two_core_models S f X z H
    h hcase he hlinear h1132 hcontrol hH hHz hn
  obtain ⟨B,hB,hBH,hBL,hfaith,hperm,hout⟩ := ofFlag_large_generation_cubic_hall S f X z H
    h hcase he hlinear h1132 hcontrol hH hHz hn
  have hBT : B ≤ f.Li 0 ⊔ (T : Subgroup G) :=
    (le_inf (hBL.trans inf_le_left)
      ((hBL.trans inf_le_right).trans h.line_component_centralizes)).trans
        (ofFlag_component_point_fixer_le_first_join S f)
  let U := T.subtype hH.1.1.2
  let B' := B.subgroupOf H
  have hB'H : B ≤ H := hBH.trans inf_le_left
  have hB' : Nat.card B' = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hB'H).toEquiv,hB]
  have hUmap : (U : Subgroup H).map H.subtype = (T : Subgroup G) := by
    change ((T : Subgroup G).subgroupOf H).map H.subtype = _
    exact map_subgroupOf_eq_of_le hH.1.1.2
  have hperm' : (B' : Set H) * (U : Set H) = (U : Set H) * (B' : Set H) := by
    apply Set.image_injective.mpr H.subtype_injective
    rw [Set.image_mul,Set.image_mul]
    change ((B'.map H.subtype : Subgroup G) : Set G) *
      (((U : Subgroup H).map H.subtype : Subgroup G) : Set G) =
      (((U : Subgroup H).map H.subtype : Subgroup G) : Set G) *
        ((B'.map H.subtype : Subgroup G) : Set G)
    rw [hUmap,map_subgroupOf_eq_of_le hB'H]
    exact hperm
  obtain ⟨hi,htri⟩ := cubic_product_index U B' hB' hperm' (sylow_index_fifteen hm U)
  have hmap : (B' ⊔ (U : Subgroup H)).map H.subtype = B ⊔ (T : Subgroup G) := by
    rw [Subgroup.map_sup,hUmap,map_subgroupOf_eq_of_le hB'H]
  have hle : B' ⊔ (U : Subgroup H) ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H := by
    apply sup_le
    · intro b hb
      exact hBH hb
    · intro t ht
      exact ⟨t.property,D.sylow_normalizes_component ht⟩
  have hproper : (H ⊓ normalizer (L : Set G)).subgroupOf H ≠ ⊤ := by
    intro hh
    exact hH.1.2 ((subgroupOf_eq_top.mp hh).trans inf_le_right)
  have heq : B' ⊔ (U : Subgroup H) = (H ⊓ normalizer (L : Set G)).subgroupOf H :=
    ((coatom_of_index_five _ hi).le_iff_eq hproper).mp hle |>.symm
  have heqG : B ⊔ (T : Subgroup G) = H ⊓ normalizer (L : Set G) := by
    rw [←hmap,heq,map_subgroupOf_eq_of_le inf_le_left]
  have hA : f.Li 0 ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le ((LocalGeometry.localResidual_le _).trans (inf_le_left.trans L.le_normalizer))
      D.sylow_normalizes_component
  refine ⟨B,hB,hBL,hfaith,hperm,heqG,?_,?_,?_,?_⟩
  · apply le_antisymm (inf_le_inf_left H hA)
    rw [←heqG]
    exact le_inf (sup_le hB'H hH.1.1.2) (sup_le hBT le_sup_right)
  · change ((H ⊓ normalizer (L : Set G)).subgroupOf H).index = 5
    rwa [←heq]
  · have hh := relIndex_map_map_of_injective (U : Subgroup H)
      (B' ⊔ (U : Subgroup H)) H.subtype_injective
    rw [hmap,heqG,hUmap] at hh
    exact hh.trans htri
  · have hc := normalCore_eq_twoCore_of_five_models hm U
      (B' ⊔ (U : Subgroup H)) le_sup_right hi
    rw [heq] at hc
    rw [hc]
    exact hcore


private theorem ofFlag_first_join_five_models (hfour : S.field.degree = 2) :
    Nonempty (((f.Li 0 ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (f.Li 0 ⊔ (T : Subgroup G) : Subgroup G)) ≃* alternatingGroup (Fin 5)) ∨
    Nonempty (((f.Li 0 ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (f.Li 0 ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨f₀,hu,_,hq,_⟩ := LocalGeometry.exists_unique_marked_flag D S c
  have hh : f.Li 0 = f₀.Li 0 := congrArg
    (fun U => LocalGeometry.localResidual L (c.preimage U))
    (hu 0 _ (f.dimension 0) (f.invariant 0))
  have hseed : Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃*
      Theory.PSL2.Group S.field.Carrier) := hh.symm ▸ hq 0
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (S.field.card_eq.trans (by rw [hfour]; rfl))
  exact Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement
    (f.Li 0) (T : Subgroup G) (f.sylow_normalizes_Li 0) T.isPGroup' (hseed.some.trans e5)

/-- Both original sides have the same index-five intersection and the same
normal core R₁. This is a marked pair inside N_G(R₁), not a uniqueness
assertion about abstract A₅ overgroups. -/
theorem ofFlag_large_generation_paired_borel
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (hcase : Source.ClassicalRefinementCase L (f.Li 0) (ofFlag S f X z H).K 1 S.field.degree)
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H))
    (hn : 1 < ChapterE.generationParameter H) :
    let A := f.Li 0 ⊔ (T : Subgroup G)
    let C := H ⊓ A
    C = H ⊓ normalizer (L : Set G) ∧
      C.relIndex H = 5 ∧ C.relIndex A = 5 ∧
      ((C.subgroupOf H).normalCore).map H.subtype = f.Ri 0 ∧
      ((C.subgroupOf A).normalCore).map A.subtype = f.Ri 0 ∧
      H ⊔ A ≤ normalizer (f.Ri 0 : Set G) := by
  obtain ⟨B,_,_,_,_,_,hinter,hi,htri,hcore⟩ :=
    ofFlag_large_generation_common_borel S f X z H h hcase he hlinear h1132 hcontrol hH hHz hn
  let A := f.Li 0 ⊔ (T : Subgroup G)
  let C := H ⊓ A
  have hTC : (T : Subgroup G) ≤ C := le_inf hH.1.1.2 le_sup_right
  have hfour := ofFlag_large_generation_field_four S f X z H h hcase he
    hlinear h1132 hcontrol hH hHz hn
  have hm := ofFlag_first_join_five_models S f hfour
  let U := T.subtype (show (T : Subgroup G) ≤ A from le_sup_right)
  have hTA : (T : Subgroup G).relIndex A = 15 := sylow_index_fifteen hm U
  have hCA : C.relIndex A = 5 := by
    have ht : (T : Subgroup G).relIndex C = 3 := by
      simpa only [C,A,hinter] using htri
    have hh := relIndex_mul_relIndex (T : Subgroup G) C A hTC inf_le_right
    rw [ht,hTA] at hh
    omega
  have hcoreA := normalCore_eq_twoCore_of_five_models hm U (C.subgroupOf A)
    (fun t ht => hTC ht) hCA
  have hHcore := ofFlag_large_generation_core_eq_radical S f X z H h hcase he
    hlinear h1132 hcontrol hH hHz hn
  have hHN : H ≤ normalizer (f.Ri 0 : Set G) := by
    rw [←hHcore]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hAN : A ≤ normalizer (f.Ri 0 : Set G) :=
    A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
  refine ⟨hinter,?_,hCA,?_,congrArg (map A.subtype) hcoreA,sup_le hHN hAN⟩
  · simpa only [C,A,hinter] using hi
  · simpa only [C,A,hinter] using hcore

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
