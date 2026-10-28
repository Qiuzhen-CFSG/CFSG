module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.JankoNormalizer
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import Theory.GroupTheory.PCoreCentralQuotient

/-!
# Centralizer restrictions on the ordinary J4 radical normalizer

The source local characteristic-two condition and the full normalizer
control make the component radical self-centralizing. This descends through
its central covering kernel: the normalizer has characteristic two, and a
central quotient preserves this property.

Actual involution fusion reduces containment in any involution centralizer
to the two certified native models. The first is excluded by the full moved
module; the second has no factor 27 in its order, whereas the full SL3(4)
quotient of the residual supplies that divisor. A centralizer of the radical
normalizer lies in the radical, so Cauchy's theorem now makes it trivial.

Both the B=L application in Source and the odd-normalizer application below
preserve full W and the original quotient maps. Exhaustive maximal-two-local
placement, degree-two centralizer control and the final 11.1.5 assembly remain
with qt-d-1222-natural-point-fixed-summand. These restrictions do not assert
that placement or full Sylow containment. Earlier-source discharge remains
with qt-d-1222-natural-normalizer-source.

Source: Aschbacher--Smith C.2.8, C.3.1--5, and the local inspections on
printed pp.611--612 and622. Native involution fusion and order certificates
retain their imported source attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem radical_selfcentralizing
    {A : Type*} [Group A] [Finite A] (P C : Subgroup A)
    (hP : IsPRadical 2 P) (hn : normalizer (P : Set A) ≤ C)
    (hC : centralizer (pCore 2 C : Set C) ≤ pCore 2 C) :
    centralizer (P : Set A) ≤ P := by
  have hQP : C.pCoreIn 2 ≤ P :=
    le_of_normalizer_le_normalizer_of_pCore_normalizer_le P (C.pCoreIn 2)
      hP.isPGroup (isPGroup_pCoreIn 2 C) hP.2.le
      (hn.trans (C.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image C (pCore 2 C))))
  intro x hx
  have hxC : x ∈ C := hn (Subgroup.centralizer_le_normalizer _ hx)
  apply hQP
  refine ⟨⟨x,hxC⟩,hC ?_,rfl⟩
  intro y hy
  exact Subtype.ext (hx y (hQP (mem_map_of_mem C.subtype hy)))

private theorem first_conjugate_or_second_type (z : Janko4.Model) (hz : orderOf z = 2) :
    (∃ g : Janko4.Model, centralizer ({z} : Set Janko4.Model) =
      Janko4.InvolutionCentralizers.First.centralizer.map (MulAut.conj g).toMonoidHom) ∨
    Nonempty (centralizer ({z} : Set Janko4.Model) ≃*
      Janko4.InvolutionCentralizers.Second.ambientCentralizer) := by
  rcases Janko4.OuterReduction.involution_isConj_of_max1_odd_index
    Janko4.OuterReduction.max1_odd_index_unconditional hz with h | h
  · obtain ⟨g,hg⟩ := isConj_iff.mp h
    left
    refine ⟨g,?_⟩
    change _ = (centralizer ({Janko4.a} : Set Janko4.Model)).map _
    rw [map_centralizer_equiv,Set.image_singleton]
    exact congrArg (fun z => centralizer ({z} : Set Janko4.Model)) hg.symm
  · have hs : IsConj (Janko4.InvolutionCentralizers.Second.seed : Janko4.Model)
        ((Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b) ^ 5) := by
      obtain ⟨g,hg⟩ := Janko4.Simplicity.Max1Fusion.seed_fuses_second
        Janko4.matrixA_mul_self Janko4.matrixB_pow_four
      have ha : Janko4.Simplicity.a Janko4.matrixA_mul_self = Janko4.a := by
        apply Janko4.toMatrix_injective; rfl
      have hb : Janko4.Simplicity.b Janko4.matrixB_pow_four = Janko4.b := by
        apply Janko4.toMatrix_injective; rfl
      rw [ha,hb] at hg
      have hw : Janko4.Simplicity.word Janko4.a Janko4.b "ababb" =
          Janko4.a * Janko4.b * Janko4.a * Janko4.b * Janko4.b := by
        simp [Janko4.Simplicity.word,mul_assoc]
      rw [hw] at hg
      exact isConj_iff.mpr ⟨g,hg.symm⟩
    obtain ⟨g,hg⟩ := isConj_iff.mp (hs.trans h).symm
    right
    let e := MulAut.conj g
    have he : (centralizer ({z} : Set Janko4.Model)).map e.toMonoidHom =
        Janko4.InvolutionCentralizers.Second.ambientCentralizer := by
      rw [map_centralizer_equiv,Set.image_singleton]
      change centralizer ({e z} : Set Janko4.Model) =
        centralizer ({(Janko4.InvolutionCentralizers.Second.seed : Janko4.Model)} : Set Janko4.Model)
      exact congrArg (fun z => centralizer ({z} : Set Janko4.Model)) hg
    exact ⟨(e.subgroupMap _).trans (MulEquiv.subgroupCongr he)⟩


private theorem component_local_characteristic_two
    {G : Type*} [Group G] [Finite G] {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K) :
    centralizer (pCore 2 (ordinaryComponentSubgroup M K) :
      Set (ordinaryComponentSubgroup M K)) ≤ pCore 2 (ordinaryComponentSubgroup M K) := by
  let := h.ordinary_component_normal K hK
  let f := inclusion h.local_le
  let C := K.comap f
  have hcM : centralizer (pCore 2 M : Set M) ≤ pCore 2 M := by
    simpa only [h.local_fitting] using centralizer_generalizedFitting_le M
  have hcC := normal_core_selfCentralizing hcM C
  let e : ordinaryComponentSubgroup M K ≃* C := {
    toFun k := ⟨⟨k.val.val.val,k.property⟩,k.val.property⟩
    invFun m := ⟨⟨f m.val,m.property⟩,m.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mpr hcC

/-- The original component radical is self-centralizing in K, using the
source local characteristic-two condition and full radical-normalizer control. -/
theorem ordinary_jankoFour_component_radical_selfcentralizing
    {G : Type*} [Group G] [Finite G] {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Janko4.Model) :
    centralizer (ordinaryComponentSubgroup R K : Set K) ≤ ordinaryComponentSubgroup R K := by
  exact radical_selfcentralizing _ _ (h.ordinary_radical_intersection_isRadical K hK)
    (ordinary_jankoFour_component_radical_normalizer_control h K hK e)
    (component_local_characteristic_two h K hK)

private theorem radical_normalizer_characteristic_two
    {A : Type*} [Group A] [Finite A] (P : Subgroup A)
    (hP : IsPRadical 2 P) (hc : centralizer (P : Set A) ≤ P) :
    centralizer (pCore 2 (normalizer (P : Set A)) : Set (normalizer (P : Set A))) ≤
      pCore 2 (normalizer (P : Set A)) := by
  intro x hx
  have hxP : (x : A) ∈ P := by
    apply hc
    intro y hy
    have hy' : y ∈ (pCore 2 (normalizer (P : Set A))).map
        (normalizer (P : Set A)).subtype := hP.2.ge hy
    obtain ⟨v,hv,hvy⟩ := hy'
    rw [←hvy]
    exact congrArg Subtype.val (hx v hv)
  have hxP' : (x : A) ∈ (pCore 2 (normalizer (P : Set A))).map
      (normalizer (P : Set A)).subtype := hP.2.ge hxP
  obtain ⟨y,hy,he⟩ := hxP'
  exact (Subtype.ext he : y = x) ▸ hy

private theorem radical_centralizer_le_of_normalizer_characteristic_two
    {A : Type*} [Group A] [Finite A] (P : Subgroup A)
    (hP : IsPRadical 2 P)
    (hc : centralizer (pCore 2 (normalizer (P : Set A)) : Set (normalizer (P : Set A))) ≤
      pCore 2 (normalizer (P : Set A))) : centralizer (P : Set A) ≤ P := by
  intro x hx
  have hn := Subgroup.centralizer_le_normalizer _ hx
  have hh : (⟨x,hn⟩ : normalizer (P : Set A)) ∈ pCore 2 (normalizer (P : Set A)) := by
    apply hc
    intro y hy
    have hyP : (y : A) ∈ P := hP.2.le (mem_map_of_mem (normalizer (P : Set A)).subtype hy)
    exact Subtype.ext (hx y hyP)
  have hmem : x ∈ (pCore 2 (normalizer (P : Set A))).map (normalizer (P : Set A)).subtype :=
    mem_map_of_mem (normalizer (P : Set A)).subtype hh
  exact hP.2.le hmem

private theorem radical_selfcentralizing_central_image
    {A E : Type*} [Group A] [Group E] [Finite A] [Finite E]
    (P : Subgroup A) (hP : IsPRadical 2 P) (hc : centralizer (P : Set A) ≤ P)
    (f : A →* E) (hf : Function.Surjective f) (hk : f.ker ≤ center A)
    (hker : f.ker ≤ P) (hbar : IsPRadical 2 (P.map f)) :
    centralizer (P.map f : Set E) ≤ P.map f := by
  let N := normalizer (P : Set A)
  let Nb := normalizer (P.map f : Set E)
  have he : Nb.comap f = N := by
    rw [comap_normalizer_eq_of_surjective _ hf,comap_map_eq_self hker]
  let a : N →* Nb := {
    toFun n := ⟨f n.val,by change n.val ∈ Nb.comap f; rw [he]; exact n.property⟩
    map_one' := Subtype.ext (map_one f)
    map_mul' x y := Subtype.ext (map_mul f x.val y.val) }
  have ha : Function.Surjective a := by
    intro y
    obtain ⟨x,hx⟩ := hf y
    have hn : x ∈ N := by rw [←he]; change f x ∈ Nb; rw [hx]; exact y.property
    exact ⟨⟨x,hn⟩,Subtype.ext hx⟩
  have hak : a.ker ≤ center N := by
    intro n hn
    have hfn : n.val ∈ f.ker := congrArg Subtype.val hn
    exact mem_center_iff.mpr (fun x => Subtype.ext (mem_center_iff.mp (hk hfn) x))
  exact radical_centralizer_le_of_normalizer_characteristic_two _ hbar
    (a.centralizer_pCore_le_of_surjective_centralKernel ha hak
      (radical_normalizer_characteristic_two P hP hc))

/-- Self-centralization passes through the literal component center, whose
full kernel lies in the radical. The original W is unchanged. -/
theorem ordinary_jankoFour_projected_radical_selfcentralizing
    {G : Type*} [Group G] [Finite G] {H M B R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Janko4.Model) :
    centralizer (((ordinaryComponentSubgroup R K).map
      (QuotientGroup.mk' (center K))) : Set (K ⧸ center K)) ≤
      (ordinaryComponentSubgroup R K).map (QuotientGroup.mk' (center K)) := by
  have hr := h.ordinary_radical_intersection_isRadical K hK
  have hc := ordinary_jankoFour_component_radical_selfcentralizing h K hK e
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  apply radical_selfcentralizing_central_image _ hr hc (QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
    ?_ (ordinary_projected_radical h K hK)
  rw [QuotientGroup.ker_mk',hz]
  exact pCore_le_of_pCore_normalizer_le _ hr.isPGroup hr.2.le

private theorem radical_normalizer_centralizer_trivial
    (P : Subgroup Janko4.Model) (hp : IsPGroup 2 P)
    (hc : centralizer (P : Set Janko4.Model) ≤ P)
    (hi : ∀ z : Janko4.Model, orderOf z = 2 →
      ¬ normalizer (P : Set Janko4.Model) ≤ centralizer ({z} : Set Janko4.Model)) :
    centralizer (normalizer (P : Set Janko4.Model) : Set Janko4.Model) = ⊥ := by
  let C := centralizer (normalizer (P : Set Janko4.Model) : Set Janko4.Model)
  have hCP : C ≤ P := (centralizer_le P.le_normalizer).trans hc
  have hodd : ¬ 2 ∣ Nat.card C := by
    intro hd
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 hd
    apply hi z (by simpa only [Subgroup.orderOf_coe] using hz)
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact z.property x hx
  obtain ⟨k,hk⟩ := (hp.to_le hCP).exists_card_eq
  apply C.eq_bot_of_card_eq
  have hk0 : k = 0 := by
    by_contra hn
    apply hodd
    rw [hk]
    exact dvd_pow_self 2 hn
  simpa [hk0] using hk

open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation
variable {G : Type*} [Group G] [Finite G] {H M B R W : Subgroup G}
open CFSG.Quasithin.Chapter12.Section02

private theorem projected_cover_twentySeven {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hn : (B.subgroupOf M).Normal)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (he : ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Janko4.Model) :
    let X := ((ordinaryCoverProjection h K hK).range).map ek.toMonoidHom
    27 ∣ Nat.card X := by
  obtain ⟨_,hf,_,_,a,_,_⟩ := c28_covering_jankoFour_local D S h hstrict hn hBL hc hVB e he K hK
  let X₀ := (ordinaryCoverProjection h K hK).range
  let X := X₀.map ek.toMonoidHom
  let t := ek.subgroupMap X₀
  let q := t.toMonoidHom.quotientPCoreEquivOfSurjective t.surjective
    (by rw [t.toMonoidHom.ker_eq_bot t.injective]; exact IsPGroup.of_subsingleton 2 _)
  have ha := q.symm.trans a
  have hd : 27 ∣ Nat.card (X ⧸ pCore 2 X) := by
    have hcard : Nat.card (X ⧸ pCore 2 X) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 3) S.field.Carrier) := Nat.card_congr ha.toEquiv
    rw [hcard,OddNormalizer.linear_three_order]
    norm_num [S.field.card_eq,hf]
  exact hd.trans (pCore 2 X).card_quotient_dvd_card

/-- The actual full projected radical normalizer lies in no involution
centralizer of J4. This combines the full moved-module argument with the
three-part of the full SL3(4) quotient. -/
theorem c28_covering_jankoFour_radical_normalizer_avoids_involutions
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hn : (B.subgroupOf M).Normal)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (he : ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Janko4.Model) :
    ∀ z : Janko4.Model, orderOf z = 2 →
      ¬ normalizer (((ordinaryComponentSubgroup R K).map
        (QuotientGroup.mk' (center K))).map ek.toMonoidHom : Set Janko4.Model) ≤
        centralizer ({z} : Set Janko4.Model) := by
  intro z hz hnz
  rcases first_conjugate_or_second_type z hz with ⟨g,hg⟩ | hs
  · rw [hg] at hnz
    exact ordinary_jankoFour_radical_normalizer_avoids_first h hn K hK ek g hnz
  · obtain ⟨b⟩ := hs
    let P₀ := (ordinaryComponentSubgroup R K).map (QuotientGroup.mk' (center K))
    let X₀ := (ordinaryCoverProjection h K hK).range
    have hXN : X₀.map ek.toMonoidHom ≤ normalizer (P₀.map ek.toMonoidHom : Set Janko4.Model) := by
      rw [←map_equiv_normalizer_eq P₀ ek]
      exact map_mono (ordinary_projected_cover_normalizes_radical h hn K hK)
    have hd := (projected_cover_twentySeven D S h hstrict hn hBL hc hVB e he K hK ek).trans
      (card_dvd_of_le (hXN.trans hnz))
    rw [Nat.card_congr b.toEquiv,Janko4.InvolutionCentralizers.Second.ambient_card] at hd
    norm_num at hd

/-- The full radical normalizer has trivial centralizer in the literal
central quotient. No maximal-local or full-Sylow placement is assumed. -/
theorem c28_covering_jankoFour_radical_normalizer_centralizer
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hn : (B.subgroupOf M).Normal)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (he : ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b))
    (K : Subgroup H) (hK : IsComponent H K)
    (ek : K ⧸ center K ≃* Janko4.Model) :
    centralizer (normalizer (((ordinaryComponentSubgroup R K).map
      (QuotientGroup.mk' (center K))) : Set (K ⧸ center K)) : Set (K ⧸ center K)) = ⊥ := by
  let P₀ := (ordinaryComponentSubgroup R K).map (QuotientGroup.mk' (center K))
  let P := P₀.map ek.toMonoidHom
  have hs : centralizer (P : Set Janko4.Model) ≤ P := by
    rw [←Theory.Quasithin.map_centralizer]
    exact map_mono (ordinary_jankoFour_projected_radical_selfcentralizing h K hK ek)
  have ht : centralizer (normalizer (P : Set Janko4.Model) : Set Janko4.Model) = ⊥ :=
    radical_normalizer_centralizer_trivial P ((ordinary_projected_radical h K hK).isPGroup.map _)
      hs (c28_covering_jankoFour_radical_normalizer_avoids_involutions D S h hstrict hn hBL hc hVB e he K hK ek)
  apply (map_eq_bot_iff_of_injective _ (f := ek.toMonoidHom) ek.injective).mp
  rw [Theory.Quasithin.map_centralizer,map_equiv_normalizer_eq]
  exact ht

/-- Application to the actual odd-normalizer covering residual, retaining
the original full module and the literal component quotient. Outer and
moved cases remain with the odd-normalizer owner. -/
theorem pushingUp_jankoFour_radical_normalizer_centralizer
    {T : Sylow 2 G} {L V A : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (h : OddNormalizer.PushingUpFieldFourCase D S A) :
    ∃ J H W : Subgroup G,
      Chapter4.PushLE L (Chapter4.Section04.oddActorResidual L A) J ∧
      IsMaximalTwoLocal H ∧ J ≤ H ∧
      let B := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let M := H ⊓ normalizer (L : Set G)
      let R := J.pCoreIn 2
      ∃ (_hC : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
        (K : Subgroup H) (_hK : IsComponent H K) (ek : K ⧸ center K ≃* Janko4.Model),
        centralizer (normalizer (((ordinaryComponentSubgroup R K).map
          (QuotientGroup.mk' (center K))) : Set (K ⧸ center K)) : Set (K ⧸ center K)) = ⊥ ∧
        ∀ z : Janko4.Model, orderOf z = 2 →
          ¬ normalizer (((ordinaryComponentSubgroup R K).map
            (QuotientGroup.mk' (center K))).map ek.toMonoidHom : Set Janko4.Model) ≤
            centralizer ({z} : Set Janko4.Model) := by
  obtain ⟨J,H,W,hpush,hH,hJH,hstrict,_,hC,hcover,hN,hVB,⟨e,he⟩,_,_,_,
    _,_,_,K,hK,_,_,_,_,_⟩ := h
  have hBL := (map_subtype_le (solvableResidual (L ⊓ H : Subgroup G))).trans inf_le_left
  obtain ⟨⟨ek⟩,_,_,_⟩ := c28_covering_ordinary_jankoFour D S hC hBL hcover hVB e K hK
  exact ⟨J,H,W,hpush,hH,hJH,hC,K,hK,ek,
    c28_covering_jankoFour_radical_normalizer_centralizer D S hC hstrict hN
      hBL hcover hVB e he K hK ek,
    c28_covering_jankoFour_radical_normalizer_avoids_involutions D S hC hstrict hN
      hBL hcover hVB e he K hK ek⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
