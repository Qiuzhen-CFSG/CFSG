module
public import Theory.Mathieu.M22.Properties.PairRecognition
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.PairQuotients
public import Theory.Mathieu.M22.ChapterHLocalClassification.Quintet.Structure
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Automorphisms.Compatibility
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeStabilizers
public import Theory.ElementaryAbelian.Injective

/-!
# The first source involution stabilizer

An order-3840 subgroup of Aut(M₂₂) intersects the inner group in order
1920. The established M₂₂ recognition gives a genuine invariant pair;
three-transitivity makes this pair unique, so its normalizer preserves the
same pair. Thus the whole subgroup is the full-design pair stabilizer.
Its actual five-hexad action supplies the S₅ quotient. Recognition of the
native quintet by the same argument transports its checked elementary
order-32 core; no subgroup is identified by order alone.

Applying this to the faithful restriction of the original cubic projection
proves C_H(r₁)Q/Q has shape S₅/E₃₂. Both original involution classes and
their literal centralizer images are retained. The second stabilizer type,
returning class, subsequent local geometry and ambient recognition remain
separate obligations.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.2), printed p.597, DOI 10.1007/BF01232280.
The imported native quintet calculations retain their original ATLAS
attribution; this module introduces no finite computation certificate.
-/

public section

open Subgroup MulAction
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Sporadic.Mathieu Sporadic.Mathieu.M22ValueBound.Concrete

private theorem pair_invariant_unique {S T : Finset (Fin 22)} (hS : S.card = 2)
    (hT : T.card = 2) (hle : stabilizer M22 S ≤ stabilizer M22 T) : T = S := by
  classical
  apply Finset.eq_of_subset_of_card_le ?_ (by omega)
  intro a ha
  by_contra haS
  have hsmall : (T ∪ S).card < (Finset.univ : Finset (Fin 22)).card := by
    have hu := Finset.card_union_le T S
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hsmall
  have hbT : b ∉ T := fun h => hb (Finset.mem_union_left S h)
  have hbS : b ∉ S := fun h => hb (Finset.mem_union_right T h)
  rcases Finset.card_eq_two.mp hS with ⟨x, y, hxy, rfl⟩
  have hxa : x ≠ a := by intro he; subst a; exact haS (by simp)
  have hya : y ≠ a := by intro he; subst a; exact haS (by simp)
  have hxb : x ≠ b := by intro he; subst b; exact hbS (by simp)
  have hyb : y ≠ b := by intro he; subst b; exact hbS (by simp)
  let u : Fin 3 ↪ Fin 22 := ⟨![x,y,a], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let v : Fin 3 ↪ Fin 22 := ⟨![x,y,b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
    grind⟩
  obtain ⟨g,hg⟩ := isMultiplyPretransitive_iff.mp m22_isThreePretransitive u v
  have hgi (i : Fin 3) : g • u i = v i := congrArg (fun e : Fin 3 ↪ Fin 22 => e i) hg
  have hgx : g • x = x := hgi 0
  have hgy : g • y = y := hgi 1
  have hga : g • a = b := hgi 2
  have hgs : g ∈ stabilizer M22 ({x,y} : Finset (Fin 22)) := by
    change g • ({x,y} : Finset (Fin 22)) = _
    rw [Finset.smul_finset_insert, Finset.smul_finset_singleton, hgx, hgy]
  exact hbT (hga ▸ (mem_stabilizer_finset'.mp (hle hgs)) ha)

private theorem pair_normalizer_le {S : Finset (Fin 22)} (hS : S.card = 2) :
    normalizer ((stabilizer M22 S).map inclusion : Set m22DesignAut) ≤
      stabilizer m22DesignAut S := by
  intro g hg
  apply mem_stabilizer_iff.mpr
  apply pair_invariant_unique hS (by rw [Finset.card_smul_finset, hS])
  intro u hu
  have hm : inclusion u ∈ (stabilizer M22 S).map inclusion := mem_map_of_mem _ hu
  have hn := (mem_normalizer_iff.mp
    ((normalizer ((stabilizer M22 S).map inclusion : Set m22DesignAut)).inv_mem hg)
      (inclusion u)).mp hm
  obtain ⟨v,hv,he⟩ := hn
  have hvs : (inclusion v : m22DesignAut) • S = S := hv
  have hmul : inclusion u * g = g * inclusion v := by
    rw [he]
    simp only [inv_inv, mul_inv_cancel_left, mul_assoc]
  change (inclusion u : m22DesignAut) • (g • S) = g • S
  rw [← mul_smul, hmul, mul_smul, hvs]

private theorem pair_outer_equiv {S : Finset (Fin 22)} (hS : S.card = 2) :
    Nonempty (stabilizer m22DesignAut S ≃* outerFirst) := by
  rcases Finset.card_eq_two.mp hS with ⟨x,y,hxy,rfl⟩
  obtain ⟨g,hg1,hg2⟩ := is_two_pretransitive_iff.mp m22_isTwoPretransitive
    (by decide : (1 : Fin 22) ≠ 2) hxy
  have hg : (inclusion g : m22DesignAut) • m22Pair12 = ({x,y} : Finset (Fin 22)) := by
    change g • m22Pair12 = _
    rw [m22Pair12, Finset.smul_finset_insert, Finset.smul_finset_singleton, ← hg1, ← hg2]
  exact ⟨(stabilizerEquivStabilizer hg.symm).symm⟩

/-- Recognizes the actual pair stabilized by an order-3840 design subgroup. -/
theorem design_card3840_eq_pair (R : Subgroup m22DesignAut) (hc : Nat.card R = 3840) :
    ∃ S : Finset (Fin 22), S.card = 2 ∧ R = stabilizer m22DesignAut S := by
  let I := R.comap inclusion
  have hmap : I.map inclusion = R ⊓ M22ValueBound.Concrete.inner := by
    rw [map_comap_eq, inclusion_range, inf_comm]
  have hcI : Nat.card (M22ValueBound.Concrete.inner.subgroupOf R) = Nat.card I := by
    have e := (MulEquiv.subgroupCongr (inf_subgroupOf_left M22ValueBound.Concrete.inner R).symm).trans
      ((subgroupOfEquivOfLe (show R ⊓ M22ValueBound.Concrete.inner ≤ R from inf_le_left)).trans
        ((MulEquiv.subgroupCongr hmap.symm).trans
          (I.equivMapOfInjective inclusion inclusion_injective).symm))
    exact Nat.card_congr e.toEquiv
  have hinner : Nat.card (M22ValueBound.Concrete.inner : Subgroup m22DesignAut) = 443520 := by
    rw [← inclusion_range]
    exact (Nat.card_congr (MonoidHom.ofInjective M22ValueBound.Concrete.inclusion_injective).toEquiv).symm.trans m22_order
  have hnot : ¬ R ≤ M22ValueBound.Concrete.inner := by
    intro hle
    have hd := card_dvd_of_le hle
    rw [hc,hinner] at hd
    norm_num at hd
  have hle : (M22ValueBound.Concrete.inner.subgroupOf R).index ≤ 2 := by
    have hi := relIndex_le_of_le_right (H := M22ValueBound.Concrete.inner) (K := R) (L := ⊤) le_top
      (by simp [inner_index])
    rw [relIndex_top_right, inner_index] at hi
    exact hi
  have hne : (M22ValueBound.Concrete.inner.subgroupOf R).index ≠ 1 := fun hi => hnot (relIndex_eq_one.mp hi)
  have hpos : (M22ValueBound.Concrete.inner.subgroupOf R).index ≠ 0 := index_ne_zero_of_finite
  have hi : (M22ValueBound.Concrete.inner.subgroupOf R).index = 2 := by omega
  have hIc : Nat.card I = 1920 := by
    have he := (M22ValueBound.Concrete.inner.subgroupOf R).card_mul_index
    rw [hcI,hi,hc] at he
    omega
  obtain ⟨S,hS,hIS⟩ := m22_card1920_eq_pair_stabilizer I hIc
  have hnorm : R ≤ normalizer (I.map inclusion : Set m22DesignAut) := by
    rw [hmap]
    exact (normal_subgroupOf_iff_le_normalizer (show R ⊓ M22ValueBound.Concrete.inner ≤ R from inf_le_left)).mp
      (by rw [inf_subgroupOf_left]; infer_instance)
  have hRS : R ≤ stabilizer m22DesignAut S := by
    apply hnorm.trans
    rw [hIS]
    exact pair_normalizer_le hS
  refine ⟨S,hS,eq_of_le_of_card_ge hRS ?_⟩
  have he := (pair_outer_equiv hS).some
  rw [Nat.card_congr he.toEquiv, outerFirst_card, hc]


/-- An embedded order-3840 group has the genuine pair stabilizer structure. -/
theorem aut_card3840_equiv_pair {A : Type*} [Group A]
    (f : A →* MulAut M22) (hf : Function.Injective f) (hc : Nat.card A = 3840) :
    Nonempty (A ≃* outerFirst) := by
  let d := designAutEquiv.symm.toMonoidHom.comp f
  have hd : Function.Injective d := designAutEquiv.symm.injective.comp hf
  have hcard : Nat.card d.range = 3840 :=
    (Nat.card_congr (MonoidHom.ofInjective hd).toEquiv).symm.trans hc
  obtain ⟨S,hS,he⟩ := design_card3840_eq_pair d.range hcard
  exact ⟨(MonoidHom.ofInjective hd).trans
    ((MulEquiv.subgroupCongr he).trans (pair_outer_equiv hS).some)⟩

private theorem quintet_core_card : Nat.card (pCore 2 MathieuCode.M22Quintet.Q) = 32 := by
  have he := M22ChapterH.Quintet.core_card
  change Nat.card ((pCore 2 MathieuCode.M22Quintet.Q).map
    MathieuCode.M22Quintet.Q.subtype) = 32 at he
  rwa [card_map_of_injective MathieuCode.M22Quintet.Q.subtype_injective] at he

private theorem quintet_card : Nat.card MathieuCode.M22Quintet.Q = 3840 := by
  have hi : (pCore 2 MathieuCode.M22Quintet.Q).index = 120 := by
    change Nat.card (MathieuCode.M22Quintet.Q ⧸ pCore 2 MathieuCode.M22Quintet.Q) = _
    rw [Nat.card_congr M22ChapterH.Quintet.quotientEquiv.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  rw [← (pCore 2 MathieuCode.M22Quintet.Q).card_mul_index,quintet_core_card,hi]

private theorem outerFirst_core_elementary : IsElementaryAbelian 2 (pCore 2 outerFirst) := by
  let f := MathieuCode.m22PairStabilizerEquivAut.toMonoidHom.comp
    MathieuCode.M22Quintet.Q.subtype
  have hf : Function.Injective f := MathieuCode.m22PairStabilizerEquivAut.injective.comp
    MathieuCode.M22Quintet.Q.subtype_injective
  let e := (aut_card3840_equiv_pair f hf quintet_card).some.symm
  let ec := (e.subgroupMap (pCore 2 outerFirst)).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  let ek : pCore 2 MathieuCode.M22Quintet.Q ≃* MathieuCode.M22Quintet.K :=
    (pCore 2 MathieuCode.M22Quintet.Q).equivMapOfInjective
      MathieuCode.M22Quintet.Q.subtype MathieuCode.M22Quintet.Q.subtype_injective
  exact IsElementaryAbelian.of_injective (ec.trans ek).toMonoidHom (ec.trans ek).injective

/-- The first group shape includes an elementary core, not merely an order. -/
theorem aut_card3840_structure {A : Type*} [Group A]
    (f : A →* MulAut M22) (hf : Function.Injective f) (hc : Nat.card A = 3840) :
    IsElementaryAbelian 2 (pCore 2 A) ∧ Nat.card (pCore 2 A) = 32 ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 5)) := by
  let e := (aut_card3840_equiv_pair f hf hc).some
  let ec := (e.subgroupMap (pCore 2 A)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  let := outerFirst_core_elementary
  refine ⟨IsElementaryAbelian.of_injective ec.toMonoidHom ec.injective,?_,?_⟩
  · rw [Nat.card_congr ec.toEquiv,← outerPairAction_ker_eq_twoCore,outerPairAction_ker_card]
  · exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans outerFirstQuotientEquiv⟩

variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
variable (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e))
variable [IsExtraspecial 2 (core z)]

/-- The literal first source vector stabilizer has shape S₅/E₃₂. -/
theorem coreVectorStabilizer_structure_four (r : core z) (hrc : r ∉ center (core z))
    (hr : VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r))) = 4) :
    IsElementaryAbelian 2 (pCore 2 (coreVectorStabilizer h r)) ∧
      Nat.card (pCore 2 (coreVectorStabilizer h r)) = 32 ∧
      Nonempty ((coreVectorStabilizer h r ⧸ pCore 2 (coreVectorStabilizer h r)) ≃*
        Equiv.Perm (Fin 5)) :=
  aut_card3840_structure (e.projection.comp (coreVectorStabilizer h r).subtype)
    (coreVectorStabilizer_projection_injective h e r hrc)
    (coreVectorStabilizer_card_four h e X r hr)


include h e in
/-- The original element-centralizer image has the first stabilizer structure. -/
theorem coreCentralizerImage_structure_of_card (r : core z) (hrc : r ∉ center (core z))
    (hc : Nat.card ((Subgroup.centralizer ({(r : centralizer z)} : Set (centralizer z))).map
      (QuotientGroup.mk' (core z))) = 3840) :
    let C := (Subgroup.centralizer ({(r : centralizer z)} : Set (centralizer z))).map
      (QuotientGroup.mk' (core z))
    IsElementaryAbelian 2 (pCore 2 C) ∧ Nat.card (pCore 2 C) = 32 ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 5)) := by
  dsimp only
  rw [← coreVectorStabilizer_eq_centralizer_image h r hrc] at hc ⊢
  exact aut_card3840_structure (e.projection.comp (coreVectorStabilizer h r).subtype)
    (coreVectorStabilizer_projection_injective h e r hrc) hc

omit [IsExtraspecial 2 (core z)] in
include h in
/-- Source (4.2): both distinct classes, with the complete S₅/E₃₂ structure
of the first literal quotient stabilizer. The second structure is not asserted. -/
theorem source_first_stabilizer_structure :
    ∃ r₁ r₂ : core z,
      orderOf r₁ = 2 ∧ orderOf r₂ = 2 ∧
      r₁ ∉ center (core z) ∧ r₂ ∉ center (core z) ∧
      ¬ IsConj (r₁ : centralizer z) (r₂ : centralizer z) ∧
      Nat.card ((Subgroup.centralizer ({(r₁ : centralizer z)} : Set (centralizer z))).map
        (QuotientGroup.mk' (core z))) = 3840 ∧
      Nat.card ((Subgroup.centralizer ({(r₂ : centralizer z)} : Set (centralizer z))).map
        (QuotientGroup.mk' (core z))) = 1920 ∧
      (let C := (Subgroup.centralizer ({(r₁ : centralizer z)} : Set (centralizer z))).map
        (QuotientGroup.mk' (core z))
       IsElementaryAbelian 2 (pCore 2 C) ∧ Nat.card (pCore 2 C) = 32 ∧
         Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 5))) ∧
      ∀ r : core z, orderOf r = 2 → r ∉ center (core z) →
        IsConj (r : centralizer z) (r₁ : centralizer z) ∨
          IsConj (r : centralizer z) (r₂ : centralizer z) := by
  let := h.extraspecial
  obtain ⟨e⟩ := h.cubic_quotient
  obtain ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,hsep,hc₁,hc₂,hcov⟩ :=
    source_involution_classes_stabilizers h
  exact ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,hsep,hc₁,hc₂,
    coreCentralizerImage_structure_of_card h e r₁ h₁c hc₁,hcov⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
