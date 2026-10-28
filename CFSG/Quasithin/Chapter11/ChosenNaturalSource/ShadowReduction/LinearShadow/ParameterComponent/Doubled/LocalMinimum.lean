module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.ReciprocalSource
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Setup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.NormalizerRank
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceCompleteBound
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.LargerFieldThree.FieldBounds
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.EquivariantBest
/-!
# The doubled local minimum, global s-value and automizer rank

An involution moving fewer than 2n binary dimensions in the full doubled
normalizer belongs to the identical natural SL₃ component. Every nontrivial
natural actor moves at least n dimensions on each copy, and an inner
transvection attains the bound. Faithful coordinates on the original V_M
transport both the whole automizer and the attaining actor, proving m=2n.
The actual E.6.1 setup and the proved E.6.3 theorem then give s=2n.

The same faithful coordinates embed the original automizer in the doubled
normalizer, proving its two-rank is at most 3n. The final consumer supplies
both bounds to the reciprocal source contradiction. Weak-closure escape and
the strict r-bound remain explicit proof obligations of this source task. The earlier rank-one reduction
retains its producer qt-d-1222-shadow-rankone-recognition.

Source: Aschbacher--Smith, 11.3.6, printed p.772, first paragraph.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.SL3DoubledNaturalOffenders
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
namespace LocalMinimum
variable (F : BinaryField)
private theorem doubled_codim (A : Subgroup (SL F.Carrier)) :
    fixedCodim (representation F.Carrier) A = 2 * fixedCodim (linearNatural F 3) A := by
  have he := fixedCodim_map_equivariant (representation F.Carrier)
    ((linearNatural F 3).prod (linearNatural F 3))
    (MonoidHom.id (SL F.Carrier))
    (LinearEquiv.finTwoArrow (R := ZMod 2) (M := Fin 3 → F.Carrier))
    (fun _ _ => rfl) A
  simpa only [Subgroup.map_id,fixedCodim_prod,two_mul] using he
private theorem inner_lower (A : Subgroup (SL F.Carrier)) (hA : A ≠ ⊥) :
    2*F.degree ≤ fixedCodim (representation F.Carrier) A := by
  have hp := (ChapterB.NaturalExtensions.LargerFieldThree.field_dimensions_pos F 3 hA).1
  rw [doubled_codim,ChapterK.Linear.Natural.fixedCodim_eq_field_codim]
  exact Nat.mul_le_mul_left 2 (Nat.le_mul_of_pos_right _ hp)
/-- Every involution of the full binary doubled normalizer moves at least 2n dimensions. -/
theorem involution_lower (b : Ambient F.Carrier)
    (hb : b ∈ SL3DoubledNaturalOffenders.normalizer F.Carrier) (ho : orderOf b = 2) :
    2*F.degree ≤ fixedCodim (action F.Carrier) (zpowers b) := by
  by_contra h
  have hc : fixedCodim (action F.Carrier) (zpowers b) < 2*F.degree := by omega
  have hsq : b^2=1 := by simpa only [ho] using pow_orderOf_eq_one b
  let : IsElementaryAbelian 2 (zpowers b) := IsElementaryAbelian.zpowers_of_pow_eq_one hsq
  have hin := SmallNormalizer.elementary_le_component F.card_eq (zpowers b)
    (zpowers_le.mpr hb) (by have := F.degree_pos; omega)
  obtain ⟨g,hg⟩ := hin (mem_zpowers b)
  have hne : zpowers g ≠ ⊥ := by
    intro he
    have hg1 : g=1 := mem_bot.mp (he ▸ mem_zpowers g)
    rw [hg1,map_one] at hg
    rw [← hg,orderOf_one] at ho
    omega
  have hl := inner_lower F (zpowers g) hne
  have he := fixedCodim_map_equivariant (representation F.Carrier) (action F.Carrier)
    (representation F.Carrier).asGroupHom (LinearEquiv.refl _ _) (fun _ _ => rfl) (zpowers g)
  rw [MonoidHom.map_zpowers,hg] at he
  omega
/-- A literal inner transvection attains the doubled lower bound. -/
theorem inner_attains : ∃ g : SL F.Carrier, orderOf g=2 ∧
    fixedCodim (representation F.Carrier) (zpowers g) = 2*F.degree := by
  let g := Matrix.SpecialLinearGroup.transvection (by decide : (0:Fin 3) ≠ 1) (1:F.Carrier)
  have hg (v : Fin 3 → F.Carrier) : linearNatural F 3 g v = v + Pi.single 0 (v 1) := by
    change ((1:Matrix (Fin 3) (Fin 3) F.Carrier) + Matrix.single 0 1 1).mulVec v = _
    simp only [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec_eq,one_mul]
    congr 1
    ext k
    by_cases hk : k=0 <;> simp [hk]
  have ho : orderOf g=2 := by
    apply orderOf_eq_prime
    · rw [pow_two]
      simpa only [CharTwo.neg_eq] using
        Matrix.SpecialLinearGroup.transvection_mul_neg (by decide : (0:Fin 3) ≠ 1) (1:F.Carrier)
    · intro h
      have hh := hg (Pi.single 1 1)
      rw [h,map_one,Module.End.one_apply] at hh
      have hz := congrFun hh 0
      simp at hz
  let q : (Fin 3 → F.Carrier) →ₗ[ZMod 2] F.Carrier :=
    ((LinearMap.proj 1 : (Fin 3 → F.Carrier) →ₗ[F.Carrier] F.Carrier)).restrictScalars (ZMod 2)
  have hq : Function.Surjective q := fun x => ⟨fun _ => x,rfl⟩
  have hk : q.ker = fixedSpace (linearNatural F 3) (zpowers g) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    change v 1 = 0 ↔ linearNatural F 3 g v = v
    rw [hg,add_eq_left]
    constructor
    · intro h; simp only [h,Pi.single_zero]
    · intro h
      simpa only [Pi.single_eq_same,Pi.zero_apply] using congrFun h 0
  have hd : fixedCodim (linearNatural F 3) (zpowers g) = F.degree := by
    exact (((Submodule.quotEquivOfEq _ _ hk.symm).trans
      (q.quotKerEquivOfSurjective hq)).finrank_eq).trans
      (NaturalTensor.finrank_field F.Carrier F.card_eq)
  exact ⟨g,ho,by rw [doubled_codim,hd]⟩


open ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}

/-- Faithful coordinates for the whole original automizer, identifying its natural component. -/
theorem automizer_marking_component (d : Coordinates D S)
    [IsElementaryAbelian 2 (fullModule L V)] :
    ∃ (E : Additive (fullModule L V) ≃ₗ[ZMod 2] Space S.field.Carrier)
      (f : Automizer (fullModule L V) →* Ambient S.field.Carrier),
      Function.Injective f ∧
      (∀ a v, E (automizerRepresentation (fullModule L V) a v) = action S.field.Carrier (f a) (E v)) ∧
      f.range ≤ SL3DoubledNaturalOffenders.normalizer S.field.Carrier ∧
      component S.field.Carrier ≤ f.range ∧
      (inducedAutomizer (fullModule L V) L).map f = component S.field.Carrier := by
  obtain ⟨m,⟨c⟩⟩ := d
  let W := fullModule L V
  have hi : Function.Injective c.coordinates := by
    apply c.coordinates.ker_eq_bot_iff.mp
    rw [c.kernel_eq,bot_subgroupOf]
  let j : Additive W →+ Space S.field.Carrier :=
    { toFun v := (c.coordinates v.toMul).toAdd
      map_zero' := c.coordinates.map_one
      map_add' := c.coordinates.map_mul }
  let E : Additive W ≃ₗ[ZMod 2] Space S.field.Carrier :=
    LinearEquiv.ofBijective (j.toZModLinearMap 2) ⟨hi,c.onto⟩
  let f : Automizer W →* Ambient S.field.Carrier :=
    (Units.mapEquiv E.conjRingEquiv.toMulEquiv).toMonoidHom.comp
      (automizerRepresentation W).asGroupHom
  have hf : Function.Injective f := by
    apply (Units.mapEquiv E.conjRingEquiv.toMulEquiv).injective.comp
    intro a b he
    exact automizerRepresentation_injective W (congrArg Units.val he)
  have hE (a : Automizer W) (v : Additive W) :
      E (automizerRepresentation W a v) = action S.field.Carrier (f a) (E v) := by
    change E _ = E (automizerRepresentation W a (E.symm (E v)))
    rw [E.symm_apply_apply]
  let N := normalizer (W : Set G)
  let ψ : N →* Ambient S.field.Carrier := f.comp W.normalizerMonoidHom.rangeRestrict
  let q := m.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q :=
    m.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  have hL (l : L) : ψ (inclusion c.normalized l) =
      (representation S.field.Carrier).asGroupHom (q l) := by
    apply Units.ext
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := E.surjective w
    change action S.field.Carrier (f (W.normalizerMonoidHom.rangeRestrict (inclusion c.normalized l))) (E v) = _
    rw [← hE]
    exact c.equivariant l v.toMul
  have himage : (L.subgroupOf N).map ψ = component S.field.Carrier := by
    apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      exact ⟨q ⟨l,hl⟩,(hL ⟨l,hl⟩).symm⟩
    · rintro _ ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨inclusion c.normalized l,l.property,hL l⟩
  have hn : N ≤ normalizer (L : Set G) := (fullModule_normalizer ⟨m,⟨c⟩⟩).le
  refine ⟨E,f,hf,hE,?_,?_,?_⟩
  · rintro _ ⟨a,rfl⟩
    obtain ⟨x,rfl⟩ := W.normalizerMonoidHom.rangeRestrict_surjective a
    change ψ x ∈ SL3DoubledNaturalOffenders.normalizer S.field.Carrier
    rw [SL3DoubledNaturalOffenders.normalizer,← himage]
    apply (L.subgroupOf N).le_normalizer_map ψ
    apply mem_map_of_mem
    apply mem_normalizer_iff.mpr
    intro l
    exact mem_normalizer_iff.mp (hn x.property) l
  · rw [← himage]
    rintro _ ⟨x,hx,rfl⟩
    exact ⟨W.normalizerMonoidHom.rangeRestrict x,rfl⟩
  · change ((L.subgroupOf N).map W.normalizerMonoidHom.rangeRestrict).map f = _
    rw [map_map]
    exact himage

private theorem automizer_marking (d : Coordinates D S)
    [IsElementaryAbelian 2 (fullModule L V)] :
    ∃ (E : Additive (fullModule L V) ≃ₗ[ZMod 2] Space S.field.Carrier)
      (f : Automizer (fullModule L V) →* Ambient S.field.Carrier),
      Function.Injective f ∧
      (∀ a v, E (automizerRepresentation (fullModule L V) a v) = action S.field.Carrier (f a) (E v)) ∧
      f.range ≤ SL3DoubledNaturalOffenders.normalizer S.field.Carrier ∧
      component S.field.Carrier ≤ f.range := by
  obtain ⟨E,f,hf,hE,hN,hC,_⟩ := automizer_marking_component d
  exact ⟨E,f,hf,hE,hN,hC⟩

/-- The 3n bound on the literal source automizer M/C_M(V_M), obtained
from its faithful doubled coordinates and the full binary normalizer bound. -/
theorem automizer_rank (d : Coordinates D S) :
    primeRank 2 (inducedAutomizer (fullModule L V) (normalizer (L : Set G))) ≤
      3 * S.field.degree := by
  let := fullModule_elementary d
  let : Finite (Module.End (ZMod 2) (Space S.field.Carrier)) :=
    Finite.of_injective DFunLike.coe DFunLike.coe_injective
  obtain ⟨_,f,hf,_,hN,_⟩ := automizer_marking d
  let j := f.codRestrict (SL3DoubledNaturalOffenders.normalizer S.field.Carrier)
    (fun a => hN ⟨a,rfl⟩)
  have hj : Function.Injective j := by
    intro a b he
    exact hf (congrArg Subtype.val he)
  have hb := (primeRank_le_of_injective 2 j hj).trans
    (AutomizerRank.normalizer_rank S.field.degree_pos S.field.card_eq)
  exact (primeRank_le_of_injective 2
    (inducedAutomizer (fullModule L V) (normalizer (L : Set G))).subtype
    (inducedAutomizer (fullModule L V) (normalizer (L : Set G))).subtype_injective).trans hb

/-- The local involution minimum on the literal original V_M is 2n. -/
theorem localM_eq (d : Coordinates D S) :
    @localM G _ (fullModule L V) (fullModule_elementary d) = 2*S.field.degree := by
  let := fullModule_elementary d
  obtain ⟨E,f,hf,hE,hN,hC⟩ := automizer_marking d
  obtain ⟨g,hg,hcod⟩ := inner_attains S.field
  obtain ⟨a,ha⟩ := hC (show (representation S.field.Carrier).asGroupHom g ∈ component S.field.Carrier from ⟨g,rfl⟩)
  have hi : Function.Injective (representation S.field.Carrier).asGroupHom :=
    fun _ _ he => representation_injective S.field.Carrier (congrArg Units.val he)
  have hoa : orderOf a=2 := by
    rw [← orderOf_injective f hf a,ha,orderOf_injective _ hi,hg]
  have he (b : Automizer (fullModule L V)) :
      fixedCodim (action S.field.Carrier) (zpowers (f b)) =
        fixedCodim (automizerRepresentation (fullModule L V)) (zpowers b) := by
    simpa only [MonoidHom.map_zpowers] using (fixedCodim_map_equivariant
      (automizerRepresentation (fullModule L V)) (action S.field.Carrier) f E hE (zpowers b)).symm
  have hca : fixedCodim (automizerRepresentation (fullModule L V)) (zpowers a) = 2*S.field.degree := by
    rw [← he,ha]
    have hh := fixedCodim_map_equivariant (representation S.field.Carrier) (action S.field.Carrier)
      (representation S.field.Carrier).asGroupHom (LinearEquiv.refl _ _) (fun _ _ => rfl) (zpowers g)
    rw [MonoidHom.map_zpowers] at hh
    exact hh.symm.trans hcod
  obtain ⟨b,hb,hcb⟩ := moduleM_attained (automizerRepresentation (fullModule L V)) ⟨a,hoa⟩
  apply Nat.le_antisymm ((moduleM_le_involution _ hoa).trans_eq hca)
  have hl := involution_lower S.field (f b) (hN ⟨b,rfl⟩)
    ((orderOf_injective f hf b).trans hb)
  rw [he] at hl
  exact hl.trans_eq hcb

/-- E.6.3 now gives the source value of s on the full doubled module. -/
theorem globalS_eq (d : Coordinates D S) :
    @globalS G _ (fullModule L V) (fullModule_elementary d) = (2*S.field.degree : ℕ∞) := by
  let := fullModule_elementary d
  have hm := localM_eq d
  have hbound : 2 < localM (fullModule L V) := by
    rw [hm]
    have := S.nonbinary
    omega
  exact (ChapterE.Section06.FrobeniusReduction.lower_bound_knownSimple
    (doubled_hypothesisE61 d) hbound).2.1.trans (congrArg Nat.cast hm)

end LocalMinimum

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The literal E-generation application no longer assumes the doubled s-value. -/
theorem source_parameter_eq_twice_of_escape (h : Hypothesis1131At D S U₁ H)
    (d : Coordinates D S)
    (hw : ¬ ChapterE.indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤ H.pCoreIn 2)
    (hu : ChapterE.generationParameter H ≤ 2*S.field.degree) :
    ChapterE.generationParameter H = 2*S.field.degree :=
  parameter_eq_twice h d hw (LocalMinimum.globalS_eq d) hu

/-- Discharge the s-coordinate in the original reciprocal contradiction.
The other three geometric outputs still have to be constructed. -/
theorem source_contradiction_of_local_bounds (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (d : Coordinates D S) (r : RankOneReduction S H)
    (hu : ChapterE.generationParameter H ≤ 2*S.field.degree)
    (hw : ¬ ChapterE.indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤ H.pCoreIn 2)
    (hr : (2*S.field.degree : ℕ∞) < ChapterE.globalR (fullModule L V))
    (ha : primeRank 2
      (ChapterE.inducedAutomizer (fullModule L V) (normalizer (L : Set G))) ≤ 3*S.field.degree) : False :=
  source_contradiction_of_geometry h p hc d ⟨hw,LocalMinimum.globalS_eq d,hr,ha⟩ r hu

/-- The original reciprocal contradiction now needs only the remaining
weak-closure escape and strict r-bound from the doubled local geometry.
The s-value and literal automizer rank are both constructed above. -/
theorem source_contradiction_of_escape_and_r (h : Hypothesis1131At D S U₁ H)
    (p : Preceding1133 D S U₁ H) (hc : ¬ Proposition1132At D S U₁ H)
    (d : Coordinates D S) (r : RankOneReduction S H)
    (hu : ChapterE.generationParameter H ≤ 2*S.field.degree)
    (hw : ¬ ChapterE.indexedWeakClosure (fullModule L V) (T : Subgroup G) 0 ≤ H.pCoreIn 2)
    (hr : (2*S.field.degree : ℕ∞) < ChapterE.globalR (fullModule L V)) : False :=
  source_contradiction_of_local_bounds h p hc d r hu hw hr (LocalMinimum.automizer_rank d)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
