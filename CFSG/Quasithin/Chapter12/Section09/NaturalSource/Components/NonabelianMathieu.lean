module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianRemaining
public import Theory.Mathieu.M22.TripleCover.NormalImage

/-!
# Excluding the triple-M₂₂ actor and reducing to the six-space rows

The normal perfect point image in the triple-M₂₂ extension must be its
entire triple cover. The literal quotient map then sends the containing
point component onto M₂₂. Its intersection with L₁T contains a full image
Sylow and retains the point residual's seven-section. If that intersection
had trivial two-core, its order would divide |GLₙ₋₁(2)|, contradicting the
order 128 of a Mathieu Sylow. Its nontrivial core places it in an M₂₂
two-local containing that Sylow, where seven-divisibility is impossible.

Together with NonabelianRemaining, this leaves only G.11.2(4–5), both
in original degree four. In degree five the catalogue thus implies
abelianity. Exhaustive construction of the catalogue and the remaining
degree-four geometry are still obligations of this source owner. The
endpoint applies the degree-five conclusion to the original fusion and
terminal construction, retaining local control as an explicit premise.
Source: Aschbacher--Smith 12.9.4, printed pp.859--860.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag
open Section08.NormalGeometry Section08.InvariantFlag.Symplectic
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The original point residual and Sylow join retain the binary Levi quotient order. -/
theorem point_join_core_card {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : 4 ≤ n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) :
    Nat.card ((F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G)) = Nat.card (LinearGroup (n-1)) := by
  let := h.chosen.elementary
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let W := space (V := V) (F.Vi 1)
  obtain ⟨a,hak,ha⟩ := point_join_action h hn earlier F
  have ha' : Function.Surjective a := by
    intro y
    obtain ⟨b,hb⟩ := ha y
    exact ⟨inclusion le_sup_left b,hb⟩
  have hJ : J ≤ L ⊔ (T : Subgroup G) := sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl
  have hk : IsPGroup 2 a.ker := by
    have hh := (h.action_kernel_isPGroup earlier.structural).comap_of_injective
      (inclusion hJ) (inclusion_injective hJ)
    rw [setupSeedAction_ker] at hh
    rw [hak]
    exact hh
  let e := a.pCoreQuotientEquiv ha' hk
  have hv : finrank (ZMod 2) (Additive V) = n :=
    h.naturalMarking.coordinates.finrank_eq.trans (by simp)
  have hw : finrank (ZMod 2) W = 1 := flag_space_finrank F 1 (by have := h.rank; omega)
  have hq : finrank (ZMod 2) (Additive V ⧸ W) = n-1 := by
    have hh := W.finrank_quotient_add_finrank
    omega
  let b := (Module.finBasisOfFinrankEq (ZMod 2) W hw).equivFun
  let c := (Module.finBasisOfFinrankEq (ZMod 2) (Additive V ⧸ W) hq).equivFun
  let d := quotientTwoCoreEquivOfCoordinates W b c
  rw [Nat.card_congr (e.trans d).toEquiv,Nat.card_prod]
  have hc1 : Nat.card (LinearGroup 1) = 1 := by
    rw [← Nat.card_congr (matrixEquivLinear 1).toEquiv, Matrix.card_GL_field]
    simp
  rw [hc1,one_mul]

/-- The image of the literal intersection of L₁T with its containing component. -/
@[expose] def pointIntersectionImage (F : InvariantFlag T V n) (L D : Subgroup G)
    {X : Type*} [Group X] (f : D →* X) : Subgroup X :=
  (f.comp (inclusion (show (F.Li L 1 ⊔ (T : Subgroup G)) ⊓ D ≤ D from inf_le_right))).range

/-- A two-core-free image of the original intersection has order dividing the point Levi order. -/
theorem point_intersection_corefree_card {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : 4 ≤ n) (earlier : EarlierSetupResults K)
    (F : InvariantFlag T V n) {D : Subgroup G}
    {X : Type*} [Group X] [Finite X] (ψ : D →* X)
    (hcore : pCore 2 (pointIntersectionImage F L D ψ) = ⊥) :
    Nat.card (pointIntersectionImage F L D ψ) ∣ Nat.card (LinearGroup (n-1)) := by
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let A := J ⊓ D
  let f := ψ.comp (inclusion (show A ≤ D from inf_le_right))
  change pCore 2 f.range = ⊥ at hcore
  have hcoref : pCore 2 A ≤ f.ker := by
    have hh : (pCore 2 A).map f.rangeRestrict ≤ pCore 2 f.range :=
      le_sSup ⟨Normal.map inferInstance f.rangeRestrict f.rangeRestrict_surjective,
        pCore_isPGroup.map f.rangeRestrict⟩
    rw [hcore] at hh
    have hh' := (Subgroup.map_eq_bot_iff _).mp (bot_unique hh)
    intro x hx
    exact congrArg Subtype.val (hh' hx)
  let g := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion (show A ≤ J from inf_le_left))
  have hkg : IsPGroup 2 g.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  have hgcore : g.ker ≤ pCore 2 A := le_sSup ⟨inferInstance,hkg⟩
  let r : (A ⧸ g.ker) →* f.range := QuotientGroup.lift g.ker f.rangeRestrict
    (fun x hx => Subtype.ext (hcoref (hgcore hx)))
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,hx⟩ := f.rangeRestrict_surjective y
    exact ⟨QuotientGroup.mk' g.ker x,hx⟩
  have hd := card_dvd_of_surjective r hr
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv] at hd
  exact (hd.trans g.range.card_subgroup_dvd_card).trans (dvd_of_eq (point_join_core_card h hn earlier F))

/-- Relative subnormality puts the full quotient Sylow in the actual intersection image. -/
theorem point_intersection_sylow (F : InvariantFlag T V n) {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn F.H)
    {X : Type*} [Group X] [Finite X] (ψ : D →* X) (hψ : Function.Surjective ψ) :
    ∃ S : Sylow 2 X, (S : Subgroup X) ≤ pointIntersectionImage F L D ψ := by
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  let A := J ⊓ D
  let H := F.H
  let C := D.subgroupOf H
  obtain ⟨S,hS⟩ := (T.subtype (F.invariant 1)).exists_subgroupOf_eq_of_subnormal C hD.2.subnormal
  let c : C ≃* D := subgroupOfEquivOfLe hD.1
  let P := (S.mapSurjective (f := c.toMonoidHom) c.surjective).mapSurjective hψ
  refine ⟨P,?_⟩
  rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
  have hyT : (y : G) ∈ (T : Subgroup G) := by
    rw [hS] at hy
    exact hy
  have hyA : (y : G) ∈ A := ⟨(show (T : Subgroup G) ≤ J from le_sup_right) hyT,y.property⟩
  exact ⟨⟨y,hyA⟩,rfl⟩

/-- The original intersection cannot have a surjective M₂₂ image retaining its seven-section. -/
theorem point_mathieu_image_excluded {K : GroupClass.{u}}
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n) {D : Subgroup G}
    (hD : D ∈ Chapter1.cComponentsIn F.H)
    (ψ : D →* Sporadic.Mathieu.M22) (hψ : Function.Surjective ψ)
    (h7 : 7 ∣ Nat.card (pointIntersectionImage F L D ψ)) : False := by
  let J := pointIntersectionImage F L D ψ
  obtain ⟨S,hSJ⟩ := point_intersection_sylow F hD ψ hψ
  have hcore : pCore 2 J ≠ ⊥ := by
    intro hz
    have hc := point_intersection_corefree_card h (by omega) earlier F ψ hz
    have h128 : 128 ∣ Nat.card S := S.pow_dvd_card_of_pow_dvd_card (n := 7)
      (by rw [Sporadic.Mathieu.m22_order]; decide)
    have hd := (h128.trans (card_dvd_of_le hSJ)).trans hc
    rcases hn with rfl | rfl
    · rw [←Nat.card_congr (slEquivLinear 3).toEquiv,Atlas.Comparisons.Exceptional.sl3Two_card] at hd
      exact (by decide : ¬ 128 ∣ 168) hd
    · rw [←Nat.card_congr (slEquivLinear 4).toEquiv,Atlas.Order20160A8.sl4Two_card] at hd
      exact (by decide : ¬ 128 ∣ 20160) hd
  have hloc : IsTwoLocal (normalizer (J.pCoreIn 2 : Set Sporadic.Mathieu.M22)) := by
    refine ⟨J.pCoreIn 2,?_,pCore_isPGroup.map J.subtype,rfl⟩
    intro he
    exact hcore ((map_eq_bot_iff_of_injective _ J.subtype_injective).mp he)
  have hJN : J ≤ normalizer (J.pCoreIn 2 : Set Sporadic.Mathieu.M22) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  exact Sporadic.Mathieu.M22TwoLocalOrders.not_seven_dvd_card_twoLocal S _ hloc
    (hSJ.trans hJN) (h7.trans (card_dvd_of_le hJN))
private theorem seven_dvd_image {A X : Type*}
    [Group A] [Finite A] [Group X] (f : A →* X) (B : Subgroup A)
    (hc : Nat.Coprime 7 (Nat.card f.ker)) (h7 : 7 ∣ Nat.card B) :
    7 ∣ Nat.card (B.map f) := by
  let g := f.comp B.subtype
  have hg : Nat.card g.ker ∣ Nat.card f.ker := by
    let j : g.ker →* f.ker := {
      toFun x := ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact card_dvd_of_injective j
      (fun x y h => Subtype.ext (Subtype.ext (congrArg (fun t : f.ker => (t : A)) h)))
  have he := g.ker.card_mul_index
  rw [index_ker] at he
  have hrg : g.range = B.map f := by simp [g, MonoidHom.range_comp]
  rw [hrg] at he
  exact (hc.coprime_dvd_right hg).dvd_of_dvd_mul_left (he.symm ▸ h7)

/-- The original faithful nonabelian actor is not the triple-M₂₂ extension. -/
theorem point_hat_not_triple_mathieu
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U) :
    ¬ Nonempty (F.TerminalHdot ≃*
      Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel.actionGroup) := by
  rintro ⟨e⟩
  obtain ⟨C⟩ := componentGeometry earlier h hn F
  let D := F.terminalDot C.K1
  let B := D.map e.toMonoidHom
  let q := dotMap F F.terminalHatAction C.K1 C.point_le
  let a : D ≃* B := D.equivMapOfInjective e.toMonoidHom e.injective
  let := C.component.perfect
  let : Group.IsPerfect D := Group.IsPerfect.map _
  let : D.Normal := C.normal.map (QuotientGroup.mk' F.terminalHatAction.ker)
    (QuotientGroup.mk'_surjective _)
  let : Group.IsPerfect B := Group.IsPerfect.map _
  let : B.Normal := Normal.map inferInstance e.toMonoidHom e.surjective
  have hPD : F.terminalDot (F.Li L 1) ≤ D := map_mono (comap_mono C.contains)
  have h7D : 7 ∣ Nat.card D := (point_hat_seven_dvd h hn F hne).trans (card_dvd_of_le hPD)
  have h7B : 7 ∣ Nat.card B := by rwa [card_map_of_injective e.injective]
  obtain ⟨f,hf,hker⟩ := Sporadic.Mathieu.M22TripleCover.NormalImage.exists_quotient B h7B
  let k := a.toMonoidHom.comp q
  have hk : Function.Surjective k := a.surjective.comp (dotMap_surjective _ _ _ _)
  let ψ := f.comp k
  have hψ : Function.Surjective ψ := hf.comp hk
  let P := (F.terminalDot (F.Li L 1)).map e.toMonoidHom
  have hPB : P ≤ B := map_mono hPD
  let A := P.subgroupOf B
  have h7A : 7 ∣ Nat.card A := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPB).toEquiv,card_map_of_injective e.injective]
    exact point_hat_seven_dvd h hn F hne
  have h7f : 7 ∣ Nat.card (A.map f) := seven_dvd_image f A (by rw [hker]; decide) h7A
  have hAJ : A.map f ≤ pointIntersectionImage F L C.K1 ψ := by
    rintro y ⟨b,hb,rfl⟩
    obtain ⟨d,hd,he⟩ := hb
    obtain ⟨t,ht,rfl⟩ := hd
    have htK : (t : G) ∈ C.K1 := C.contains ht
    refine ⟨⟨t,⟨(show F.Li L 1 ≤ F.Li L 1 ⊔ (T : Subgroup G) from le_sup_left) ht,
      htK⟩⟩,?_⟩
    change f (k ⟨t,htK⟩) = f b
    exact congrArg f (Subtype.ext he)
  exact point_mathieu_image_excluded h hn earlier F ⟨C.point_le,C.component⟩ ψ hψ
    (h7f.trans (card_dvd_of_le hAJ))

/-- Exclude the actual G.11.2(13) group in both original degrees. -/
theorem nonabelian_not_caseThirteen
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] :
    ¬ ChapterG.Section11.CaseThirteen F.terminalRepresentation :=
  fun hc => point_hat_not_triple_mathieu h hn earlier F hne hc.2

/-- The printed catalogue leaves only its two original six-dimensional rows, both with n=4. -/
theorem nonabelian_catalogue_six_space
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (X : Subgroup F.TerminalHdot)
    (hc : ChapterG.Section11.Conclusion F.terminalRepresentation B X) :
    n = 4 ∧ (ChapterG.Section11.CaseFour F.terminalRepresentation ∨
      ChapterG.Section11.CaseFive F.terminalRepresentation B) := by
  exact (nonabelian_catalogue_three_rows h hn earlier F hne B X hc).resolve_right
    (nonabelian_not_caseThirteen h hn earlier F hne)

/-- The corrected catalogue also reduces to the natural A₇ and split orthogonal six-space rows. -/
theorem nonabelian_corrected_catalogue_six_space
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (W : Submodule (ZMod 2) (Additive F.Uhat))
    (X : Subgroup F.TerminalHdot) (X₀ : Subgroup X)
    (hc : ChapterG.Section11.FullLinearFour.ConclusionWithFullLinearFour
      F.terminalRepresentation B v W X X₀) :
    n = 4 ∧ (ChapterG.Section11.CaseFour F.terminalRepresentation ∨
      ChapterG.Section11.CaseFive F.terminalRepresentation B) := by
  exact (nonabelian_corrected_catalogue_three_rows h hn earlier F hne B v W X X₀ hc).resolve_right
    (nonabelian_not_caseThirteen h hn earlier F hne)

/-- Degree-five abelianity, conditional only on the actual printed catalogue witness. -/
theorem five_point_span_abelian_of_catalogue
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (X : Subgroup F.TerminalHdot)
    (hc : ChapterG.Section11.Conclusion F.terminalRepresentation B X) :
    IsMulCommutative F.U := by
  by_contra hne
  have he := (nonabelian_catalogue_six_space h (Or.inr rfl) earlier F hne B X hc).1
  omega

/-- Degree-five abelianity for the corrected catalogue, including the exceptional full-linear row. -/
theorem five_point_span_abelian_of_corrected_catalogue
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 5)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 5) [IsElementaryAbelian 2 F.Uhat]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (W : Submodule (ZMod 2) (Additive F.Uhat))
    (X : Subgroup F.TerminalHdot) (X₀ : Subgroup X)
    (hc : ChapterG.Section11.FullLinearFour.ConclusionWithFullLinearFour
      F.terminalRepresentation B v W X X₀) : IsMulCommutative F.U := by
  by_contra hne
  have he := (nonabelian_corrected_catalogue_six_space h (Or.inr rfl) earlier F hne B v W X X₀ hc).1
  omega

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
