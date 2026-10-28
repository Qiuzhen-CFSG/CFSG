module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ComponentOrbitExclusion
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Mathieu.Recognition
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.CatalogueTensor
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.TwistedTensor
public import CFSG.Quasithin.ChapterG.Section11.NontrivialActorCatalogue
public import Theory.Representation.BinaryPermutation.PointStabilizerRank

/-!
# Component rows of the original G.11 catalogue

The solvable extraspecial extension and the natural A₇, split-six and G₂(2)
actions are excluded using the original terminal group's nonsolvability,
point-centralizer three-rank bound and invariant extraspecial square form.
The actual orthogonal coordinates identify the literal two-residual, while
the native Mathieu extension identifies its generalized Fitting triple cover.
Both identifications retain the original action-kernel quotient. Finally the
SL₂(8) triple tensor moves four dimensions on every involution, excluding the
original low-rank clause of G.11.1.

These source adapters feed the original-flag reduction in `CatalogueExclusion`;
they do not assume the marked catalogue or identify actions from group orders.
Source: Aschbacher--Smith G.11.2(1--7,11,13) and 14.4.2,
printed pp.364,1006--1007; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
open ClassicalOrthogonal.FourPlusMatrix
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension CoreGeometry LargerDimension.LocalAction.Components
open Chapter14.Section03.NonabelianSource.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The genuine orthogonal row of G.11 identifies the literal two-residual,
not only the generalized Fitting subgroup. -/
theorem source_case_seven_catalogue (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (X : Subgroup F.TerminalHdot)
    (hm : ChapterG.Section11.CaseSeven F.terminalRepresentation X) :
    letI := chosen.elementary
    letI := F.U_normal
    RankCore.ActionAlternative.{0} (sourceAction F
      (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)) := by
  let := chosen.elementary
  let := F.U_normal
  obtain ⟨_,_,e₀,f₀,h₀⟩ := hm
  let N := generalizedFitting F.TerminalHdot
  let e := e₀.trans Binary.orthogonalEquiv.symm
  let f := f₀.trans Binary.binaryCoordinates
  have hf (a : N) (w : Additive F.Uhat) :
      f (F.terminalRepresentation a w) = Binary.action (e a) (f w) := by
    change Binary.binaryCoordinates (f₀ (F.terminalRepresentation a w)) = _
    have hh := h₀ a w
    change f₀ (F.terminalRepresentation a w) = _ at hh
    rw [hh]
    have hh := Binary.binaryCoordinates_projective_equivariant
      (Binary.orthogonalEquiv.symm (e₀ a)) (f₀ w)
    rw [MulEquiv.apply_symm_apply] at hh
    exact hh
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_,_,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hres := OrthogonalOrbit.residual_eq_of_coordinates F.terminalRepresentation
    hyp.faithful B hyp.nondegenerate hyp.preserves N e f hf
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  let R := (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))
  have hR : R.map q.toMonoidHom = N := by
    dsimp only [R]
    rw [map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _),
      map_pResidual_of_surjective 2 _ q.surjective,hres]
  let eR : R ≃* N := (q.subgroupMap R).trans (MulEquiv.subgroupCongr hR)
  refine .orthogonal ((eR.trans e).trans elementaryEquiv)
    (f.trans Binary.binaryCoordinates.symm) ?_
  intro k w
  apply Binary.binaryCoordinates.injective
  change Binary.binaryCoordinates (Binary.binaryCoordinates.symm
    (f (F.terminalRepresentation (q k.val) w))) = _
  rw [Binary.binaryCoordinates.apply_symm_apply]
  change f (F.terminalRepresentation (eR k) w) =
    Binary.binaryCoordinates (((elementaryEquiv (e (eR k))).val.val)
      (Binary.binaryCoordinates.symm (f w)))
  rw [hf]
  rw [show Binary.binaryCoordinates (((elementaryEquiv (e (eR k))).val.val)
      (Binary.binaryCoordinates.symm (f w))) =
      Binary.action (e (eR k)) (Binary.binaryCoordinates (Binary.binaryCoordinates.symm (f w))) from
        toOrthogonal_coordinates (e (eR k)) (Binary.binaryCoordinates.symm (f w))]
  rw [Binary.binaryCoordinates.apply_symm_apply]


open Sporadic.Mathieu
open Janko4.InvolutionCentralizers.First.QuotientExtension
open ChapterH.Section10To12

private theorem triple_of_native {Q : Type*} [Group Q] [Finite Q]
    (e : Q ≃* LargerDimension.Mathieu.ActorCatalogue.Native.Model)
    (hcore : pCore 2 Q = ⊥) : IsTripleM22 (generalizedFitting Q) := by
  let j := e.symm.toMonoidHom.comp coverInclusion
  have hj : Function.Injective j := e.symm.injective.comp (Subgroup.inclusion_injective _)
  have hind : j.range.index = 2 := by
    rw [MonoidHom.range_comp,coverInclusion_range]
    exact (coverSubgroup.index_map_equiv e.symm).trans coverSubgroup_index
  have hF := generalizedFitting_eq_range_of_quasisimple_index_two j hj hind hcore
  let c := (MulEquiv.subgroupCongr hF).trans (MonoidHom.ofInjective hj).symm
  have hc : (center (generalizedFitting Q)).map c.toMonoidHom = center M22TripleCover := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr c ⟨x,hx⟩).property
    · intro x hx
      exact ⟨c.symm x,((centerCongr c).symm ⟨x,hx⟩).property,c.apply_symm_apply x⟩
  exact {
    quasisimple := IsQuasisimple.of_mulEquiv c.symm
    center_card := (Nat.card_congr (centerCongr c).toEquiv).trans M22TripleCover.center_card
    centralQuotient := ⟨(QuotientGroup.congr _ _ c hc).trans M22TripleCover.centralQuotientEquiv⟩ }

/-- The whole group in G.11.2(13) determines its literal triple-cover
component. The original source hypotheses supply irreducibility. -/
theorem source_case_thirteen_catalogue (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (hm : ChapterG.Section11.CaseThirteen F.terminalRepresentation) :
    letI := chosen.elementary
    letI := F.U_normal
    RankCore.ActionAlternative.{0} (sourceAction F
      (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)) := by
  let := chosen.elementary
  let := F.U_normal
  obtain ⟨hd,⟨e⟩⟩ := hm
  let hk := source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ
  let q := QuotientGroup.quotientMulEquivOfEq hk.symm
  have hK := triple_of_native (q.trans e) (pCore_quotient_pCore_eq_bot 2)
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_,_,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  have hi := hyp.irreducible_of_not_solvable
    (source_large_terminal_not_solvable d earlier hq chosen structural alternatives F hne hZ hlarge)
  refine .tripleM22 hK ?_ hd
  change IsIrreducible (F.terminalRepresentation.comp q.toMonoidHom)
  exact (irreducible_comp_surjective_iff q.toMonoidHom q.surjective _).mpr hi


private theorem extraspecial_model_solvable : Group.IsSolvable RankTwo.ExtraspecialModel.Model := by
  have hp : IsPGroup 3 RankTwo.ExtraspecialModel.P := IsPGroup.of_card
    (n := 3) (HeisenbergPrime.card (p := 3))
  have hs : IsPGroup 2 RankTwo.ExtraspecialModel.S := IsPGroup.of_card
    (n := 4) (Semidihedral.standardModel_card 4 (Nat.le_refl 4))
  let := hp.isNilpotent
  let := hs.isNilpotent
  exact Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
    SemidirectProduct.range_inl_eq_ker_rightHom.ge

/-- The actual SD₁₆ extension of the cubic extraspecial group is solvable,
so no subgroup in G.11.2(3) can be the original large terminal group. -/
theorem source_case_three_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U)
    (hm : ChapterG.Section11.CaseThree F.terminalRepresentation) : False := by
  obtain ⟨_,H,_,⟨e⟩⟩ := hm
  let := extraspecial_model_solvable
  exact source_large_terminal_not_solvable d earlier hq chosen structural alternatives
    F hne hZ hlarge (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)

/-- The two small-degree catalogue rows are incompatible with the original
extraspecial order, before any group recognition is used. -/
theorem source_large_terminal_dimension_ge_six (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hlarge : 64 < Nat.card F.U) : 6 ≤ finrank (ZMod 2) (Additive F.Uhat) := by
  have hcenter := (source_extraspecial_order d earlier hq chosen structural alternatives
    F hne hZ).1.center_order_p
  have hc : Nat.card F.U = 2 ^ (finrank (ZMod 2) (Additive F.Uhat) + 1) := by
    rw [card_eq_card_quotient_mul_card_subgroup (center F.U),hcenter]
    change Nat.card (Additive F.Uhat) * 2 = _
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,pow_succ]
  by_contra hn
  have hb := Nat.pow_le_pow_right (n := 2) (by decide)
    (by omega : finrank (ZMod 2) (Additive F.Uhat) + 1 ≤ 6)
  rw [← hc] at hb
  norm_num at hb
  omega


/-- The original SL₂(8) scalar-extension marking excludes the low-rank
clause: every involution of the whole acting group moves four dimensions. -/
theorem source_case_eleven_not_lowRank
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (v : Additive F.Uhat) (hv : v ≠ 0)
    (X : Subgroup F.TerminalHdot) [IsElementaryAbelian 2 X]
    (hm : ChapterG.Section11.CaseEleven F.terminalRepresentation) :
    ¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v X := by
  intro hw
  obtain ⟨a,_,ha,_,hr,_⟩ := hw.exists_involution hv
  obtain ⟨_,e,σ,_,_,ht⟩ := hm
  have hh := RankTwo.TwistedTensor.ambient_rank_eq_four σ F.terminalRepresentation e ht a ha
  omega

/-- The original A₇ row has the actual irreducible six-dimensional component,
so the previously proved source point-centralizer bound excludes it. -/
theorem source_case_four_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hm : ChapterG.Section11.CaseFour F.terminalRepresentation) : False := by
  let := chosen.elementary
  obtain ⟨hd,e,f,hf⟩ := hm
  let C := generalizedFitting F.TerminalHdot
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup C := e.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hna : ¬ IsMulCommutative C := Group.IsPerfect.not_isMulCommutative C
  have hC : IsComponent F.TerminalHdot C := SimpleSocle.isComponent hna
  have hc : centralizer (C : Set F.TerminalHdot) = ⊥ := SimpleSocle.centralizer_eq_bot hna
  let τ := (BinaryPermutation.alternatingCoreRepresentation (Fin 7)).comp e.toMonoidHom
  let : IsIrreducible (BinaryPermutation.alternatingCoreRepresentation (Fin 7)) :=
    AlternatingSevenBinarySmallModels.core_irreducible
  have hiτ : IsIrreducible τ :=
    (irreducible_comp_surjective_iff e.toMonoidHom e.surjective _).mpr inferInstance
  let E : Representation.Equiv (F.terminalRepresentation.comp C.subtype) τ := .mk f (by
    intro a
    apply LinearMap.ext
    intro w
    exact hf a w)
  have hi : IsIrreducible (F.terminalRepresentation.comp C.subtype) :=
    (RepEquiv.ofRepresentationEquiv E).irreducible_of_euqiv hiτ
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_,heX,B,v,hyp,_,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let := heX
  have hX : F.terminalDot (F.X g) ≠ ⊥ := by
    intro hz
    have hh := hyp.dimension_bound.1
    have hb := Group.rank_le_of_surjective
      (QuotientGroup.mk' ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
      (QuotientGroup.mk'_surjective _)
    have hzero : Group.rank (F.terminalDot (F.X g)) = 0 := by
      rw [hz]
      exact Group.rank_eq_zero _
    omega
  have hmove : ⁅C,F.terminalDot (F.X g)⁆ ≠ ⊥ := by
    intro hh
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer,hc] at hh
    exact hX (le_bot_iff.mp hh)
  exact source_no_alternating_seven_component d earlier hq chosen structural alternatives
    F hne hZ hd g hgP hgH C hC hmove hi e

/-- The split six-space row contains the actual natural A₈ subgroup.
Its point stabilizer has three-rank two, contradicting the original bound. -/
theorem source_case_five_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hm : ChapterG.Section11.CaseFive F.terminalRepresentation B) : False := by
  obtain ⟨_,c,K,hKn,_,e,he⟩ := ChapterG.Section11.SplitSix.caseFive_selfcentralizing_marking hm
  let := hKn
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  obtain ⟨_,_,B',v,_,hline,_⟩ := source_terminal_marked_hypothesis F d earlier hq chosen
    structural alternatives hne g hgP hgH
  let C := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hHc : F.H ≤ centralizer (F.ZU : Set G) := by
    rw [hZ]
    exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hD : D = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact mem_map_of_mem _ (hHc b.property)
  have hu := CaseOneHS.source_center_centralizing_point_image_three_rank_le_one
    d earlier hq chosen structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (C.subgroupOf D) ≤ 1 at hu
  have hpD : C ≤ D := by rw [hD]; exact le_top
  rw [primeRank_equiv 3 (subgroupOfEquivOfLe hpD)] at hu
  have hr : 2 ≤ primeRank 3 (C.subgroupOf K) := by
    let a := BinaryNaturalDual.Transport.stabilizerEquiv (F.terminalRepresentation.comp K.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) e c.toLinearEquiv he v
    have hb := BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer
      (by simp : 8 ≤ Fintype.card (Fin 8)) (c v)
    exact hb.trans (primeRank_equiv 3 a).ge
  let j : C.subgroupOf K →* C := {
    toFun a := ⟨a.val.val,a.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro a b hab
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C => z.val) hab))
  have hl := Theory.GroupTheory.primeRank_le_of_injective 3 j hj
  omega

/-- The actual G₂(2) natural action is transitive on nonzero vectors and
therefore cannot preserve the original extraspecial square form. -/
theorem source_case_six_exclusion (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (hm : ChapterG.Section11.CaseSix F.terminalRepresentation) : False := by
  let := chosen.elementary
  obtain ⟨hd,e,f,hf⟩ := hm
  let c := source_closure_geometry F d earlier hq chosen structural alternatives hne
  obtain ⟨g,_,hgP,hgH⟩ := exists_source_conjugator d earlier hq chosen structural F
  let q := F.uhatQuadraticForm (by decide) c.two c.frattini_point
    (center_frattini_bot_of_center_point F c hZ)
  obtain ⟨_,hqi,hqn⟩ := quadratic_intersection_of_center_point F c (by decide) hZ g
    (disjoint_iff.mpr (F.parabolic_displaced_centers (by decide) L chosen.normalizes
      c.seed_center g hgP hgH).1)
  have hterminal (a : F.TerminalHdot) (w : Additive F.Uhat) :
      q (F.terminalRepresentation a w) = q w := by
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective F.terminalHatAction.ker a
    exact hqi a w.toMul
  have htrans : ∀ x y : Additive F.Uhat, x ≠ 0 → y ≠ 0 →
      ∃ b, F.terminalRepresentation b x = y := by
    intro x y hx hy
    obtain ⟨b,hb⟩ := Atlas.G2.Natural.action_transitive (x := f x) (y := f y)
      (fun hz => hx (f.map_eq_zero_iff.mp hz)) (fun hz => hy (f.map_eq_zero_iff.mp hz))
    refine ⟨e.symm b,f.injective ?_⟩
    rw [hf,e.apply_symm_apply]
    exact hb
  exact not_nondegenerate_quadratic_of_nonzero_transitive F.terminalRepresentation
    (by omega) htrans q hterminal hqn


end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
