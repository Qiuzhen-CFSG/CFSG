module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicComponents
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow
public import Theory.SpecificGroups.PSL3Two.Automorphisms.SylowStabilizer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure

/-!
# The surviving linear action of the original cubic completion

A normal A₅ component in the faithful action quotient is impossible.
Each solvable vertex normalizes its intersection with a Sylow four-group:
that intersection is the two-core of the corresponding proper subgroup
of A₅. The common-normal-subgroup property of the Goldschmidt triple
would then put this four-group in the trivial ambient two-core.

For a PSL₃(2) component, a cubic residual outside the component preserves
its Sylow subgroup and hence acts trivially, by the two-group automorphism
stabilizer. This contradicts the original nonnormalization obstruction.
Thus both cubic residuals lie in the component and generate the whole
action residual. The original Sylow preserves a parabolic of PSL₃(2),
so its action is inner. Triviality of the component centralizer then
identifies the entire action quotient D/C_D(W) with PSL₃(2).

The final application retains the escaping cubic from the actual
order-four chief interval, both original generators and all exact kernels.
The natural-module and ambient geometric exclusion of the remaining
PSL₃(2) case is still needed for solvability of D. Earlier 14.3.4 remains
the named independent faithful-classification input.

Source: Aschbacher–Smith, proof of 14.5.8, printed pp.1014–1015,
and its use in 14.7.20(2), printed p.1049, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
universe u

private theorem alternating_normal_sylow_intersection
    {D : Type*} [Group D] [Finite D]
    (S : Sylow 2 D) (J A : Subgroup D) [J.Normal] [Group.IsSolvable A]
    (e : J ≃* alternatingGroup (Fin 5)) (hSA : (S : Subgroup D) ≤ A) :
    A ≤ normalizer (((S : Subgroup D) ⊓ J : Subgroup D) : Set D) := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal J
  let B := A.subgroupOf J
  have hRB : (R : Subgroup J) ≤ B := by rw [hR]; exact comap_mono hSA
  have hBA : B.map J.subtype ≤ A := (subgroupOf_map_subtype A J).le.trans inf_le_left
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hBA).comp
      (B.equivMapOfInjective J.subtype J.subtype_injective).toMonoidHom)
    ((inclusion_injective hBA).comp (B.equivMapOfInjective J.subtype J.subtype_injective).injective)
  have hBN := alternatingGroup.solvable_sylow_overgroup_le_normalizer_of_equiv e R B hRB
  have hcore : B.pCoreIn 2 = (R : Subgroup J) := by
    apply le_antisymm
    · have hh := pCoreIn_le_sylow B (R.subtype hRB)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hRB] using hh
    · exact le_pCoreIn_of_normalizes R.isPGroup' hRB hBN
  have he : (A ⊓ J).pCoreIn 2 = (S : Subgroup D) ⊓ J := by
    have hh := congrArg (map J.subtype) hcore
    rw [map_pCoreIn_of_injective 2 _ _ J.subtype_injective,
      subgroupOf_map_subtype,hR,subgroupOf_map_subtype] at hh
    exact hh
  rw [←he]
  exact ((le_inf A.le_normalizer le_normalizer_of_normal).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (A ⊓ J) (pCore 2 (A ⊓ J : Subgroup D)))

private theorem goldschmidt_no_alternating_normal
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : CFSG.Quasithin.ChapterF.IsGoldschmidtTriple A B)
    (hcore : pCore 2 D = ⊥) (J : Subgroup D) [J.Normal]
    (e : J ≃* alternatingGroup (Fin 5)) : False := by
  let : Group.IsSolvable A := SymmetricThreeTwoCore.solvable ht.quotient_left.some
  let : Group.IsSolvable B := SymmetricThreeTwoCore.solvable ht.quotient_right.some
  obtain ⟨S,hS⟩ := ht.intersection_sylow
  have hSA : (S : Subgroup D) ≤ A := hS.symm.le.trans inf_le_left
  have hSB : (S : Subgroup D) ≤ B := hS.symm.le.trans inf_le_right
  have hA := alternating_normal_sylow_intersection S J A e hSA
  have hB := alternating_normal_sylow_intersection S J B e hSB
  have hbot : (S : Subgroup D) ⊓ J = ⊥ :=
    ht.common_normal_eq_bot hcore _ (inf_le_left.trans hS.ge)
      (normal_subgroupOf_of_le_normalizer hA) (normal_subgroupOf_of_le_normalizer hB)
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal J
  have hRbot : (R : Subgroup J) = ⊥ := by
    apply map_injective J.subtype_injective
    rw [hR,subgroupOf_map_subtype,hbot,Subgroup.map_bot]
  have hc := Theory.PSL2.SylowFixedQuotients.alternating_sylow_card
    (R.mapSurjective (f := e.toMonoidHom) e.surjective)
  change Nat.card ((R : Subgroup J).map e.toMonoidHom) = 4 at hc
  simp [hRbot] at hc

private theorem goldschmidt_escaping_residual_centralizes_linear
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (J : Subgroup D) [J.Normal]
    (e : J ≃* Matrix.PSL3Two.PSL)
    (hout : ¬ (pResidual 2 B).map B.subtype ≤ J) :
    (pResidual 2 B).map B.subtype ≤ centralizer (J : Set D) := by
  let R := (pResidual 2 B).map B.subtype
  obtain ⟨S,hS⟩ := ht.intersection_sylow
  have hSB : (S : Subgroup D) ≤ B := hS.symm.le.trans inf_le_right
  have hBJ : B ≤ normalizer (J : Set D) := le_normalizer_of_normal
  have hJB : IsPGroup 2 (J ⊓ B : Subgroup D) := by
    have hh := (ht.right_subnormal_core_iff_not_residual_le J
      (Normal.isSubnormal inferInstance)).mpr hout
    exact (pCore_isPGroup.map B.subtype).to_le ((inf_comm J B).le.trans hh)
  let f : J ≃* Matrix.PSL3Two.SL := e.trans Matrix.PSL3Two.equiv.symm
  let a : B →* MulAut Matrix.PSL3Two.SL := (MulAut.congr f).toMonoidHom.comp
    (J.normalizerMonoidHom.comp (inclusion hBJ))
  have ha (x : B) (k : J) : a x (f k) =
      f (J.normalizerMonoidHom ⟨x,hBJ x.property⟩ k) := by
    change f (J.normalizerMonoidHom ⟨x,hBJ x.property⟩ (f.symm (f k))) = _
    rw [f.symm_apply_apply]
  have htriv := NormalSylowQuotientAction.pPerfect_action_eq_one S J B R
    hBJ hSB hJB (map_subtype_le _) (isPPerfect_embedded_pResidual 2 B)
    f.toMonoidHom f.surjective a ha Matrix.PSL3Two.automorphism_sylow_stabilizer_two
  intro r hr
  apply mem_centralizer_iff.mpr
  intro j hj
  have he := congrArg (fun b : MulAut Matrix.PSL3Two.SL => b (f ⟨j,hj⟩))
    (htriv ⟨r,hr⟩)
  rw [ha] at he
  have hfix := congrArg Subtype.val (f.injective he)
  change r * j * r⁻¹ = j at hfix
  exact ((mul_inv_eq_iff_eq_mul).mp hfix).symm

private theorem goldschmidt_linear_component_residual
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (J : Subgroup D) [J.Normal]
    [Group.IsPerfect J] (e : J ≃* Matrix.PSL3Two.PSL)
    (hcases : ((pResidual 2 A).map A.subtype ≤ J ∧ J ⊔ B = ⊤) ∨
      ((pResidual 2 B).map B.subtype ≤ J ∧ J ⊔ A = ⊤))
    (hout : ¬ (pResidual 2 B).map B.subtype ≤
      normalizer ((pResidual 2 A).map A.subtype : Set D)) :
    (pResidual 2 A).map A.subtype ≤ J ∧
      (pResidual 2 B).map B.subtype ≤ J ∧ pResidual 2 D = J := by
  have hboth : (pResidual 2 A).map A.subtype ≤ J ∧
      (pResidual 2 B).map B.subtype ≤ J := by
    rcases hcases with ⟨hA,_⟩ | ⟨hB,_⟩
    · refine ⟨hA,?_⟩
      by_contra hn
      exact hout (((goldschmidt_escaping_residual_centralizes_linear ht J e hn).trans
        (centralizer_le hA)).trans (Subgroup.centralizer_le_normalizer _))
    · refine ⟨?_,hB⟩
      by_contra hn
      have hc := goldschmidt_escaping_residual_centralizes_linear ht.symm J e hn
      exact hout ((hB.trans (le_centralizer_iff.mp hc)).trans (Subgroup.centralizer_le_normalizer _))
  refine ⟨hboth.1,hboth.2,le_antisymm ?_ ?_⟩
  · rw [ht.twoResidual_eq_sup]
    exact sup_le hboth.1 hboth.2
  · apply le_pResidual_of_isPPerfect J
    intro N hN hq
    let : N.Normal := hN
    by_contra hn
    let : Nontrivial (J ⧸ N) := QuotientGroup.nontrivial_iff.mpr hn
    let : Group.IsPerfect (J ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (J ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (J ⧸ N) inferInstance


private theorem goldschmidt_linear_residual_eq_top
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 D = ⊥)
    (J : Subgroup D) [J.Normal] [Group.IsPerfect J] [IsSimpleGroup J]
    (e : J ≃* Matrix.PSL3Two.PSL) (hres : pResidual 2 D = J) : J = ⊤ := by
  let : Group.IsSolvable A := SymmetricThreeTwoCore.solvable ht.quotient_left.some
  have hquot : IsPGroup 2 (D ⧸ J) := hres ▸ isPGroup_quotient_pResidual 2
  have hC : centralizer (J : Set D) = ⊥ := centralizer_eq_bot_of_simple_two_quotient
    J (Group.IsPerfect.not_isMulCommutative J) hquot hcore
  obtain ⟨S,hS⟩ := ht.intersection_sylow
  have hSA : (S : Subgroup D) ≤ A := hS.symm.le.trans inf_le_left
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal J
  let P := A.subgroupOf J
  have hRP : (R : Subgroup J) ≤ P := by rw [hR]; exact comap_mono hSA
  have hproper : P ≠ ⊤ := by
    intro hz
    have hJA : J ≤ A := subgroupOf_eq_top.mp hz
    exact Group.IsPerfect.not_isSolvable J
      (Group.isSolvable_of_isSolvable_injective (f := inclusion hJA) (inclusion_injective hJA))
  have hRA : (pResidual 2 A).map A.subtype ≤ J := hres ▸ map_pResidual_le 2 A.subtype
  have hnot : ¬ IsPGroup 2 P := by
    intro hp
    have hp' : IsPGroup 2 (A ⊓ J : Subgroup D) :=
      (subgroupOf_map_subtype A J) ▸ hp.map J.subtype
    have hle : A ⊓ J ≤ (pCore 2 A).map A.subtype :=
      le_pCoreIn_of_normalizes hp' inf_le_left
        ((le_inf A.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf)
    exact ((ht.left_subnormal_core_iff_not_residual_le J
      (Normal.isSubnormal inferInstance)).mp hle) hRA
  obtain ⟨f,_,hP⟩ := Matrix.PSL3Two.exists_sylow_line_marking e R P hRP hproper hnot
  have hSJ : (S : Subgroup D) ≤ J := by
    intro s hs
    let a : MulAut J := MulAut.conjNormal s
    have hPa : P.map a.toMonoidHom = P := by
      apply eq_of_le_of_card_ge
      · rintro x ⟨x,hx,rfl⟩
        change s * (x : D) * s⁻¹ ∈ A
        exact A.mul_mem (A.mul_mem (hSA hs) hx) (A.inv_mem (hSA hs))
      · rw [card_map_of_injective (f := a.toMonoidHom) a.injective]
    let b := MulAut.congr f a
    have hb : Matrix.PSL3Two.lineParabolicSL.map b.toMonoidHom = Matrix.PSL3Two.lineParabolicSL := by
      have he : b.toMonoidHom.comp f.toMonoidHom = f.toMonoidHom.comp a.toMonoidHom := by
        apply MonoidHom.ext
        intro x
        change f (a (f.symm (f x))) = f (a x)
        rw [f.symm_apply_apply]
      rw [←hP,map_map,he,←map_map,hPa]
    have hbR : (Matrix.PSL3Two.MarkedAutomorphisms.residual Matrix.PSL3Two.lineParabolicSL).map
        b.toMonoidHom = Matrix.PSL3Two.MarkedAutomorphisms.residual Matrix.PSL3Two.lineParabolicSL := by
      change ((pResidual 2 Matrix.PSL3Two.lineParabolicSL).map
        Matrix.PSL3Two.lineParabolicSL.subtype).map b.toMonoidHom = _
      rw [map_embedded_pResidual,hb]
      rfl
    obtain ⟨g,_,hg⟩ := Matrix.PSL3Two.MarkedAutomorphisms.preserving_residual_is_conj
      _ (Or.inr rfl) b hbR
    let j := f.symm g
    have ha : a = MulAut.conj j := by
      apply MulEquiv.ext
      intro x
      apply f.injective
      have hh := congrArg (fun c : MulAut Matrix.PSL3Two.SL => c (f x)) hg
      change f (a (f.symm (f x))) = g * f x * g⁻¹ at hh
      rw [f.symm_apply_apply] at hh
      change f (a x) = f (j * x * j⁻¹)
      simpa only [map_mul,map_inv,j,f.apply_symm_apply] using hh
    have hsj : s * (j : D)⁻¹ ∈ centralizer (J : Set D) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer J]
      change (MulAut.conjNormal : D →* MulAut J) (s * (j : D)⁻¹) = 1
      rw [map_mul,map_inv,MulAut.conjNormal_val]
      change a * (MulAut.conj j)⁻¹ = 1
      rw [ha,mul_inv_cancel]
    have he : s = (j : D) := mul_inv_eq_one.mp (mem_bot.mp (hC ▸ hsj))
    exact he.symm ▸ j.property
  have hh := pResidual_sup_sylow_eq_top S
  rw [hres,sup_eq_left.mpr hSJ] at hh
  exact hh


/-- A core-free Goldschmidt completion with a normal linear-three component
and nonnormalizing cubic residuals is exactly that component. -/
theorem goldschmidt_linear_completion
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 D = ⊥)
    (J : Subgroup D) [J.Normal] [Group.IsPerfect J] [IsSimpleGroup J]
    (e : J ≃* Matrix.PSL3Two.PSL)
    (hcases : ((pResidual 2 A).map A.subtype ≤ J ∧ J ⊔ B = ⊤) ∨
      ((pResidual 2 B).map B.subtype ≤ J ∧ J ⊔ A = ⊤))
    (hout : ¬ (pResidual 2 B).map B.subtype ≤
      normalizer ((pResidual 2 A).map A.subtype : Set D)) : J = ⊤ := by
  exact goldschmidt_linear_residual_eq_top ht hcore J e
    (goldschmidt_linear_component_residual ht J e hcases hout).2.2


open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The A₅ component alternative is impossible in the original cubic
completion: its faithful image would have a normal Sylow four-group. -/
theorem cubic_generated_component_not_alternating_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    ¬ Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨_,⟨e⟩⟩ := cubic_generated_component_action_kernel_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨_,_,hnq,_⟩ := cubic_generated_component_action_reduction_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  let : (J.map q).Normal := hnq
  obtain ⟨_,ht,hcore⟩ := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  rintro ⟨a⟩
  exact goldschmidt_no_alternating_normal ht hcore (J.map q) (e.symm.trans a)

/-- The original full point-normality interface. -/
theorem cubic_generated_component_not_alternating
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    ¬ Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) := by
  apply cubic_generated_component_not_alternating_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- Every C-component of the original escaping cubic completion has the
actual PSL₃(2) two-core quotient. The earlier A₅ alternative is discharged. -/
theorem cubic_generated_component_linear_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  obtain ⟨hJL,hJf⟩ := cubic_generated_component_faithful_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he J hJ
  let eJ := J.equivMapOfInjective D.subtype D.subtype_injective
  let eQ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  rcases (faithful (J.map D.subtype) hJL hJf).1 with a | a
  · exact (cubic_generated_component_not_alternating_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ ⟨eQ.trans a.some⟩).elim
  · exact ⟨eQ.trans a.some⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_component_linear
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL) := by
  apply cubic_generated_component_linear_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- Both original cubic residuals lie in the component image. They generate
the entire two-residual of the literal action quotient, isomorphic to PSL₃(2). -/
theorem cubic_generated_component_action_residual_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    J.Normal ∧ (q.subgroupMap J).ker = pCore 2 J ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL) ∧
      pResidual 2 (D ⧸ C) = J.map q ∧
      ((F.Li L 2).subgroupOf D).map q ⊔ (Y.subgroupOf D).map q = J.map q ∧
      Nonempty ((pResidual 2 (D ⧸ C)) ≃* Matrix.PSL3Two.PSL) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨a⟩ := cubic_generated_component_linear_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨hk,⟨e⟩⟩ := cubic_generated_component_action_kernel_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨hnJ,hjq,hnq,hcases⟩ := cubic_generated_component_action_reduction_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  let : (J.map q).Normal := hnq
  let : IsQuasisimple (J.map q) := hjq.2
  obtain ⟨_,ht,_⟩ := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have ho := cubic_generated_action_normalizer_obstruction_of_normalizes_point h structural Y hYH hYL hout
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  have ha : (pResidual 2 (((F.P L).subgroupOf D).map q)).map
      (((F.P L).subgroupOf D).map q).subtype = ((F.Li L 2).subgroupOf D).map q := by
    rw [←map_embedded_pResidual,hr.1]
  have hb : (pResidual 2 (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q)).map
      (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).subtype = (Y.subgroupOf D).map q := by
    rw [←map_embedded_pResidual,hr.2]
  have hh := goldschmidt_linear_component_residual ht (J.map q) (e.symm.trans a)
    (by rwa [ha,hb]) (by rwa [ha,hb])
  have hgen : ((F.Li L 2).subgroupOf D).map q ⊔ (Y.subgroupOf D).map q = J.map q := by
    rw [←ha,←hb,←ht.twoResidual_eq_sup]
    exact hh.2.2
  exact ⟨hnJ,hk,⟨a⟩,hh.2.2,hgen,
    ⟨(MulEquiv.subgroupCongr hh.2.2).trans (e.symm.trans a)⟩⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_component_action_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    J.Normal ∧ (q.subgroupMap J).ker = pCore 2 J ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL) ∧
      pResidual 2 (D ⧸ C) = J.map q ∧
      ((F.Li L 2).subgroupOf D).map q ⊔ (Y.subgroupOf D).map q = J.map q ∧
      Nonempty ((pResidual 2 (D ⧸ C)) ≃* Matrix.PSL3Two.PSL) := by
  apply cubic_generated_component_action_residual_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

/-- The entire faithful action quotient of the nonsolvable cubic completion
is PSL₃(2); the parabolic preserved by the original Sylow excludes outer action. -/
theorem cubic_generated_component_action_quotient_of_normalizes_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hYL : Y ≤ normalizer (F.Li L 1 : Set G)) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    Nonempty ((D ⧸ C) ≃* Matrix.PSL3Two.PSL) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨_,_,⟨a⟩,hr,_,_⟩ := cubic_generated_component_action_residual_of_normalizes_point
    h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨_,⟨e⟩⟩ := cubic_generated_component_action_kernel_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  obtain ⟨_,hj,hnj,_⟩ := cubic_generated_component_action_reduction_of_normalizes_point h hab structural previous faithful Y hYH hYL hYp hYT hout he J hJ
  let : (J.map q).Normal := hnj
  let : IsQuasisimple (J.map q) := hj.2
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (J.map q) := (e.symm.trans a).isSimpleGroup
  obtain ⟨_,ht,hcore⟩ := cubic_generated_action_triple_of_normalizes_point h hab structural previous Y hYH hYL hYp hYT hout he
  have hjtop := goldschmidt_linear_residual_eq_top ht hcore (J.map q) (e.symm.trans a) hr
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hjtop.symm).trans (e.symm.trans a))⟩

/-- The original full point-normality interface. -/
theorem cubic_generated_component_action_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    Nonempty ((D ⧸ C) ≃* Matrix.PSL3Two.PSL) := by
  apply cubic_generated_component_action_quotient_of_normalizes_point
    (h := h) (hab := hab) (structural := structural) (previous := previous) (faithful := faithful)
    (Y := Y) (hYH := hYH) (hYp := hYp) (hYT := hYT)
    (hout := hout) (he := he) (J := J) (hJ := hJ)
  exact hYH.trans ((normal_subgroupOf_iff_le_normalizer
    ((F.Li_le L 1).trans inf_le_right)).mp hn)

open NoncentralChiefRefinement ChapterA.Section04 in
/-- For the literal order-four chief interval, a nonsolvable cubic completion
has a normal faithful PSL₃(2) component whose image is the entire
faithful action quotient. The original star kernel and both cubic generators are retained. -/
theorem extraspecial_four_interval_cubic_linear_residual
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hUN : F.U ≤ N.val.map F.H.subtype)
    (hBC : B.val.map F.H.subtype ≤ centralizer (F.U : Set G))
    (hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U)
    (hm : ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype)
    (hc : Nat.card (Section N B) = 4) :
    ∃ Y : Subgroup G, ∃ hYH : Y ≤ F.H,
      Y ≤ K F ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧
      Y ≤ normalizer (F.Li L 1 : Set G) ∧ ¬ Y ≤ normalizer (L : Set G) ∧
      Nat.card (star F Y) = 3 ∧
      star F Y ≠ (center (pResidual 2 (HStar F.H))).map (pResidual 2 (HStar F.H)).subtype ∧
      ((starMap F).comp (inclusion hYH)).ker = pCore 2 Y ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3 ∧
      Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)) ∧
      let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
      let W := conjugateSpanBy (F.Vi 1) D
      letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
        (le_normalizer_conjugateSpanBy _ _)
      let C := centralizer (W.subgroupOf D : Set D)
      let q := QuotientGroup.mk' C
      Group.IsSolvable D ∨ ∃ J : Subgroup G, ∃ _hJD : J ≤ D,
        (J.subgroupOf D).IsCComponent ∧ (J.subgroupOf D).Normal ∧
        J ∈ Chapter1.LStar G (T : Subgroup G) ∧ IsFaithfulSignalizerType J ∧
        (J.subgroupOf (J ⊔ (T : Subgroup G))).Normal ∧
        Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL) ∧
        (q.subgroupMap (J.subgroupOf D)).ker = pCore 2 (J.subgroupOf D) ∧
        Nonempty ((J ⧸ pCore 2 J) ≃* (J.subgroupOf D).map q) ∧
        pResidual 2 (D ⧸ C) = (J.subgroupOf D).map q ∧
        ((F.Li L 2).subgroupOf D).map q ⊔ (Y.subgroupOf D).map q = (J.subgroupOf D).map q ∧
        Nonempty ((pResidual 2 (D ⧸ C)) ≃* Matrix.PSL3Two.PSL) ∧
        Nonempty ((D ⧸ C) ≃* Matrix.PSL3Two.PSL) := by
  classical
  obtain ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he⟩ :=
    extraspecial_four_interval_escaping_symmetricThree h hab structural previous hex hcard hexp
      N B hNB hUN hBC hp hm hc
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  refine ⟨Y,hYH,hYK,hYp,hYT,hYL,hout,hcY,hZ,hker,hquot,he,?_⟩
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  by_cases hs : Group.IsSolvable D
  · exact Or.inl hs
  right
  obtain ⟨J,hJD,hJ,hmax,hf,hnJ,_⟩ := cubic_generated_nonsolvable_component
    h hab structural previous faithful hn Y hYH hYp hYT hout he hs
  obtain ⟨hnD,hk,⟨a⟩,hres,hgen,hmodel⟩ := cubic_generated_component_action_residual
    h hab structural previous faithful hn Y hYH hYp hYT hout he (J.subgroupOf D) hJ
  obtain ⟨_,⟨e⟩⟩ := cubic_generated_component_action_kernel h hab structural previous faithful hn
    Y hYH hYp hYT hout he (J.subgroupOf D) hJ
  let eJ := subgroupOfEquivOfLe hJD
  let eQ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  exact ⟨J,hJD,hJ,hnD,hmax,hf,hnJ,⟨eQ.symm.trans a⟩,hk,⟨eQ.symm.trans e⟩,hres,hgen,hmodel,
    cubic_generated_component_action_quotient h hab structural previous faithful hn
      Y hYH hYp hYT hout he (J.subgroupOf D) hJ⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
