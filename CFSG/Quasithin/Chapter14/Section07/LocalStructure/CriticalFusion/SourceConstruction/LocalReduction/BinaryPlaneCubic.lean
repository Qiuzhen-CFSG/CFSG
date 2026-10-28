module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneCubicLift
public import Theory.Representation.OrthogonalFourPlusMatrix.ExchangeCubicFixer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.OriginalAt.Alternating.PointAction

/-!
# A cubic supplement on the original reciprocal plane

The actual critical involution exchanges the two orthogonal factors and
lies in O₂(L₁T). Its commutators with L₁ lie in O₂(L₁), whose star image
is the full inner Sylow. The exchanged-factor construction therefore
produces an actual cubic in L₁* fixing the whole displacement line,
including the reciprocal section point. The existing literal lift puts
an order-three element in L_Y = O²(C_{L₁}(P)), and proves
L₁ = L_Y O₂(L₁).

The final application retains the same selected path, Y, I₀ and reduced
point span as the previous construction. There is no fixed-cubic or
recognition premise. The lifting theorem also has same-G,T and guarded
many-overgroup versions, preserving the universal published API. The
whole exchanged-branch specialization, exclusion of Y₀ ≤ M, Thompson
contradiction, later reductions through 14.7.52 and all four source Data
inputs remain with the original assembly.

Source: Aschbacher–Smith, proof of 14.7.32, printed pp.1058–1059,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components Swapped Swapped.LinearTwo ModuleAlternatives
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section04.LargerDimension.LocalAction.Components

private theorem orthogonal_exchange_cubic_fixer
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (σ : Representation (ZMod 2) D W)
    (N : Subgroup D) [N.Normal] (hm : HasOrthogonalFourOrbit σ N)
    (A : Subgroup D) (hAN : A ≤ N) (S : Sylow 2 N)
    (hSA : (S : Subgroup N).map N.subtype ≤ A)
    (t : D) (ht2 : t^2=1) (hr : NaturalTensor.operatorFixedCodim (σ t)=2)
    (a : D) (ha : a ∈ A) (ha3 : orderOf a=3)
    (hdisp : t*a*t⁻¹*a⁻¹ ∈ (S : Subgroup N).map N.subtype) :
    ∃ b ∈ A, orderOf b=3 ∧ ∀ z ∈ (σ t-LinearMap.id).range, σ b z=z := by
  obtain ⟨f,e,he⟩ := hm
  let f' := f.trans ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.symm
  let E := e.trans ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
  let γ : Representation (ZMod 2) D ClassicalOrthogonal.FourPlusMatrix.Binary.V :=
    E.conjRingEquiv.toMonoidHom.comp σ
  have hE (g : D) (v : W) : E (σ g v)=γ g (E v) := by
    change E (σ g v)=E (σ g (E.symm (E v)))
    rw [E.symm_apply_apply]
  have hres (g : N) : γ g=ClassicalOrthogonal.FourPlusMatrix.Binary.action (f' g) := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := E.surjective v
    rw [←hE]
    change ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates (e (σ g w))=_
    rw [he,OrthogonalEight.binaryCoordinates_equivariant]
    rfl
  have him : N.map γ.asGroupHom = actionImage ClassicalOrthogonal.FourPlusMatrix.Binary.action := by
    ext z
    constructor
    · rintro ⟨g,hg,rfl⟩
      exact ⟨f' ⟨g,hg⟩,Units.ext (hres ⟨g,hg⟩).symm⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨g,rfl⟩ := f'.surjective g
      exact ⟨g,g.property,Units.ext (hres g)⟩
  have hn (g : D) : γ.asGroupHom g ∈ linearNormalizer ClassicalOrthogonal.FourPlusMatrix.Binary.action := by
    change γ.asGroupHom g ∈ normalizer (actionImage ClassicalOrthogonal.FourPlusMatrix.Binary.action : Set _)
    rw [←him]
    exact N.le_normalizer_map γ.asGroupHom (mem_map_of_mem _
      (show g ∈ normalizer (N : Set D) from le_normalizer_of_normal (mem_top g)))
  let j := γ.asGroupHom.codRestrict _ hn
  let A' := (A.subgroupOf N).map f'.toMonoidHom
  let S' := S.mapSurjective (f := f'.toMonoidHom) f'.surjective
  have hSA' : (S' : Subgroup _) ≤ A' := by
    apply map_mono
    intro x hx
    exact hSA (mem_map_of_mem _ hx)
  let aN : N := ⟨a,hAN ha⟩
  have ha' : f' aN ∈ A' := mem_map_of_mem _ ha
  have ha3' : orderOf (f' aN)=3 :=
    (f'.orderOf_eq aN).trans ((N.orderOf_coe aN).symm.trans ha3)
  have hj2 : (j t)^2=1 := by rw [←map_pow,ht2,map_one]
  have hjr : NaturalTensor.operatorFixedCodim (j t).val.val=2 := by
    exact (NaturalTensor.operatorFixedCodim_eq_of_equiv (σ t) (γ t) E (hE t)).symm.trans hr
  let dN : N := ⟨t*a*t⁻¹*a⁻¹,(map_subtype_le _ hdisp)⟩
  have hdS : dN ∈ S := by
    obtain ⟨v,hv,hve⟩ := hdisp
    exact (show v=dN from Subtype.ext hve) ▸ hv
  have hconj : ClassicalOrthogonal.FourPlusMatrix.Binary.action
      (ClassicalOrthogonal.FourPlusMatrix.Binary.normalizerConjugation (j t) (f' aN)) =
        γ t * γ a * γ t⁻¹ := by
    apply LinearMap.ext
    intro v
    have hh := ClassicalOrthogonal.FourPlusMatrix.Binary.normalizerConjugation_action
      (j t) (f' aN) (γ t⁻¹ v)
    have hcan : γ t (γ t⁻¹ v)=v := by
      rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one]
      rfl
    change ClassicalOrthogonal.FourPlusMatrix.Binary.action
      (ClassicalOrthogonal.FourPlusMatrix.Binary.normalizerConjugation (j t) (f' aN))
        (γ t (γ t⁻¹ v)) = γ t
          (ClassicalOrthogonal.FourPlusMatrix.Binary.action (f' aN) (γ t⁻¹ v)) at hh
    rw [hcan,←hres aN] at hh
    exact hh
  have hdEq : ClassicalOrthogonal.FourPlusMatrix.Binary.normalizerConjugation (j t)
      (f' aN)*(f' aN)⁻¹=f' dN := by
    apply ClassicalOrthogonal.FourPlusMatrix.Binary.action_injective
    rw [map_mul,hconj,←map_inv f',←hres aN⁻¹,←hres dN]
    change γ t*γ a*γ t⁻¹*γ a⁻¹=γ (t*a*t⁻¹*a⁻¹)
    rw [map_mul,map_mul,map_mul]
  have hd' : ClassicalOrthogonal.FourPlusMatrix.Binary.normalizerConjugation (j t)
      (f' aN)*(f' aN)⁻¹ ∈ S' := by
    rw [hdEq]
    exact mem_map_of_mem _ hdS
  obtain ⟨b,hb,hb3,hfix⟩ := ClassicalOrthogonal.FourPlusMatrix.Binary.exists_cubic_fixing_rank_two_displacement
    A' S' hSA' (j t) hj2 hjr (f' aN) ha' ha3' hd'
  obtain ⟨bN,hbN,rfl⟩ := hb
  refine ⟨bN,hbN,?_,?_⟩
  · exact (N.orderOf_coe bN).trans ((f'.orderOf_eq bN).symm.trans hb3)
  · intro z hz
    apply E.injective
    rw [hE,hres]
    apply hfix
    obtain ⟨w,hw⟩ := hz
    refine ⟨E w,?_⟩
    change γ t (E w)-E w=E z
    rw [←hE,←map_sub]
    exact congrArg E hw

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

private theorem critical_fixed_cubic_of_orthogonal
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (σ : Representation (ZMod 2) (HStar F.H) W) (hf : Function.Injective σ)
    (N : Subgroup (HStar F.H)) [N.Normal] (hm : HasOrthogonalFourOrbit σ N)
    (hLN : star F (F.Li L 1) ≤ N)
    (S : Sylow 2 N) (hS : (S : Subgroup N).map N.subtype = star F ((F.Li L 1).pCoreIn 2))
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (hR : c.Uα ≤ F.Ri L 1) (ha : Nat.card (star F c.Uα) = 2) :
    ∃ x ∈ star F (F.Li L 1), orderOf x=3 ∧
      ∀ z ∈ s.imageSpace c.Zα, σ x z=z := by
  let : Finite W := Finite.of_surjective (fun v : F.U => (s.coordinates v).toAdd)
    (Multiplicative.toAdd.surjective.comp s.onto)
  have hkernel : (σ.comp (starMap F)).ker = pCore 2 F.H := by
    ext x
    change σ (starMap F x) = 1 ↔ x ∈ pCore 2 F.H
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff _).mp (hf (hx.trans σ.map_one.symm))
    · intro hx
      have he : starMap F x = 1 := (QuotientGroup.eq_one_iff _).mpr hx
      rw [he,map_one]
  obtain ⟨f,e,he⟩ := hm
  have hno (x : F.H) : fixedCodim (σ.comp (starMap F)) (zpowers x) ≠ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact OrthogonalEight.equivariant_extension_no_transvection
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W).toMonoidHom.comp σ.asGroupHom)
      N f e he (starMap F x)
  have hCZ : c.Zα ≤ ⁅F.U,c.Uα⁆ := by
    rw [←critical_intersection_commutator_of_no_transvections h hab structural hkernel hno s c hs ha]
    exact commutator_mono inf_le_left le_rfl
  let A := star F c.Uα
  obtain ⟨t,ht,_htuniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp ha
  have ht2 : (t : HStar F.H)^2 = 1 := by
    have hh := pow_card_eq_one' (x := t)
    change t^Nat.card A = 1 at hh
    rw [show Nat.card A = 2 from ha] at hh
    exact congrArg Subtype.val hh
  have htgen : zpowers (t : HStar F.H) = A := by
    have hh := congrArg (Subgroup.map A.subtype) (zpowers_eq_top_of_prime_card ha ht)
    rw [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hAH : c.Uα ≤ F.H := (critical_le_Q h structural c).trans (Q_le_H F)
  have hsr : s.imageSpace ⁅F.U,c.Uα⁆ = (σ t - LinearMap.id).range := by
    rw [commutator_comm,s.imageSpace_commutator c.Uα F.U hAH le_rfl,s.imageSpace_self,
      subspaceCommutator_comp_map]
    change subspaceCommutator σ ⊤ A = _
    calc
      subspaceCommutator σ ⊤ A = subspaceCommutator σ ⊤ (zpowers (t : HStar F.H)) :=
        congrArg (subspaceCommutator σ ⊤) htgen.symm
      _ = _ := CyclicFixedRank.commutator_eq_range σ t
  have hr : NaturalTensor.operatorFixedCodim (σ t)=2 := by
    change Module.finrank (ZMod 2) (σ t-LinearMap.id).range=2
    rw [←hsr]
    exact critical_commutator_image_rank_of_no_transvections h hab structural hkernel hno s c hs ha
  have hc : 3 ∣ Nat.card (F.Li L 1) := by
    simpa only [pointResidual_core_quotient_card (F := F) h structural] using
      (Subgroup.card_quotient_dvd_card (pCore 2 (F.Li L 1)))
  obtain ⟨l,hl3⟩ := exists_prime_orderOf_dvd_card' (G := F.Li L 1) 3 hc
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  let lH : F.H := ⟨l,hLH l.property⟩
  have hlH3 : orderOf lH=3 := (F.H.orderOf_coe lH).symm.trans
    ((F.Li L 1).orderOf_coe l |>.trans hl3)
  have hk : IsPGroup 2 (starMap F).ker := by
    rw [starMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hlstar3 : orderOf (starMap F lH)=3 :=
    ((starMap F).orderOf_map_eq_of_coprime_of_isPGroup_ker hk lH
      (by rw [hlH3]; decide)).trans hlH3
  let J := F.Li L 1 ⊔ (T : Subgroup G)
  have hJL : J ≤ normalizer (F.Li L 1 : Set G) :=
    sup_le (F.Li L 1).le_normalizer (T_normalizes_L₁ h structural)
  have hJR : J ≤ normalizer (F.Ri L 1 : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hcomm : ⁅F.Ri L 1,F.Li L 1⁆ ≤ (F.Li L 1).pCoreIn 2 := by
    apply le_trans _ (inf_pCoreIn_le_of_le 2 (show F.Li L 1 ≤ J from le_sup_left))
    exact le_inf
      (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 J).trans hJL))
      (le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hJR))
  obtain ⟨u,hu,huEq⟩ := t.property
  have hdisp : (t : HStar F.H)*starMap F lH*(t : HStar F.H)⁻¹*(starMap F lH)⁻¹ ∈
      (S : Subgroup N).map N.subtype := by
    rw [hS,←huEq]
    have hh : (⁅u,lH⁆ : F.H) ∈ ((F.Li L 1).pCoreIn 2).subgroupOf F.H :=
      hcomm (commutator_mem_commutator (hR hu) l.property)
    refine ⟨⁅u,lH⁆,hh,?_⟩
    simp only [commutatorElement_def,map_mul,map_inv]
  obtain ⟨x,hx,hx3,hfix⟩ := orthogonal_exchange_cubic_fixer σ N ⟨f,e,he⟩
    (star F (F.Li L 1)) hLN S (by rw [hS]; exact map_mono (subgroupOf_mono F.H (pCoreIn_le 2 _)))
    t ht2 hr (starMap F lH) (mem_map_of_mem _ l.property) hlstar3 hdisp
  refine ⟨x,hx,hx3,?_⟩
  intro z hz
  apply hfix
  rw [←hsr]
  exact s.imageSpace_mono hCZ hz

/-- The original point quotient, using only structure at the same G,T. -/
theorem pointResidual_core_quotient_card_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    Nat.card ((F.Li L 1) ⧸ pCore 2 (F.Li L 1)) = 3 := by
  let B : Subgroup G := F.Li L 1 ⊔ (T : Subgroup G)
  obtain ⟨f,hf,hk⟩ := exists_point_permutation_action_at (F := F) h structural
  let E : pResidual 2 B ≃* F.Li L 1 :=
    (equivMapOfInjective (pResidual 2 B) (B).subtype (B).subtype_injective).trans
      (MulEquiv.subgroupCongr (residual_group_at h structural))
  let Q := QuotientGroup.congr _ _ E (pCore_map_iso 2 E)
  rw [← Nat.card_congr Q.toEquiv,
    Nat.card_congr (f.pResidualCoreQuotientEquiv hf hk).toEquiv,
    Equiv.Perm.twoResidual_eq_alternating]
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_fin]
    rfl
  have hthree : IsPGroup 3 (alternatingGroup (Fin 3)) :=
    IsPGroup.of_card (n := 1) (by simpa using hc)
  have hcore : pCore 2 (alternatingGroup (Fin 3)) = ⊥ := by
    exact le_bot_iff.mp ((le_inf le_rfl le_top).trans
      (pCore_isPGroup.disjoint_of_coprime (hthree.to_subgroup ⊤)
        (by decide : Nat.Coprime 2 3)).le_bot)
  rw [hcore, Nat.card_congr QuotientGroup.quotientBot.toEquiv, hc]

/-- The reciprocal-plane lift and supplement need only structure at the same G,T. -/
theorem point_plane_residual_core_supplement_of_cubic_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
    (P : Subgroup G) (hPU : P ≤ F.U) (hZP : F.Vi 1 ≤ P)
    (hfour : Nat.card P = 4)
    (w : W) (hw : w ∈ s.imageSpace P) (hw0 : w ≠ 0)
    (x : HStar F.H) (hx : x ∈ star F (F.Li L 1)) (hxw : σ x w = w)
    (hx3 : orderOf x = 3) :
    let R := (pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
      (F.Li L 1 ⊓ centralizer (P : Set G)).subtype
    R ⊔ (F.Li L 1).pCoreIn 2 = F.Li L 1 ∧
      ∃ l : F.H, (l : G) ∈ R ∧ orderOf (l : G) = 3 ∧ starMap F l = x ∧
        zpowers (l : G) ⊔ (F.Li L 1).pCoreIn 2 = F.Li L 1 := by
  dsimp only
  obtain ⟨l,hl,hl3,hlx⟩ := point_plane_cubic_lift h hab σ s P hPU hZP hfour w hw hw0 x hx hxw hx3
  let A := F.Li L 1
  let R := (pResidual 2 (A ⊓ centralizer (P : Set G) : Subgroup G)).map
    (A ⊓ centralizer (P : Set G)).subtype
  have hRA : R ≤ A := (map_subtype_le _).trans inf_le_left
  let a : A := ⟨l,hRA hl⟩
  have ha3 : orderOf a = 3 := (A.orderOf_coe a).symm.trans hl3
  let q := QuotientGroup.mk' (pCore 2 A)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hq3 : orderOf (q a) = 3 := (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk a
    (by rw [ha3]; decide)).trans ha3
  have hqn : q a ≠ 1 := by intro he; rw [he,orderOf_one] at hq3; omega
  have hgen : zpowers a ⊔ pCore 2 A = ⊤ := by
    have hh := zpowers_eq_top_of_prime_card (pointResidual_core_quotient_card_at h structural) hqn
    rw [←MonoidHom.map_zpowers] at hh
    have he := congrArg (Subgroup.comap q) hh
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using he
  have hgenG : zpowers (l : G) ⊔ A.pCoreIn 2 = A := by
    have he := congrArg (Subgroup.map A.subtype) hgen
    simpa only [Subgroup.map_sup,MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,
      pCoreIn,a,Subgroup.subtype_apply] using he
  refine ⟨le_antisymm (sup_le hRA (pCoreIn_le 2 A)) ?_,l,hl,hl3,hlx,hgenG⟩
  exact hgenG.ge.trans (sup_le_sup (zpowers_le.mpr hl) le_rfl)

/-- The guarded structural producer is applied only in the actual many-overgroup branch. -/
theorem point_plane_residual_core_supplement_of_cubic_of_many
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (HStar F.H) W)
    (s : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))
    (P : Subgroup G) (hPU : P ≤ F.U) (hZP : F.Vi 1 ≤ P)
    (hfour : Nat.card P = 4)
    (w : W) (hw : w ∈ s.imageSpace P) (hw0 : w ≠ 0)
    (x : HStar F.H) (hx : x ∈ star F (F.Li L 1)) (hxw : σ x w = w)
    (hx3 : orderOf x = 3) :
    let R := (pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
      (F.Li L 1 ⊓ centralizer (P : Set G)).subtype
    R ⊔ (F.Li L 1).pCoreIn 2 = F.Li L 1 ∧
      ∃ l : F.H, (l : G) ∈ R ∧ orderOf (l : G) = 3 ∧ starMap F l = x ∧
        zpowers (l : G) ⊔ (F.Li L 1).pCoreIn 2 = F.Li L 1 :=
  point_plane_residual_core_supplement_of_cubic_at h hab (structural hmany)
    σ s P hPU hZP hfour w hw hw0 x hx hxw hx3

/-- The original exchanged branch supplies the cubic and full point-residual supplement
for the specified reciprocal plane. All model premises are discharged. -/
theorem local_nonnormal_component_plane_residual_supplement
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal)
    (c : CriticalPath (L := L) F) (hs : c.RankSelection)
    (hR : c.Uα ≤ F.Ri L 1) (ha : Nat.card (star F c.Uα) = 2)
    (hPU : F.Vi 1 ⊔ c.Zα ≤ F.U) (hfour : Nat.card (F.Vi 1 ⊔ c.Zα : Subgroup G)=4) :
    let P := F.Vi 1 ⊔ c.Zα
    let R := (pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
      (F.Li L 1 ⊓ centralizer (P : Set G)).subtype
    R ⊔ (F.Li L 1).pCoreIn 2=F.Li L 1 ∧
      ∃ l : F.H, (l:G) ∈ R ∧ orderOf (l:G)=3 ∧
        zpowers (l:G) ⊔ (F.Li L 1).pCoreIn 2=F.Li L 1 := by
  obtain ⟨hU,a,hm,_⟩ := local_nonnormal_component_whole_orthogonal d h hab structural
    previous faithful earlier I K hI hKI hK hnormal
  let := hU
  obtain ⟨t,ht,htn,k,hk,hfin,hchar,b,he1,he2,horbit,hS⟩ :=
    local_nonnormal_component_exchanged_actor d h hab structural previous faithful earlier
      I K hI hKI hK hnormal
  let N := Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G))
  let : N.Normal := by
    dsimp only [N]
    rw [←horbit]
    exact b.orbit_normal
  obtain ⟨S,hcore⟩ := local_nonnormal_component_point_core_sylow d h hab structural
    previous faithful earlier I K hI hKI hK hnormal
  let s₀ := ModuleBound.OriginalF916.conjugationSection a
    (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))
  let s : BinaryConjugationSection F.H F.U (F.Vi 1)
      (a.representation.comp (starMap F)) := {
    section_le := s₀.le
    kernel_le := s₀.line_le
    normalized := s₀.normalizes
    coordinates := s₀.quotient
    onto := s₀.surjective
    kernel_eq := s₀.kernel
    equivariant := fun x v => (s₀.conjugates x v).symm }
  have hLN : star F (F.Li L 1) ≤ N := map_mono (subgroupOf_mono F.H
    (local_nonnormal_component_point_le_orbit d h hab structural previous faithful earlier
      I K hI hKI hK hnormal))
  obtain ⟨x,hx,hx3,hfix⟩ := critical_fixed_cubic_of_orthogonal h hab structural
    a.representation a.faithful N hm hLN S hcore s c hs hR ha
  let P := F.Vi 1 ⊔ c.Zα
  have hpc : Nat.card (s.imageSpace P)=2 := by
    rw [s.imageSpace_card_eq_relIndex P hPU]
    have hh := relIndex_mul_card_of_le (show F.Vi 1 ≤ P from le_sup_left)
    have hp : Nat.card (F.Vi 1)=2 := by simpa using F.card 1 (by decide)
    rw [hp,hfour] at hh
    omega
  obtain ⟨z,hz0,_⟩ := (Nat.card_eq_two_iff' (0 : s.imageSpace P)).mp hpc
  have hz0' : (z : Additive (F.U ⧸ (F.Vi 1).subgroupOf F.U)) ≠ 0 := fun he => hz0 (Subtype.ext he)
  have hPZ : s.imageSpace P=s.imageSpace c.Zα := by
    dsimp only [P]
    rw [sup_comm,s.imageSpace_sup_kernel c.Zα (le_sup_right.trans hPU)]
  obtain ⟨hgen,l,hl,hl3,_,hlgen⟩ := point_plane_residual_core_supplement_of_cubic_at h hab
    (structural.at T) a.representation s P hPU le_sup_left hfour z z.property hz0' x hx
    (hfix z (hPZ ▸ z.property)) hx3
  exact ⟨hgen,l,hl,hl3,hlgen⟩

/-- The same constructed Y and I₀ retain their reduced point span and non-subnormal
image, now with an actual cubic supplement in the plane-centralizer residual. -/
theorem local_nonnormal_component_weakClosure_cubic
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    ∃ c : CriticalPath (L := L) F, c.RankSelection ∧ c.Uα ≤ F.Ri L 1 ∧
      Nat.card (star F c.Uα) = 2 ∧
      let P := F.Vi 1 ⊔ c.Zα
      let J := F.Li L 1 ⊔ (T : Subgroup G)
      let R := F.H.pCoreIn 2 ⊔ conjugateSpanBy c.Uα J
      let Y := (F.H.pCoreIn 2 ⊔ c.Qα) ⊔ R
      let I₀ := J ⊔ Y
      let W₀ := ChapterE.indexedWeakClosure V R 0
      IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧ P ≤ F.U ⊓ c.Uα ∧
      R ≤ (T : Subgroup G) ∧ J ≤ normalizer (R : Set G) ∧
      R ≤ normalizer (P : Set G) ∧ Chapter1.IsSylowIn 2 R Y ∧
      Y ⊓ centralizer (P : Set G) = Y.pCoreIn 2 ∧
      Nonempty (Y ⧸ pCore 2 Y ≃* Equiv.Perm (Fin 3)) ∧
      V ≤ W₀ ∧ W₀ ≤ R ∧ I₀ ≤ normalizer (W₀ : Set G) ∧
      IsTwoLocal (normalizer (W₀ : Set G)) ∧ normalizer (W₀ : Set G) ≠ ⊤ ∧
      I₀ = J ⊔ c.Qα ∧ HasCharacteristicTwo I₀ ∧
      IsSQTK KnownSimple.IsKnownSimple I₀ ∧
      IsPReduced 2 ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀) ∧
      P ≤ conjugateSpanBy (F.Vi 1) I₀ ∧ conjugateSpanBy (F.Vi 1) I₀ ≤ W₀ ∧
      letI : ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀).Normal :=
        normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
      let q := QuotientGroup.mk'
        (centralizer ((conjugateSpanBy (F.Vi 1) I₀).subgroupOf I₀ : Set I₀))
      ¬ (((F.Li L 1).subgroupOf I₀).map q).IsSubnormal ∧
        ((F.Li L 1).subgroupOf I₀).map q ≠ ⊥ ∧
        ¬ F.H.pCoreIn 2 ⊔ c.Qα ≤ normalizer (F.Li L 1 : Set G) ∧
        Y ≤ normalizer ((pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
          (F.Li L 1 ⊓ centralizer (P : Set G)).subtype : Set G) ∧
        let RY := (pResidual 2 (F.Li L 1 ⊓ centralizer (P : Set G) : Subgroup G)).map
          (F.Li L 1 ⊓ centralizer (P : Set G)).subtype
        RY ⊔ (F.Li L 1).pCoreIn 2=F.Li L 1 ∧
          ∃ l : F.H, (l:G) ∈ RY ∧ orderOf (l:G)=3 ∧
            zpowers (l:G) ⊔ (F.Li L 1).pCoreIn 2=F.Li L 1 := by
  obtain ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hsub,hne,hYn,hres⟩ :=
    local_nonnormal_component_weakClosure_residual d h hab structural previous
      faithful earlier I K hI hKI hK hnormal
  have hcubic := local_nonnormal_component_plane_residual_supplement d h hab structural previous
    faithful earlier I K hI hKI hK hnormal c hs hR ha (hplane.trans inf_le_left) hfour
  exact ⟨c,hs,hR,ha,hE,hfour,hplane,hRT,hJR,hRN,hSylow,hcore,he,hVW,hWR,hIW,
    hlocal,hproper,hIeq,hcharI,hsqtk,hred,hPVI,hVIW,hsub,hne,hYn,hres,hcubic⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
