module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.ActionAlternatives

/-!
# Nonsolvable shifted-center exclusions at G,T

The marked type-a2 action and the original faithful-family exclusion
eliminate S6, the natural G2(2) row and the remaining alternating-eight
rows. Each deduction retains the original shifted actor and module.
Source: Aschbacher--Smith 14.3.25,30--31, pp.1001--1003.

The universal APIs are preserved. The proofs below specialize their
source arguments without promoting a local earlier implication to a
universal statement. This extension remains above Section04.
-/

public noncomputable section

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SymmetricSix.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
omit [IsElementaryAbelian 2 F.Uhat] in
theorem source_contrary_simple_normal_le_center_centralizer_at
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥)
    (K : Subgroup F.TerminalHdot) [K.Normal] [IsSimpleGroup K]
    (hKa : ¬ IsMulCommutative K) (hKc : centralizer (K : Set F.TerminalHdot) = ⊥) :
    K ≤ F.terminalDot (centralizer (F.ZU : Set G)) := by
  obtain ⟨g,l,e,hgL,hgP,hgH,hlL,hl,hspace,hgen,he,heI,heT,heU,heV,
    haH,ha,hfaith,_,hNC,_⟩ :=
    source_shifted_amalgam_faithful_at d earlier hq chosen structural alternatives F hne hseed hI
  let a := l⁻¹ * e * l
  let N := conjugateSpanBy (zpowers a) F.H
  have hNH : N ≤ F.H := conjugateSpanBy_le_self (zpowers_le.mpr haH)
  let : (N.subgroupOf F.H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNH).mpr (le_normalizer_conjugateSpanBy _ _)
  let : (F.terminalDot N).Normal := Normal.map inferInstance
    (QuotientGroup.mk' F.terminalHatAction.ker) (QuotientGroup.mk'_surjective _)
  have hN : F.terminalDot N ≠ ⊥ := by
    intro hbot
    have hmem : QuotientGroup.mk' F.terminalHatAction.ker ⟨a,haH⟩ ∈ F.terminalDot N :=
      mem_map_of_mem _ (le_conjugateSpanBy _ _ (mem_zpowers a))
    have hh := (QuotientGroup.eq_one_iff (⟨a,haH⟩ : F.H)).mp (mem_bot.mp (hbot ▸ hmem))
    exact hfaith hh
  exact (simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot K hKa hKc _ hN).trans
    (map_mono (comap_mono hNC))
theorem source_no_alternating_six_image_of_contrary_center_at
    (hseed : centralLTSeed F L = ⊥) (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥)
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 4)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hline : hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v})
    (j : F.TerminalHdot →* Equiv.Perm (Fin 6)) (hj : Function.Injective j)
    (c : B.IsometryEquiv polarForm)
    (he : ∀ a w, c (F.terminalRepresentation a w) = polarAction (j a) (c w)) :
    ¬ alternatingGroup (Fin 6) ≤ j.range := by
  intro hA
  let K := (alternatingGroup (Fin 6)).comap j
  have hmap : K.map j = alternatingGroup (Fin 6) := by
    change ((alternatingGroup (Fin 6)).comap j).map j = _
    exact map_comap_eq_self hA
  let eK := (K.equivMapOfInjective j hj).trans (MulEquiv.subgroupCongr hmap)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup K := eK.isSimpleGroup
  let : K.Normal := inferInstanceAs (((alternatingGroup (Fin 6)).comap j).Normal)
  have hKa : ¬ IsMulCommutative K := by
    intro hab
    let := hab
    let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6))
      (Group.isSolvable_of_surjective (f := eK.toMonoidHom) eK.surjective)
  have hKc : centralizer (K : Set F.TerminalHdot) = ⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply hj
    rw [map_one]
    apply mem_bot.mp
    rw [← _root_.GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 6 (by decide)]
    intro a ha
    obtain ⟨k,hk,rfl⟩ := (show a ∈ K.map j from hmap.symm ▸ ha)
    exact (map_mul j k x).symm.trans ((congrArg j (hx k hk)).trans (map_mul j x k))
  have hKC := source_contrary_simple_normal_le_center_centralizer_at d earlier hq chosen structural alternatives
    F hne hseed hI K hKa hKc
  obtain ⟨_,_,hdim,_⟩ := source_four_marked_geometry_at d earlier hq chosen structural alternatives
    F hne hd g hgP hgH
  let W := (hatSpace F (F.E g)).map c.toLinearEquiv.toLinearMap
  have hWdim : finrank (ZMod 2) W=2 := (c.toLinearEquiv.finrank_map_eq _).trans hdim
  have hiso : ∀ x∈W, ∀ y∈W, polarForm x y=0 := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    change polarForm (c x) (c y)=0
    rw [c.map_app]
    exact hyp.isotropic x hx y hy
  have hv : c v ≠ 0 := fun hz => hyp.point_ne_zero (c.injective (hz.trans c.map_zero.symm))
  obtain ⟨a,ha3,hav,w,hw,haw⟩ := PointCubicPlane.exists_matrix_cubic (c v) hv W hWdim hiso
    ⟨v,hyp.point_mem,rfl⟩
  obtain ⟨b,hb⟩ := hA a.property
  have hbK : b ∈ K := by change j b ∈ alternatingGroup (Fin 6); rw [hb]; exact a.property
  have hb3 : b^3=1 := by
    apply hj
    rw [map_pow,hb,map_one]
    exact congrArg Subtype.val ha3
  have hbv : b ∈ ChapterG.Section10.pointCentralizer F.terminalRepresentation v := by
    apply c.injective
    change c (F.terminalRepresentation b v)=c v
    rw [he,hb]
    exact hav
  obtain ⟨x,hx,rfl⟩ := hw
  apply haw
  change polarAction a.val (c x) ∈ W
  rw [←hb,←he]
  exact ⟨F.terminalRepresentation b x,
    source_point_cube_preserves_intersection_at d earlier hq chosen structural alternatives F hne
      v hline g hgP b hbv (hKC hbK) hb3 x hx,rfl⟩
omit [IsElementaryAbelian 2 F.Uhat] in
theorem source_centerless_of_symmetricSix_model_at
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 6))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  by_contra hI
  have hseed := source_seed_exclusion_of_six_model_at d earlier hq chosen structural alternatives
    classification F hne hc (.inr model)
  obtain ⟨g,_,hgP,hgH⟩ := CaseOneLarge.exists_source_conjugator_at d earlier hq chosen structural F
  obtain ⟨heU,heX,B,v,hyp,hline,_⟩ := CaseOneLarge.source_terminal_marked_hypothesis_at F
    d earlier hq chosen structural alternatives hne g hgP hgH
  let := heU
  let := heX
  have hd : finrank (ZMod 2) (Additive F.Uhat)=4 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive F.Uhat)
    change Nat.card F.Uhat = _ at hh
    rw [hc,Nat.card_zmod] at hh
    exact (Nat.pow_right_injective (a := 2) (by decide)
      (show 2^4=2^finrank (ZMod 2) (Additive F.Uhat) from hh)).symm
  obtain ⟨c,j,hj,he⟩ := exists_binarySymplecticFour_embedding F.terminalRepresentation
    hyp.faithful hd B hyp.alternating hyp.nondegenerate hyp.preserves
  have hform : Matrix.PSp4Three.form (n := 2) (F := ZMod 2)=polarForm := by
    unfold Matrix.PSp4Three.form polarForm
    congr 1
    ext i k
    exact ZMod.neg_eq_self_mod_two _
  let c' : B.IsometryEquiv polarForm := { c.toLinearEquiv with
    map_app' := fun x y => by rw [←hform]; exact c.map_app y x }
  let j' := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.toMonoidHom.comp j
  have hj' : Function.Injective j' :=
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.injective.comp hj
  have he' : ∀ a w, c' (F.terminalRepresentation a w) = polarAction (j' a) (c' w) := by
    intro a w
    have heq : polarRepresentation (j' a)=j a := by
      rw [← Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv_apply]
      exact Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.apply_symm_apply (j a)
    change c (F.terminalRepresentation a w) = polarAction (j' a) (c w)
    rw [← polarRepresentation_apply,heq]
    exact he a w
  have hnot := source_no_alternating_six_image_of_contrary_center_at d earlier hq chosen structural alternatives
    F hne hseed hI hd g hgP hgH B v hyp hline.symm j' hj' c' he'
  obtain ⟨e⟩ := model
  have hsur : Function.Surjective j' := by
    have h := Finite.surjective_of_injective (hj'.comp e.symm.injective)
    intro a
    obtain ⟨b,hb⟩ := h a
    exact ⟨e.symm b,hb⟩
  apply hnot
  rw [MonoidHom.range_eq_top.mpr hsur]
  exact le_top
omit [IsElementaryAbelian 2 F.Uhat] in
theorem source_centerless_of_four_nonsolvable_model_at
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1) (hc : Nat.card F.Uhat = 16)
    (model : Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 5)) ∨
      Nonempty (Hdot F F.uhatAction ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (Hdot F F.uhatAction ≃* Equiv.Perm (Fin 6))) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  rcases model with h5 | h6 | hS
  · exact source_centerless_of_symmetricFive_model_at d earlier hq chosen structural alternatives
      classification F hne hZ hc h5
  · exact source_centerless_of_alternatingSix_model_at d earlier hq chosen structural alternatives
      classification F hne hc h6
  · exact source_centerless_of_symmetricSix_model_at d earlier hq chosen structural alternatives
      F hne classification hc hS
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/G2.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
theorem source_contrary_g2_cubic_centralizes_center_at
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥)
    (e : F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2))
    (x : F.H) (hx : orderOf x = 3) : (x:G) ∈ centralizer (F.ZU : Set G) := by
  let K := commutator F.TerminalHdot
  have hmap : K.map e.toMonoidHom=commutator (Atlas.G2.Model (ZMod 2)) := by
    change (commutator F.TerminalHdot).map e.toMonoidHom = _
    rw [map_commutator_eq,MonoidHom.range_eq_top.mpr e.surjective,commutator_def]
  let eK := (e.subgroupMap K).trans (MulEquiv.subgroupCongr hmap)
  let : IsSimpleGroup (commutator (Atlas.G2.Model (ZMod 2))) := Atlas.G2.isSimple_commutator_binary
  let : IsSimpleGroup K := eK.isSimpleGroup
  have hKa : ¬ IsMulCommutative K := by
    intro hcomm
    let := hcomm
    have hp : (Nat.card K).Prime := IsSimpleGroup.prime_card
    rw [Nat.card_congr eK.toEquiv,Atlas.G2.LieAutomorphismExtensions.card_binaryDerived] at hp
    norm_num at hp
  have hKc : centralizer (K : Set F.TerminalHdot)=⊥ := by
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    apply e.injective
    rw [map_one]
    apply Atlas.G2.LieAutomorphismExtensions.binaryConjugation_injective
    rw [map_one]
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    obtain ⟨k,hk,hky⟩ := (show y.val∈K.map e.toMonoidHom from hmap.symm ▸ y.property)
    have hcomm := congrArg e (hx k hk)
    have hky' : e k=y.val := hky
    change e x*y.val*(e x)⁻¹=y.val
    have hh : e x*y.val=y.val*e x := by
      simpa only [map_mul,hky'] using hcomm.symm
    rw [hh,mul_inv_cancel_right]
  have hKC := source_contrary_simple_normal_le_center_centralizer_at d earlier hq chosen structural
    alternatives F hne hseed hI K hKa hKc
  let : Group.IsPerfect (commutator (Atlas.G2.Model (ZMod 2))) := by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := eK.symm.toMonoidHom) eK.symm.surjective
  have hKn : ¬ Group.IsSolvable K := Group.IsPerfect.not_isSolvable K
  let C := (centralizer (F.ZU : Set G)).subgroupOf F.H
  let : C.Normal := normal_subgroupOf_of_le_normalizer
    (F.H_normalizes_ZU.trans (normalizer_le_normalizer_centralizer F.ZU))
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  have hQ : pCore 2 F.H ≤ q.ker := by
    have hzero : (pCore 2 F.H).map q = ⊥ := by
      by_contra hnot
      let : ((pCore 2 F.H).map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
      have hle := simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot K hKa hKc
        ((pCore 2 F.H).map q) hnot
      let : Group.IsNilpotent K := (pCore_isPGroup.map q |>.to_le hle).isNilpotent
      exact hKn inferInstance
    exact (Subgroup.map_eq_bot_iff _).mp hzero
  have hz : center K = ⊥ := by
    rcases (inferInstance : (center K).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (hKa (center_eq_top_iff.mp hz)).elim
  apply CComponentPrimeRank.prime_actor_mem_of_normal_image q C K hKC
    (by rw [QuotientGroup.ker_mk']; exact
      source_center_centralizing_kernel_le_core_at d earlier hq chosen structural alternatives F hne)
    hQ (by rw [hz,card_bot]; simp) ?_ ?_ (by decide) ?_ x hx
  · rw [primeRank_congr 3 eK]
    exact Atlas.G2.EvenThreeRank.two_le_primeRank_derived
  · let := chosen.elementary
    let : IsElementaryAbelian 2 (F.Vi 1) := IsElementaryAbelian.of_le (F.le_seed 1)
    have hlocal : IsTwoLocal F.H := by
      refine ⟨F.Vi 1,?_,IsElementaryAbelian.isPGroup 2 (F.Vi 1),rfl⟩
      intro hz
      have hc := F.card 1 (by decide)
      rw [hz,card_bot] at hc
      norm_num at hc
    exact (d.qtke.twoLocal_sqtk hlocal).stronglyQuasithin 3 (by decide) (by decide)
  · exact Atlas.G2.binaryDerived_outer_isTwoGroup.of_equiv (MulAut.outerCongr eK).symm
omit structural alternatives hne in
theorem source_point_residual_cubic_generation_at :
    closure {x : G | x ∈ F.Li L 1 ∧ orderOf x = 3} = F.Li L 1 := by
  let := chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨D⟩ := F.naturalSeedMarking_of_ambient (by decide) L chosen.normalizes h.naturalMarking
  let q := QuotientGroup.mk' (pCore 2 (F.Li L 1))
  have hc : Nat.card (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) = 3 :=
    (Nat.card_congr D.quotientEquiv.toEquiv).trans BinaryLinear.SmallParabolicLevi.derived_two_card
  have hp : pResidual 2 (F.Li L 1) = ⊤ := (pResidual_eq_top_iff 2 _).mpr (by
    change IsPPerfect 2 ((pResidual 2 (L ⊓ F.Gi 1 : Subgroup G)).map (L ⊓ F.Gi 1).subtype)
    exact isPPerfect_embedded_pResidual 2 _)
  have hgen := cubic_closure_eq_twoResidual_of_cube_image q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    (fun a => by simpa only [hc] using pow_card_eq_one' (x := q a))
  rw [hp] at hgen
  have hm := congrArg (map (F.Li L 1).subtype) hgen
  rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,range_subtype] at hm
  convert hm using 2
  ext x
  constructor
  · rintro ⟨hx,h3⟩
    exact ⟨⟨x,hx⟩,((F.Li L 1).orderOf_coe ⟨x,hx⟩).symm.trans h3,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,((F.Li L 1).orderOf_coe y).trans hy⟩
theorem source_centerless_of_cubics_centralize_center_at
    (hseed : centralLTSeed F L = ⊥)
    (hfix : ∀ x : F.H, orderOf x = 3 → (x:G) ∈ centralizer (F.ZU : Set G)) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  by_contra hI
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨e,he,heI,heT,heU,_⟩ :=
    source_center_involution_at d earlier hq chosen structural alternatives F hne hI
  have hstab := source_involution_stabilizer_at d earlier hq chosen structural alternatives
    F hne hseed e he heI heT
  have hL1 : F.Li L 1 ≤ centralizer ({e} : Set G) := by
    rw [← source_point_residual_cubic_generation_at d earlier hq chosen F]
    apply (closure_le _).mpr
    intro x hx
    have hxc := hfix ⟨x,(F.Li_le L 1 hx.1).2⟩
      (((F.H.orderOf_coe ⟨x,(F.Li_le L 1 hx.1).2⟩)).symm.trans hx.2)
    exact mem_centralizer_singleton_iff.mpr (hxc e heU).symm
  have hP : F.P L ≤ centralizer ({e} : Set G) := hstab ▸ inf_le_right
  have hNP : L ⊓ F.Gi 2 ≤ F.P L := by
    intro x hx
    refine ⟨mem_sup_left hx.1,?_⟩
    apply mem_iInf.mpr
    intro i
    apply mem_iInf.mpr
    intro hi
    have hi2 : i=2 := by omega
    subst i
    exact hx.2
  have hgen := NormalGeometry.flag_generation_of_linear F h.naturalMarking.geometryAction
    h.residual 2 (NormalGeometry.flag_linear_generation F (by decide) 2 (by decide) (by decide))
  have hLC : L ≤ centralizer ({e} : Set G) := by
    rw [←hgen]
    exact conjugateSpanBy_le hL1 ((hNP.trans hP).trans (centralizer ({e} : Set G)).le_normalizer)
  have heSeed : e ∈ centralLTSeed F L := by
    refine ⟨?_,map_subtype_le (center F.U) heU⟩
    rw [centerIn_eq_inf_centralizer]
    refine ⟨mem_sup_right ((source_center_location_at d earlier hq chosen structural alternatives F hne).2.1 heI),?_⟩
    have hLT : L ⊔ (T:Subgroup G) ≤ centralizer ({e} : Set G) := by
      apply sup_le hLC
      intro t ht
      exact mem_centralizer_singleton_iff.mpr (omega_centralizes_sylow heT t ht)
    intro x hx
    exact mem_centralizer_singleton_iff.mp (hLT hx)
  have he1 : e=1 := by simpa [hseed] using heSeed
  simp [he1] at he
theorem source_centerless_of_g2_natural_at
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    [IsElementaryAbelian 2 F.Uhat]
    (model : ChapterG.Section11.CaseSix F.terminalRepresentation) :
    Chapter12.Section08.centerIn (F.I₂ L) = ⊥ := by
  by_contra hI
  have hseed := source_seed_exclusion_of_g2_natural_at d earlier hq chosen structural alternatives
    classification F hne model
  have hc := source_centerless_of_cubics_centralize_center_at d earlier hq chosen structural
    alternatives F hne hseed (source_contrary_g2_cubic_centralizes_center_at d earlier hq chosen
      structural alternatives F hne hseed hI model.2.choose)
  exact hI hc
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/AlternatingEight.lean. -/
section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterG.Section11
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne
theorem source_seed_exclusion_of_large_residual_at
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hR : IsQuasisimple (solvableResidual F.TerminalHdot))
    (hirr : IsIrreducible (F.terminalRepresentation.comp (solvableResidual F.TerminalHdot).subtype))
    (hlarge : 168 < Nat.card (solvableResidual F.TerminalHdot)) : centralLTSeed F L = ⊥ := by
  by_contra hz
  let := chosen.elementary
  obtain ⟨K,hn,hK,hm⟩ := source_lift_dotted_residual d chosen F hR
  let := hn
  let q := QuotientGroup.mk' F.uhatAction.ker
  let R := solvableResidual F.TerminalHdot
  change K.map q = R at hm
  let π : K →* R := (q.comp K.subtype).codRestrict R
    (fun k => show q k ∈ R from hm ▸ mem_map_of_mem q k.property)
  have hπ : Function.Surjective π := by
    intro r
    obtain ⟨k,hk,he⟩ := (show (r : F.TerminalHdot) ∈ K.map q from hm.symm ▸ r.property)
    exact ⟨⟨k,hk⟩,Subtype.ext he⟩
  have hi := (irreducible_comp_surjective_iff π hπ
    (F.terminalRepresentation.comp R.subtype)).mpr hirr
  have hρ : ((F.terminalRepresentation.comp R.subtype).comp π) =
      (elementaryRepresentation (p := 2) F.uhatAction).comp K.subtype := by
    ext k x
    rfl
  rw [hρ] at hi
  have hout := source_irreducible_actor_escapes_at d earlier hq chosen structural alternatives F hne K hi
  have hcoreH := F.pCore_le_uhatAction_ker_of_tilde_kernel (by decide)
    (source_action_kernel_at d earlier hq chosen structural alternatives F)
  have hcore : pCore 2 K ≤ π.ker := by
    have hp : (pCore 2 K).map K.subtype ≤ pCore 2 F.H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩
    intro k hk
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff _).mpr (hcoreH (hp (mem_map_of_mem K.subtype hk)))
  let β := QuotientGroup.lift (pCore 2 K) π hcore
  have hsur : Function.Surjective β := by
    intro z
    obtain ⟨k,rfl⟩ := hπ z
    exact ⟨QuotientGroup.mk' (pCore 2 K) k,rfl⟩
  have hbound := Nat.card_le_card_of_surjective β hsur
  let i := K.equivMapOfInjective F.H.subtype F.H.subtype_injective
  let iq := QuotientGroup.congr (pCore 2 K) (pCore 2 (K.map F.H.subtype)) i (pCore_map_iso 2 i)
  obtain ⟨hc,_,_⟩ := source_faithful_component_classification_at d earlier hq chosen structural
    alternatives classification F hz hK hout
  rcases hc with hA | hP
  · obtain ⟨e⟩ := hA
    have hc : Nat.card (K ⧸ pCore 2 K) = 60 := by
      rw [Nat.card_congr (iq.trans e).toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    change Nat.card R ≤ Nat.card (K ⧸ pCore 2 K) at hbound
    change 168 < Nat.card R at hlarge
    omega
  · obtain ⟨e⟩ := hP
    have hc : Nat.card (K ⧸ pCore 2 K) = 168 :=
      (Nat.card_congr (iq.trans e).toEquiv).trans Matrix.PSL3Two.card_PSL
    change Nat.card R ≤ Nat.card (K ⧸ pCore 2 K) at hbound
    change 168 < Nat.card R at hlarge
    omega
theorem source_seed_exclusion_of_alternatingEight_at
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (J : Subgroup F.TerminalHdot) [J.Normal]
    (e : J ≃* alternatingGroup (Fin 8))
    (c : Additive F.Uhat ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hc : ∀ (j : J) w, c (F.terminalRepresentation j w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e j) (c w)) :
    centralLTSeed F L = ⊥ := by
  have hJc := BinaryPermutation.EightCommutant.centralizer_eq_bot_of_coordinates
    F.terminalRepresentation F.terminalRepresentation_injective J e c hc
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 8)) := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent (MulAut.Outer J) :=
    (alternatingGroup.EightComponent.outer_two.of_equiv (MulAut.outerCongr e).symm).isNilpotent
  let : Group.IsSolvable (F.TerminalHdot ⧸ J) := quotient_isSolvable_of_centralizer_eq_bot J hJc
  have hr : solvableResidual F.TerminalHdot = J :=
    le_antisymm (solvableResidual_le_of_solvable_quotient J) (le_solvableResidual_of_isPerfect J)
  let : IsQuasisimple (alternatingGroup (Fin 8)) :=
    ⟨((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hi : IsIrreducible (F.terminalRepresentation.comp J.subtype) := by
    let σ := (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)).comp e.toMonoidHom
    let E : RepEquiv (F.terminalRepresentation.comp J.subtype) σ := {
      toLinearEquiv := c
      isIntertwining' j := by apply LinearMap.ext; intro w; exact hc j w }
    exact E.irreducible_of_euqiv
      ((irreducible_comp_surjective_iff e.toMonoidHom e.surjective _).mpr
        (BinaryPermutation.alternatingNatural_isIrreducible (by simp)))
  apply source_seed_exclusion_of_large_residual_at d earlier hq chosen structural alternatives F hne classification
  · rw [hr]
    exact IsQuasisimple.of_mulEquiv e.symm
  · rwa [hr]
  · rw [hr,Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
theorem source_no_alternatingEight_natural_at
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (v : Additive F.Uhat) (hline : Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2))
    (J : Subgroup F.TerminalHdot) [J.Normal]
    (e : J ≃* alternatingGroup (Fin 8))
    (c : Additive F.Uhat ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8))
    (hc : ∀ (j : J) w, c (F.terminalRepresentation j w) =
      BinaryPermutation.alternatingNaturalRepresentation (Fin 8) (e j) (c w)) : False := by
  have hJc := BinaryPermutation.EightCommutant.centralizer_eq_bot_of_coordinates
    F.terminalRepresentation F.terminalRepresentation_injective J e c hc
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup J := e.isSimpleGroup
  have hJa : ¬ IsMulCommutative J := by
    intro hab
    let := hab
    have hp : (Nat.card J).Prime := IsSimpleGroup.prime_card
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hp
    norm_num [Nat.factorial] at hp
  have hJC : J ≤ F.terminalDot (centralizer (F.ZU : Set G)) := by
    by_cases hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥
    · exact source_simple_normal_le_center_centralizer_at d earlier hq chosen structural alternatives
        F hne hZ hI g hgP hgH J hJa hJc
    · exact source_contrary_simple_normal_le_center_centralizer_at d earlier hq chosen structural alternatives
        F hne (source_seed_exclusion_of_alternatingEight_at d earlier hq chosen structural alternatives
          F hne classification J e c hc) hI J hJa hJc
  let C := ChapterG.Section10.pointCentralizer F.terminalRepresentation v
  let D := F.terminalDot (centralizer (F.ZU : Set G))
  have hr : 2 ≤ primeRank 3 (C.subgroupOf J) := by
    let a := BinaryNaturalDual.Transport.stabilizerEquiv (F.terminalRepresentation.comp J.subtype)
      (BinaryPermutation.alternatingNaturalRepresentation (Fin 8)) e c hc v
    have hb := BinaryPermutation.PointStabilizerRank.two_le_natural_stabilizer
      (by simp : 8 ≤ Fintype.card (Fin 8)) (c v)
    exact hb.trans (primeRank_equiv 3 a).ge
  let f : C.subgroupOf J →* C.subgroupOf D := {
    toFun := fun a => ⟨⟨a.val.val,hJC a.val.property⟩,a.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : C.subgroupOf D => z.val.val) he))
  have hl := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
  have hu := source_center_centralizing_point_image_three_rank_le_one_at d earlier hq chosen
    structural alternatives F hne v hline.symm g hgP hgH
  change primeRank 3 (C.subgroupOf D) ≤ 1 at hu
  omega
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end
