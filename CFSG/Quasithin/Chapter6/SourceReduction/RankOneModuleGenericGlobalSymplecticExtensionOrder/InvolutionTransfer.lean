module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.ThirdCentralizer
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSpecialTransfer
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.CentralFusion
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.GroupTheory.SylowIndexTwoExtension

/-!
# Ambient involution transfer for the prepared symplectic row

The whole right residual has its actual PSL₂ quotient. Its cyclic field
character on the original Sylow T has kernel S, so generalized Thompson
transfer in the original simple group fuses every involution into S.
The compatible pure comparison transports the native parabolic conjugators
into L join O²(H), and puts every such involution in the actual Z(S).
Consequently every ambient involution centralizer has characteristic two,
and every Sylow two-subgroup of it has order at least q⁴.

The same quotient gives [T:S] dividing the original n. At odd degree this
proves S=T and hence the whole third-involution centralizer containment.
At even degree the field-involution Sylow placement of F.4.37, including
its Sp₄(4) exception, still needs proof. No ambient order comparison or
recognition is used or asserted here; both orientations and n=2 remain.

Source: Aschbacher–Smith A.1.37(2), F.4.27, F.4.30 and F.4.38–39,
printed pp.31,288–290,294; the original application is 5.3.3, p.659
of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem endpoint_conjugator {F : Type*} [Field F]
    {S P : Subgroup G} (hSP : S ≤ P) {R : Subgroup (Sp F)}
    (e : P ≃* R) (a : S → Sp F)
    (ha : ∀ s : S, (e ⟨s.val,hSP s.property⟩).val = a s)
    (x z : S) (g : Sp F) (hg : g ∈ R) (he : g*a x*g⁻¹=a z) :
    ∃ k ∈ P, k*x.val*k⁻¹=z.val := by
  let k := e.symm ⟨g,hg⟩
  refine ⟨k.val,k.property,?_⟩
  have hh : k * (⟨x.val,hSP x.property⟩ : P) * k⁻¹ = ⟨z.val,hSP z.property⟩ := by
    apply e.injective
    apply Subtype.ext
    simpa only [map_mul,map_inv,coe_mul,coe_inv,k,e.apply_symm_apply,ha] using he
  exact congrArg Subtype.val hh

private theorem pair_central_fusion
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hF : Nat.card F = 2^m) (hm : 0 < m)
    {P Q C S : Subgroup G} (hCP : C ≤ P) (hCQ : C ≤ Q) (hSC : S ≤ C)
    (hs : Chapter1.IsSylowIn 2 S C)
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P C Q hCP hCQ)
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) :
    Nat.card S = Nat.card F^4 ∧
    ∀ x : S, x^2=1 → ∃ g ∈ P ⊔ Q, ∃ z : S, z ∈ center S ∧ g*x.val*g⁻¹=z.val := by
  obtain ⟨R,hR⟩ := hs
  have hRS : (R : Subgroup C) = S.subgroupOf C := by
    apply map_injective C.subtype_injective
    rw [hR,map_subgroupOf_eq_of_le hSC]
  let U := (unipotentSylow hF hm).subtype unipotent_le_borel
  let : (U : Subgroup (borel (F := F))).Normal := unipotent_normal_in_borel
  let := Sylow.unique_of_normal U (inferInstance : U.Normal)
  have hSU : (S.subgroupOf C).map e.middle.toMonoidHom = unipotent.subgroupOf borel := by
    rw [←hRS]
    exact congrArg Sylow.toSubgroup (Subsingleton.elim
      (R.mapSurjective (f := e.middle.toMonoidHom) e.middle.surjective) U)
  let a : S ≃* unipotent (F := F) := (subgroupOfEquivOfLe hSC).symm.trans
    ((e.middle.subgroupMap (S.subgroupOf C)).trans
      ((MulEquiv.subgroupCongr hSU).trans (subgroupOfEquivOfLe unipotent_le_borel)))
  have hl (s : S) :
      (e.left ⟨s.val,(hSC.trans hCP) s.property⟩).val = (a s).val :=
    congrArg Subtype.val (e.left_commutes ⟨s.val,hSC s.property⟩)
  have hr (s : S) :
      (e.right ⟨s.val,(hSC.trans hCQ) s.property⟩).val = (a s).val :=
    congrArg Subtype.val (e.right_commutes ⟨s.val,hSC s.property⟩)
  refine ⟨(Nat.card_congr a.toEquiv).trans card_unipotent,?_⟩
  intro x hx
  have hax : (a x)^2=1 := by rw [←map_pow,hx,map_one]
  obtain ⟨g,hg,u,hu,hgu⟩ := SourceFusionOrder.involution_parabolic_conjugate_center (a x) hax
  let z := a.symm u
  have hz : z ∈ center S := (centerCongr a.symm ⟨u,hu⟩).property
  have hez : g*(a x).val*g⁻¹=(a z).val := by rw [a.apply_symm_apply]; exact hgu
  rcases hg with hg | hg
  · obtain ⟨k,hk,hkx⟩ := endpoint_conjugator (hSC.trans hCP) e.left
      (fun s => (a s).val) hl x z g hg hez
    exact ⟨k,mem_sup_left hk,z,hz,hkx⟩
  · obtain ⟨k,hk,hkx⟩ := endpoint_conjugator (hSC.trans hCQ) e.right
      (fun s => (a s).val) hr x z g hg hez
    exact ⟨k,mem_sup_right hk,z,hz,hkx⟩

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he

/-- The original inner Sylow has order q⁴, and its involutions are fused
into its center using actual conjugators in the two-factor join. -/
theorem Preparation.symplectic_inner_sylow_card_and_fusion :
    Nat.card (sourceS L H) = Nat.card F^4 ∧
    ∀ x : sourceS L H, x^2=1 → ∃ g ∈ L ⊔ residual H,
      ∃ z : sourceS L H, z ∈ center (sourceS L H) ∧ g*x.val*g⁻¹=z.val := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0 ⊓ P 1
  have hf := d.hypothesisF11 h hH.1.1.2
  have hSC : sourceS L H ≤ C := le_inf (le_sup_right.trans le_sup_left)
    (le_sup_right.trans le_sup_left)
  have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
    change Chapter1.IsSylowIn 2 (sourceS L H) (P 0 ⊓ P 1)
    rw [show P 0 ⊓ P 1 = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hf]
    exact hf.sylow_commonBorel
  have hjoin : P 0 ⊔ P 1 = L ⊔ residual H := by
    rw [ChapterF.Source.parabolics_generate]
    exact sup_eq_left.mpr
      ((d.symplectic_sourceS_le_factors h hH.1.1.2 hp F hm hF he 0).trans le_sup_left)
  have hh : Nat.card (sourceS L H) = Nat.card F^4 ∧
      ∀ x : sourceS L H, x^2=1 → ∃ g ∈ P 0 ⊔ P 1,
        ∃ z : sourceS L H, z ∈ center (sourceS L H) ∧ g*x.val*g⁻¹=z.val := by
    rcases he with he | he <;> obtain ⟨e⟩ := he
    · exact pair_central_fusion hF hm inf_le_left inf_le_right hSC hs e
    · simpa only [sup_comm] using
        pair_central_fusion hF hm inf_le_right inf_le_left hSC hs e.reverse
  rwa [hjoin] at hh

/-- The full original Sylow quotient has order dividing n. -/
theorem Preparation.symplectic_source_sylow_index_dvd :
    (sourceS L H).relIndex (T : Subgroup G) ∣ n := by
  obtain ⟨_,_,_,_,_,_,hpsl,_⟩ := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).2.2
  exact d.residual_sylow_index_dvd h hH.1.1.2
    (d.symplectic_sourceS_le_factors h hH.1.1.2 hp F hm hF he) hpsl

/-- Cyclic field-action transfer fuses every ambient involution into S,
including even degrees and the four-element field. -/
theorem Preparation.symplectic_involution_fused_into_sourceS (x : G) (hx : orderOf x=2) :
    ∃ y ∈ sourceS L H, IsConj x y := by
  obtain ⟨_,_,_,_,_,_,hpsl,_⟩ := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).2.2
  exact d.residual_involution_fused_into_sourceS h hH.1.1.2
    (d.symplectic_sourceS_le_factors h hH.1.1.2 hp F hm hF he) hpsl x hx

/-- Every ambient involution is conjugate to an element of the actual Z(S).
No identification of S with the ambient Sylow is assumed. -/
theorem Preparation.symplectic_involution_fused_into_center (x : G) (hx : orderOf x=2) :
    ∃ z : sourceS L H, z ∈ center (sourceS L H) ∧ IsConj x z.val := by
  obtain ⟨y,hy,hxy⟩ := d.symplectic_involution_fused_into_sourceS h hH hp F hm hF he x hx
  have hy2 : (⟨y,hy⟩ : sourceS L H)^2=1 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hxy
    apply Subtype.ext
    change y^2=1
    rw [←hg]
    change (MulAut.conj g x)^2=1
    rw [←map_pow,show x^2=1 from hx ▸ pow_orderOf_eq_one x,map_one]
  obtain ⟨g,_,z,hz,hg⟩ := (d.symplectic_inner_sylow_card_and_fusion h hH hp F hm hF he).2
    ⟨y,hy⟩ hy2
  exact ⟨z,hz,hxy.trans (isConj_iff.mpr ⟨g,hg⟩)⟩

/-- All ambient involution centralizers have characteristic two in the
prepared symplectic row, before the outer-Sylow transfer conclusion. -/
theorem Preparation.symplectic_involution_centralizer_characteristicTwo (x : G) (hx : orderOf x=2) :
    HasCharacteristicTwo (centralizer ({x} : Set G)) ∧
      generalizedFitting (centralizer ({x} : Set G)) = pCore 2 (centralizer ({x} : Set G)) := by
  obtain ⟨z,hz,hxz⟩ := d.symplectic_involution_fused_into_center h hH hp F hm hF he x hx
  obtain ⟨g,hg⟩ := isConj_iff.mp hxz
  have hz2 : orderOf z.val=2 := by rw [←hg]; exact ((MulAut.conj g).orderOf_eq x).trans hx
  have hc := (d.symplectic_center_centralizer_characteristicTwo h hH.1.1.2 hp F hm hF he
    z.val (mem_map_of_mem _ hz) hz2).1
  rw [←hg] at hc
  have hxC := HasCharacteristicTwo.of_equiv
    (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) x).symm hc
  exact ⟨hxC,generalizedFitting_eq_pCore_of_selfCentralizing 2 hxC⟩

omit d h hH hp [Field F] [Finite F] [CharP F 2] hm hF he in
private theorem centralizer_sylow_lower (S : Subgroup G) (hS : IsPGroup 2 S)
    (x z : G) (hz : S ≤ centralizer ({z} : Set G)) (hconj : IsConj z x)
    (P : Sylow 2 (centralizer ({x} : Set G))) : Nat.card S ≤ Nat.card P := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hconj
  let a := MulAut.conj g
  let D := S.map a.toMonoidHom
  let C := centralizer ({x} : Set G)
  have hDC : D ≤ C := by
    rintro _ ⟨s,hs,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change a s * x = x * a s
    have hh := congrArg a (mem_centralizer_singleton_iff.mp (hz hs))
    simpa only [map_mul,show a z=x from hg] using hh
  have hpD : IsPGroup 2 D := hS.map _
  have hh := card_le_sylow_two (hpD.comap_subtype (K := C)) P
  change Nat.card (D.subgroupOf C) ≤ Nat.card P at hh
  rw [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv,
    show Nat.card D=Nat.card S from card_map_of_injective a.injective] at hh
  exact hh

/-- The Sylow two-subgroups of every full ambient involution centralizer
have order at least q⁴. This is the inner lower bound used in F.4.38. -/
theorem Preparation.symplectic_involution_centralizer_sylow_lower_bound
    (x : G) (hx : orderOf x=2) (P : Sylow 2 (centralizer ({x} : Set G))) :
    Nat.card F^4 ≤ Nat.card P := by
  obtain ⟨z,hz,hxz⟩ := d.symplectic_involution_fused_into_center h hH hp F hm hF he x hx
  have hSC : sourceS L H ≤ centralizer ({z.val} : Set G) := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val ((mem_center_iff.mp hz) ⟨s,hs⟩))
  rw [←(d.symplectic_inner_sylow_card_and_fusion h hH hp F hm hF he).1]
  exact centralizer_sylow_lower (sourceS L H) (pCore_isPGroup.map _) x z.val hSC hxz.symm P

/-- At odd original degree the original inner Sylow is the entire ambient Sylow. -/
theorem Preparation.symplectic_sourceS_eq_sylow_of_odd (hn : Odd n) :
    sourceS L H = (T : Subgroup G) := by
  have hd := d.symplectic_source_sylow_index_dvd h hH hp F hm hF he
  obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
  have ht : (sourceS L H).relIndex (T : Subgroup G) ∣ 2^k := by
    rw [←hk]
    exact relIndex_dvd_card _ _
  exact le_antisymm (sourceS_le_sylow h.sylow_normalizes hH.1.1.2)
    (relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes (hn.coprime_two_right.pow_right k) hd ht))

/-- At odd degree the full third-involution centralizer lies in the whole
middle, with the transfer premise discharged. -/
theorem Preparation.symplectic_square_centralizer_le_middle_of_odd (hn : Odd n)
    (z : sourceS L H) (hz : orderOf z=2) (hsq : ∃ y : sourceS L H, y^2=z) :
    centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) :=
  d.symplectic_square_centralizer_le_middle_of_sylow h hH hp F hm hF he
    (d.symplectic_sourceS_eq_sylow_of_odd h hH hp F hm hF he hn) z hz hsq
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
