module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorCentralizers
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PResidual.SectionSylowRelative
public import Theory.GroupTheory.SylowCoverQuotientAction
public import Theory.GroupTheory.SubgroupCoverTransport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Source.Three

/-!
# The original tensor point residual in the solvable uniqueness family

The marked point stabilizer gives XT/O₂(XT) ≅ S₃ wr C₂. Its literal
embedded two-residual is X = O²(C_{L₀}(z)), so X/O₂(X) is the elementary
cubic plane. Maximality of a Sylow subgroup of the wreath quotient makes
T maximal in XT. A lifted invariant subgroup and two-perfectness then
prove irreducibility of the actual Frattini action, giving X ∈ Ξ(G,T).

The complete Chapter1 embedding theorem applies to the original C_G(z)
and every chosen Sylow three-subgroup of X. The original S is Sylow in
C_{N_{G_z}(X)}(X/O₂(X)); quiet Thompson control bounds N_G(S) by M.
Every solvable overgroup of S in that section centralizer therefore lies
in M. Its adequate Held alternative is retained; none of the ambient exclusions or G_z = K_z M_z is inferred
from the abstract quotient alone. Tensor-base recognition, the rest of
8.3.7--12 and the quiet tensor exclusions remain with the selected-module
owner. Final point-control assembly remains with its existing owner.
Source: Aschbacher--Smith 1.3.1--4 and 8.3.7, pp.508--511,724--725.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

private theorem marking_kernel
    (q : localJoin T L →* BinaryTensorThree.PointParabolic.Actor)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (he : ∀ (a : localJoin T L) (v : Additive D.fullModule),
      e (Additive.ofMul
        (D.fullModule.normalizerMonoidHom
          ⟨a,D.maximalLocal_normalizes_fullModule
            ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) a.property)⟩
          v.toMul)) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (e v)) :
    q.ker = (quietTensorLinearAction D e).ker := by
  ext a
  change q a = 1 ↔ quietTensorLinearAction D e a = 1
  constructor
  · intro ha
    apply LinearEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    rw [quietTensorLinearAction_apply,he,ha,map_one,map_one]
    rfl
  · intro ha
    have hact : BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) = 1 := by
      apply LinearMap.ext
      intro w
      obtain ⟨v,rfl⟩ := e.surjective w
      rw [←he,←quietTensorLinearAction_apply,ha]
      rfl
    have hq := BinaryTensorThree.action_faithful
      (hact.trans BinaryTensorThree.action.map_one.symm)
    rw [←BinaryTensorThree.PointParabolic.actorEquiv_apply] at hq
    exact BinaryTensorThree.PointParabolic.actorEquiv.injective
      (hq.trans BinaryTensorThree.PointParabolic.actorEquiv.map_one.symm)

private theorem point_parabolic_cover
    (q : localJoin T L →* BinaryTensorThree.PointParabolic.Actor)
    (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (he : ∀ (a : localJoin T L) (v : Additive D.fullModule),
      e (Additive.ofMul
        (D.fullModule.normalizerMonoidHom
          ⟨a,D.maximalLocal_normalizes_fullModule
            ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) a.property)⟩
          v.toMul)) =
        BinaryTensorThree.action (BinaryTensorThree.PointParabolic.tensorHom (q a)) (e v))
    {z : G} (hzV : z ∈ D.fullModule)
    (hez : e (Additive.ofMul ⟨z,hzV⟩) = BinaryTensorThree.point)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    ∃ f : (CentralizerSetup.XT ⟨T,localOrbit T L,z⟩) →*
        BinaryTensorThree.PointParabolic.PairP,
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hXT : d.XT = localJoin T L ⊓ centralizer ({z} : Set G) :=
    quiet_XT_eq_point_centralizer (L := L) hzT
  have hXH : d.XT ≤ localJoin T L := hXT.le.trans inf_le_left
  have hfix (a : localJoin T L) :
      q a ∈ BinaryTensorThree.PointParabolic.PairP ↔
        (a : G) ∈ centralizer ({z} : Set G) := by
    rw [← BinaryTensorThree.PointParabolic.fixes_point_iff]
    have hh := he a (Additive.ofMul ⟨z,hzV⟩)
    rw [hez] at hh
    constructor
    · intro hf
      have hz := e.injective (hh.trans (hf.trans hez.symm))
      have hz' := congrArg (fun v : Additive D.fullModule => (v.toMul : G)) hz
      change (a : G)*z*(a : G)⁻¹ = z at hz'
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hz')
    · intro ha
      have hz : Additive.ofMul
          (D.fullModule.normalizerMonoidHom
            ⟨a,D.maximalLocal_normalizes_fullModule
              ((sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) a.property)⟩
            ⟨z,hzV⟩) = Additive.ofMul ⟨z,hzV⟩ := by
        apply congrArg Additive.ofMul
        apply Subtype.ext
        change (a : G)*z*(a : G)⁻¹ = z
        rw [mem_centralizer_singleton_iff.mp ha,mul_inv_cancel_right]
      exact hh.symm.trans ((congrArg e hz).trans hez)
  let f : d.XT →* BinaryTensorThree.PointParabolic.PairP :=
    (q.comp (inclusion hXH)).codRestrict _ (fun x =>
      (hfix (inclusion hXH x)).mpr ((hXT.le x.property).2))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := hq y
    have hz : (x : G) ∈ centralizer ({z} : Set G) :=
      (hfix x).mp (hx ▸ y.property)
    refine ⟨⟨x,hXT.ge ⟨x.property,hz⟩⟩,?_⟩
    exact Subtype.ext hx
  refine ⟨f,hf,?_⟩
  have hfk : f.ker = q.ker.comap (inclusion hXH) := by
    ext x
    change f x = 1 ↔ q (inclusion hXH x) = 1
    exact Subtype.ext_iff
  rw [hfk]
  exact hk.comap_of_injective _ (inclusion_injective hXH)

/-- The actual point-centralizer parabolic has the binary-plane wreath quotient. -/
theorem quiet_tensor_point_quotient
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let H := CentralizerSetup.XT ⟨T,localOrbit T L,z⟩
    Nonempty ((H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) := by
  dsimp only
  obtain ⟨q,hq,he⟩ := quiet_exists_tensor_marking_of_action_image D e
    (quiet_tensor_action_image_of_orbit_image D hn e hbase)
  obtain ⟨p,b,hp,hb,hz⟩ := quiet_tensor_marking_at_original_fixed_point D q hq e he
  have hk : IsPGroup 2 p.ker := by
    rw [marking_kernel D p b hb,quietTensorLinearAction_ker]
    exact full_module_local_kernel_isTwoGroup D hn
  obtain ⟨f,hf,hk⟩ := point_parabolic_cover D p hp hk b hb hzV (hz z hzV hz1 hzT) hzT
  exact ⟨(f.pCoreQuotientEquiv hf hk).trans Matrix.PSL3Two.WreathPair.pointQuotientEquiv⟩

/-- The original X is exactly the embedded two-residual of XT. -/
theorem quiet_point_residual_eq {z : G}
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    (pResidual 2 d.XT).map d.XT.subtype = d.X := by
  dsimp only
  let C := localOrbit T L ⊓ centralizer ({z} : Set G)
  have hnC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf (le_normalizer_componentOrbit L T)
      (hzT.trans (centralizer ({z} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  exact embedded_pResidual_join_pGroup _ _ (isPPerfect_embedded_pResidual 2 C)
    T.isPGroup' (hnC.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C)))

/-- The literal residual X, modulo its own two-core, is an elementary cubic plane. -/
theorem quiet_tensor_point_residual_quotient
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let X := CentralizerSetup.X ⟨T,localOrbit T L,z⟩
    Nonempty ((X ⧸ pCore 2 X) ≃* Multiplicative (Fin 2 → ZMod 3)) := by
  dsimp only
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  obtain ⟨f⟩ := quiet_tensor_point_quotient D hn e hbase hzV hz1 hzT
  obtain ⟨r⟩ := WreathTwoResidual.residual_core_quotient_equiv_elementaryNine f
  let c : (pResidual 2 d.XT) ≃* d.X :=
    ((pResidual 2 d.XT).equivMapOfInjective d.XT.subtype d.XT.subtype_injective).trans
      (MulEquiv.subgroupCongr (quiet_point_residual_eq (T := T) (L := L) hzT))
  exact ⟨(QuotientGroup.congr _ _ c.symm (pCore_map_iso 2 c.symm)).trans r⟩


private instance : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Multiplicative.toAdd.injective
    ext i
    change (3 : ℕ) • x.toAdd i = 0
    exact (show ∀ a : ZMod 3, (3 : ℕ) • a = 0 by decide) _

/-- The maximal Sylow supplement makes the actual tensor point residual a
member of Ξ(G,T); its irreducible Frattini action is proved, not assumed. -/
theorem quiet_tensor_point_residual_mem_Xi
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    CentralizerSetup.X ⟨T,localOrbit T L,z⟩ ∈ Chapter1.Xi G (T : Subgroup G) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hp : IsPPerfect 2 d.X := isPPerfect_embedded_pResidual 2 _
  have hTX : (T : Subgroup G) ≤ normalizer (d.X : Set G) := by
    rw [←quiet_point_residual_eq (T := T) (L := L) hzT]
    exact (show (T : Subgroup G) ≤ d.XT from le_sup_right).trans
      (le_normalizer_embedded_pResidual 2 d.XT)
  obtain ⟨f⟩ := quiet_tensor_point_quotient D hn e hbase hzV hz1 hzT
  obtain ⟨c⟩ := quiet_tensor_point_residual_quotient D hn e hbase hzV hz1 hzT
  let : IsElementaryAbelian 3 (Chapter1.XiQuotient d.X) :=
    IsElementaryAbelian.of_injective c.toMonoidHom c.injective
  have hq : Chapter1.XiOddQuotient 3 (Chapter1.XiQuotient d.X) := by
    refine Or.inl ⟨inferInstance,?_⟩
    rw [Nat.card_congr c.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  have hcover : (T : Subgroup G) ⋖ d.XT := by
    let S := T.subtype (show (T : Subgroup G) ≤ d.XT from le_sup_right)
    have hc := WreathTwoResidual.sylow_isCoatom_of_core_quotient S f
    have hh := (covBy_map_subtype_iff d.XT _ _).mpr hc.covBy_top
    simpa only [S,Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ d.XT from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype] using hh
  refine ⟨hp,hTX,?_,⟨3,by decide,by decide,hq⟩,?_⟩
  · change d.S ≠ ⊥
    intro hs
    have hVS : D.fullModule ≤ d.S :=
      (le_inf (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D))
        (le_centralizer _)).trans (quiet_kernel_le_point_radical D hzV hzT)
    exact hz1 (mem_bot.mp (hs ▸ hVS hzV))
  · let π : d.X →* Chapter1.XiFrattiniQuotient d.X :=
      (QuotientGroup.mk' (frattini (Chapter1.XiQuotient d.X))).comp
        (QuotientGroup.mk' (pCore 2 d.X))
    have hπ : Function.Surjective π :=
      (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
    apply quotient_irreducible_of_twoPerfect_cover d.X (T : Subgroup G) hp T.isPGroup'
      hTX hcover (p := 3) (by decide) (IsElementaryAbelian.isPGroup 3 _)
      π hπ (Chapter1.xiFrattiniAction (T : Subgroup G) d.X hTX)
    intro t x
    simp only [π,Chapter1.xiFrattiniAction,MonoidHom.comp_apply,quotientAut_apply_mk]
    congr 2

/-- The intrinsic embedding alternatives applied in 8.3.7, for every Sylow
three-subgroup of the original X. The additional adequate Held case is retained. -/
theorem quiet_tensor_point_embedding_alternatives
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    Chapter1.XiEmbedding.AdequateConclusion 3 (T : Subgroup G) d.X
      ((P : Subgroup d.X).map d.X.subtype) d.Gz := by
  dsimp only
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hXi := quiet_tensor_point_residual_mem_Xi D hn e hbase hzV hz1 hzT
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) d.Gz :=
    ⟨T.subtype hzT,map_subgroupOf_eq_of_le hzT⟩
  have hXT : d.XT ≤ d.Gz := sup_le (d.X_le.trans inf_le_right) hzT
  obtain ⟨c⟩ := quiet_tensor_point_residual_quotient D hn e hbase hzV hz1 hzT
  have hq : Chapter1.XiOddQuotient 3 (Chapter1.XiQuotient d.X) := by
    refine Or.inl ⟨IsElementaryAbelian.of_injective c.toMonoidHom c.injective,?_⟩
    rw [Nat.card_congr c.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hlocal : IsTwoLocal d.Gz := isTwoLocal_involution_centralizer hz2
  exact (Chapter1.XiEmbedding.localInput_of_mem_Xi hXi hT hXT (by decide) hq P).adequate_three_knownSimple (D.simpleQTKE.twoLocal_sqtk hlocal) hT

/-- The original S is Sylow in the actual section centralizer Y_z. -/
theorem quiet_point_sectionCentralizer_sylow {z : G}
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    Chapter1.IsSylowIn 2 d.S
      (commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2)) := by
  dsimp only
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hTX : (T : Subgroup G) ≤ normalizer (d.X : Set G) := by
    rw [←quiet_point_residual_eq (T := T) (L := L) hzT]
    exact (show (T : Subgroup G) ≤ d.XT from le_sup_right).trans
      (le_normalizer_embedded_pResidual 2 d.XT)
  exact exists_sylow_sectionCentralizer_of_normalizes d.X
    (d.Gz ⊓ normalizer (d.X : Set G))
    (le_inf (d.X_le.trans inf_le_right) d.X.le_normalizer) inf_le_right
    (isPPerfect_embedded_pResidual 2 _) T (le_inf hzT hTX)

/-- Quiet Thompson control bounds the normalizer of the original point radical. -/
theorem quiet_tensor_point_radical_normalizer_le
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    normalizer (CentralizerSetup.S ⟨T,localOrbit T L,z⟩ : Set G) ≤ D.maximalLocal := by
  have hJV : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) := by
    rwa [quiet_tensor_fullModule_eq_module D e hbase]
  exact (source_two_overgroup_normalizer_le_of_centralizes D hJV _
    (isPGroup_pCoreIn 2 _) ((le_inf (sSup_le fun _ hA => hA.1) hJV).trans
      (quiet_kernel_le_point_radical D hzV hzT))).2

/-- Every solvable overgroup of S in the literal section centralizer lies in M. -/
theorem quiet_tensor_solvable_point_section_overgroup_le
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (H : Subgroup G) [Group.IsSolvable H]
    (hSH : CentralizerSetup.S ⟨T,localOrbit T L,z⟩ ≤ H)
    (hHY : let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
      H ≤ commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2)) :
    H ≤ D.maximalLocal := by
  exact quiet_tensor_solvable_overgroup_le D hn e hbase hzV hz1 hzT H
    ((quiet_point_sectionCentralizer_sylow (T := T) (L := L) hzT).restrict hSH hHY)

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
