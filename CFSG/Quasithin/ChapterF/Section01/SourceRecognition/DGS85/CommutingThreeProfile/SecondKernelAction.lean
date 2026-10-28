module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SecondKernelLayer
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.LinearResidualLayer
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.Commutator.NormalPrimeQuotient
public import Theory.Representation.Suzuki.MinimalDegree
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# The faithful original Suzuki action on the second-kernel quotient

The constructed elementary quotient of Q_beta by its intersection with the
full second ball kernel carries conjugation by the starred endpoint.
Elementarity kills the intrinsic two-core, so this action descends to the
original marked local quotient. The common Sylows supply the neighboring
placement and fix Z_beta; no representation or descent premise is required.

If the descended action were trivial, [L_beta,Q_beta] would centralize
V_beta. Three subgroups and centrality of [V_beta,Q_beta]=Z_beta then make
[V_beta,L_beta] centralize Q_beta. The proved (12.3)(d) generation identity
contradicts the nonzero center. Thus the actual representation is nontrivial,
including in the binary case, with the original conjugation formula retained.

Full movement also persists on any normal subgroup with two-group quotient.
The same reciprocal commutator argument therefore rules out a two-group
image for this action. In Sz(2), a kernel divisible by five would leave just
such an image; the remaining normal two-kernel lies in the trivial two-core.
For q > 2 simplicity supplies faithfulness. The actual representation thus
has degree at least 4 log_2(q), and the literal quotient has order at least
q^4, including q = 2.

The natural center and commutator identity are earlier Chapter 8 inputs;
span generation is supplied by the preceding Chapter 12 intersection
argument, for example SuzukiCoreProduct. Suzuki selection, full second-kernel
containment, the q^4 upper bound and final (12.9)/(13.1) assembly remain
separate. In particular, the quotient denominator is the literal restriction
of the full ball kernel to Q_beta; no equality with its two-core is assumed.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(12.1)(c,e,f), (12.3)(d), (12.6), printed pp.178--183.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo Reduction CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem second_kernel_action (h : HypothesisF11 L S) (i : Bool)
    (hplace : Q (reducedFamily L S) (base (reducedFamily L S) i) ≤ ReducedLayer.star L S (!i))
    (hnat : Noncommuting.HasNaturalCenter (ReducedLayer.star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ ≤
        Z (reducedFamily L S) (base (reducedFamily L S) i)) :
    let F := reducedFamily L S
    let v := base F i
    let : ((ballKernel F v 2).subgroupOf (Q F v)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
    let := source_second_kernel_elementary h i hplace hnat hcomm
    ∃ σ : Representation (ZMod 2) (ReducedLayer.star L S i ⧸ pCore 2 (ReducedLayer.star L S i))
      (Additive (Q F v ⧸ (ballKernel F v 2).subgroupOf (Q F v))),
      ∀ a : ReducedLayer.star L S i, ∀ x : Q F v,
        (σ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk x))).toMul =
          QuotientGroup.mk ⟨(a : G₀ L S) * x * (a : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp
              ((ReducedLayer.star_le_stabilizer i).trans
                (CommutingTrivial.stabilizer_normalizes_Q F v) a.property) x).mp x.property⟩ := by
  let F := reducedFamily L S
  let v := base F i
  let A := ReducedLayer.star L S i
  let D := Q F v
  let N := ballKernel F v 2
  let : N.subgroupOf D |>.Normal := normal_subgroupOf_of_le_normalizer
    ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
  let := source_second_kernel_elementary h i hplace hnat hcomm
  have hAD : A ≤ normalizer (D : Set (G₀ L S)) :=
    (ReducedLayer.star_le_stabilizer i).trans (CommutingTrivial.stabilizer_normalizes_Q F v)
  have hAN : A ≤ normalizer (N : Set (G₀ L S)) :=
    (ReducedLayer.star_le_stabilizer i).trans (stabilizer_le_normalizer_ballKernel F v 2)
  obtain ⟨α,hα⟩ := exists_quotient_conjugation_action A D N hAD hAN inferInstance
  have hDD : ⁅D,D⁆ ≤ N := by
    have hd : _root_.commutator D ≤ N.subgroupOf D :=
      (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N.subgroupOf D)).mp
        inferInstance
    have hm := map_mono (f := D.subtype) hd
    rw [map_subtype_commutator, subgroupOf_map_subtype] at hm
    exact hm.trans inf_le_left
  have hkill := quotient_conjugation_action_kills_commutator_layer A D N D
    inferInstance hAD hDD α hα
  have hk : pCore 2 A ≤ α.ker := by
    intro a ha
    apply hkill
    change (a : G₀ L S) ∈ Q F v
    rw [← ReducedLayer.star_core h i]
    exact mem_map_of_mem A.subtype ha
  let β := QuotientGroup.lift (pCore 2 A) α hk
  let : MulDistribMulAction (A ⧸ pCore 2 A) (D ⧸ N.subgroupOf D) :=
    MulDistribMulAction.compHom _ β
  refine ⟨Representation.ofElementaryAbelianAction,?_⟩
  intro a x
  exact hα a x


private theorem second_kernel_action_nontrivial (h : HypothesisF11 L S) (i : Bool)
    (hplace : Q (reducedFamily L S) (base (reducedFamily L S) i) ≤ ReducedLayer.star L S (!i))
    (hnat : Noncommuting.HasNaturalCenter (ReducedLayer.star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcentral : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      centralizer (ReducedLayer.star L S i : Set (G₀ L S)))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, ReducedLayer.star L S i⁆) :
    let F := reducedFamily L S
    let v := base F i
    let : ((ballKernel F v 2).subgroupOf (Q F v)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
    let := source_second_kernel_elementary h i hplace hnat hcomm.le
    ∀ σ : Representation (ZMod 2) (ReducedLayer.star L S i ⧸ pCore 2 (ReducedLayer.star L S i))
      (Additive (Q F v ⧸ (ballKernel F v 2).subgroupOf (Q F v))),
      (∀ a : ReducedLayer.star L S i, ∀ x : Q F v,
        (σ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk x))).toMul =
          QuotientGroup.mk ⟨(a : G₀ L S) * x * (a : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp
              ((ReducedLayer.star_le_stabilizer i).trans
                (CommutingTrivial.stabilizer_normalizes_Q F v) a.property) x).mp x.property⟩) →
      σ ≠ 1 := by
  dsimp only
  intro σ hσ he
  let F := reducedFamily L S
  let v := base F i
  let A := ReducedLayer.star L S i
  let D := Q F v
  let W := V F v 1
  let N := ballKernel F v 2
  let : N.subgroupOf D |>.Normal := normal_subgroupOf_of_le_normalizer
    ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
  have hn : A ≤ normalizer (D : Set (G₀ L S)) :=
    (ReducedLayer.star_le_stabilizer i).trans (CommutingTrivial.stabilizer_normalizes_Q F v)
  have hAN : ⁅A,D⁆ ≤ N := by
    apply commutator_le.mpr
    intro a ha x hx
    let a₀ : A := ⟨a,ha⟩
    let x₀ : D := ⟨x,hx⟩
    let y : D := ⟨a*x*a⁻¹,(mem_normalizer_iff.mp (hn ha) x).mp hx⟩
    have hh : (QuotientGroup.mk y : D ⧸ N.subgroupOf D) = QuotientGroup.mk x₀ := by
      have hr := hσ a₀ x₀
      rw [he] at hr
      exact hr.symm
    have hm := QuotientGroup.eq_iff_div_mem.mp hh
    change a*x*a⁻¹/x ∈ N at hm
    simpa only [commutatorElement_def, div_eq_mul_inv] using hm
  have hAD : ⁅A,D⁆ ≤ D := le_normalizer_iff_commutator_le_right.mp hn
  have h1 : ⁅⁅A,D⁆,W⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact ((le_inf hAD hAN).trans (source_core_span_centralizer_eq_second_kernel h i hplace hnat).ge).trans inf_le_right
  have h2 : ⁅⁅D,W⁆,A⁆ = ⊥ := by
    rw [commutator_comm D W]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hcomm.le.trans hcentral)
  have h3 : ⁅⁅W,A⁆,D⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate h1 h2
  have heZ : Z F v = ⊥ := by
    change ⁅⁅V F v 1, ReducedLayer.star L S i⁆,Q F v⁆ = ⊥ at h3
    rw [←hfull,hcomm] at h3
    exact h3
  exact base_Z_ne_bot (reduced_triple h) i heZ


/-- Common Sylows and the preceding span generation construct the nontrivial
original action on the literal second-kernel quotient. -/
theorem source_original_second_kernel_action (h : HypothesisF11 L S) (i : Bool)
    (T : Sylow 2 (ReducedLayer.star L S (!i)))
    (hT : (T : Subgroup (ReducedLayer.star L S (!i))).map (ReducedLayer.star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (ReducedLayer.star L S i))
    (hR : (R : Subgroup (ReducedLayer.star L S i)).map (ReducedLayer.star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hnat : Noncommuting.HasNaturalCenter (ReducedLayer.star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, ReducedLayer.star L S i⁆) :
    let F := reducedFamily L S
    let v := base F i
    let hplace : Q F v ≤ ReducedLayer.star L S (!i) :=
      (le_sup_left.trans hT.ge).trans (map_subtype_le _)
    let : ((ballKernel F v 2).subgroupOf (Q F v)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
    let := source_second_kernel_elementary h i hplace hnat hcomm.le
    ∃ ρ : Representation (ZMod 2)
      (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))
      (Additive (Q F v ⧸ (ballKernel F v 2).subgroupOf (Q F v))),
      ρ ≠ 1 ∧
      ∀ a : L (if i then 1 else 0), ∀ x : Q F v,
        (ρ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk x))).toMul =
          QuotientGroup.mk ⟨(ReducedLayer.originalActor (L := L) (S := S) i a : G₀ L S) * x *
            (ReducedLayer.originalActor (L := L) (S := S) i a : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp
              ((ReducedLayer.star_le_stabilizer i).trans
                (CommutingTrivial.stabilizer_normalizes_Q F v)
                  (ReducedLayer.originalActor (L := L) (S := S) i a).property) x).mp x.property⟩ := by
  let F := reducedFamily L S
  let v := base F i
  have hplace : Q F v ≤ ReducedLayer.star L S (!i) :=
    (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  let : ((ballKernel F v 2).subgroupOf (Q F v)).Normal :=
    normal_subgroupOf_of_le_normalizer
      ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
  let := source_second_kernel_elementary h i hplace hnat hcomm.le
  obtain ⟨σ,hσ⟩ := second_kernel_action h i hplace hnat hcomm.le
  have hn := second_kernel_action_nontrivial h i hplace hnat hcomm
    (ReducedLayer.source_center_centralizes_star_of_neighbor_inclusion h i hzy R hR)
    hfull σ hσ
  let ρ := σ.comp (ReducedLayer.originalQuotient h i).toMonoidHom
  refine ⟨ρ,?_,?_⟩
  · intro he
    apply hn
    apply MonoidHom.ext
    intro z
    apply LinearMap.ext
    intro x
    obtain ⟨w,rfl⟩ := (ReducedLayer.originalQuotient h i).surjective z
    exact DFunLike.congr_fun (DFunLike.congr_fun he w) x
  · intro a x
    exact hσ (ReducedLayer.originalActor (L := L) (S := S) i a) x

private theorem suzuki_faithful_of_odd_image {n : ℕ}
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup n) W)
    (hcore : pCore 2 (SuzukiMatrixGroup n) = ⊥)
    (hne : ρ ≠ 1) (himage : ¬ IsPGroup 2 ρ.asGroupHom.range) : Function.Injective ρ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · let f := ρ.asGroupHom
    have h5 : ¬ 5 ∣ Nat.card f.ker := by
      intro hdiv
      have hc : Nat.card f.ker * Nat.card f.range = 20 := by
        rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
        simpa only [suzukiZero_card, Subgroup.index_eq_card] using f.ker.card_mul_index
      have hd : Nat.card f.range ∣ 4 := by
        have hh : 5 * Nat.card f.range ∣ 5 * 4 := by
          rw [show 5*4 = Nat.card f.ker * Nat.card f.range from hc.symm]
          exact Nat.mul_dvd_mul hdiv (dvd_refl _)
        exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 5) hh
      exact himage (IsPGroup.of_card_dvd_pow (n := 2) hd)
    have hpk : IsPGroup 2 f.ker := IsPGroup.of_card_dvd_pow (n := 2)
      (((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr h5).symm.dvd_of_dvd_mul_right
        (show Nat.card f.ker ∣ 2^2*5 by simpa [suzukiZero_card] using f.ker.card_subgroup_dvd_card))
    have hk : f.ker = ⊥ := bot_unique
      ((le_sSup ⟨inferInstance,hpk⟩ : f.ker ≤ pCore 2 _).trans hcore.le)
    intro x y hxy
    apply (f.ker_eq_bot_iff.mp hk)
    exact Units.ext hxy
  · let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 n hn).1
    exact ρ.ker_eq_bot_iff.mp (ρ.normal_ker.eq_bot_or_eq_top.resolve_right
      (fun hk => hne (MonoidHom.ker_eq_top_iff.mp hk)))

private theorem second_kernel_action_not_two_image (h : HypothesisF11 L S) (i : Bool) (hb : 2 < b (reducedFamily L S))
    (hplace : Q (reducedFamily L S) (base (reducedFamily L S) i) ≤ ReducedLayer.star L S (!i))
    (hnat : Noncommuting.HasNaturalCenter (ReducedLayer.star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hcentral : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      centralizer (ReducedLayer.star L S i : Set (G₀ L S)))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, ReducedLayer.star L S i⁆) :
    let F := reducedFamily L S
    let v := base F i
    let : ((ballKernel F v 2).subgroupOf (Q F v)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
    let := source_second_kernel_elementary h i hplace hnat hcomm.le
    ∀ σ : Representation (ZMod 2) (ReducedLayer.star L S i ⧸ pCore 2 (ReducedLayer.star L S i))
      (Additive (Q F v ⧸ (ballKernel F v 2).subgroupOf (Q F v))),
      (∀ a : ReducedLayer.star L S i, ∀ x : Q F v,
        (σ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk x))).toMul =
          QuotientGroup.mk ⟨(a : G₀ L S) * x * (a : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp
              ((ReducedLayer.star_le_stabilizer i).trans
                (CommutingTrivial.stabilizer_normalizes_Q F v) a.property) x).mp x.property⟩) →
      ¬ IsPGroup 2 σ.asGroupHom.range := by
  dsimp only
  intro σ hσ himage
  let F := reducedFamily L S
  let v := base F i
  let A := ReducedLayer.star L S i
  let D := Q F v
  let W := V F v 1
  let N := ballKernel F v 2
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite A := Finite.of_injective (inclusion (ReducedLayer.star_le_stabilizer i))
    (inclusion_injective _)
  let : N.subgroupOf D |>.Normal := normal_subgroupOf_of_le_normalizer
    ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
  let := source_second_kernel_elementary h i hplace hnat hcomm.le
  let π := QuotientGroup.mk' (pCore 2 A)
  let f := σ.asGroupHom.comp π
  let K := f.ker
  have hn : A ≤ normalizer (D : Set (G₀ L S)) :=
    (ReducedLayer.star_le_stabilizer i).trans (CommutingTrivial.stabilizer_normalizes_Q F v)
  have hKN : ⁅K.map A.subtype,D⁆ ≤ N := by
    apply commutator_le.mpr
    rintro a ⟨a₀,ha,rfl⟩ x hx
    let x₀ : D := ⟨x,hx⟩
    let y : D := ⟨(a₀ : G₀ L S)*x*(a₀ : G₀ L S)⁻¹,
      (mem_normalizer_iff.mp (hn a₀.property) x).mp hx⟩
    have he : σ (QuotientGroup.mk a₀) = 1 := congrArg Units.val (show f a₀ = 1 from ha)
    have hh : (QuotientGroup.mk y : D ⧸ N.subgroupOf D) = QuotientGroup.mk x₀ := by
      have hr := hσ a₀ x₀
      rw [he] at hr
      exact hr.symm
    have hm := QuotientGroup.eq_iff_div_mem.mp hh
    change (a₀ : G₀ L S)*x*(a₀ : G₀ L S)⁻¹/x ∈ N at hm
    simpa only [commutatorElement_def, div_eq_mul_inv, Subgroup.subtype_apply] using hm
  have hKD : ⁅K.map A.subtype,D⁆ ≤ D :=
    (commutator_mono (map_subtype_le K) le_rfl).trans
      (le_normalizer_iff_commutator_le_right.mp hn)
  have hker : ⁅D,K.map A.subtype⁆ ≤ centralizer (W : Set (G₀ L S)) := by
    rw [commutator_comm]
    exact ((le_inf hKD hKN).trans (source_core_span_centralizer_eq_second_kernel
      h i hplace hnat).ge).trans inf_le_right
  have hWQ : W ≤ D := V_le_Q F (reduced_triple h).generate
    (fun z => (source_Z_Q_U (reduced_triple h) z).1) (reduced_kernel_sylow h) hb v
  have hDA : D ≤ A := by
    change Q F v ≤ A
    rw [←ReducedLayer.star_core h i]
    exact pCoreIn_le 2 A
  have hWA : W ≤ A := hWQ.trans hDA
  have hmove : ⁅W,D⁆ ≠ ⊥ := by
    rw [hcomm]
    exact base_Z_ne_bot (reduced_triple h) i
  have hnot := not_isPGroup_quotient_of_reciprocal_centralizer A W D (Z F v)
    hWA (ReducedLayer.star_normalizes_span h i)
    ((isPGroup_pCoreIn 2 _).to_le hWQ) hfull.symm hcomm.le hcentral hmove K hker
  apply hnot
  have hr : f.range = σ.asGroupHom.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
      ← MonoidHom.range_eq_map]
  exact (hr.symm ▸ himage).of_equiv (QuotientGroup.quotientKerEquivRange f).symm

/-- The literal second-kernel quotient has its faithful original Suzuki action
and order at least q⁴, also for Sz(2). The earlier natural center, common
Sylows, and (12.3)(d) span generation retain their source roles. -/
theorem source_suzuki_second_kernel_faithful (h : HypothesisF11 L S) (i : Bool)
    (hb : 2 < b (reducedFamily L S)) {n : ℕ}
    (e : (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0))) ≃* SuzukiMatrixGroup n)
    (T : Sylow 2 (ReducedLayer.star L S (!i)))
    (hT : (T : Subgroup (ReducedLayer.star L S (!i))).map (ReducedLayer.star L S (!i)).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) i) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (R : Sylow 2 (ReducedLayer.star L S i))
    (hR : (R : Subgroup (ReducedLayer.star L S i)).map (ReducedLayer.star L S i).subtype =
      Q (reducedFamily L S) (base (reducedFamily L S) (!i)) ⊔
        Q (reducedFamily L S) (base (reducedFamily L S) i))
    (hnat : Noncommuting.HasNaturalCenter (ReducedLayer.star L S (!i))
      (Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
      (Q (reducedFamily L S) (base (reducedFamily L S) (!i))))
    (hzy : Z (reducedFamily L S) (base (reducedFamily L S) i) ≤
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hcomm : ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1,
      Q (reducedFamily L S) (base (reducedFamily L S) i)⁆ =
        Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hfull : V (reducedFamily L S) (base (reducedFamily L S) i) 1 =
      ⁅V (reducedFamily L S) (base (reducedFamily L S) i) 1, ReducedLayer.star L S i⁆) :
    let F := reducedFamily L S
    let v := base F i
    let hplace : Q F v ≤ ReducedLayer.star L S (!i) :=
      (le_sup_left.trans hT.ge).trans (map_subtype_le _)
    let : ((ballKernel F v 2).subgroupOf (Q F v)).Normal :=
      normal_subgroupOf_of_le_normalizer
        ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
    let := source_second_kernel_elementary h i hplace hnat hcomm.le
    ∃ ρ : Representation (ZMod 2)
      (L (if i then 1 else 0) ⧸ pCore 2 (L (if i then 1 else 0)))
      (Additive (Q F v ⧸ (ballKernel F v 2).subgroupOf (Q F v))),
      Function.Injective ρ ∧
      (2 ^ (2 * n + 1)) ^ 4 ≤ Nat.card (Q F v ⧸ (ballKernel F v 2).subgroupOf (Q F v)) ∧
      ∀ a : L (if i then 1 else 0), ∀ x : Q F v,
        (ρ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk x))).toMul =
          QuotientGroup.mk ⟨(ReducedLayer.originalActor (L := L) (S := S) i a : G₀ L S) * x *
            (ReducedLayer.originalActor (L := L) (S := S) i a : G₀ L S)⁻¹,
            (mem_normalizer_iff.mp
              ((ReducedLayer.star_le_stabilizer i).trans
                (CommutingTrivial.stabilizer_normalizes_Q F v)
                  (ReducedLayer.originalActor (L := L) (S := S) i a).property) x).mp x.property⟩ := by
  let F := reducedFamily L S
  let v := base F i
  let A := ReducedLayer.star L S i
  let D := Q F v
  let N := ballKernel F v 2
  have hplace : Q F v ≤ ReducedLayer.star L S (!i) :=
    (le_sup_left.trans hT.ge).trans (map_subtype_le _)
  let : N.subgroupOf D |>.Normal := normal_subgroupOf_of_le_normalizer
    ((Q_le_stabilizer F v).trans (stabilizer_le_normalizer_ballKernel F v 2))
  let := source_second_kernel_elementary h i hplace hnat hcomm.le
  let : ∀ j, Finite (F j) := finite_endpoints (reduced_triple h)
  let : Finite (ReducedLayer.star L S i) := Finite.of_injective
    (inclusion (ReducedLayer.star_le_stabilizer i)) (inclusion_injective _)
  let : Finite D := Finite.of_injective (inclusion (Q_le_stabilizer F v)) (inclusion_injective _)
  obtain ⟨σ,hσ⟩ := second_kernel_action h i hplace hnat hcomm.le
  have hz := ReducedLayer.source_center_centralizes_star_of_neighbor_inclusion h i hzy R hR
  have hn := second_kernel_action_nontrivial h i hplace hnat hcomm hz hfull σ hσ
  have hp := second_kernel_action_not_two_image h i hb hplace hnat hcomm hz hfull σ hσ
  let eA := (ReducedLayer.originalQuotient h i).symm.trans e
  let τ : Representation (ZMod 2) (SuzukiMatrixGroup n) (Additive (D ⧸ N.subgroupOf D)) :=
    σ.comp eA.symm.toMonoidHom
  have htne : τ ≠ 1 := by
    intro he
    apply hn
    apply MonoidHom.ext
    intro z
    apply LinearMap.ext
    intro x
    have hh := DFunLike.congr_fun (DFunLike.congr_fun he (eA z)) x
    change σ (eA.symm (eA z)) x = x at hh
    change σ z x = x
    simpa only [eA.symm_apply_apply] using hh
  have htimage : ¬ IsPGroup 2 τ.asGroupHom.range := by
    have he : τ.asGroupHom = σ.asGroupHom.comp eA.symm.toMonoidHom := by
      apply MonoidHom.ext
      intro z
      apply Units.ext
      rfl
    rw [he, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eA.symm.surjective,
      ←MonoidHom.range_eq_map]
    exact hp
  have hc : pCore 2 (SuzukiMatrixGroup n) = ⊥ := by
    rw [←pCore_map_iso 2 eA, pCore_quotient_pCore_eq_bot, Subgroup.map_bot]
  have hτ := suzuki_faithful_of_odd_image τ hc htne htimage
  have hσf : Function.Injective σ := by
    intro x y hxy
    apply eA.injective
    apply hτ
    change σ (eA.symm (eA x)) = σ (eA.symm (eA y))
    simpa only [eA.symm_apply_apply] using hxy
  let ρ := σ.comp (ReducedLayer.originalQuotient h i).toMonoidHom
  have hd : 4 * (2*n+1) ≤ Module.finrank (ZMod 2) (Additive (D ⧸ N.subgroupOf D)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn'
    · have hh := Representation.BinaryPrimeDegree.orderOf_le_finrank τ hτ
        (by decide : Nat.Prime 5) (by decide : 5 ≠ 2)
        (by rw [suzukiZero_card]; decide)
      simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_five,
        Nat.mul_zero,Nat.zero_add,Nat.mul_one] using hh
    · exact Representation.Suzuki.finrank_ge (by omega) τ hτ
  have hcard : (2 ^ (2*n+1))^4 ≤ Nat.card (D ⧸ N.subgroupOf D) := by
    change (2 ^ (2*n+1))^4 ≤ Nat.card (Additive (D ⧸ N.subgroupOf D))
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ←pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    simpa only [Nat.mul_comm] using hd
  refine ⟨ρ,hσf.comp (ReducedLayer.originalQuotient h i).injective,hcard,?_⟩
  intro a x
  exact hσ (ReducedLayer.originalActor (L := L) (S := S) i a) x

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
