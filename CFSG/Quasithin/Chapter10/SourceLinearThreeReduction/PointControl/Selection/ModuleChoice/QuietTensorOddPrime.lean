module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorInvariantBinaryExclusion
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorHeldExclusion
public import Theory.SpecificGroups.PSL2.PrimeThreeFreeResidual
public import Theory.GroupTheory.AutomorphismOddImage
public import Theory.GroupTheory.PCoreRestriction

/-!
# The odd-prime ambient centralizer argument

The full action kernel on K_z/O₂(K_z) meets T inside the original S.
Dickson's theorem makes the image of every three-free two-perfect subgroup
odd in the actual exchanged PSL₂ square. Its intersection with T therefore
lies in S. If a three-free T-invariant subgroup escaped M, minimal descent
would supply an original H-star of generation one. Restricting the E-family
to its two-residual joined with S contradicts the checked weak closures.

This proves the ambient three-free containment used in 8.3.8, without a
faithful action assumption, a bound on C_M(V), or the later M=L₀T equality.
Source applies it to the actual plane-radical fixed space and then proves
8.3.9. Tensor-base recognition, the remaining 8.3.10--12 geometry and both
quiet exclusions remain with the selected-module owner.
Source: Aschbacher--Smith 8.3.8--9, printed p.725.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03 Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- The full quotient-action kernel meets the original Sylow only inside
the original point radical. Quotient centralization is kept separate from
ordinary centralization throughout. -/
theorem quiet_tensor_point_action_kernel_sylow_le
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let f := (pCoreNormalizerAction 2 d.Kz).comp
      (inclusion (le_normalizer_conjugateSpanBy d.X d.Gz))
    (T : Subgroup G) ⊓ f.ker.map d.Gz.subtype ≤ d.S := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let f := (pCoreNormalizerAction 2 d.Kz).comp
    (inclusion (le_normalizer_conjugateSpanBy d.X d.Gz))
  let B := f.ker.map d.Gz.subtype
  let C := commutatorPreimage (d.Gz ⊓ normalizer (d.X : Set G)) d.X (d.X.pCoreIn 2)
  have hi := quiet_tensor_point_localInput D hn e hbase hzV hz1 hzT P
  have hKn : d.Gz ≤ normalizer (d.Kz : Set G) := le_normalizer_conjugateSpanBy _ _
  have hcoreH : d.Gz.pCoreIn 2 ≤ normalizer (d.X : Set G) := by
    rw [←hi.residual]
    exact le_sup_left.trans (le_normalizer_embedded_pResidual 2 _)
  have hcore : d.Kz.pCoreIn 2 ≤ normalizer (d.X : Set G) :=
    (pCoreIn_mono_of_normalizes d.Kz_le_Gz hKn).trans hcoreH
  have hBN : B ≤ normalizer (d.X : Set G) := by
    rintro g ⟨x,hx,rfl⟩
    apply mem_normalizer_of_pCoreNormalizerAction_preserves_image d.Kz d.X d.X_le_Kz
      hi.perfect hcore (inclusion hKn x)
    change pCoreNormalizerAction 2 d.Kz (inclusion hKn x) = 1 at hx
    rw [hx]
    exact map_id _
  have hBK : ⁅d.Kz,B⁆ ≤ d.Kz.pCoreIn 2 := by
    apply commutator_le_core_of_pCoreNormalizerAction_eq_one 2 d.Kz B
      ((map_subtype_le _).trans hKn)
    rintro ⟨b,x,hx,rfl⟩
    exact hx
  have hBC : B ≤ C := by
    apply le_commutatorPreimage (le_inf (map_subtype_le _) hBN)
    rw [commutator_comm]
    exact (le_inf (le_normalizer_iff_commutator_le_left.mp hBN)
      ((commutator_mono d.X_le_Kz le_rfl).trans hBK)).trans
        (inf_pCoreIn_le_of_le 2 d.X_le_Kz)
  have hS := isSylowIn_iff.mp (quiet_point_sectionCentralizer_sylow (T := T) (L := L) hzT)
  have he : (T : Subgroup G) ⊓ C = d.S :=
    hS.2.2 _ (T.isPGroup'.to_le inf_le_left) (le_inf d.S_le_T hS.2.1) inf_le_right
  exact (inf_le_inf_left _ hBC).trans_eq he

/-- Actual odd-prime square coordinates on the literal normal closure. -/
theorem quiet_tensor_point_odd_square
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩)) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    ∃ K : Subgroup G, IsQuasisimple (XiQuotient K) ∧
      Nonempty (XiQuotient d.Kz ≃* XiQuotient K × XiQuotient K) ∧
      ∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let P₀ := (P : Subgroup d.X).map d.X.subtype
  have hi : LocalInput 3 (T : Subgroup G) d.X P₀ d.Gz :=
    quiet_tensor_point_localInput D hn e hbase hzV hz1 hzT P
  have hT : IsSylowIn 2 (T : Subgroup G) d.Gz :=
    ⟨T.subtype hzT,map_subgroupOf_eq_of_le hzT⟩
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hsq : IsSQTK KnownSimple.IsKnownSimple d.Gz :=
    D.simpleQTKE.twoLocal_sqtk (isTwoLocal_involution_centralizer hz2)
  let hA := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremA_knownSimple (G := Y)
  let hC := fun (Y : Type _) [Group Y] [Finite Y] => ChapterA.Section02.theoremC_knownSimple (G := Y)
  rcases hi.normal_or_detected_containment hA hC hsq hT with
    hnormal | ⟨K,hK,hKn,hcomm,hPK,hX⟩
  · exact (quiet_tensor_point_residual_not_normal D hmany hmin hn hJ cL e hbase
      hzV hz1 hzT hnormal).elim
  have hKH : componentOrbit K (T : Subgroup G) ≤ d.Gz :=
    (componentOrbit_le_sup K (T : Subgroup G)).trans (sup_le hK.mem.1 hzT)
  have he : d.Kz = componentOrbit K (T : Subgroup G) :=
    Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.normalClosure_eq_of_commutator
      hi.complement_le hX hKH hKn hcomm
  by_cases hTK : (T : Subgroup G) ≤ normalizer (K : Set G)
  · have horbit : componentOrbit K (T : Subgroup G) = K :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer K (T : Subgroup G) K le_rfl hTK)
        (le_componentOrbit K (T : Subgroup G))
    have heK : d.Kz = K := he.trans horbit
    rw [horbit] at hKn hcomm hPK
    have hr := InvariantThree.Source.alternatives_knownSimple hi hsq hT hK.mem.1
      hKn hK.quasisimple hPK hcomm
    have hx := quiet_tensor_point_invariant_exclusions D hn e hbase hzV hz1 hzT P
    change ¬ LinearThreeModel 3 (XiQuotient d.Kz) ∧
      ¬ Nonempty (XiQuotient d.Kz ≃* Sporadic.Mathieu.M11) at hx
    rw [heK] at hx
    rcases hr with ⟨_,hs | ⟨_,hl | hsym | hexc⟩⟩ | ⟨_,_,_,hh⟩
    · exact (hs.1.1 hTK).elim
    · exact (hx.1 hl).elim
    · exact (quiet_tensor_point_automizer_not_cyclic D hn e hbase hzV hz1 hzT P hsym.2).elim
    · rcases hexc.2 with hm | h4 | h5
      · exact (hx.2 hm).elim
      · exact (quiet_tensor_point_binary_excluded D hmany hmin hn hJ cL e hbase
          hzV hz1 hzT P (by dsimp only; rw [heK]; exact hK.mem) (Or.inl rfl)
          (by rw [heK]; exact h4)).elim
      · exact (quiet_tensor_point_binary_excluded D hmany hmin hn hJ cL e hbase
          hzV hz1 hzT P (by dsimp only; rw [heK]; exact hK.mem) (Or.inr rfl)
          (by rw [heK]; exact h5)).elim
    · exact (quiet_tensor_point_held_excluded D hmany hmin hn hJ cL e hbase
        hzV hz1 hzT P (by dsimp only; rw [heK]; exact hK.mem)
        (by rw [heK]; exact hK.quasisimple) (by rw [heK]; exact hh)).elim
  · let hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) d.X P₀ d.Gz K :=
      { toLocalInput := hi
        sqtk := hsq
        component := hK.mem
        quasisimple := hK.quasisimple
        orbit_normal := hKn
        complement_le_orbit := hPK
        orbit_commutator := hcomm
        noncentral := hK.noncentral_component_core
        not_invariant := hTK
        sylow_two := hT }
    refine ⟨K,hK.quasisimple,?_,?_⟩
    · rw [he]
      exact swapped_product hs
    obtain ⟨_,_,hm⟩ := SwappedSylow.embedding_of_theoremsAC hA hC hs
    rcases hm with ⟨n,hnEven,_,hm⟩ | hm
    · have hn0 : n ≠ 0 := by
        intro hn0
        obtain ⟨F,_,_,hF,_⟩ := hm
        have hh := Finite.one_lt_card (α := F)
        simp only [hn0,pow_zero] at hF
        omega
      have hn2 : 2 ≤ n := by obtain ⟨k,hk⟩ := hnEven; omega
      have hnTwo := quiet_tensor_point_binary_degree_two D hmany hmin hn hJ cL e hbase
        hzV hz1 hzT P hs he hn2 hm
      subst n
      obtain ⟨F,_,_,hF,⟨a⟩⟩ := hm
      obtain ⟨b⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
        (by simpa using hF)
      obtain ⟨c⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
      exact ⟨5,by decide,by decide,ZMod 5,inferInstance,inferInstance,by simp,
        ⟨a.trans (b.trans c.symm)⟩⟩
    · exact hm


/-- Every two-perfect three-free subgroup of the original point centralizer
has odd image on K_z/O₂(K_z). The original action, including its kernel,
is used without replacing it by a faithful quotient. -/
theorem quiet_tensor_point_twoPerfect_image_odd
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    (Y : Subgroup G) (hY : Y ≤ centralizer ({z} : Set G))
    (hpY : IsPPerfect 2 Y) (hthree : ¬ 3 ∣ Nat.card Y) :
    let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
    let f := (pCoreNormalizerAction 2 d.Kz).comp
      (inclusion (hY.trans (le_normalizer_conjugateSpanBy d.X d.Gz)))
    Odd (Nat.card f.range) := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  obtain ⟨K,hq,⟨c⟩,p,hp,ho,F,_,_,hF,⟨a⟩⟩ :=
    quiet_tensor_point_odd_square D hmany hmin hn hJ cL e hbase hzV hz1 hzT P
  let : IsQuasisimple (XiQuotient K) := hq
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hcenter,houter⟩ := Theory.PSL2.primeField_center_outer_of_equiv hp ho hF a
  have hz : center (XiQuotient d.Kz) = ⊥ := by
    have hc : center (XiQuotient K × XiQuotient K) = ⊥ := by
      rw [Subgroup.center_prod,hcenter]
      simp
    apply eq_bot_iff.mpr
    intro x hx
    have hh : c x ∈ center (XiQuotient K × XiQuotient K) := (centerCongr c ⟨x,hx⟩).property
    rw [hc] at hh
    exact c.injective ((mem_bot.mp hh).trans c.map_one.symm)
  have hout : IsPGroup 2 (MulAut.Outer (XiQuotient d.Kz)) :=
    (AutomorphismSquare.outer_isPGroup_two hcenter houter).of_equiv (MulAut.outerCongr c).symm
  apply odd_card_automorphism_image_of_twoPerfect _ hz hout hpY hthree
  intro U hpU hUthree
  let b := U.equivMapOfInjective c.toMonoidHom c.injective
  have hm := Theory.PSL2.PrimeThreeFreeResidual.odd_card_square ho hF a
    (U.map c.toMonoidHom) (hpU.of_surjective b.toMonoidHom b.surjective)
    (by rwa [card_map_of_injective c.injective])
  rwa [card_map_of_injective c.injective] at hm

/-- The two-part of every original three-free two-perfect subgroup lies in
S. This is the precise Sylow-placement step used in source 8.3.8. -/
theorem quiet_tensor_point_twoPerfect_sylow_le
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    (Y : Subgroup G) (hY : Y ≤ centralizer ({z} : Set G))
    (hpY : IsPPerfect 2 Y) (hthree : ¬ 3 ∣ Nat.card Y) :
    (T : Subgroup G) ⊓ Y ≤ CentralizerSetup.S ⟨T,localOrbit T L,z⟩ := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let f := (pCoreNormalizerAction 2 d.Kz).comp
    (inclusion (le_normalizer_conjugateSpanBy d.X d.Gz))
  let g := f.comp (inclusion hY)
  have hodd : Odd (Nat.card g.range) :=
    quiet_tensor_point_twoPerfect_image_odd D hmany hmin hn hJ cL e hbase
      hzV hz1 hzT P Y hY hpY hthree
  let A := (T : Subgroup G).subgroupOf Y
  have himage : A.map g = ⊥ := by
    obtain ⟨n,he⟩ := (T.isPGroup'.comap_subtype.map g).exists_card_eq
    change Nat.card (A.map g) = 2 ^ n at he
    have hoddA := hodd.of_dvd_nat (card_dvd_of_le (map_le_range g A))
    have hn0 : n = 0 := by
      by_contra hh
      exact hoddA.not_two_dvd_nat (he ▸ dvd_pow_self 2 hh)
    apply (A.map g).eq_bot_of_card_eq
    rw [he,hn0,pow_zero]
  intro y hy
  apply quiet_tensor_point_action_kernel_sylow_le D hn e hbase hzV hz1 hzT P
  refine ⟨hy.1,⟨y,hY hy.2⟩,?_,rfl⟩
  have hh : g ⟨y,hy.2⟩ ∈ A.map g := mem_map_of_mem g hy.1
  rw [himage] at hh
  exact mem_bot.mp hh


private theorem quiet_tensor_point_hstar_not_three_free
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hHGz : H ≤ centralizer ({z} : Set G)) (hthree : ¬ 3 ∣ Nat.card H) : False := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  let I := (pResidual 2 H).map H.subtype
  let Y := I ⊔ d.S
  have hHI : H ≤ normalizer (I : Set G) := le_normalizer_embedded_pResidual 2 H
  have hTI : (T : Subgroup G) ≤ normalizer (I : Set G) := hH.1.1.2.trans hHI
  have hTS : (T : Subgroup G) ≤ normalizer (d.S : Set G) :=
    le_sup_right.trans (d.XT.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image d.XT (pCore 2 d.XT)))
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    (le_inf hTI hTS).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hHY : H ≤ normalizer (Y : Set G) :=
    (le_embedded_pResidual_sup_sylow_of_normalizes T H
      (hH.1.1.2.trans H.le_normalizer)).trans
      (sup_le (le_sup_left.trans Y.le_normalizer) hTY)
  have hIS : (T : Subgroup G) ⊓ I ≤ d.S :=
    quiet_tensor_point_twoPerfect_sylow_le D hmany hmin hn hJ cL e hbase
      hzV hz1 hzT P I ((map_subtype_le _).trans hHGz) (isPPerfect_embedded_pResidual 2 H)
      (fun hd => hthree (hd.trans (card_dvd_of_le (map_subtype_le _))))
  have hinter : (T : Subgroup G) ⊓ Y = d.S := by
    apply le_antisymm _ (le_inf d.S_le_T le_sup_right)
    rintro y ⟨hyT,hyY⟩
    have hyprod : y ∈ (I : Set G) * (d.S : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ (d.S_le_T.trans hTI)]
      exact hyY
    obtain ⟨i,hi,s,hs,hprod⟩ := hyprod
    have hiT : i ∈ (T : Subgroup G) := by
      have hh := (T : Subgroup G).mul_mem hyT ((T : Subgroup G).inv_mem (d.S_le_T hs))
      rwa [←hprod,mul_inv_cancel_right] at hh
    rw [←hprod]
    exact d.S.mul_mem (hIS ⟨hiT,hi⟩) hs
  have hpos := source_hstar_generation_positive D hH
  have hle := quiet_binaryThree_three_free_hstar_generation_le_one D hmany hmin hn hJ cL hH hthree
  have he : generationParameter H = 1 := by omega
  let R := T.subtype hH.1.1.2
  have hR : (R : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hgen : IsEGeneratedAt 1 R := by
    simpa only [he] using isEGenerated_generationParameter_of_pos hpos R
  apply hH.1.2
  apply NormalSectionContainment.le_of_isEGenerated (Y := Y) (V := D.fullModule) R hgen hHY
  · rw [hR]
    exact (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule
  · rw [hR,hinter]
    exact (quiet_tensor_point_radical_control D hn e hbase hzV hz1 hzT).1
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (source_fullModule_normalizer D).le)
  · intro j hj
    rw [hR,hinter]
    exact quiet_tensor_weakClosure_low D hn e hbase hzV hz1 hzT hj
  · rw [(quiet_tensor_source_parameters D hn e hbase).2.2]
    decide

/-- Every three-free T-invariant subgroup of the original point centralizer
lies in M. Minimal descent supplies an actual H-star; its two-residual has
the required Sylow intersection by the odd-prime square calculation. -/
theorem quiet_tensor_point_three_free_le
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    (Y : Subgroup G) (hY : Y ≤ centralizer ({z} : Set G))
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hthree : ¬ 3 ∣ Nat.card Y) : Y ≤ D.maximalLocal := by
  classical
  by_contra hout
  let J := Y ⊔ (T : Subgroup G)
  have hJz : J ≤ centralizer ({z} : Set G) := sup_le hY hzT
  have hJout : ¬ J ≤ D.maximalLocal := fun hh => hout (le_sup_left.trans hh)
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian z hzV) hz1
  have hzTmem : z ∈ (T : Subgroup G) :=
    D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D) hzV
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hz2,pow_one])
  have hzJ : zpowers z ≤ J := (zpowers_le.mpr hzTmem).trans le_sup_right
  have hJn : J ≤ normalizer (zpowers z : Set G) := by
    calc
      J ≤ centralizer ({z} : Set G) := hJz
      _ = centralizer (zpowers z : Set G) := by rw [zpowers_eq_closure,centralizer_closure]
      _ ≤ normalizer (zpowers z : Set G) := Subgroup.centralizer_le_normalizer _
  have hJH : J ∈ Chapter1.H G := by
    intro hzero
    have hzcore := le_pCoreIn_of_normalizes hp hzJ hJn (mem_zpowers z)
    exact hz1 (mem_bot.mp (hzero ▸ hzcore))
  let family : Set (Subgroup G) :=
    {H | (H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ D.maximalLocal) ∧ H ≤ J}
  have hmem : J ∈ family := ⟨⟨⟨hJH,(show (T : Subgroup G) ≤ J from le_sup_right)⟩,hJout⟩,le_rfl⟩
  obtain ⟨H,hH⟩ := (Set.toFinite family).exists_minimalFor id family ⟨J,hmem⟩
  have hstar : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal :=
    ⟨hH.1.1,fun B hB hBH => hH.2 ⟨hB,hBH.trans hH.1.2⟩ hBH⟩
  have hthreeJ : ¬ 3 ∣ Nat.card J := by
    intro hd
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes Y (T : Subgroup G) hTY
    have hdiv : 3 ∣ Nat.card Y * Nat.card (T : Subgroup G) := by
      rw [hprod]
      exact dvd_mul_of_dvd_right hd _
    rcases Nat.prime_three.dvd_mul.mp hdiv with hY3 | hT3
    · exact hthree hY3
    · obtain ⟨n,he⟩ := T.isPGroup'.exists_card_eq
      rw [he] at hT3
      exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hT3)
  exact quiet_tensor_point_hstar_not_three_free D hmany hmin hn hJ cL e hbase
    hzV hz1 hzT P hstar (hH.1.2.trans hJz)
    (fun hd => hthreeJ (hd.trans (card_dvd_of_le hH.1.2)))

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
