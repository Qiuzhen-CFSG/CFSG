module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.PointCoreSocle
public import Theory.Representation.PSL3Two.NaturalDualFlags

/-!
# The semisimple linear row of the original nonsolvable pair

The natural-plus-dual model has both marked fixed lines in the opposite
flag commutator. The original component supplements the two-core of H₀,
which centralizes V₀. Thus the literal H₂,L₂T residual commutators have
these same containments. The original weight criterion gives weight four
for z. For either natural component C_V(L) lies in V_K, and for the
five-dimensional A₆ component its generator has weight four.

These prove the semisimple linear case of 13.4.14(1) under the retained
earlier source inputs and the corresponding branch of whole-module
recognition. The product case has its separate established proofs.
Source: Aschbacher–Smith 13.4.14, printed p.911, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Representation.BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

private theorem omega_commutator_residual (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P) :
    ⁅omegaOneCenterAmbient (T : Subgroup G),P⁆ =
      ⁅omegaOneCenterAmbient (T : Subgroup G),(pResidual 2 P).map P.subtype⁆ := by
  apply le_antisymm ?_ (commutator_mono le_rfl (map_subtype_le _))
  rw [commutator_comm,commutator_comm _ ((pResidual 2 P).map P.subtype)]
  apply commutator_le.mpr
  intro p hp z hz
  obtain ⟨k,hk,t,ht,hkt⟩ := mem_sup_of_normal_left.mp
    ((pResidual_sup_sylow_eq_top (T.subtype hTP)) ▸ mem_top (⟨p,hp⟩ : P))
  have he : k.val*t.val = p := congrArg Subtype.val hkt
  have hzfix : t.val*z*t.val⁻¹ = z := mul_inv_eq_iff_eq_mul.mpr
    (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t.val ht)
  have hec : ⁅p,z⁆ = ⁅k.val,z⁆ := by
    rw [←he,commutatorElement_def,commutatorElement_def,mul_inv_rev]
    calc
      k.val*t.val*z*(t.val⁻¹*k.val⁻¹)*z⁻¹ =
          k.val*(t.val*z*t.val⁻¹)*k.val⁻¹*z⁻¹ := by group
      _ = _ := by rw [hzfix]
  rw [hec]
  exact commutator_mem_commutator (mem_map_of_mem P.subtype hk) hz

/-- Both opposite residual-commutator containments in the original pair. -/
theorem original_pair_semisimple_geometry
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hiA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))
    (q : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      BinaryLinearThree.Group)
    (hqA : (A.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL)
    (hqB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL)
    (hqT : ((T : Subgroup G).subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL)
    (E : let := he
      let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
      Representation.Equiv ((BinaryLinearThree.W.prod BinaryLinearThree.W.dual).comp
        (q.toMonoidHom.comp (QuotientGroup.mk' _)))
        (elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans
            (le_normalizer_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B))))))) :
    let := he
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    Z ⊓ centralizer (B : Set G) ≤ ⁅Z,(pResidual 2 A).map A.subtype⁆ ∧
    Z ⊓ centralizer (A : Set G) ≤ ⁅Z,(pResidual 2 B).map B.subtype⁆ := by
  let := he
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z X
  let C := K.map X.subtype
  let Q := X.pCoreIn 2
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  change (A.subgroupOf C).map f = _ at hqA
  change (B.subgroupOf C).map f = _ at hqB
  change ((T : Subgroup G).subgroupOf C).map f = _ at hqT
  have hUX : U ≤ X := conjugateSpanBy_le_self (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
  have hXU := le_normalizer_conjugateSpanBy Z X
  have hker := Amalgam.original_pair_action_kernel h₀ D m hTA hTB eA eB hne hiA hiB
  have hUT : U ≤ (T : Subgroup G) := by
    have huq : U ≤ Q := by
      intro x hx
      exact mem_map_of_mem X.subtype (hker.1.le_pCore (show (⟨x,hUX hx⟩ : X) ∈ U.subgroupOf X from hx))
    exact huq.trans (hker.2.2.2.symm.le.trans inf_le_left)
  have hQT : Q ≤ (T : Subgroup G) := hker.2.2.2.symm.le.trans inf_le_left
  have hQU : Q ≤ centralizer (U : Set G) := hker.2.2.2.symm.le.trans inf_le_right
  have hgen : C ⊔ Q = X := (Amalgam.original_pair_linear_core_supplement
    h₀ D m h1332 hTA hTB eA eB hne hiA hiB K hK eK).2
  let : (Q.subgroupOf X).Normal := by
    change ((X.pCoreIn 2).subgroupOf X).Normal
    change (((pCore 2 X).map X.subtype).comap X.subtype).Normal
    rw [comap_map_eq_self_of_injective X.subtype_injective]
    infer_instance
  have reps (P : Subgroup G) (hPX : P ≤ X) (hQP : Q ≤ P) :=
    centralizing_supplement_representatives X C Q U P (map_subtype_le K) (pCoreIn_le 2 X)
      hgen hQU hPX hQP
  have hZ : U ⊓ centralizer (T : Set G) = Z := by
    apply le_antisymm
    · intro z hz
      exact (mem_omegaOneCenterAmbient_iff _ _).mpr ⟨hUT hz.1,
        elemPow_eq_one_of_isElementaryAbelian _ hz.1,hz.2⟩
    · exact le_inf (le_conjugateSpanBy Z X) (fun _ hz =>
        ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
  have hfix (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P) :
      U ⊓ centralizer (P : Set G) = Z ⊓ centralizer (P : Set G) := by
    apply le_antisymm
    · intro x hx
      exact ⟨hZ ▸ ⟨hx.1,centralizer_le hTP hx.2⟩,hx.2⟩
    · exact inf_le_inf_right _ (le_conjugateSpanBy Z X)
  let S := modelSpace U C ((map_subtype_le K).trans hXU) f (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) E
  have sZ : S Z = fixedSpace (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) Matrix.PSL3Two.borelSL := by
    have hs := modelSpace_fixed U C ((map_subtype_le K).trans hXU) f (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) E
      (T : Subgroup G) (reps (T : Subgroup G) (hTA.trans le_sup_left) hQT)
    change S (U ⊓ centralizer (T : Set G)) =
      fixedSpace (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) (((T : Subgroup G).subgroupOf C).map f) at hs
    rw [hZ,hqT] at hs
    exact hs
  have sA : S (Z ⊓ centralizer (A : Set G)) =
      fixedSpace (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) Matrix.PSL3Two.pointParabolicSL := by
    dsimp only [S]
    rw [←hfix A hTA,modelSpace_fixed U C ((map_subtype_le K).trans hXU) f (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) E A (reps A le_sup_left (hQT.trans hTA)),hqA]
  have sB : S (Z ⊓ centralizer (B : Set G)) =
      fixedSpace (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) Matrix.PSL3Two.lineParabolicSL := by
    dsimp only [S]
    rw [←hfix B hTB,modelSpace_fixed U C ((map_subtype_le K).trans hXU) f (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) E B (reps B le_sup_right (hQT.trans hTB)),hqB]
  have sCA := modelSpace_commutator U C ((map_subtype_le K).trans hXU) f
    (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) E Z A (le_conjugateSpanBy Z X) (le_sup_left.trans hXU)
    (reps A le_sup_left (hQT.trans hTA))
  have sCB := modelSpace_commutator U C ((map_subtype_le K).trans hXU) f
    (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) E Z B (le_conjugateSpanBy Z X) (le_sup_right.trans hXU)
    (reps B le_sup_right (hQT.trans hTB))
  change S ⁅Z,A⁆ = subspaceCommutator (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) (S Z) ((A.subgroupOf C).map f) at sCA
  change S ⁅Z,B⁆ = subspaceCommutator (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) (S Z) ((B.subgroupOf C).map f) at sCB
  rw [sZ,hqA] at sCA
  rw [sZ,hqB] at sCB
  have hcU (P : Subgroup G) (hPX : P ≤ X) : ⁅Z,P⁆ ≤ U :=
    (commutator_mono (le_conjugateSpanBy Z X) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hPX.trans hXU))
  have transfer (P R : Subgroup G) (hPU : P ≤ U) (hRU : R ≤ U) : S P ≤ S R ↔ P ≤ R :=
    modelSpace_le_iff U C ((map_subtype_le K).trans hXU) f (BinaryLinearThree.W.prod BinaryLinearThree.W.dual) E hPU hRU
  have tests := BinaryLinearThree.NaturalDualFlags.flag_tests
  have h₁ : Z ⊓ centralizer (B : Set G) ≤ ⁅Z,A⁆ :=
    (transfer _ _ (inf_le_left.trans (le_conjugateSpanBy Z X)) (hcU A le_sup_left)).mp
      (by rw [sB,sCA]; exact tests.1)
  have h₂ : Z ⊓ centralizer (A : Set G) ≤ ⁅Z,B⁆ :=
    (transfer _ _ (inf_le_left.trans (le_conjugateSpanBy Z X)) (hcU B le_sup_right)).mp
      (by rw [sA,sCB]; exact tests.2)
  rw [omega_commutator_residual A hTA] at h₁
  rw [omega_commutator_residual B hTB] at h₂
  exact ⟨h₁,h₂⟩

/-- Apply the two model containments to the original escaping vector
and the fixed line C_V(L). -/
theorem original_semisimple_weight_and_commutator
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hiA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))
    (q : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      BinaryLinearThree.Group)
    (hqA : (A.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL)
    (hqB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL)
    (hqT : ((T : Subgroup G).subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL)
    (E : let := he
      let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
      Representation.Equiv ((BinaryLinearThree.W.prod BinaryLinearThree.W.dual).comp
        (q.toMonoidHom.comp (QuotientGroup.mk' _)))
        (elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans
            (le_normalizer_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))))))
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hAz : A ≤ centralizer ({z.val} : Set G))
 :
    m.weight z = 4 ∧
    V ⊓ centralizer (L : Set G) ≤
      ⁅omegaOneCenterAmbient (T : Subgroup G),(pResidual 2 A).map A.subtype⁆ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have geo := original_pair_semisimple_geometry h₀ D m h1332 hTA hTB eA eB hne
    hiA hiB K hK eK he q hqA hqB hqT E
  have hz1 : z ≠ 1 := fun heq => hzL (congrArg Subtype.val heq ▸ one_mem _)
  have hzA : z.val ∈ Z ⊓ centralizer (A : Set G) :=
    ⟨hzT,fun a ha => (hAz ha z.val (Set.mem_singleton _)).symm⟩
  have hwtest := original_omega_residual_weight_iff D m hZV W hW hTW z hzT hz1
  rw [←hB] at hwtest
  have hBM : B ≤ normalizer (L : Set G) := by rw [hB,hM]; exact inf_le_left
  have hF : V ⊓ centralizer (L : Set G) ≤ Z ⊓ centralizer (B : Set G) :=
    le_inf (Solvable.fixed_le_original_omegaCenter h structural D m)
      (le_centralizer_iff.mp (hBM.trans (normalizer_component_le_fixed_centralizer h structural D m)))
  exact ⟨hwtest.mp (geo.2 hzA),hF.trans geo.1⟩

/-- Both weights are four in the five-dimensional ordinary component row. -/
theorem ordinary_semisimple_both_weights
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hiA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))
    (q : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      BinaryLinearThree.Group)
    (hqA : (A.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL)
    (hqB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL)
    (hqT : ((T : Subgroup G).subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL)
    (E : let := he
      let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
      Representation.Equiv ((BinaryLinearThree.W.prod BinaryLinearThree.W.dual).comp
        (q.toMonoidHom.comp (QuotientGroup.mk' _)))
        (elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans
            (le_normalizer_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))))))
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hAz : A ≤ centralizer ({z.val} : Set G))
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (N : Subgroup G)
    (hN : N ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (N : Set G))
    (hNM : ¬ N ≤ normalizer (L : Set G))
    (hfN : N ∈ MainForward.faithfulLocalComponents T)
    (eN : (N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 6))
    (hfixedN : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) N,N⁆ :
      Subgroup G) ⊓ centralizer (N : Set G) ≠ ⊥)
    (hA : A ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    m.weight z = 4 ∧
    ∃ DN : ChosenModule T N ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) N,N⁆,
      ∃ mN : CoreMarking DN, ∃ hd : m.constant.val ∈
        ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) N,N⁆,
        mN.weight ⟨m.constant.val,hd⟩ = 4 := by
  have hs := original_semisimple_weight_and_commutator h₀ D m h1332 hTA hTB eA eB hne
    hiA hiB K hK eK he q hqA hqB hqT E h structural hM hZV W hW hTW hB
    z hzT hzL hAz
  obtain ⟨DN,mN,hd,_,_,_,_,_,_,P,hP,hPH,_,_,_,htest,_⟩ :=
    ordinary_six_original_reciprocal_weight_detection h₀ h structural modules D m
      h1332 fixed hindex hM z hzT hzL hN hHN hNM hfN eN hfixedN
  obtain ⟨P₀,_,_,_,_,_,_,_,_,_,_,_,_,hunique⟩ :=
    ordinary_six_full_centralizer_parabolic h₀ h structural modules D m h1332 fixed
      hindex hM z hzT hzL hN hHN hNM hfN eN
  have hAP : A = P := (hunique A hA hAz).trans (hunique P hP hPH.le).symm
  refine ⟨hs.1,DN,mN,hd,htest.mp ?_⟩
  rw [←hAP]
  exact hs.2

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- For either recognized natural component, the same semisimple H₀ model
places the original fixed line in V_N. The independent large-distance input
remains explicit, as in the preceding component recognition. -/
theorem natural_semisimple_weight_and_membership
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hiA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL)
    (he : IsElementaryAbelian 2 (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))
    (q : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      BinaryLinearThree.Group)
    (hqA : (A.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL)
    (hqB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL)
    (hqT : ((T : Subgroup G).subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL)
    (E : let := he
      let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
      Representation.Equiv ((BinaryLinearThree.W.prod BinaryLinearThree.W.dual).comp
        (q.toMonoidHom.comp (QuotientGroup.mk' _)))
        (elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans
            (le_normalizer_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)))))))
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hAz : A ≤ centralizer ({z.val} : Set G))
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (N : Subgroup G)
    (hN : N ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (N : Set G))
    (hNM : ¬ N ≤ normalizer (L : Set G))
    (hfN : N ∈ MainForward.faithfulLocalComponents T)
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (model : Nonempty ((N ⧸ pCore 2 N) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 6)))
    (hfixedN : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) N,N⁆ :
      Subgroup G) ⊓ centralizer (N : Set G) = ⊥)
    (hA : A ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    m.weight z = 4 ∧ V ⊓ centralizer (L : Set G) ≤
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) N,N⁆ := by
  have hs := original_semisimple_weight_and_commutator h₀ D m h1332 hTA hTB eA eB hne
    hiA hiB K hK eK he q hqA hqB hqT E h structural hM hZV W hW hTW hB
    z hzT hzL hAz
  have hv := (small_component_natural_residual_fixed_iff hl h₀ h structural modules D m
    h1332 fixed hindex hM z hzT hzL hN hHN hNM hfN model hfixedN A hA hAz).mp hs.2
  exact ⟨hs.1,hv⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
