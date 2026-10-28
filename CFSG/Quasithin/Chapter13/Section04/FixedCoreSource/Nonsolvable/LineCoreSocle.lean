module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.PointCoreSocle
public import Theory.Representation.PSL3Two.FanoFlagDuality

/-!
# The line-core socle row of the original nonsolvable pair

Flag-preserving core duality exchanges the two parabolics and allows the
point-core socle calculation to apply to the line core. The full original
H₀ action and all original quotient maps are retained. The escaping vector
has weight four; C_V(L) lies outside both the socle and [Z,O²(H₂)].

For either natural component module, the established residual criterion
therefore excludes C_V(L) from V_K. For a five-dimensional A₆ component,
outside-parabolic uniqueness identifies the same residual criterion and
forces weight two for the original fixed generator. These are exactly the
line-core clauses of 13.4.14(2i), conditional on the retained earlier
source inputs and the corresponding branch of the proved whole-module
recognition. Semisimple rows and final nonsolvable assembly remain separate.
Source: Aschbacher–Smith 13.4.14, printed p.911; H.5, pp.385–386,
refs/quasithin.pdf.
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

private theorem reversed_point_core_geometry
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
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL)
    (hqB : (B.subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL)
    (hqT : ((T : Subgroup G).subgroupOf (K.map (A ⊔ B).subtype)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL)
    (E : let := he
      let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
      Representation.Equiv (BinaryLinearThree.U₂.comp
        (q.toMonoidHom.comp (QuotientGroup.mk' _)))
        (elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans
            (le_normalizer_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B))))))) :
    let := he
    let X := A ⊔ B
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z X
    let ρ := elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z X)))
    let Soc := (sSup {N : Subrepresentation ρ | IsAtom N}).toSubmodule
    Z ⊓ centralizer (A : Set G) ≤ ⁅Z,(pResidual 2 B).map B.subtype⁆ ∧
    ¬ Z ⊓ centralizer (B : Set G) ≤ ⁅Z,(pResidual 2 A).map A.subtype⁆ ∧
    binarySpace ((Z ⊓ centralizer (A : Set G)).subgroupOf U) ≤ Soc ∧
    ¬ binarySpace ((Z ⊓ centralizer (B : Set G)).subgroupOf U) ≤ Soc := by
  revert K hK eK he q hqA hqB hqT E
  rw [sup_comm A B]
  intro K hK eK he q hqA hqB hqT E
  exact original_pair_point_core_geometry h₀ D m h1332 hTB hTA eB eA hne.symm
    hiB hiA K hK eK he q hqB hqA hqT E

/-- Both literal fixed-line, residual-commutator and full-actor socle tests
for the line-core branch under one marking of the original pair. -/
theorem original_pair_line_core_geometry
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
      Representation.Equiv (BinaryLinearThree.FanoDecomposition.lineCoreRepresentation.comp
        (q.toMonoidHom.comp (QuotientGroup.mk' _)))
        (elementaryRepresentation (p := 2) (U.normalizerMonoidHom.comp
          (inclusion ((map_subtype_le K).trans
            (le_normalizer_conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B))))))) :
    let := he
    let X := A ⊔ B
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z X
    let ρ := elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z X)))
    let Soc := (sSup {N : Subrepresentation ρ | IsAtom N}).toSubmodule
    Z ⊓ centralizer (A : Set G) ≤ ⁅Z,(pResidual 2 B).map B.subtype⁆ ∧
    ¬ Z ⊓ centralizer (B : Set G) ≤ ⁅Z,(pResidual 2 A).map A.subtype⁆ ∧
    binarySpace ((Z ⊓ centralizer (A : Set G)).subgroupOf U) ≤ Soc ∧
    ¬ binarySpace ((Z ⊓ centralizer (B : Set G)).subgroupOf U) ≤ Soc := by
  let := he
  let C := K.map (A ⊔ B).subtype
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  let q' := q.trans Matrix.PSL3Two.flagDuality
  have hA : (A.subgroupOf C).map
      (q'.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.lineParabolicSL := by
    change (A.subgroupOf C).map (Matrix.PSL3Two.flagDuality.toMonoidHom.comp f) = _
    rw [←map_map,hqA,Matrix.PSL3Two.flagDuality_map_point]
  have hB : (B.subgroupOf C).map
      (q'.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.pointParabolicSL := by
    change (B.subgroupOf C).map (Matrix.PSL3Two.flagDuality.toMonoidHom.comp f) = _
    rw [←map_map,hqB,Matrix.PSL3Two.flagDuality_map_line]
  have hT : ((T : Subgroup G).subgroupOf C).map
      (q'.toMonoidHom.comp (QuotientGroup.mk' _)) = Matrix.PSL3Two.borelSL := by
    change ((T : Subgroup G).subgroupOf C).map (Matrix.PSL3Two.flagDuality.toMonoidHom.comp f) = _
    rw [←map_map,hqT,Matrix.PSL3Two.flagDuality_map_borel]
  exact reversed_point_core_geometry h₀ D m h1332 hTA hTB eA eB hne hiA hiB
    K hK eK he q' hA hB hT
      ((BinaryLinearThree.FanoDecomposition.flagCoreDuality_comp f).trans E)


/-- The original escaping vector has weight four, and the original fixed
line is outside the full H₀ socle and opposite residual commutator. -/
theorem original_line_core_weight_and_socle
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
      Representation.Equiv (BinaryLinearThree.FanoDecomposition.lineCoreRepresentation.comp
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
    let := he
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z (A ⊔ B)
    let ρ := elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z (A ⊔ B))))
    m.weight z = 4 ∧
    ¬ V ⊓ centralizer (L : Set G) ≤ ⁅Z,(pResidual 2 A).map A.subtype⁆ ∧
    ¬ binarySpace ((V ⊓ centralizer (L : Set G)).subgroupOf U) ≤
      (sSup {N : Subrepresentation ρ | IsAtom N}).toSubmodule := by
  let := he
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have geo := original_pair_line_core_geometry h₀ D m h1332 hTA hTB eA eB hne
    hiA hiB K hK eK he q hqA hqB hqT E
  have hz1 : z ≠ 1 := fun heq => hzL (congrArg Subtype.val heq ▸ one_mem _)
  have hzA : z.val ∈ Z ⊓ centralizer (A : Set G) :=
    ⟨hzT,fun a ha => (hAz ha z.val (Set.mem_singleton _)).symm⟩
  have hwtest := original_omega_residual_weight_iff D m hZV W hW hTW z hzT hz1
  rw [←hB] at hwtest
  have hBM : B ≤ normalizer (L : Set G) := by rw [hB,hM]; exact inf_le_left
  have hF : V ⊓ centralizer (L : Set G) = Z ⊓ centralizer (B : Set G) := by
    apply le_antisymm
    · exact le_inf (Solvable.fixed_le_original_omegaCenter h structural D m)
        (le_centralizer_iff.mp (hBM.trans (normalizer_component_le_fixed_centralizer h structural D m)))
    · have hf := Solvable.original_second_flag_fixed D m W hW hTW
      rw [←hB] at hf
      intro v hv
      apply hf.le
      exact ⟨hZV hv.1,centralizer_le (map_subtype_le (pResidual 2 B)) hv.2⟩
  rw [hF]
  exact ⟨hwtest.mp (geo.1 hzA),geo.2.1,geo.2.2.2⟩

/-- The five-dimensional ordinary A₆ row has the opposite pair of weights,
four in V and two for the original fixed generator in V_N. -/
theorem ordinary_line_core_both_weights
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
      Representation.Equiv (BinaryLinearThree.FanoDecomposition.lineCoreRepresentation.comp
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
    let := he
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U₀ := conjugateSpanBy Z (A ⊔ B)
    let U := ⁅conjugateSpanBy Z N,N⁆
    let ρ := elementaryRepresentation (p := 2)
      (U₀.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z (A ⊔ B))))
    m.weight z = 4 ∧
    ¬ binarySpace ((V ⊓ centralizer (L : Set G)).subgroupOf U₀) ≤
      (sSup {S : Subrepresentation ρ | IsAtom S}).toSubmodule ∧
    ∃ DN : ChosenModule T N U, ∃ mN : CoreMarking DN, ∃ hd : m.constant.val ∈ U,
      mN.weight ⟨m.constant.val,hd⟩ = 2 := by
  have hs := original_line_core_weight_and_socle h₀ D m h1332 hTA hTB eA eB hne
    hiA hiB K hK eK he q hqA hqB hqT E h structural hM hZV W hW hTW hB
    z hzT hzL hAz
  obtain ⟨DN,mN,hd,_,_,_,_,_,_,P,hP,hPH,_,_,_,_,htest⟩ :=
    ordinary_six_original_reciprocal_weight_detection h₀ h structural modules D m
      h1332 fixed hindex hM z hzT hzL hN hHN hNM hfN eN hfixedN
  obtain ⟨P₀,_,_,_,_,_,_,_,_,_,_,_,_,hunique⟩ :=
    ordinary_six_full_centralizer_parabolic h₀ h structural modules D m h1332 fixed
      hindex hM z hzT hzL hN hHN hNM hfN eN
  have hAP : A = P := (hunique A hA hAz).trans (hunique P hP hPH.le).symm
  refine ⟨hs.1,hs.2.2,DN,mN,hd,htest.mp ?_⟩
  rw [←hAP]
  exact hs.2.1

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

/-- For either recognized natural component, the same line-core H₀ model
excludes the original fixed line from V_N. The independent large-distance input
remains explicit, as in the preceding component recognition. -/
theorem natural_line_core_weight_and_membership
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
      Representation.Equiv (BinaryLinearThree.FanoDecomposition.lineCoreRepresentation.comp
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
    let := he
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U₀ := conjugateSpanBy Z (A ⊔ B)
    let U := ⁅conjugateSpanBy Z N,N⁆
    let ρ := elementaryRepresentation (p := 2)
      (U₀.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z (A ⊔ B))))
    m.weight z = 4 ∧ ¬ V ⊓ centralizer (L : Set G) ≤ U ∧
    ¬ binarySpace ((V ⊓ centralizer (L : Set G)).subgroupOf U₀) ≤
      (sSup {S : Subrepresentation ρ | IsAtom S}).toSubmodule := by
  have hs := original_line_core_weight_and_socle h₀ D m h1332 hTA hTB eA eB hne
    hiA hiB K hK eK he q hqA hqB hqT E h structural hM hZV W hW hTW hB
    z hzT hzL hAz
  have hv : ¬ V ⊓ centralizer (L : Set G) ≤ ⁅conjugateSpanBy
      (omegaOneCenterAmbient (T : Subgroup G)) N,N⁆ := by
    intro hh
    exact hs.2.1 ((small_component_natural_residual_fixed_iff hl h₀ h structural modules D m
      h1332 fixed hindex hM z hzT hzL hN hHN hNM hfN model hfixedN A hA hAz).mpr hh)
  exact ⟨hs.1,hv,hs.2.2⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
