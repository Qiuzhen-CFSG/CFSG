module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.LineCoreSocle
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.PointCoreSocle
public import Theory.Representation.PSL3Two.FanoFlagDuality

/-!
# The line-core socle row of the original nonsolvable pair: structure at the original group

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

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/LineCoreSocle` proof for the local step.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Representation.BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The original escaping vector has weight four, and the original fixed
line is outside the full H₀ socle and opposite residual commutator. -/
theorem original_line_core_weight_and_socle_at
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
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
    · exact le_inf (LocalGeometry.fixed_le_original_omegaCenter_at h structural D m)
        (le_centralizer_iff.mp (hBM.trans (normalizer_component_le_fixed_centralizer_at h structural D m)))
    · have hf := Solvable.original_second_flag_fixed D m W hW hTW
      rw [←hB] at hf
      intro v hv
      apply hf.le
      exact ⟨hZV hv.1,centralizer_le (map_subtype_le (pResidual 2 B)) hv.2⟩
  rw [hF]
  exact ⟨hwtest.mp (geo.1 hzA),geo.2.1,geo.2.2.2⟩

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
