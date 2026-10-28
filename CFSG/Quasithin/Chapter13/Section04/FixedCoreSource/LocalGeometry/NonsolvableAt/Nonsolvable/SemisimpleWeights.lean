module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.SemisimpleWeights
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.PointCoreSocle
public import Theory.Representation.PSL3Two.NaturalDualFlags

/-!
# The semisimple linear row of the original nonsolvable pair: structure at the original group

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

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/SemisimpleWeights` proof for the local step.
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

/-- Apply the two model containments to the original escaping vector
and the fixed line C_V(L). -/
theorem original_semisimple_weight_and_commutator_at
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
    le_inf (LocalGeometry.fixed_le_original_omegaCenter_at h structural D m)
      (le_centralizer_iff.mp (hBM.trans (normalizer_component_le_fixed_centralizer_at h structural D m)))
  exact ⟨hwtest.mp (geo.2 hzA),hF.trans geo.1⟩

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
