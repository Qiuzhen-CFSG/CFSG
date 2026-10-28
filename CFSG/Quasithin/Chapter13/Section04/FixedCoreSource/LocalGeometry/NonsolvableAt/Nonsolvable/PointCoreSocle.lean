module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CentralFourAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.PointCoreSocle
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OriginalResidualWeights
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearFullQuotient
public import Theory.Representation.BinaryConjugationCoordinates.SupplementSpaces
public import Theory.Representation.PSL3Two.FanoSocleFlags

/-!
# The point-core socle row of the original nonsolvable pair: structure at the original group

For H₀=H₂ join L₂T with the actual point-core module for its L₃(2)
component, the same quotient marking sends H₂, L₂T and T to the point
parabolic, line parabolic and flag Sylow. The centralizing two-core
supplement transports the Fano fixed spaces, seed commutators and socle
to the full original H₀ action on V₀=⟨Ω₁Z(T)^H₀⟩.

Consequently C_Z(L₂T) lies in Soc(V₀) and [Z,O²(H₂)], while C_Z(H₂)
lies in neither Soc(V₀) nor [Z,L₂]. The original five-dimensional weight
test forces z to have weight two. In both natural component rows C_V(L)
lies in V_K. In the five-dimensional ordinary A₆ row the same fixed
line has weight four in V_K: original outside-parabolic uniqueness
identifies the reciprocal weight test with H₂, rather than changing the
chosen actor or quotient map.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/PointCoreSocle` proof for the local step.
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

/-- Apply the point-core row to the literal Sylow-normalized second plane
and an escaping original centralizer. The weight test forces weight two,
and the original fixed line lies in both the full H₀ socle and [Z,O²(A)].
The whole-seed premise is supplied by either recognized component row. -/
theorem original_point_core_weight_and_socle_at
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
      Representation.Equiv (BinaryLinearThree.U₂.comp
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
    (hAM : ¬ A ≤ normalizer (L : Set G)) :
    let := he
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z (A ⊔ B)
    let ρ := elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z (A ⊔ B))))
    m.weight z = 2 ∧
    V ⊓ centralizer (L : Set G) ≤ ⁅Z,(pResidual 2 A).map A.subtype⁆ ∧
    binarySpace ((V ⊓ centralizer (L : Set G)).subgroupOf U) ≤
      (sSup {N : Subrepresentation ρ | IsAtom N}).toSubmodule := by
  let := he
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have geo := original_pair_point_core_geometry h₀ D m h1332 hTA hTB eA eB hne
    hiA hiB K hK eK he q hqA hqB hqT E
  have hz1 : z ≠ 1 := fun heq => hzL (congrArg Subtype.val heq ▸ one_mem _)
  have hfixA := m.central_four_fixed_of_escape_at h structural z hz1 hzT A hAz hAM
  rw [inf_eq_right.mpr hZV] at hfixA
  have hn : z.val ∉ ⁅Z,(pResidual 2 B).map B.subtype⁆ := by
    intro hz
    apply geo.2.1
    rw [hfixA]
    exact zpowers_le.mpr hz
  have hwtest := original_omega_residual_weight_iff D m hZV W hW hTW z hzT hz1
  rw [←hB] at hwtest
  have hw : m.weight z = 2 := by
    have hn4 : m.weight z ≠ 4 := fun hh => hn (hwtest.mpr hh)
    exact (m.nonfixed_weight z hzL).resolve_right hn4
  have hBM : B ≤ normalizer (L : Set G) := by rw [hB,hM]; exact inf_le_left
  have hF : V ⊓ centralizer (L : Set G) ≤ Z ⊓ centralizer (B : Set G) :=
    le_inf (LocalGeometry.fixed_le_original_omegaCenter_at h structural D m)
      (le_centralizer_iff.mp (hBM.trans (normalizer_component_le_fixed_centralizer_at h structural D m)))
  refine ⟨hw,hF.trans geo.1,?_⟩
  exact fun v hv => geo.2.2.1 (hF hv)

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
