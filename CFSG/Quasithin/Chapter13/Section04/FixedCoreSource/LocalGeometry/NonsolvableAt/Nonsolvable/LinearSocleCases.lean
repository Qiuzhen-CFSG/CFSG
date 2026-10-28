module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearWholeModuleAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.LineCoreSocle
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.PointCoreSocle
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.SemisimpleWeights
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.LinearSocleCases
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.SemisimpleWeights
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.LineCoreSocle
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearWholeModule

/-!
# Weight and socle alternatives for the original nonsolvable pair: structure at the original group

Whole-module recognition supplies one of the three actual six-dimensional
linear models under one quotient marking. Applying the semisimple, point-core
and line-core calculations gives the original weight, residual commutator
and full-H₀ socle alternatives without an additional chosen-model premise.

The source application constructs the original H₂,L₂T pair for either
recognized component row. It obtains the whole omega-center containment
from that recognition, applies the earlier plane amalgam, and discharges
all local hypotheses of the linear alternatives. The product alternative
retains its weight-four and component-commutator bounds. The companion
LineCoreSocle and SemisimpleWeights theorems give the component membership
and reciprocal five-dimensional weights in their respective rows.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/LinearSocleCases` proof for the local step.
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

/-- Exhaust all three linear models and transfer their weight and socle
conclusions to the original full actor and its literal residual. -/
theorem original_linear_weight_socle_alternatives_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hiA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hiB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
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
    (hAM : ¬ A ≤ normalizer (L : Set G))
    (hindex : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B)) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let U := conjugateSpanBy Z (A ⊔ B)
    let F := V ⊓ centralizer (L : Set G)
    let R := ⁅Z,(pResidual 2 A).map A.subtype⁆
    ∃ he : IsElementaryAbelian 2 U, let := he
      let ρ := elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy Z (A ⊔ B))))
      let Soc := (sSup {S : Subrepresentation ρ | IsAtom S}).toSubmodule
      Nat.card U = 64 ∧
      ((m.weight z = 4 ∧ F ≤ R) ∨
       (m.weight z = 2 ∧ F ≤ R ∧ binarySpace (F.subgroupOf U) ≤ Soc) ∨
       (m.weight z = 4 ∧ ¬ F ≤ R ∧ ¬ binarySpace (F.subgroupOf U) ≤ Soc)) := by
  let X := A ⊔ B
  obtain ⟨C,hC,_,_,_,_,⟨eC⟩⟩ := hlin.1
  let K := C.subgroupOf X
  have hmap : K.map X.subtype = C := map_subgroupOf_eq_of_le hC.1
  have eK : ((K.map X.subtype) ⧸ pCore 2 (K.map X.subtype)) ≃* Matrix.PSL3Two.PSL :=
    hmap.symm ▸ eC
  obtain ⟨he,q,hqA,hqB,hqT,hm,hcard⟩ := Amalgam.original_pair_linear_whole_module_at
    h₀ h structural D m hTA hTB eA eB hne (fun hx => hAM (le_sup_left.trans hx))
    hindex hiA hiB hres h1332 K hC.2 eK
  refine ⟨he,hcard,?_⟩
  rcases hm with hm | hm | hm
  · exact Or.inl (original_semisimple_weight_and_commutator_at h₀ D m h1332 hTA hTB eA eB
      hne hiA hiB K hC.2 eK he q hqA hqB hqT hm.some h structural hM hZV W hW hTW hB
      z hzT hzL hAz)
  · exact Or.inr (Or.inl (original_point_core_weight_and_socle_at h₀ D m h1332 hTA hTB
      eA eB hne hiA hiB K hC.2 eK he q hqA hqB hqT hm.some h structural hM hZV W hW hTW hB
      z hzT hzL hAz hAM))
  · exact Or.inr (Or.inr (original_line_core_weight_and_socle_at h₀ D m h1332 hTA hTB
      eA eB hne hiA hiB K hC.2 eK he q hqA hqB hqT hm.some h structural hM hZV W hW hTW hB
      z hzT hzL hAz))

open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
