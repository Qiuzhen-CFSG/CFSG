module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.Basic
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic.Transport
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic.Tilde
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic.Seed
public import Theory.AtlasPort.LinearGroups.G2.BinaryDerivedSimplicity
public import CFSG.KnownSimple.CarrierCatalogue

/-!
# The marked parabolic in the G₂(2)′ branch of 13.5.21

The literal commutator seed has a two-dimensional image in the natural central
quotient. Its stabilizer inside K* has index three over a Sylow 2-subgroup.
Relative normality then gives the same bound in K*T*, including its possible
outer action. The common marked-stabilizer argument identifies L₁*T* and its
embedded two-residual.

For the last clause, the actual parabolic residual generates the entire
seven-dimensional octonion trace-zero module. The universal orthogonal cover
therefore yields generation on every perfect central extension of the natural
quotient, without a splitting assumption. The original quotient and tilde maps
transport this to the precise premise used in 13.5.14.

The natural central quotient and the earlier configuration conclusions remain
explicit inputs; their discharge belongs to the parent marked-module assembly.
Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.5.21,
printed p. 924 (PDF p. 941). The concrete model calculations use the attributed
ATLAS ports imported by the descendants of this module; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff. No additional upstream source is copied.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic
open Section08.Source
open Atlas.G2.Natural.BinaryPlane
variable {G : Type*} [Group G] [Finite G]

private theorem normal_component_eq_actor {H : Type*} [Group H]
    (N A : Subgroup H) [N.Normal] (hNA : N ≤ A) (hne : N ≠ ⊥)
    (e : A ≃* Actor) : N = A := by
  let : IsSimpleGroup A := e.isSimpleGroup_congr.mpr Atlas.G2.isSimple_commutator_binary
  rcases (inferInstance : (N.subgroupOf A).Normal).eq_bot_or_eq_top with hb | ht
  · have hmap := congrArg (map A.subtype) hb
    rw [map_subgroupOf_eq_of_le hNA, Subgroup.map_bot] at hmap
    exact (hne hmap).elim
  · have hmap := congrArg (map A.subtype) ht
    rw [map_subgroupOf_eq_of_le hNA, ← MonoidHom.range_eq_map, A.range_subtype] at hmap
    exact hmap

variable (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
  [(D.V₁.subgroupOf D.UH).Normal] [IsElementaryAbelian 2 (Action.ModuleGroup D)]

/-- The G₂(2)′ branch of 13.5.21(5),(6), with the literal quotient, seed,
selected component, Sylow and ambient tilde maps. The configuration's
two-dimensional commutator seed and the independently produced natural central
quotient remain explicit. The parent source assembly discharges these premises;
irreducibility of the seed follows from the original F.9 hypothesis. -/
theorem source_conclusions (K : Subgroup G) (s : Selected D K)
    (_hproper : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hSQ : IsStronglyQuasithin (Hstar D.H))
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hLK : D.L₁ ≤ K) (hseed : D.Vplus = ⁅D.V,D.L₁⁆)
    (hm : ⁅starImage D.H K,starImage D.H D.L₁⁆ ≠ ⊥)
    (hc : ⁅starImage D.H K,starImage D.H D.V⁆ = starImage D.H K)
    (hdim : Module.finrank (ZMod 2) (Action.seedSpace D) = 2)
    (hseedgen : Action.seedSpace D =
      subspaceCommutator (Action.starRepresentation D h) (Action.seedSpace D) (starImage D.H D.L₁))
    (e : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)) ≃* Actor)
    (Z : Subrepresentation (Action.starRepresentation D h))
    (hZ : Z.toSubmodule = fixedSpace (Action.starRepresentation D h) (starImage D.H K))
    (c : (Action.Space D ⧸ Z.toSubmodule) ≃ₗ[ZMod 2] Coefficients)
    (he : ∀ g : (starImage D.H K ⊔ starImage D.H D.V : Subgroup (Hstar D.H)),
      ∀ w, c (Z.quotientRepresentation g.val w) = action (e g) (c w)) :
    (starImage D.H D.T).relIndex (markedParabolic D h K) = 3 ∧
      localStar D = markedParabolic D h K ∧
      (pResidual 2 (markedParabolic D h K)).map (markedParabolic D h K).subtype =
        starImage D.H D.L₁ ∧
      D.UH = ⁅D.QH,K⁆ ∧
      D.tilde D.UH = ⁅D.tilde D.UH,D.tilde D.L₁⁆ := by
  have hg := group_conclusions s h hSQ hindex hU hLK hseed hm hc
  let : (K.subgroupOf D.H).Normal := hg.1
  let : (starImage D.H K).Normal :=
    (inferInstance : (K.subgroupOf D.H).Normal).map _ (QuotientGroup.mk'_surjective _)
  have hneq : starImage D.H K ≠ ⊥ := by
    intro hzero
    apply s.moved
    rw [hzero,commutator_bot_left]
  have hKA := normal_component_eq_actor (starImage D.H K)
    (starImage D.H K ⊔ starImage D.H D.V) le_sup_left hneq e
  let f : starImage D.H K ≃* Actor := (MulEquiv.subgroupCongr hKA).trans e
  have hf (g : starImage D.H K) (w : Action.Space D ⧸ Z.toSubmodule) :
      c (Z.quotientRepresentation g.val w) = action (f g) (c w) := he ((MulEquiv.subgroupCongr hKA) g) w
  let ρ := Action.starRepresentation D h
  let p := Z.toSubmodule.mkQ
  have hp (g : Hstar D.H) (v : Action.Space D) :
      p (ρ g v) = Z.quotientRepresentation g (p v) := rfl
  have hk : p.ker = fixedSpace ρ (starImage D.H K) := by
    rw [Submodule.ker_mkQ]
    exact hZ
  have hL : starImage D.H D.L₁ ≤ starImage D.H K := map_mono (comap_mono hLK)
  have hd : Disjoint (Action.seedSpace D) p.ker := by
    rw [hk]
    exact seed_disjoint D h K hLK hdim hseedgen
  have hcard : Nat.card (Action.seedSpace D) = 4 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hdim]
    norm_num
  have hS : (starSylow D h : Subgroup (Hstar D.H)) ≤
      subspaceStabilizer ρ (Action.seedSpace D) := le_sup_right.trans (localStar_stabilizes_seed D h)
  have hi := Geometry.index_bound (starImage D.H K) (starSylow D h) ρ
    Z.quotientRepresentation p hp f c hf (Action.seedSpace D) hcard hd hS
  have hpar := marked_parabolic_of_index_bound D h hLK hm hi
  have hnot : ¬ starImage D.H D.L₁ ≤ (starSylow D h : Subgroup (Hstar D.H)) := by
    intro hle
    exact localStar_not_le_sylow D h hm (sup_le hle le_rfl)
  have hfull := Transport.local_generation (starImage D.H K) (starImage D.H D.L₁)
    (starSylow D h) hL (starSylow_normalizes_local D h)
    (localStar_residual_twoPerfect D h) hnot ρ Z.quotientRepresentation p
    Z.toSubmodule.mkQ_surjective hp hk.le
    (linear_generation D h s hLK hg.1 hseed) f c hf
    (Action.seedSpace D) hcard hd (localStar_stabilizes_seed D h)
  exact ⟨hpar.1,hpar.2.1,hpar.2.2,hg.2.2.2,tilde_generation_of_linear D h hfull⟩
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic
