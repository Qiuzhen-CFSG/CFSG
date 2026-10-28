module
public import Theory.Representation.BinaryPermutation.SynthemeCoreWeights
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.SecondFlag
public import Theory.GroupTheory.PResidual.FiniteLocalPair
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Weights

/-!
# The weight of the product alternative in the original core

If the original L₂ normalizes a subgroup N centralized by a weight-two
vector z, then N centralizes the constant vector: the tetrahedral action
writes that vector as the product of three L₂-conjugates of z. The genuine
fixed-generator centralizer theorem places N in M=N_G(L). Relabeling the
six coordinates transports this calculation to the actual invariant plane,
with the original L/centralCore L quotient and embedded residual retained.

Apply this to N=O²(P), where P is the outside parabolic in C_G(z).
The product alternative's commutator bound supplies normalization; the
Sylow supplement P=O²(P)T then contradicts P escaping M. Consequently the
product alternative has weight four. This proves that part of 13.4.10(8i)
without assuming its full module decomposition. The placement and weight of
C_V(L) in the other component module, comparison at both escaping weights,
and the later graph argument remain separate obligations.

Source: Aschbacher–Smith 13.4.10(8), printed pp.909–910.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem marked_second_residual_weight_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (J : Subgroup G) (hJL : J ≤ L)
    (himage : (J.subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      synthemeStabilizer ⊓ alternatingGroup (Fin 6))
    (N : Subgroup G)
    (hN : (pResidual 2 J).map J.subtype ≤ normalizer (N : Set G))
    (z : V) (hzN : z.val ∈ centralizer (N : Set G)) (hweight : m.weight z = 2) :
    N ≤ normalizer (L : Set G) := by
  let K := (pResidual 2 J).map J.subtype
  have hKL : K ≤ L := (map_subtype_le _).trans hJL
  obtain ⟨f,hf,hmark⟩ := Solvable.second_parabolic_residual_action D m J hJL himage
  obtain ⟨a,b,hab⟩ := SynthemeCoreChief.weight_two_constant_sum (m.coordinate z).toAdd hweight
  obtain ⟨k,hk⟩ := hf a
  obtain ⟨j,hj⟩ := hf b
  let act (k : K) : V := V.normalizerMonoidHom ⟨k.val,D.normalizes (hKL k.property)⟩ z
  have hact (k : K) : (m.coordinate (act k)).toAdd =
      coreRepresentation (Fin 6) (ResidualPairRecognition.synthemeHom (f k))
        (m.coordinate z).toAdd := by
    rw [←hmark k]
    exact m.equivariant (inclusion hKL k) z
  have heq : z * act k * act j = m.constant := by
    apply m.coordinate.injective
    apply Multiplicative.toAdd.injective
    rw [m.coordinate.map_mul,m.coordinate.map_mul]
    change (m.coordinate z).toAdd + (m.coordinate (act k)).toAdd +
      (m.coordinate (act j)).toAdd = (m.coordinate m.constant).toAdd
    rw [hact,hact,hk,hj,m.constant_coordinate]
    exact hab
  have hmem (k : K) : (act k).val ∈ centralizer (N : Set G) := by
    exact (mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer N (hN k.property)) z.val).mp hzN
  have hc : m.constant.val ∈ centralizer (N : Set G) := by
    rw [←heq]
    exact (centralizer (N : Set G)).mul_mem
      ((centralizer (N : Set G)).mul_mem hzN (hmem k)) (hmem j)
  have hn : N ≤ centralizer ({m.constant.val} : Set G) := by
    intro n hn
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hc n hn)
  exact hn.trans (fixed_generator_centralizer h structural D m
    ⟨m.constant.property,m.constant_fixed⟩
    (fun hh => m.constant_ne_one (Subtype.ext hh))).le

/-- Normalization by the actual original second residual transports a
weight-two fixed vector to the constant line and hence to M. -/
theorem original_second_residual_weight_two
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (N : Subgroup G)
    (hN : (pResidual 2 ((L ⊔ (T : Subgroup G)) ⊓ normalizer
        (m.naturalPreimage W : Set G) : Subgroup G)).map
      ((L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)).subtype ≤
        normalizer (N : Set G))
    (z : V) (hzN : z.val ∈ centralizer (N : Set G)) (hweight : m.weight z = 2) :
    N ≤ normalizer (L : Set G) := by
  obtain ⟨g,hg⟩ := m.natural_plane_alignment W hW hT
  have hweight' : (m.relabel g).weight z = 2 := by
    change wordWeight (representation (Fin 6) g.val⁻¹ (m.coordinate z).toAdd.val) = 2
    rw [wordWeight_permute]
    exact hweight
  have hN' := hN
  rw [Solvable.second_flag_normalizer_eq D _ hT,
    Solvable.second_parabolic_full_residual _ (m.sylow_normalizes_inner_plane W hT)] at hN'
  exact marked_second_residual_weight_two h structural D (m.relabel g)
    (L ⊓ normalizer (m.naturalPreimage W : Set G)) inf_le_left
    (m.aligned_inner_plane_image W g hg) N hN' z hzN hweight'

/-- The retained commutator bound already forces the product branch's
original escaping vector to have weight four. -/
theorem original_product_weight_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (W : Submodule (ZMod 2) (natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (P : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (z : V) (hzL : z.val ∉ centralizer (L : Set G))
    (hPz : P ≤ centralizer ({z.val} : Set G))
    (hcomm :
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let K₂ := (pResidual 2 P).map P.subtype
      let L₂ := (pResidual 2 B).map B.subtype
      ⁅K₂,L₂⁆ ≤ K₂.pCoreIn 2) : m.weight z = 4 := by
  rcases m.nonfixed_weight z hzL with hw | hw
  · exfalso
    let K₂ := (pResidual 2 P).map P.subtype
    have hn := le_normalizer_iff_commutator_le_left.mpr (hcomm.trans (pCoreIn_le 2 K₂))
    have hzN : z.val ∈ centralizer (K₂ : Set G) := by
      apply mem_centralizer_iff.mpr
      intro k hk
      exact (mem_centralizer_singleton_iff.mp (hPz (map_subtype_le _ hk)))
    have hKM := original_second_residual_weight_two h structural D m W hW hT K₂ hn z hzN hw
    have hTP : (T : Subgroup G) ≤ P := hP.1.1.2
    have hs : K₂ ⊔ (T : Subgroup G) = P :=
      embedded_pResidual_sup_of_common_sylow P T (T.subtype hTP)
        (by rw [T.coe_subtype,map_subgroupOf_eq_of_le hTP])
    exact hP.1.2 (hs ▸ sup_le hKM D.sylow_normalizes_component)
  · exact hw

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
