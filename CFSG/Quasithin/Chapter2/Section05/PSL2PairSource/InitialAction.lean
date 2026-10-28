module

public import Theory.GroupTheory.CrossingPairCentralizer
public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.PrimeModel
public import CFSG.Quasithin.Chapter2.Section05.ShadowPair
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# Earlier-source centralizer and faithful action of the PSL₂ crossing pair

`Incoming` retains the ambient finite simple QTKE hypothesis with its unrestricted
K-group class parameter, the original Sylow and marked elements, and the actual
prime-field model. Its decomposition, normality and odd-core clauses belong to
2.5.18/20. The crossing mark and commuting-pair clauses belong to the preceding
paragraphs of 2.5.21 and remain to be constructed by the section assembly.

From these inputs this module proves t ∈ Kˣ, C_G(t) ≤ N_G(KKˣ), triviality of
the pair centralizer, faithfulness of both literal conjugation actions, and
C_G(t) = KS = H. The prime-model stabilizer calculation makes C_J(K) a normal
two-group. Perfectness identifies the two-residual, with its actual ambient
subtype map, with K. No later marked-class or mixed-action claim is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
2.5.21, printed p.566 (PDF p.583).
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.PSL2PairSource
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {p : ℕ} [Fact p.Prime]

/-- The incoming data on p.566 after the crossing identities and commutation
have been established. None of the later centralizer, faithfulness, residual
or marked-fusion conclusions is a field. The final section assembly must
construct this data, including the crossing identities from 2.5.21 itself. -/
structure Incoming (κ : GroupClass.{u}) (G : Type u) [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] where
  ambient : IsSimpleQTKE κ G
  T : Sylow 2 G
  H : Subgroup G
  S : Subgroup G
  K : Subgroup G
  t : G
  x : G
  z : G
  prime_ge : 7 ≤ p
  parameter : IsFermatOrMersennePrime p
  model : K ≃* PSL(2, ZMod p)
  sylow : Sylow 2 (centralizer ({t} : Set G))
  sylow_eq : (sylow : Subgroup (centralizer ({t} : Set G))).map
    (centralizer ({t} : Set G)).subtype = S
  s_le_t : S ≤ (T : Subgroup G)
  t_mem : t ∈ S
  t_order : orderOf t = 2
  x_mem : x ∈ (T : Subgroup G)
  x_normalizes : x ∈ normalizer (S : Set G)
  x_square : x ^ 2 ∈ S
  normalK : (K.subgroupOf (centralizer ({t} : Set G))).Normal
  generated : centralizer ({t} : Set G) =
    K ⊔ S ⊔ (centralizer ({t} : Set G) ⊓ centralizer (K : Set G))
  h_eq : H = K ⊔ S
  oddCore : pPrimeCore 2 (centralizer ({t} : Set G)) = ⊥
  crossing_mark : x⁻¹ * t * x ∈ K
  z_eq : z = t * (x⁻¹ * t * x)
  nonfusion : ¬ IsConj t z
  disjoint : (S ⊓ centralizer (K : Set G)) ⊓
    conjugate (S ⊓ centralizer (K : Set G)) x = ⊥
  commuting : ⁅K, conjugate K x⁆ = ⊥

namespace Incoming
variable (d : Incoming κ G p)

private theorem k_le_j : d.K ≤ centralizer ({d.t} : Set G) := by
  rw [d.generated]
  exact le_sup_of_le_left le_sup_left

private theorem s_le_j : d.S ≤ centralizer ({d.t} : Set G) := by
  rw [← d.sylow_eq]
  exact map_subtype_le _

/-- The original centralizer acts on its normal component K. -/
theorem j_normalizes_k : centralizer ({d.t} : Set G) ≤ normalizer (d.K : Set G) := by
  let : (d.K.subgroupOf (centralizer ({d.t} : Set G))).Normal := d.normalK
  exact (normal_subgroupOf_iff_le_normalizer d.k_le_j).mp inferInstance

/-- The original involution belongs to Kˣ, as required by the source's action
on the pair. This is derived from tˣ ∈ K and x² ∈ S. -/
theorem mark_mem : d.t ∈ conjugate d.K d.x :=
  CrossingPair.mark_mem_crossing_factor d.K d.S d.t d.x
    (d.s_le_j.trans d.j_normalizes_k) d.x_square d.crossing_mark

/-- This discharges the centralizer-containment premise of ShadowPair. -/
theorem centralizer_le_pair_normalizer : centralizer ({d.t} : Set G) ≤
    normalizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G) :=
  CrossingPair.centralizer_normalizes_pair d.K d.S d.t d.x d.s_le_j
    d.j_normalizes_k d.generated d.x_normalizes d.crossing_mark d.commuting

/-- The pair centralizer vanishes by relative normality, Sylow restriction
and the earlier O(C_G(t)) = 1; it is not an assumed action kernel. -/
theorem pair_centralizer :
    centralizer ((d.K ⊔ conjugate d.K d.x : Subgroup G) : Set G) = ⊥ :=
  CrossingPair.pair_centralizer_eq_bot d.K d.S d.t d.x d.sylow d.sylow_eq
    d.s_le_j d.j_normalizes_k d.generated d.x_normalizes d.x_square
    d.crossing_mark d.commuting d.disjoint d.oddCore

/-- The original centralizer also preserves the crossing factor. -/
theorem j_normalizes_l :
    centralizer ({d.t} : Set G) ≤ normalizer (conjugate d.K d.x : Set G) := by
  have hSL := CrossingPair.sylow_normalizes_crossing d.K d.S d.x
    (d.s_le_j.trans d.j_normalizes_k) d.x_normalizes
  have hKL : d.K ≤ normalizer (conjugate d.K d.x : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.mp d.commuting).trans
      (Subgroup.centralizer_le_normalizer _)
  have hCL : centralizer (d.K : Set G) ≤ normalizer (conjugate d.K d.x : Set G) := by
    apply le_trans _ (CrossingPair.crossing_factor_normalized d.K d.t d.x d.j_normalizes_k)
    intro g hg
    exact mem_centralizer_singleton_iff.mpr (hg _ d.crossing_mark).symm
  rw [d.generated]
  exact sup_le (sup_le hKL hSL) (inf_le_right.trans hCL)

/-- Faithfulness of the two actual conjugation actions of C_G(t). -/
theorem pair_action_injective : Function.Injective
    (CrossingPair.pairAction (centralizer ({d.t} : Set G)) d.K (conjugate d.K d.x)
      d.j_normalizes_k d.j_normalizes_l) :=
  CrossingPair.pairAction_injective _ _ _ _ _ d.pair_centralizer

/-- The full normalizer action on KKˣ is faithful, including factor-swapping
normalizer elements. -/
theorem normalizer_action_injective : Function.Injective
    (d.K ⊔ conjugate d.K d.x).normalizerMonoidHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [normalizerMonoidHom_ker, d.pair_centralizer]
  exact bot_subgroupOf _

private theorem crossing_stabilizer_isTwoGroup :
    IsPGroup 2 (MulAction.stabilizer (MulAut (conjugate d.K d.x))
      (⟨d.t, d.mark_mem⟩ : conjugate d.K d.x)) := by
  let L := conjugate d.K d.x
  let tL : L := ⟨d.t, d.mark_mem⟩
  let eL : L ≃* PSL(2, ZMod p) :=
    ((MulAut.conj d.x⁻¹).subgroupMap d.K).symm.trans d.model
  have ht : orderOf (eL tL) = 2 := by
    rw [eL.orderOf_eq, ← orderOf_coe tL]
    exact d.t_order
  have hp := involution_aut_stabilizer_isTwoGroup d.prime_ge d.parameter (eL tL) ht
  let A := MulAction.stabilizer (MulAut L) tL
  let B := MulAction.stabilizer (MulAut PSL(2, ZMod p)) (eL tL)
  let f : A →* B := ((MulAut.congr eL).toMonoidHom.comp A.subtype).codRestrict B (by
    intro a
    change eL (a.val (eL.symm (eL tL))) = eL tL
    rw [eL.symm_apply_apply]
    exact congrArg eL a.property)
  apply hp.of_injective f
  intro a b hab
  apply Subtype.ext
  apply (MulAut.congr eL).injective
  exact congrArg Subtype.val hab

/-- The faithful action puts the original C_J(K) in a two-group, using the
prime-field PGL coverage and the exact Fermat/Mersenne reflected torus. -/
theorem relative_centralizer_isTwoGroup :
    IsPGroup 2 (centralizer ({d.t} : Set G) ⊓ centralizer (d.K : Set G) : Subgroup G) :=
  CrossingPair.centralizer_isTwoGroup_of_fixed_action _ d.K (conjugate d.K d.x)
    d.j_normalizes_l d.pair_centralizer ⟨d.t, d.mark_mem⟩ le_rfl
    d.crossing_stabilizer_isTwoGroup

/-- The equality C_G(t) = KS asserted on p.566, derived from the incoming
centralizer supplement and the actual pair action. -/
theorem centralizer_eq_join : centralizer ({d.t} : Set G) = d.K ⊔ d.S :=
  CrossingPair.centralizer_supplement_eq _ d.K d.S d.sylow d.sylow_eq
    d.k_le_j d.j_normalizes_k d.generated d.relative_centralizer_isTwoGroup

/-- The original H is the full involution centralizer in the prime pair branch. -/
theorem centralizer_eq_H : centralizer ({d.t} : Set G) = d.H :=
  d.centralizer_eq_join.trans d.h_eq.symm

/-- The actual model gives a centerless factor. -/
theorem factor_center_eq_bot : center d.K = ⊥ := by
  apply bot_unique
  intro c hc
  have hh : d.model c ∈ center PSL(2, ZMod p) := (centerCongr d.model ⟨c, hc⟩).property
  rw [GorensteinWalter.psl2_center_eq_bot, mem_bot] at hh
  exact d.model.injective (hh.trans d.model.map_one.symm)

/-- The actual prime-field factor is quasisimple, rather than merely carrying
a group-family label. -/
theorem factor_quasisimple : IsQuasisimple d.K := by
  have hp4 : 4 ≤ Nat.card (ZMod p) := by simpa using (show 4 ≤ p by have := d.prime_ge; omega)
  let : IsSimpleGroup PSL(2, ZMod p) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hp4
  let : IsSimpleGroup d.K := (MulEquiv.isSimpleGroup_congr d.model).mpr inferInstance
  let : Group.IsPerfect PSL(2, ZMod p) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three (ZMod p) (by omega)
  let : Group.IsPerfect d.K :=
    Group.IsPerfect.ofSurjective (f := d.model.symm.toMonoidHom) d.model.symm.surjective
  refine { toIsPerfect := inferInstance, simple := ?_ }
  exact ((QuotientGroup.quotientMulEquivOfEq d.factor_center_eq_bot).trans
    QuotientGroup.quotientBot).isSimpleGroup

/-- The source's O²(J) = K, with the two-residual embedded by the literal
subtype map J → G. -/
theorem twoResidual_eq : (pResidual 2 (centralizer ({d.t} : Set G))).map
    (centralizer ({d.t} : Set G)).subtype = d.K := by
  let J := centralizer ({d.t} : Set G)
  let KJ := d.K.subgroupOf J
  let : KJ.Normal := d.normalK
  let : Group.IsPerfect PSL(2, ZMod p) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three (ZMod p) (by simpa using (show 3 < p by have := d.prime_ge; omega))
  let e : KJ ≃* PSL(2, ZMod p) := (subgroupOfEquivOfLe d.k_le_j).trans d.model
  let : Group.IsPerfect KJ := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hperfect : IsPPerfect 2 KJ := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (KJ ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (KJ ⧸ N) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (KJ ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (KJ ⧸ N) inferInstance
  have hsup : KJ ⊔ (d.sylow : Subgroup J) = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup, show KJ.map J.subtype = d.K from map_subgroupOf_eq_of_le d.k_le_j,
      d.sylow_eq, ← MonoidHom.range_eq_map, range_subtype]
    exact d.centralizer_eq_join.symm
  have he := pResidual_eq_of_isPPerfect_sup KJ (d.sylow : Subgroup J)
    hperfect d.sylow.isPGroup' hsup
  change (pResidual 2 J).map J.subtype = d.K
  rw [he]
  exact map_subgroupOf_eq_of_le d.k_le_j

end Incoming
end CFSG.Quasithin.Chapter2.PSL2PairSource

end
