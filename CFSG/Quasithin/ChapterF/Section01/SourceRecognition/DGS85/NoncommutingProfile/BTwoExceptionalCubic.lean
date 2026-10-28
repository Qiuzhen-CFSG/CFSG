module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoLinearModule
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaCore
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# The exceptional core and its cubic action in the linear beta branch

When D_alpha = Z_alpha, the beta-core product reduces to Q_beta = V_beta.
The actual quotient and neighboring-core indices compute both core orders
as q_alpha squared times q_beta squared and q_alpha cubed times q_beta.
The parameters come from the original two quotient markings.

A nonidentity odd-order alpha-quotient actor fixes nothing on either the
natural center or the already constructed full-core quotient. Hence it
fixes only the identity of Q_alpha. An explicit cubic matrix and Cauchy's
theorem construct such an element of order three in the actual local actor;
its conjugation automorphism on the actual core is retained.

These are the initial group and action calculations in (10.9). The beta
linearity premise is still explicit. They neither select all beta models
nor establish the bounds q_alpha = 2, q_beta <= 4, parabolic recognition,
or path parameters.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.7) and proof of (10.9), printed pp.158--159 and 162--163.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise commutatorElement MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]
local instance cubicAlgebra {k₀ : Type*} [Field k₀] [CharP k₀ 2] : Algebra (ZMod 2) k₀ :=
  ZMod.algebra k₀ 2

/-- The natural center has no nonidentity fixed points for an odd quotient actor. -/
theorem BTwoCenterActionData.center_odd_fixed
    (h : LocallyRankOneTriple P B)
    {v m w : Vertex F} (c : BTwoCenterActionData F v m w k W)
    (hω : omegaCenterIn c.actor = ⊥)
    (a : c.actor) (ho : Odd (orderOf (c.quotient a))) (ha : c.quotient a ≠ 1)
    (x : G) (hx : x ∈ Z F v) (hax : Commute x (a : G)) : x = 1 := by
  let := finite_endpoints h
  let : Finite (Z F v) := Finite.of_injective
    (inclusion (Z_le_stabilizer F v)) (inclusion_injective _)
  let : Finite (Multiplicative W) := Finite.of_surjective _ c.coordinates.onto
  let : Finite W := inferInstanceAs (Finite (Multiplicative W))
  have hn := sl2_natural_copies c.representation c.imageSylow c.quadratic c.generated c.fixed_bot
  have hf := odd_fixed_eq_bot_of_natural_copies c.representation hn (c.quotient a)
    ho (pow_orderOf_eq_one _) ha
  have hv : (c.coordinates.coordinates ⟨x,hx⟩).toAdd ∈
      fixedSpace c.representation (zpowers (c.quotient a)) := by
    apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
    apply (c.coordinates.fixed_coordinate_iff_commutator_mem a ⟨x,hx⟩).mpr
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hax.eq]
    exact one_mem _
  have hz : (c.coordinates.coordinates ⟨x,hx⟩).toAdd = 0 := by
    simpa only [hf,Submodule.mem_bot] using hv
  have hh := (c.coordinates.coordinates_eq_one_iff ⟨x,hx⟩).mp
    (Multiplicative.toAdd.injective hz)
  exact mem_bot.mp (hω ▸ hh)

/-- With D = Z, fixed-point control on the two layers gives control on the whole core. -/
theorem BTwoCenterActionData.exceptional_linear_odd_fixed
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v)
    (a : c.actor) (ho : Odd (orderOf (c.quotient a))) (ha : c.quotient a ≠ 1)
    (x : G) (hx : x ∈ Q F v) (hax : Commute x (a : G)) : x = 1 := by
  have hxD := c.linear_core_odd_fixed h hB hSyl hb hactor hcentral ht hne hcomm
    hnot eβ a ho ha x hx (by
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hax.eq]
      exact one_mem _)
  exact c.center_odd_fixed h (c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral)
    a ho ha x (hD ▸ hxD) hax

omit [Finite k] in
private theorem exists_cubic_image (H : Type*) [Group H] [Finite H]
    (π : H →* SL(2,k)) (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker) :
    ∃ a : H, orderOf a = 3 ∧ orderOf (π a) = 3 := by
  let u : SL(2,k) := ⟨!![0,1;1,1], by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩
  have hu3 : u ^ 3 = 1 := by
    apply Subtype.ext
    change (!![0,1;1,1] : Matrix (Fin 2) (Fin 2) k) ^ 3 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_succ,Matrix.mul_apply,Fin.sum_univ_two,CharTwo.add_self_eq_zero]
  have hu : u ≠ 1 := by
    intro he
    have hh := congrArg (fun a : SL(2,k) => a.val 0 0) he
    exact zero_ne_one hh
  have hou : orderOf u = 3 := orderOf_eq_prime hu3 hu
  have hdiv : 3 ∣ Nat.card H := by
    rw [←hou]
    exact (orderOf_dvd_natCard u).trans (Subgroup.card_dvd_of_surjective π hπ)
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := H) 3 hdiv
  have hne : π a ≠ 1 := by
    intro he
    let a₀ : π.ker := ⟨a,he⟩
    obtain ⟨n,hn⟩ := hk.exists_orderOf_dvd_pow a₀
    have ho : orderOf a₀ = 3 := (orderOf_injective π.ker.subtype π.ker.subtype_injective a₀).symm.trans ha
    rw [ho] at hn
    have hh : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by decide) hn
    norm_num at hh
  refine ⟨a,ha,orderOf_eq_prime ?_ hne⟩
  rw [←map_pow,←ha,pow_orderOf_eq_one,map_one]

/-- The conjugation action on the literal alpha core. -/
@[expose] def BTwoCenterActionData.coreConjugation
    {v m w : Vertex F} (c : BTwoCenterActionData F v m w k W) :
    c.actor →* MulAut (Q F v) :=
  (Q F v).normalizerMonoidHom.comp (inclusion (c.actor_le.trans
    (CommutingNontrivial.stabilizer_normalizes_Q F v)))

/-- The core automorphism is the literal conjugation map. -/
theorem BTwoCenterActionData.coreConjugation_apply
    {v m w : Vertex F} (c : BTwoCenterActionData F v m w k W)
    (a : c.actor) (x : Q F v) :
    (c.coreConjugation a x : G) = (a : G) * (x : G) * (a : G)⁻¹ := rfl

/-- The exceptional equality D = Z removes the entire residual supplement
from the beta-core product; no beta quotient model is required. -/
theorem BTwoCenterActionData.exceptional_beta_core
    (h : LocallyRankOneTriple P B)
    (hS : ∀ x, Stellmacher.IsSylowSubgroupIn (Q F x) (U F x))
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m) (hD : D F m t = Z F v) :
    Q F m = V F m 1 := by
  rw [c.beta_core_product h hS hb ht hne,hD]
  apply sup_eq_left.mpr
  exact le_iSup_of_le v (le_iSup_of_le
    ((mem_ball_one _ _ _).mpr (Or.inl c.middle.symm)) le_rfl)

/-- The cubic in p.163 is constructed in the original alpha actor. -/
theorem BTwoCenterActionData.exceptional_linear_cubic
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) :
    ∃ a : c.actor, orderOf a = 3 ∧ orderOf (c.quotient a) = 3 ∧
      (c.coreConjugation a)^3 = 1 ∧
      (∀ x : Q F v, c.coreConjugation a x = x → x = 1) := by
  let := finite_endpoints h
  let : Finite c.actor := Finite.of_injective (inclusion c.actor_le) (inclusion_injective _)
  have hk : IsPGroup 2 c.quotient.ker := by
    rw [c.kernel]
    exact (isPGroup_pCoreIn 2 (stabilizer F v)).comap_subtype
  obtain ⟨a,ha,hqa⟩ := exists_cubic_image c.actor c.quotient c.onto hk
  refine ⟨a,ha,hqa,?_,?_⟩
  · rw [←map_pow,←ha,pow_orderOf_eq_one,map_one]
  · intro x hx
    apply Subtype.ext
    apply c.exceptional_linear_odd_fixed h hB hSyl hb hactor hcentral ht hne hcomm hnot eβ hD a
      (hqa ▸ (by decide : Odd 3)) (fun he => by rw [he,orderOf_one] at hqa; omega)
      x x.property
    have he := congrArg Subtype.val hx
    change (a : G) * (x : G) * (a : G)⁻¹ = x at he
    exact show Commute (x : G) (a : G) from (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The two literal core orders at the start of (10.9), with both field
parameters retained. No order of a center or core is supplied as a premise. -/
theorem BTwoCenterActionData.exceptional_linear_core_orders
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    Nat.card (Q F v) = Nat.card k ^ 2 * Nat.card K ^ 2 ∧
      Nat.card (Q F m) = Nat.card k ^ 3 * Nat.card K := by
  let := finite_endpoints h
  have hS := source_kernel_sylow h hB hSyl
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  have hDcard : Nat.card (D F m t) = Nat.card k ^ 2 := by
    rw [hD]
    exact c.central_center_card E hω
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  obtain ⟨_,hN,hE,hcard⟩ := c.linear_central_core_structure h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ
  let := hN
  have hQa := card_eq_card_quotient_mul_card_subgroup ((D F m t).subgroupOf (Q F v))
  rw [hcard,Nat.card_congr (subgroupOfEquivOfLe d.separated).toEquiv,hDcard] at hQa
  refine ⟨hQa.trans (Nat.mul_comm _ _),?_⟩
  let I := Q F v ⊓ Q F m
  have hDI : D F m t ≤ I := le_inf d.separated inf_le_left
  have hI := ((D F m t).subgroupOf I).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hDI).toEquiv] at hI
  change (D F m t).relIndex I * Nat.card (D F m t) = Nat.card I at hI
  rw [c.linear_seed_factor_index h hB hSyl hS hb ht hne hnot eβ,hDcard] at hI
  have hi := relIndex_ker (K := (Q F m).subgroupOf c.actor) c.quotient
  rw [c.kernel,relIndex_subgroupOf c.neighbor_core_le,c.neighbor_image] at hi
  have hindex : (Q F v).relIndex (Q F m) = Nat.card k := hi.trans
    (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 c.imageSylow).symm.toEquiv)
  have hQb := (I.subgroupOf (Q F m)).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show I ≤ Q F m from inf_le_right)).toEquiv] at hQb
  change I.relIndex (Q F m) * Nat.card I = Nat.card (Q F m) at hQb
  have hi' : I.relIndex (Q F m) = Nat.card k := by
    dsimp only [I]
    rw [inf_comm,inf_relIndex_left]
    exact hindex
  rw [hi',←hI] at hQb
  rw [←hQb]
  ring

/-- The core product is a Sylow subgroup of the actual alpha vertex group. -/
theorem BTwoCenterActionData.core_product_sylow
    (h : LocallyRankOneTriple P B) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W) :
    Stellmacher.IsSylowSubgroupIn (Q F m ⊔ Q F v) (stabilizer F v) := by
  let := finite_endpoints h
  have hk : IsPGroup 2 c.quotient.ker := by
    rw [c.kernel]
    exact (isPGroup_pCoreIn 2 (stabilizer F v)).comap_subtype
  let T := c.imageSylow.comapOfKerIsPGroup c.quotient hk
    (by rw [MonoidHom.range_eq_top.mpr c.onto]; exact le_top)
  have hpre : (c.imageSylow : Subgroup SL(2,k)).comap c.quotient =
      (Q F m ⊔ Q F v).subgroupOf c.actor := by
    rw [←c.neighbor_image,comap_map_eq,c.kernel,subgroupOf_sup c.neighbor_core_le c.core_le]
  have hS : Stellmacher.IsSylowSubgroupIn (Q F m ⊔ Q F v) c.actor := by
    refine ⟨T,?_⟩
    change ((c.imageSylow : Subgroup SL(2,k)).comap c.quotient).map c.actor.subtype = _
    rw [hpre,map_subgroupOf_eq_of_le (sup_le c.neighbor_core_le c.core_le)]
  have hle : (c.sylow : Subgroup (stabilizer F v)) ≤ c.actor.subgroupOf (stabilizer F v) := by
    intro x hx
    exact c.sylow_le_actor (mem_map_of_mem _ hx)
  have hi : ¬ 2 ∣ c.actor.relIndex (stabilizer F v) :=
    fun hd => c.sylow.not_dvd_index (hd.trans (index_dvd_of_le hle))
  exact Noncommuting.sylow_in_overgroup_of_odd_relIndex _ _ _ c.actor_le hS hi

/-- The source common Sylow order in (10.9) uses both marked field parameters. -/
theorem BTwoCenterActionData.exceptional_linear_sylow_order
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ ≤ Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    Nat.card (Q F m ⊔ Q F v : Subgroup G) = Nat.card k ^ 3 * Nat.card K ^ 2 := by
  let := finite_endpoints h
  let : Finite (Q F m) := Finite.of_injective
    (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  have horders := c.exceptional_linear_core_orders h hB hSyl hb hactor hcentral ht hne
    hcomm hnot eβ hD E
  have hindex := (c.linear_seed_eq_core_and_index h hB hSyl
    (source_kernel_sylow h hB hSyl) hb ht hne hnot eβ).2
  have hn : Q F m ≤ normalizer (Q F v : Set G) :=
    c.neighbor_core_le.trans (c.actor_le.trans (CommutingNontrivial.stabilizer_normalizes_Q F v))
  have hi : (Q F m).relIndex (Q F m ⊔ Q F v) = Nat.card K := by
    rw [sup_comm,relIndex_sup_of_normalizes _ _ hn]
    exact hindex
  have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (Q F m)
    (Q F m ⊔ Q F v) bot_le le_sup_left
  simp only [relIndex_bot_left,hi,horders.2] at hc
  rw [←hc]
  ring

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
