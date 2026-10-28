module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoDihedralSeed
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoResidualSeparation
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaSelection
public import Theory.ElementaryAbelian.AutomorphismCardEight
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel

/-!
# Excluding the dihedral beta quotient in the exceptional branch

When D_alpha = Z_alpha, the dihedral seed calculations force q_alpha = 2,
both cores to have order sixteen, and the beta Frattini quotient to have
order eight. The earlier (7.4) commutator identity supplies its exact
Frattini subgroup Z_beta, whose order comes from the natural center action.

An automorphism of order dividing five acts trivially on this quotient:
its automorphism group has order 168. The Frattini automorphism kernel is
a two-group, so it acts trivially on the whole core. Characteristic two
then excludes an element of order five in the actual vertex stabilizer.
This contradicts the literal dihedral quotient marking.

Thus a supplied graph rank-one catalogue has only the binary linear row
in the exceptional branch. The regular branch D_alpha != Z_alpha and
original degree-one unitary enlargement are not settled here. The companion
source module applies the exclusion to the original full endpoint quotient.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.7), pp.158--159, and the exceptional branch of (10.9), pp.162--163.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting

private theorem automorphism_fifth_power_eq_one
    {H : Type*} [Group H] [Finite H] (hp : IsPGroup 2 H)
    (hc : Nat.card (H ⧸ frattini H) = 8)
    (a : MulAut H) (ha : a^5 = 1) : a = 1 := by
  let : Fact (IsPGroup 2 H) := ⟨hp⟩
  let : IsElementaryAbelian 2 (H ⧸ frattini H) := isElementaryAbelian_quotient_frattini
  let f := (frattini H).quotientAut
  have hpow : (f a)^5 = 1 := by rw [←map_pow,ha,map_one]
  have hdiv := orderOf_dvd_natCard (f a)
  rw [card_mulAut_of_elementary_eight _ hc] at hdiv
  have horder : orderOf (f a) = 1 := Nat.eq_one_of_dvd_coprimes
    (by decide : Nat.Coprime 5 168) (orderOf_dvd_of_pow_eq_one hpow) hdiv
  let x : f.ker := ⟨a,orderOf_eq_one_iff.mp horder⟩
  have hx5 : x^5 = 1 := Subtype.ext ha
  have hcop := (isPGroup_quotientAut_frattini_kernel hp).orderOf_coprime
    (by decide : Nat.Coprime 2 5) x
  have hx1 : x = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) (orderOf_dvd_of_pow_eq_one hx5))
  exact congrArg Subtype.val hx1

private theorem no_five_of_small_core
    {H : Type*} [Group H] [Finite H]
    (hself : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hc : Nat.card (pCore 2 H ⧸ frattini (pCore 2 H)) = 8) : ¬ 5 ∣ Nat.card H := by
  intro hfive
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := H) 5 hfive
  let f : H →* MulAut (pCore 2 H) := MulAut.conjNormal
  have hf : f a = 1 := automorphism_fifth_power_eq_one (pCore_isPGroup (p := 2) (G := H)) hc (f a) (by
    rw [←map_pow,←ha,pow_orderOf_eq_one,map_one])
  have hac : a ∈ centralizer (pCore 2 H : Set H) := by
    intro x hx
    have hh := congrArg Subtype.val (DFunLike.congr_fun hf (⟨x,hx⟩ : pCore 2 H))
    change a*x*a⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  let a₀ : pCore 2 H := ⟨a,hself hac⟩
  have ho : orderOf a₀ = 5 := (orderOf_injective (pCore 2 H).subtype
    (pCore 2 H).subtype_injective a₀).symm.trans ha
  have hh := (pCore_isPGroup (p := 2) (G := H)).orderOf_coprime (by decide : Nat.Coprime 2 5) a₀
  rw [ho] at hh
  norm_num at hh

variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local instance dihedralAlgebra : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- The hypothetical exceptional dihedral row has cores of order sixteen
and beta Frattini quotient of order eight. -/
theorem BTwoCenterActionData.exceptional_dihedral_core_orders
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ = Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* DihedralGroup 5)
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) :
    Nat.card (Q F v) = 16 ∧ Nat.card (Q F m) = 16 ∧
      Nat.card (Q F m ⧸ frattini (Q F m)) = 8 := by
  let := finite_endpoints h
  let : Finite (Q F m) := Finite.of_injective
    (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨hk,hN,hE,hquot⟩ := c.dihedral_central_core_structure h hB hSyl hb hactor
    hcentral ht hne hcomm.le hnot eβ
  let := hN
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hDc : Nat.card (D F m t) = 4 := by
    rw [hD,c.central_center_card E
      (c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral),hk]
    norm_num
  have hQa := card_eq_card_quotient_mul_card_subgroup ((D F m t).subgroupOf (Q F v))
  rw [hquot,Nat.card_congr (subgroupOfEquivOfLe d.separated).toEquiv,hDc] at hQa
  have hQa16 : Nat.card (Q F v) = 16 := hQa
  let I := Q F v ⊓ Q F m
  have hDI : D F m t ≤ I := le_inf d.separated inf_le_left
  have hI := ((D F m t).subgroupOf I).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hDI).toEquiv] at hI
  change (D F m t).relIndex I * Nat.card (D F m t) = Nat.card I at hI
  rw [c.dihedral_seed_factor_index h hB hSyl hS hb ht hne hnot eβ,hDc] at hI
  have hi := relIndex_ker (K := (Q F m).subgroupOf c.actor) c.quotient
  rw [c.kernel,relIndex_subgroupOf c.neighbor_core_le,c.neighbor_image] at hi
  have hindex : (Q F v).relIndex (Q F m) = 2 := hi.trans
    ((Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 c.imageSylow).symm.toEquiv).trans hk)
  have hQb := (I.subgroupOf (Q F m)).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show I ≤ Q F m from inf_le_right)).toEquiv] at hQb
  change I.relIndex (Q F m) * Nat.card I = Nat.card (Q F m) at hQb
  have hi' : I.relIndex (Q F m) = 2 := by
    dsimp only [I]
    rw [inf_comm,inf_relIndex_left]
    exact hindex
  have hQb16 : Nat.card (Q F m) = 16 := by rw [hi',←hI] at hQb; omega
  have hPhi := (c.beta_core_frattini_eq h hB hSyl hb hactor hcentral ht hne hcomm).1
  have hPhic : Nat.card (frattini (Q F m)) = 2 := by
    rw [←card_map_of_injective (f := (Q F m).subtype) (Q F m).subtype_injective,hPhi,
      c.central_middle_center_card h hB hSyl hb hactor hcentral E,hk]
  have hquotient := card_eq_card_quotient_mul_card_subgroup (frattini (Q F m))
  rw [hQb16,hPhic] at hquotient
  exact ⟨hQa16,hQb16,by omega⟩

/-- The exceptional branch excludes a genuine dihedral beta quotient through
its faithful action on the actual beta core. -/
theorem BTwoCenterActionData.not_exceptional_dihedral_beta
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ = Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* DihedralGroup 5) : False := by
  let := finite_endpoints h
  let H := stabilizer F m
  let A := graphLocalGroup F m
  let : Finite A := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have horders := c.exceptional_dihedral_core_orders h hB hSyl hb hactor hcentral
    ht hne hcomm hnot eβ hD E
  let a : pCore 2 H ≃* Q F m :=
    (pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let e := QuotientGroup.congr _ _ a (frattini_map_equiv a)
  have hsmall : Nat.card (pCore 2 H ⧸ frattini (pCore 2 H)) = 8 :=
    (Nat.card_congr e.toEquiv).trans horders.2.2
  have hnot5 := no_five_of_small_core (source_vertex_core_selfCentralizing h m) hsmall
  have hd : 5 ∣ Nat.card (A ⧸ pCore 2 A) := by
    rw [Nat.card_congr eβ.toEquiv,DihedralGroup.nat_card]
    decide
  exact hnot5 (hd.trans ((card_quotient_dvd_card (pCore 2 A)).trans
    (card_dvd_of_injective (inclusion (sylowGenerated_le (stabilizer F m))) (inclusion_injective _))))

/-- In the exceptional branch, all supplied graph catalogue alternatives
reduce to an actual binary linear beta marking. -/
theorem BTwoCenterActionData.exceptional_beta_quotient_linear
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (hactor : c.actor = graphLocalGroup F v)
    (hcentral : Z F m ≤ centerIn (graphLocalGroup F m))
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hcomm : ⁅V F m 1,Q F m⁆ = Z F m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (hD : D F m t = Z F v) (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hmodel : IsRankOneModel (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m))) :
    ∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) 2 (2^n) := by
  rcases c.beta_quotient_linear_or_dihedral h hB hSyl hb hactor hcentral ht hne hcomm.le
    hnot hmodel with hh | hh
  · exact hh
  · obtain ⟨e⟩ := hh
    exact (c.not_exceptional_dihedral_beta h hB hSyl hb hactor hcentral ht hne hcomm
      hnot hD E e).elim

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
