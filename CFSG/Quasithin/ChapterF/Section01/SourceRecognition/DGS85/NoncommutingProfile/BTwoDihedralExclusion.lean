module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalDihedral
public import Theory.GroupTheory.SmallNonabelianTwoGroupFiveExclusion

/-!
# Excluding the regular dihedral beta quotient

The dihedral seed calculation gives q_alpha = 2 and index two for each
adjacent-core factor over D_alpha. For the actual residual R_alpha, the
centralizer of one such factor is trivial: its opposite conjugate and the
subgroup W_alpha generate the alpha actor together with the core. Evaluating
a commutator at one representative of the nonidentity coset embeds R_alpha
in Z_beta. Hence |R_alpha| ≤ 2 and |D_alpha| ≤ 8.

In the regular branch D_alpha != Z_alpha the core orders are therefore 32,
and the elementary subgroup D_alpha has order eight. The proved small
two-group automorphism obstruction excludes order five in the faithful beta
stabilizer. Together with the previous exceptional exclusion, this removes
the dihedral beta row completely. The supplied graph catalogue consequently
has an actual binary linear beta quotient.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(10.4), pp.155--156, and (10.7), pp.158--159. The original endpoint application
is BTwoDihedralExclusionSource; the degree-one original unitary enlargements
and the residual separation and recognition in (10.8)--(10.10) remain separate.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting

private theorem residual_centralizer_bot
    {G : Type*} [Group G] (L Q I W R : Subgroup G) (g : G)
    (hL : L = W ⊔ Q) (hg : g ∈ L)
    (hgen : I ⊔ I.conjBy g = Q)
    (hQI : Q ≤ normalizer (I : Set G))
    (hWQ : W ≤ normalizer (Q : Set G))
    (hRQ : R ≤ Q) (hRW : R ≤ centralizer (W : Set G))
    (hR2 : ∀ r ∈ R, r^2 = 1) (hω : omegaCenterIn L = ⊥) :
    R ⊓ centralizer (I : Set G) = ⊥ := by
  apply bot_unique
  intro r hr
  let C := centralizer ({r} : Set G)
  have hWC : W ≤ C := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (hRW hr.1 w hw)
  have hIC : I ≤ C := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hr.2 x hx)
  have hprod : g ∈ (W : Set G) * (Q : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hWQ,←hL]
    exact hg
  obtain ⟨w,hw,q,hq,rfl⟩ := hprod
  have hJC : I.conjBy (w*q) ≤ C := by
    rintro x ⟨i,hi,rfl⟩
    have hqi : q*i*q⁻¹ ∈ I := (mem_normalizer_iff.mp (hQI hq) i).mp hi
    have hh := C.mul_mem (C.mul_mem (hWC hw) (hIC hqi)) (C.inv_mem (hWC hw))
    change (w*q)*i*(w*q)⁻¹ ∈ C
    simpa only [mul_inv_rev,mul_assoc] using hh
  have hQC : Q ≤ C := hgen ▸ sup_le hIC hJC
  have hLC : L ≤ C := hL ▸ sup_le hWC hQC
  have hrL : r ∈ L := hL ▸ mem_sup_right (hRQ hr.1)
  have hrC : r ∈ centralizer (L : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hLC ha)
  exact hω ▸ (mem_omegaCenterIn_iff _ _).mpr ⟨hrL,hrC,hR2 r hr.1⟩

private theorem card_le_of_central_index_two
    {G : Type*} [Group G] (R I D Z : Subgroup G) [Finite Z] [IsMulCommutative Z]
    (hi : D.relIndex I = 2)
    (hRD : R ≤ centralizer (D : Set G))
    (hcomm : ⁅R,I⁆ ≤ Z) (hZR : Z ≤ centralizer (R : Set G))
    (hfix : R ⊓ centralizer (I : Set G) = ⊥) : Nat.card R ≤ Nat.card Z := by
  have hnot : ¬ I ≤ D := by
    intro hh
    have hh' := relIndex_eq_one.mpr hh
    omega
  obtain ⟨x,hx,hxD⟩ := SetLike.not_le_iff_exists.mp hnot
  have hcx (r : R) : ⁅(r : G),x⁆ ∈ Z :=
    hcomm (commutator_mem_commutator r.property hx)
  let f : R →* Z := {
    toFun := fun r => ⟨⁅(r : G),x⁆,hcx r⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by
      intro r s
      apply Subtype.ext
      change ⁅(r : G)*(s : G),x⁆ = ⁅(r : G),x⁆ * ⁅(s : G),x⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hc := mem_centralizer_iff.mp (hZR (hcx s)) r r.property
      rw [hc,mul_inv_cancel_right]
      exact congrArg Subtype.val (mul_comm (⟨⁅(s : G),x⁆,hcx s⟩ : Z) ⟨⁅(r : G),x⁆,hcx r⟩) }
  apply Nat.card_le_card_of_injective f
  apply (injective_iff_map_eq_one f).mpr
  intro r hr
  have hxC : x ∈ centralizer ({(r : G)} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    exact (commutatorElement_eq_one_iff_mul_comm.mp (congrArg Subtype.val hr)).symm
  have hDC : D ≤ centralizer ({(r : G)} : Set G) := by
    intro d hd
    exact mem_centralizer_singleton_iff.mpr (hRD r.property d hd)
  have hIC : I ≤ centralizer ({(r : G)} : Set G) := by
    intro i hiI
    by_cases hiD : i ∈ D
    · exact hDC hiD
    have hxi : x⁻¹*i ∈ D :=
      (D.subgroupOf I).mul_mem_iff_of_index_two hi
        (a := ⟨x⁻¹,I.inv_mem hx⟩) (b := ⟨i,hiI⟩) |>.mpr (by
          simp only [mem_subgroupOf,inv_mem_iff,hxD,hiD])
    simpa only [mul_inv_cancel_left] using
      (centralizer ({(r : G)} : Set G)).mul_mem hxC (hDC hxi)
  have hrI : (r : G) ∈ centralizer (I : Set G) := by
    intro i hi
    exact mem_centralizer_singleton_iff.mp (hIC hi)
  exact Subtype.ext (mem_bot.mp (hfix ▸ ⟨r.property,hrI⟩))

variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

/-- The literal source residual has order at most two, so its direct product
with the natural alpha center bounds D_alpha by eight. -/
theorem BTwoCenterActionData.dihedral_D_card_le_eight
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
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) : Nat.card (D F m t) ≤ 8 := by
  let := finite_endpoints h
  have hS := source_kernel_sylow h hB hSyl
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,hd,hker⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hdis : Disjoint d.residual (Z F v) := disjoint_iff.mpr
    (bot_unique (hker.trans hω.le))
  have hT : (c.sylow : Subgroup (stabilizer F v)).map (stabilizer F v).subtype ≤ d.actor :=
    hd.symm ▸ c.sylow_le_actor
  let hD := d.elementary h hS hb c.sylow hT hdis
  let I := Q F v ⊓ Q F m
  let A := Z F w ⊔ Z F ((g : G) • w)
  have hgenL : c.actor = A ⊔ Q F v := hd.symm.trans d.actor_generators
  have hAL : A ≤ c.actor := le_sup_left.trans hgenL.ge
  have hnQ : c.actor ≤ normalizer (Q F v : Set G) :=
    c.actor_le.trans (CommutingNontrivial.stabilizer_normalizes_Q F v)
  have hnI : Q F v ≤ normalizer (I : Set G) :=
    (le_inf (Q F v).le_normalizer
      (((source_Z_Q_U h v).2.trans ((ballKernel_one_le_edge F c.middle).trans inf_le_right)).trans
        (CommutingNontrivial.stabilizer_normalizes_Q F m))).trans inf_normalizer_le_normalizer_inf
  have hs := (c.dihedral_seed_eq_core_and_index h hB hSyl hS hb ht hne hnot eβ).1
  have hgv : (g : G) • v = v := c.actor_le g.property
  have hgen : I ⊔ I.conjBy (g : G) = Q F v := by
    dsimp only [I]
    rw [conjBy,map_inf _ _ _ (MulAut.conj (g : G)).injective,←Q_translate,←Q_translate,hgv,hg]
    exact (c.seed_eq_core_intersections h hS hb ht hne).symm.trans hs
  have hRQ : d.residual ≤ Q F v := (inf_le_left.trans inf_le_left).trans d.separated
  have hRD : d.residual ≤ D F m t := inf_le_left.trans inf_le_left
  have hfix : d.residual ⊓ centralizer (I : Set G) = ⊥ :=
    residual_centralizer_bot c.actor (Q F v) I A d.residual (g : G)
      hgenL g.property hgen hnI (hAL.trans hnQ) hRQ (d.residual_centralizes h)
      (fun r hr => elemPow_eq_one_of_isElementaryAbelian r (hRD hr)) hω
  have hDZ : D F m t ≤ centralizer (D F m t : Set G) := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hy⟩ : D F m t) ⟨x,hx⟩)
  have hRI : ⁅d.residual,I⁆ ≤ Z F m :=
    (commutator_mono (hRD.trans inf_le_left) inf_le_right).trans
      (c.beta_core_frattini_eq h hB hSyl hb hactor hcentral ht hne hcomm).2.le
  let : Finite (Z F m) := Finite.of_injective
    (inclusion (Z_le_stabilizer F m)) (inclusion_injective _)
  let := graph_Z_elementary h m
  have hRc := card_le_of_central_index_two d.residual I (D F m t) (Z F m)
    (c.dihedral_seed_factor_index h hB hSyl hS hb ht hne hnot eβ)
    (hRD.trans hDZ) hRI
    ((le_centralizer_iff.mp (graph_Q_centralizes_Z h m)).trans
      (centralizer_le (hRD.trans inf_le_left))) hfix
  have hk := (c.dihedral_central_core_structure h hB hSyl hb hactor hcentral
    ht hne hcomm.le hnot eβ).1
  rw [c.central_middle_center_card h hB hSyl hb hactor hcentral E,hk] at hRc
  obtain ⟨e,_⟩ := d.direct_product h hS hb (hd.symm ▸ hω)
  rw [←d.residual_eq_source h hS hb (hd.symm ▸ hω)] at e
  have hcard : Nat.card (D F m t) = 4 * Nat.card d.residual := by
    rw [←Nat.card_congr e.toEquiv,Nat.card_prod,c.central_center_card E hω,hk]
    norm_num
  omega

private theorem dihedral_beta_card
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m)
    (hnot : ¬ stabilizer F v ≤ normalizer ((Q F m ⊓ Q F v : Subgroup G) : Set G))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* DihedralGroup 5)
    (hk : Nat.card k = 2) : Nat.card (Q F m) = 4 * Nat.card (D F m t) := by
  let := finite_endpoints h
  let : Finite (Q F m) := Finite.of_injective
    (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  have hS := source_kernel_sylow h hB hSyl
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  let I := Q F v ⊓ Q F m
  have hDI : D F m t ≤ I := le_inf d.separated inf_le_left
  let : Finite I := Finite.of_injective (inclusion (show I ≤ Q F m from inf_le_right)) (inclusion_injective _)
  have hI := ((D F m t).subgroupOf I).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hDI).toEquiv] at hI
  change (D F m t).relIndex I * Nat.card (D F m t) = Nat.card I at hI
  rw [c.dihedral_seed_factor_index h hB hSyl hS hb ht hne hnot eβ] at hI
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
  rw [hi',←hI] at hQb
  omega

/-- The dihedral beta quotient is excluded in both the exceptional and regular branches. -/
theorem BTwoCenterActionData.not_dihedral_beta
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
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* DihedralGroup 5) : False := by
  by_cases hD : D F m t = Z F v
  · exact c.not_exceptional_dihedral_beta h hB hSyl hb hactor hcentral ht hne hcomm hnot hD E eβ
  let := finite_endpoints h
  let : Finite (Q F m) := Finite.of_injective
    (inclusion (Q_le_stabilizer F m)) (inclusion_injective _)
  let : Finite (D F m t) := Finite.of_injective
    (inclusion (show D F m t ≤ Q F m from inf_le_left)) (inclusion_injective _)
  have hS := source_kernel_sylow h hB hSyl
  have hω := c.omega_eq_bot_of_central_neighbor h hB hSyl hactor hcentral
  obtain ⟨_,_,_,_,hDE,hdec,_,_⟩ := c.central_D_structure h hS hb hω ht hne
  let := hDE
  have hZD : Z F v ≤ D F m t := hdec ▸ le_sup_left
  have hk := (c.dihedral_central_core_structure h hB hSyl hb hactor hcentral ht hne hcomm.le hnot eβ).1
  have hZc : Nat.card (Z F v) = 4 := by rw [c.central_center_card E hω,hk]; norm_num
  have hDc : Nat.card (D F m t) = 8 := by
    have hi := ((Z F v).subgroupOf (D F m t)).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv,hZc] at hi
    change (Z F v).relIndex (D F m t) * 4 = Nat.card (D F m t) at hi
    have hne1 : (Z F v).relIndex (D F m t) ≠ 1 := by
      intro hh
      exact hD (le_antisymm (relIndex_eq_one.mp hh) hZD)
    have hpos : 0 < Nat.card (D F m t) := Nat.card_pos
    have hbound := c.dihedral_D_card_le_eight h hB hSyl hb hactor hcentral ht hne hcomm hnot eβ E
    omega
  have hQb : Nat.card (Q F m) = 32 := by
    rw [dihedral_beta_card h hB hSyl hb c ht hne hnot eβ hk,hDc]
  have hZb : Nat.card (Z F m) = 2 :=
    (c.central_middle_center_card h hB hSyl hb hactor hcentral E).trans hk
  let H := stabilizer F m
  let a : pCore 2 H ≃* Q F m :=
    (pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  have hQc : Nat.card (pCore 2 H) = 32 := (Nat.card_congr a.toEquiv).trans hQb
  have hnc : ¬ IsMulCommutative (pCore 2 H) := by
    intro hc
    let := hc
    let : IsMulCommutative (Q F m) :=
      ⟨⟨fun x y => a.symm.injective (by rw [map_mul,map_mul,mul_comm])⟩⟩
    have hh : Z F m = ⊥ :=
      (c.beta_core_frattini_eq h hB hSyl hb hactor hcentral ht hne hcomm).2.symm.trans
        (commutator_self_eq_bot_iff.mpr inferInstance)
    rw [hh,Subgroup.card_bot] at hZb
    omega
  let D₀ := (D F m t).subgroupOf (Q F m)
  let : IsElementaryAbelian 2 D₀ := IsElementaryAbelian.subgroupOf inf_le_left
  let D₁ := D₀.map a.symm.toMonoidHom
  let : IsElementaryAbelian 2 D₁ := IsElementaryAbelian.map _
  have hD₁ : Nat.card D₁ = 8 := by
    rw [card_map_of_injective a.symm.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (show D F m t ≤ Q F m from inf_le_left)).toEquiv).trans hDc
  have hno := SmallNonabelianTwoGroup.not_five_dvd_card_of_selfCentralizing
    (pCore 2 H) pCore_isPGroup hnc hQc D₁ inferInstance hD₁
    (source_vertex_core_selfCentralizing h m)
  let A := graphLocalGroup F m
  let : Finite A := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  have hfive : 5 ∣ Nat.card (A ⧸ pCore 2 A) := by
    rw [Nat.card_congr eβ.toEquiv,DihedralGroup.nat_card]
    decide
  exact hno (hfive.trans ((card_quotient_dvd_card (pCore 2 A)).trans
    (card_dvd_of_injective (inclusion (sylowGenerated_le (stabilizer F m))) (inclusion_injective _))))

/-- All supplied graph catalogue rows reduce to a genuine linear beta quotient. -/
theorem BTwoCenterActionData.beta_quotient_linear
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
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k))
    (hmodel : IsRankOneModel (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m))) :
    ∃ n, 0 < n ∧ ClassicalGroup.IsPSL
      (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) 2 (2^n) := by
  rcases c.beta_quotient_linear_or_dihedral h hB hSyl hb hactor hcentral ht hne hcomm.le
    hnot hmodel with hh | hh
  · exact hh
  · obtain ⟨e⟩ := hh
    exact (c.not_dihedral_beta h hB hSyl hb hactor hcentral ht hne hcomm hnot E e).elim

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
