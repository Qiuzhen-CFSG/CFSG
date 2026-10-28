module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCubic
public import Theory.SpecificGroups.Suzuki.BorelElementary

/-!
# The central seed in a hypothetical Suzuki beta branch

The central seed has an elementary quotient by D_alpha and contains the
adjacent-core intersection. Earlier (6.5) makes its beta image nontrivial.
The full edge normalizer preserves this image, so the concrete Suzuki
omega and torus calculation identifies it with the quotient Sylow center.
The full alpha core, by contrast, maps onto that entire quotient Sylow.

The two image orders and the proved seed square formula give the exact
indices: D_alpha has index q_beta in the adjacent-core intersection,
index q_beta squared in the seed, and index q_beta cubed in Q_alpha.
The seed has index q_beta in Q_alpha and is therefore proper. The alpha
field order is at most q_beta. All maps use the actual beta quotient.

This establishes the quantitative obstruction in the nonlinear branch of
the p.159 saturation argument. It does not prove saturation or exclude the
Suzuki branch; proving general saturation would contradict the properness
proved here. The binary Suzuki parameter is not covered by these omega
calculations. Earlier (6.5), (7.1), and (7.4) inputs remain explicit.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
proof of (10.7), printed pp.158--159; Suzuki Sylow structure as proved in
Theory.SpecificGroups.Suzuki.SylowOmegaGeometry and BorelElementary.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
open BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]

private theorem elementary_image_of_elementary_section
    {H : Type*} [Group H] (J D L : Subgroup G) (hJL : J ≤ L)
    [(D.subgroupOf J).Normal] [IsElementaryAbelian 2 (J ⧸ D.subgroupOf J)]
    (q : L →* H) (hD : D.subgroupOf L ≤ q.ker) :
    IsElementaryAbelian 2 ((J.subgroupOf L).map q) := by
  let f : J →* (J.subgroupOf L).map q :=
    { toFun := fun x => ⟨q ⟨x,hJL x.property⟩,⟨⟨x,hJL x.property⟩,x.property,rfl⟩⟩
      map_one' := Subtype.ext q.map_one
      map_mul' := fun x y => Subtype.ext (q.map_mul (⟨x,hJL x.property⟩ : L) (⟨y,hJL y.property⟩ : L)) }
  have hker : D.subgroupOf J ≤ f.ker := by
    intro x hx
    exact Subtype.ext (hD hx)
  let f' := QuotientGroup.lift (D.subgroupOf J) f hker
  apply IsElementaryAbelian.of_surjective f'
  intro x
  obtain ⟨a,ha,he⟩ := x.property
  exact ⟨QuotientGroup.mk' (D.subgroupOf J) ⟨a,ha⟩,Subtype.ext he⟩

private theorem suzuki_edge_seed_image
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {a b : Vertex F} (hab : (graph F).Adj a b)
    {n : ℕ} (hn : 0 < n)
    (e : (graphLocalGroup F a ⧸ pCore 2 (graphLocalGroup F a)) ≃* SuzukiMatrixGroup n)
    (J D A : Subgroup G)
    (hAS : A ≤ (stabilizer F a ⊓ stabilizer F b).pCoreIn 2)
    (hcover : (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = A ⊔ Q F a)
    (hJS : J ≤ (stabilizer F a ⊓ stabilizer F b).pCoreIn 2)
    (hnJ : stabilizer F a ⊓ stabilizer F b ≤ normalizer (J : Set G))
    (heJ : ¬ J ≤ Q F a) (hD : D ≤ Q F a)
    [(D.subgroupOf J).Normal] [IsElementaryAbelian 2 (J ⧸ D.subgroupOf J)] :
    (Q F a).relIndex J = 2^(2*n+1) ∧
      (Q F a).relIndex A = (2^(2*n+1))^2 := by
  let := finite_endpoints h
  let L := graphLocalGroup F a
  let E := stabilizer F a ⊓ stabilizer F b
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hS hab
  have hES := sylow_image_eq_edge_core (stabilizer F a) E inf_le_left
    (source_edge_core_sylow h hB hab) T hT
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le (H := L) (sylowGenerated_le _)
    (sylow_le_sylowGenerated _ T)
  have hRS : (R : Subgroup L).map L.subtype = E.pCoreIn 2 := hR.trans hES
  have hSL : E.pCoreIn 2 ≤ L := hRS ▸ map_subtype_le _
  have hJL : J ≤ L := hJS.trans hSL
  have hQL : Q F a ≤ L := (graph_Q_le_edgeCore h hab).trans hSL
  have hRs : (R : Subgroup L) = (E.pCoreIn 2).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hRS,map_subgroupOf_eq_of_le hSL]
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hc : L.pCoreIn 2 = Q F a := sylowGenerated_core _
  have hk : q.ker = (Q F a).subgroupOf L := by
    rw [←hc]
    change q.ker = ((pCore 2 L).map L.subtype).comap L.subtype
    rw [comap_map_eq_self_of_injective L.subtype_injective]
    ext x
    change e (QuotientGroup.mk' (pCore 2 L) x) = 1 ↔ x ∈ pCore 2 L
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let J₀ := J.subgroupOf L
  have hJR : J₀ ≤ (R : Subgroup L) := by rw [hRs]; exact comap_mono hJS
  have he : ¬ J₀ ≤ q.ker := by
    rw [hk]
    intro hh
    apply heJ
    have hm := map_mono (f := L.subtype) hh
    rwa [map_subgroupOf_eq_of_le hJL,map_subgroupOf_eq_of_le hQL] at hm
  have hnorm : normalizer (R : Set L) ≤ normalizer (J₀ : Set L) := by
    have hN : normalizer (R : Set L) = (normalizer (E.pCoreIn 2 : Set G)).subgroupOf L := by
      rw [←R.coe_coe,hRs]
      exact (subgroupOf_normalizer_eq hSL).symm
    rw [hN]
    intro x hx
    have hxE : (x : G) ∈ E := by
      change (x : G) ∈ stabilizer F a ⊓ stabilizer F b
      rw [←source_edge_core_normalizer h hB hab]
      exact ⟨sylowGenerated_le _ x.property,hx⟩
    exact le_normalizer_comap L.subtype (hnJ hxE)
  let R' := R.mapSurjective hq
  let : IsElementaryAbelian 2 (J₀.map q) :=
    elementary_image_of_elementary_section J D L hJL q (hk ▸ comap_mono hD)
  have hIm : J₀.map q = (center R').map (R' : Subgroup (SuzukiMatrixGroup n)).subtype := by
    apply suzuki_elementary_eq_center_of_borel_normalized hn (MulEquiv.refl _) R'
      (J₀.map q) (map_mono hJR) (fun hh => he ((Subgroup.map_eq_bot_iff _).mp hh))
    change normalizer ((R : Subgroup L).map q : Set (SuzukiMatrixGroup n)) ≤ _
    rw [←R.normalizer_map_surjective q hq]
    exact (map_mono hnorm).trans (J₀.le_normalizer_map q)
  have hi := relIndex_ker (K := J₀) q
  rw [hk,relIndex_subgroupOf hJL,hIm,
    ←suzukiSylow_omega_eq_center hn (MulEquiv.refl _) R',
    suzukiSylow_omega_card hn (MulEquiv.refl _) R'] at hi
  refine ⟨hi,?_⟩
  have hAL : A ≤ L := hAS.trans hSL
  have hsup : A.subgroupOf L ⊔ q.ker = (R : Subgroup L) := by
    rw [hk,←subgroupOf_sup hAL hQL,←hcover,←hRs]
  have hIA : (A.subgroupOf L).map q = (R' : Subgroup (SuzukiMatrixGroup n)) := by
    change _ = (R : Subgroup L).map q
    rw [←hsup,Subgroup.map_sup,Subgroup.map_ker_self,sup_bot_eq]
  have hiA := relIndex_ker (K := A.subgroupOf L) q
  rw [hk,relIndex_subgroupOf hAL,hIA,suzukiSylow_card hn (MulEquiv.refl _) R'] at hiA
  exact hiA

/-- The seed has the center image of order q_beta, while the full alpha core
has the full beta Sylow image of order q_beta squared. -/
theorem BTwoCenterActionData.suzuki_seed_core_indices
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
    {n : ℕ} (hn : 0 < n)
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SuzukiMatrixGroup n) :
    (Q F m).relIndex (centralSeed F v m t) = 2^(2*n+1) ∧
      (Q F m).relIndex (Q F v) = (2^(2*n+1))^2 := by
  let J := centralSeed F v m t
  have hS := source_kernel_sylow h hB hSyl
  have hIJ := c.seed_eq_core_intersections h hS hb ht hne
  have hJQ : J ≤ Q F v := by rw [show J = centralSeed F v m t from rfl,hIJ]; exact sup_le inf_le_left inf_le_left
  have hNJ : Q F v ⊓ Q F m ≤ J := by
    change _ ≤ centralSeed F v m t
    rw [hIJ]
    exact le_sup_left
  have hnJ := c.seed_stabilizer_normalized h hS hb ht hne
  have heJ : ¬ J ≤ Q F m := by
    intro hh
    have he : J = Q F v ⊓ Q F m := le_antisymm (le_inf hJQ hh) hNJ
    apply hnot
    change stabilizer F v ≤ normalizer (J : Set G) at hnJ
    simpa only [he,inf_comm] using hnJ
  obtain ⟨hN,hE⟩ := c.central_seed_elementary h hB hSyl hb hactor hcentral ht hne hcomm
  let := hN
  let := hE
  have hQv : Q F v ≤ (stabilizer F m ⊓ stabilizer F v).pCoreIn 2 := by
    simpa only [inf_comm] using graph_Q_le_edgeCore h c.middle
  have hQm := graph_Q_le_edgeCore h c.middle.symm
  have hcover : (stabilizer F m ⊓ stabilizer F v).pCoreIn 2 = Q F v ⊔ Q F m := by
    obtain ⟨T,hT⟩ := c.core_product_sylow h
    have he := inf_eq_sylow_map T (isPGroup_pCoreIn 2 (stabilizer F m ⊓ stabilizer F v))
      (hT ▸ sup_le hQm hQv)
    rw [inf_of_le_left ((pCoreIn_le 2 _).trans inf_le_right),hT] at he
    exact he.trans (sup_comm _ _)
  exact suzuki_edge_seed_image h hB hSyl c.middle.symm hn e J (D F m t) (Q F v) hQv hcover
    (hJQ.trans (by simpa only [inf_comm] using graph_Q_le_edgeCore h c.middle))
    (inf_le_right.trans hnJ) heJ inf_le_left

/-- Exact indices in the hypothetical nonbinary Suzuki beta branch.
The seed is proper, so proving general saturation will exclude this branch. -/
theorem BTwoCenterActionData.suzuki_seed_structure
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
    {n : ℕ} (hn : 0 < n)
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SuzukiMatrixGroup n) :
    let q := 2^(2*n+1)
    Nat.card k ≤ q ∧
      (D F m t).relIndex (Q F v ⊓ Q F m) = q ∧
      (D F m t).relIndex (centralSeed F v m t) = q^2 ∧
      (centralSeed F v m t).relIndex (Q F v) = q ∧
      (D F m t).relIndex (Q F v) = q^3 ∧
      centralSeed F v m t ≠ Q F v := by
  let q := 2^(2*n+1)
  let J := centralSeed F v m t
  let I := Q F v ⊓ Q F m
  let a := (D F m t).relIndex (V F m 1 ⊓ Q F v)
  have hS := source_kernel_sylow h hB hSyl
  have hgen := c.seed_eq_core_intersections h hS hb ht hne
  have hJQ : J ≤ Q F v := by rw [show J = centralSeed F v m t from rfl,hgen]; exact sup_le inf_le_left inf_le_left
  have hIJ : I ≤ J := by rw [show J = centralSeed F v m t from rfl,hgen]; exact le_sup_left
  obtain ⟨g,hg,hop⟩ := c.exists_opposite_lift h ht hne
  obtain ⟨d,_,_⟩ := c.exists_oppositeGeometry h hS hb g hg hop
  have hDI : D F m t ≤ I := le_inf d.separated inf_le_left
  have hDIindex : (D F m t).relIndex I = a := c.seed_factor_index_eq h hS hb ht hne
  obtain ⟨_,hcard⟩ := c.central_seed_card_square h hB hSyl hb hactor hcentral ht hne hcomm
  have hDJ : (D F m t).relIndex J = a^2 := hcard
  obtain ⟨hiJ,hiQ⟩ := c.suzuki_seed_core_indices h hB hSyl hb hactor hcentral ht hne hcomm hnot hn e
  have hIeq : I = J ⊓ Q F m := le_antisymm (le_inf hIJ inf_le_right)
    (le_inf (inf_le_left.trans hJQ) inf_le_right)
  have hIJindex : I.relIndex J = q := by rw [hIeq,inf_relIndex_left]; exact hiJ
  have hIQindex : I.relIndex (Q F v) = q^2 := by rw [show I = Q F v ⊓ Q F m from rfl,inf_relIndex_left]; exact hiQ
  have hbound := c.central_seed_field_bound h hB hSyl hb hactor hcentral ht hne hcomm hnot
  change Nat.card k ≤ a at hbound
  have ha : 0 < a := lt_of_lt_of_le (Nat.card_pos (α := k)) hbound
  have hmul := relIndex_mul_relIndex (D F m t) I J hDI hIJ
  rw [hDIindex,hIJindex,hDJ,pow_two] at hmul
  have haq : a = q := (Nat.eq_of_mul_eq_mul_left ha hmul).symm
  have hmulQ := relIndex_mul_relIndex I J (Q F v) hIJ hJQ
  rw [hIJindex,hIQindex,pow_two] at hmulQ
  have hJindex : J.relIndex (Q F v) = q := Nat.eq_of_mul_eq_mul_left
    (pow_pos (by decide : 0 < (2 : ℕ)) _) hmulQ
  have hDQ := relIndex_mul_relIndex (D F m t) J (Q F v) (hDI.trans hIJ) hJQ
  rw [hDJ,haq,hJindex,←pow_succ] at hDQ
  refine ⟨hbound.trans_eq haq,hDIindex.trans haq,by simpa only [haq] using hDJ,hJindex,hDQ.symm,?_⟩
  intro he
  have hi : J.relIndex (Q F v) = 1 := relIndex_eq_one.mpr he.ge
  have hq : 1 < q := Nat.one_lt_pow (by omega) (by decide)
  omega

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
