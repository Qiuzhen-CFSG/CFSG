module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCubic
public import Theory.SpecificGroups.SL2.SylowNormalizerCard
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.Data.Fintype.EquivFin

/-!
# The field-four Cartan and the actual neighboring core factors

The marked alpha action identifies the neighbor stabilizer with the preimage
of its SL₂ Sylow normalizer, giving valence q_alpha + 1. At q_alpha = 2,
a cubic fixing an edge therefore fixes the entire alpha neighborhood.
The field-four beta quotient supplies a cubic in the actual edge Sylow
normalizer. Its order and the normalizer index show that its cyclic subgroup
complements the edge two-core in the beta local Borel.

In the exceptional branch, Q_mu = V_mu at every alpha neighbor. The chosen
Cartan normalizes every literal Q_mu intersect Q_alpha. These are the
source invariance inputs for the two four-group complements in (5.16);
the four-group complements and the beta extension splitting are not asserted.

Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.16), pp.116--117, and the field-four case of (10.9), p.163.
The companion source module retains the original full Borel and endpoint maps.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph Noncommuting
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

/-- The actual alpha valence is computed from its marked natural quotient. -/
theorem BTwoCenterActionData.neighbor_card
    (h : LocallyRankOneTriple P B) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W) :
    Nat.card ((graph F).neighborSet v) = Nat.card k + 1 := by
  have horbit : MulAction.orbit c.actor m = (graph F).neighborSet v := by
    ext u
    constructor
    · rintro ⟨g,rfl⟩
      have hh := (Subgroup.CosetGeometry.translationGraphIso F (g : G)).map_adj_iff.mpr c.middle
      change (graph F).Adj ((g : G) • v) ((g : G) • m) at hh
      rwa [c.actor_le g.property] at hh
    · intro hu
      obtain ⟨a,ha,he⟩ := locally_transitive F c.middle hu
      obtain ⟨l,hl,b,hb,hab⟩ := c.factor a ha
      refine ⟨⟨l,hl⟩,?_⟩
      change l • m = u
      simpa only [hab,mul_smul,show b • m = m from hb.2] using he
  have hstab : MulAction.stabilizer c.actor m =
      (normalizer (c.imageSylow : Set SL(2,k))).comap c.quotient := by
    ext g
    constructor
    · intro hg
      let T := Q F m ⊔ Q F v
      have hT : T ≤ c.actor := sup_le c.neighbor_core_le c.core_le
      have hpre : (c.imageSylow : Subgroup SL(2,k)).comap c.quotient = T.subgroupOf c.actor := by
        rw [←c.neighbor_image,comap_map_eq,c.kernel,subgroupOf_sup c.neighbor_core_le c.core_le]
      have hgv : (g : G) • v = v := c.actor_le g.property
      have hgm : (g : G) • m = m := hg
      have hconj : T.map (MulAut.conj (g : G)).toMonoidHom = T := by
        rw [Subgroup.map_sup,←Q_translate,←Q_translate,hgm,hgv]
      have hgn : g ∈ normalizer (T.subgroupOf c.actor : Set c.actor) := by
        rw [←subgroupOf_normalizer_eq hT]
        exact mem_normalizer_iff_map_conj_eq.mpr hconj
      have hh := comap_normalizer_eq_of_surjective (c.imageSylow : Subgroup SL(2,k)) c.onto
      rw [hpre] at hh
      exact hh ▸ hgn
    · exact c.normalizer_fixes_neighbor h g
  rw [←horbit]
  change (MulAction.orbit c.actor m).ncard = _
  rw [←MulAction.index_stabilizer,hstab,index_comap_of_surjective _ c.onto]
  have hc := (normalizer (c.imageSylow : Set SL(2,k))).card_mul_index
  have hN : Nat.card (normalizer (c.imageSylow : Set SL(2,k))) = Nat.card k * (Nat.card k - 1) :=
    Matrix.SpecialLinearGroup.card_sylow_normalizer_even c.imageSylow
  rw [hN,
    BenderSuzuki.External.huppert614_card_specialLinearGroup] at hc
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have hpoly : Nat.card k ^ 2 - 1 = (Nat.card k - 1) * (Nat.card k + 1) := by
    have hs := Nat.sub_add_cancel (show 1 ≤ Nat.card k from by omega)
    have ht := Nat.sub_add_cancel (show 1 ≤ Nat.card k ^ 2 from by nlinarith)
    nlinarith
  rw [hpoly,←mul_assoc] at hc
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos Nat.card_pos (by omega)) hc

private theorem cubic_three_fixed {X : Type*} [Finite X]
    (hX : Nat.card X = 3) (a : Equiv.Perm X) (ha : a ^ 3 = 1)
    (x : X) (hx : a x = x) : a = 1 := by
  let : Fintype X := Fintype.ofFinite X
  let e : X ≃ Fin 3 := Fintype.equivFinOfCardEq (by simpa using hX)
  let b := e.permCongr a
  have hb : b ^ 3 = 1 := by
    change (e.permCongrHom a) ^ 3 = 1
    rw [←map_pow,ha,map_one]
  have hbx : b (e x) = e x := by simp [b,Equiv.permCongr,hx]
  have hsmall : ∀ (b : Equiv.Perm (Fin 3)) (i : Fin 3), b ^ 3 = 1 → b i = i → b = 1 := by
    decide +kernel
  have heq := hsmall b (e x) hb hbx
  apply e.permCongr.injective
  change e.permCongrHom a = e.permCongrHom 1
  rw [map_one]
  exact heq

/-- A cubic fixing an edge at a binary alpha vertex lies in the whole local permutation kernel. -/
theorem BTwoCenterActionData.binary_edge_cubic_fixes_ball
    (h : LocallyRankOneTriple P B) {v m w : Vertex F}
    (c : BTwoCenterActionData F v m w k W) (hk : Nat.card k = 2)
    (a : G) (hav : a ∈ stabilizer F v) (ham : a ∈ stabilizer F m)
    (ha : a ^ 3 = 1) : a ∈ U F v := by
  let := finite_endpoints h
  let : Finite ((graph F).neighborSet v) := finite_neighbors F v
  let aS : stabilizer F v := ⟨a,hav⟩
  have hact : localAction F v aS = 1 := by
    refine cubic_three_fixed (by rw [c.neighbor_card h,hk]) (localAction F v aS) ?_
      ⟨m,c.middle⟩ ?_
    · rw [←map_pow]
      have haa : aS ^ 3 = 1 := Subtype.ext ha
      rw [haa,map_one]
    · apply Subtype.ext
      exact ham
  have haK : aS ∈ (localAction F v).ker := hact
  rw [localAction_ker] at haK
  exact haK

/-- The field-four beta Borel has an actual cubic complement to its edge two-core. -/
theorem field_four_edge_cubic
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    {v m : Vertex F} (hm : (graph F).Adj v m)
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hK : Nat.card K = 4) :
    ∃ a : G, a ∈ graphLocalGroup F m ∧ a ∈ stabilizer F v ∧
      orderOf a = 3 ∧ a ∈ normalizer
        ((stabilizer F v ⊓ stabilizer F m).pCoreIn 2 : Set G) ∧
      Disjoint ((stabilizer F v ⊓ stabilizer F m).pCoreIn 2) (zpowers a) ∧
      (stabilizer F v ⊓ stabilizer F m).pCoreIn 2 ⊔ zpowers a =
        graphLocalGroup F m ⊓ stabilizer F v := by
  let := finite_endpoints h
  let L := graphLocalGroup F m
  let E := stabilizer F m ⊓ stabilizer F v
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  obtain ⟨T,hT⟩ := source_edge_vertex_sylow h hSyl hm.symm
  have hES := sylow_image_eq_edge_core (stabilizer F m) E inf_le_left
    (source_edge_core_sylow h hB hm.symm) T hT
  obtain ⟨R,hR⟩ := T.exists_map_subtype_eq_of_le (H := L) (sylowGenerated_le _)
    (sylow_le_sylowGenerated _ T)
  have hRS : (R : Subgroup L).map L.subtype = E.pCoreIn 2 := hR.trans hES
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Rq := R.mapSurjective hq
  have hN : (normalizer (R : Set L)).map q = normalizer (Rq : Set SL(2,K)) :=
    R.normalizer_map_surjective q hq
  have hcard : Nat.card (normalizer (Rq : Set SL(2,K))) = 12 := by
    have hh : Nat.card (normalizer (Rq : Set SL(2,K))) = Nat.card K * (Nat.card K - 1) :=
      Matrix.SpecialLinearGroup.card_sylow_normalizer_even Rq
    simpa only [hK] using hh
  have hk : q.ker ≤ (R : Subgroup L) := by
    intro x hx
    have hxcore : x ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff x).mp
      exact e.injective (hx.trans e.map_one.symm)
    exact pCore_isPGroup.le_sylow_of_normal R hxcore
  have hindex : (R : Subgroup L).relIndex (normalizer (R : Set L)) = 3 := by
    have hh := relIndex_map_map q (R : Subgroup L) (normalizer (R : Set L))
    have hkN : q.ker ≤ normalizer (R : Set L) := hk.trans R.le_normalizer
    rw [sup_eq_left.mpr hk,sup_eq_left.mpr hkN,hN] at hh
    rw [←hh]
    have hcount := relIndex_mul_relIndex (⊥ : Subgroup SL(2,K))
      (Rq : Subgroup SL(2,K)) (normalizer (Rq : Set SL(2,K))) bot_le Rq.le_normalizer
    have hRq : Nat.card Rq = 4 := by
      have hc := Nat.card_congr
        (Matrix.SpecialLinearGroup.sylowEquivAdditive K 2 Rq).symm.toEquiv
      exact hc.trans hK
    simp only [relIndex_bot_left,hRq,hcard] at hcount
    change 4 * (R.map q).relIndex (normalizer (Rq : Set SL(2,K))) = 12 at hcount
    omega
  have hdiv : 3 ∣ Nat.card (normalizer (R : Set L)) := by
    apply (show 3 ∣ Nat.card ((normalizer (R : Set L)).map q) from ?_).trans
      (card_map_dvd (normalizer (R : Set L)) q)
    rw [hN,hcard]
    decide
  let N := normalizer (R : Set L)
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := N) 3 hdiv
  have hcomp : ((R : Subgroup L).subgroupOf N).IsComplement' (zpowers a) := by
    have hc := ((R : Subgroup L).subgroupOf N).card_mul_index
    change Nat.card ((R : Subgroup L).subgroupOf N) * (R : Subgroup L).relIndex N = Nat.card N at hc
    apply isComplement'_of_coprime
    · rw [Nat.card_zpowers,ha]
      rwa [hindex] at hc
    · rw [Nat.card_zpowers,ha]
      obtain ⟨n,hn⟩ := IsPGroup.iff_card.mp (R.isPGroup'.comap_subtype (K := N))
      change Nat.card ((R : Subgroup L).subgroupOf N) = 2^n at hn
      rw [hn]
      exact (show Nat.Coprime 2 3 from by decide).pow_left n
  let f := L.subtype.comp N.subtype
  have hf : Function.Injective f := L.subtype_injective.comp N.subtype_injective
  have hRN : ((R : Subgroup L).subgroupOf N).map f = E.pCoreIn 2 := by
    change ((R : Subgroup L).subgroupOf N).map (L.subtype.comp N.subtype) = _
    have hle : (R : Subgroup L) ≤ N := R.le_normalizer
    rw [←map_map,map_subgroupOf_eq_of_le hle,hRS]
  have hNmap : N.map L.subtype = L ⊓ stabilizer F v := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      have hyN : (y : G) ∈ normalizer (E.pCoreIn 2 : Set G) := by
        rw [←hRS]
        exact (R : Subgroup L).le_normalizer_map L.subtype (mem_map_of_mem _ hy)
      have hyE : (y : G) ∈ E := by
        change (y : G) ∈ stabilizer F m ⊓ stabilizer F v
        rw [←source_edge_core_normalizer h hB hm.symm]
        exact ⟨sylowGenerated_le _ y.property,hyN⟩
      exact ⟨y.property,hyE.2⟩
    · rintro ⟨hxL,hxv⟩
      let y : L := ⟨x,hxL⟩
      refine ⟨y,?_,rfl⟩
      have hxN : x ∈ normalizer (E.pCoreIn 2 : Set G) := by
        have hxE : x ∈ E := ⟨sylowGenerated_le _ hxL,hxv⟩
        change x ∈ stabilizer F m ⊓ stabilizer F v at hxE
        rw [←source_edge_core_normalizer h hB hm.symm] at hxE
        exact hxE.2
      have hRpre : (R : Subgroup L) = (E.pCoreIn 2).subgroupOf L := by
        rw [←hRS]
        change (R : Subgroup L) = ((R : Subgroup L).map L.subtype).comap L.subtype
        rw [comap_map_eq_self_of_injective L.subtype_injective]
      change y ∈ normalizer ((R : Subgroup L) : Set L)
      rw [hRpre,←subgroupOf_normalizer_eq (hRS ▸ map_subtype_le _)]
      exact hxN
  have han : ((a : L) : G) ∈ normalizer (E.pCoreIn 2 : Set G) := by
    rw [←hRS]
    exact (R : Subgroup L).le_normalizer_map L.subtype (mem_map_of_mem _ a.property)
  have haE : ((a : L) : G) ∈ E := by
    change ((a : L) : G) ∈ stabilizer F m ⊓ stabilizer F v
    rw [←source_edge_core_normalizer h hB hm.symm]
    exact ⟨sylowGenerated_le _ (a : L).property,han⟩
  refine ⟨((a : L) : G),(a : L).property,haE.2,?_,?_,?_,?_⟩
  · exact (Subgroup.orderOf_coe (a : L)).trans ((Subgroup.orderOf_coe a).trans ha)
  · simpa only [E,inf_comm] using han
  · have hh := disjoint_map hf hcomp.disjoint
    rw [hRN,MonoidHom.map_zpowers] at hh
    change Disjoint (E.pCoreIn 2) (zpowers ((a : L) : G)) at hh
    simpa only [E,inf_comm] using hh
  · have hh := congrArg (map f) hcomp.sup_eq_top
    have htop : (⊤ : Subgroup N).map f = N.map L.subtype := by
      change (⊤ : Subgroup N).map (L.subtype.comp N.subtype) = _
      rw [←map_map,←MonoidHom.range_eq_map,range_subtype]
    rw [Subgroup.map_sup,hRN,MonoidHom.map_zpowers,htop,hNmap] at hh
    change E.pCoreIn 2 ⊔ zpowers ((a : L) : G) = L ⊓ stabilizer F v at hh
    simpa only [E,inf_comm] using hh


/-- The field-four Cartan lies in the alpha local kernel and fixes each
literal neighboring core factor. The radius-one spans equal those cores. -/
theorem BTwoCenterActionData.field_four_cartan
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hSyl : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (hb : b F = 2) {v m w t : Vertex F}
    (c : BTwoCenterActionData F v m w k W)
    (ht : (graph F).Adj v t) (hne : t ≠ m) (hD : D F m t = Z F v)
    (e : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,K))
    (hk : Nat.card k = 2) (hK : Nat.card K = 4) :
    ∃ a : G, a ∈ graphLocalGroup F m ∧ orderOf a = 3 ∧ a ∈ U F v ∧
      Disjoint ((stabilizer F v ⊓ stabilizer F m).pCoreIn 2) (zpowers a) ∧
      (stabilizer F v ⊓ stabilizer F m).pCoreIn 2 ⊔ zpowers a =
        graphLocalGroup F m ⊓ stabilizer F v ∧
      ∀ μ, (graph F).Adj v μ → Q F μ = V F μ 1 ∧
        a ∈ normalizer ((Q F μ ⊓ Q F v : Subgroup G) : Set G) := by
  let := finite_endpoints h
  obtain ⟨a,ha,hav,hoa,_,hd,hgen⟩ := field_four_edge_cubic h hB hSyl c.middle e hK
  have hball := c.binary_edge_cubic_fixes_ball h hk a hav
    (sylowGenerated_le _ ha) (by rw [←hoa]; exact pow_orderOf_eq_one a)
  refine ⟨a,ha,hoa,hball,hd,hgen,?_⟩
  intro μ hμ
  have hcore := c.exceptional_beta_core h (source_kernel_sylow h hB hSyl) hb ht hne hD
  have hamu : a • μ = μ := hball μ ((mem_ball_one F v μ).mpr (Or.inl hμ))
  constructor
  · obtain ⟨g,hgv,hgm⟩ := locally_transitive F c.middle hμ
    have hh := congrArg (map (MulAut.conj g).toMonoidHom) hcore
    simpa only [←Q_translate,←V_translate,hgm] using hh
  · apply mem_normalizer_iff_map_conj_eq.mpr
    change (Q F μ ⊓ Q F v).map (MulAut.conj a).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj a).injective,←Q_translate,←Q_translate,hamu]
    exact congrArg (Q F μ ⊓ ·) (congrArg (Q F) hav)

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
