module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Reductions

/-!
# Comparing the two natural X factors at the midpoint

The image of a two-group in SL2(2) has order at most two. Hence any subgroup
with nontrivial image gives the entire action on a natural factor. If the
transported X escaped the original opposite core, its action would force
the original X to centralize the transported moving quotient. This
contradicts the choice of the transported flag. The exact actor kernels
then give the mutual commutator bound. Its nonzero image modulo Z_middle,
together with the binary edge index, puts Z_alpha in the transported X.

The preceding containment Z_alpha <= U_lambda is an explicit input here;
no cross-commutator conclusion is assumed and no midpoint containment is
inferred just from equal cardinalities of unrelated quotients.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), final paragraphs of printed p.907.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary

private theorem two_subgroup_card_le_two (S : Subgroup SL2) (hS : IsPGroup 2 S) :
    Nat.card S ≤ 2 := by
  have hcard : Nat.card SL2 = 6 := by rw [Nat.card_eq_fintype_card]; decide
  have hd : Nat.card S ∣ 6 := hcard ▸ S.card_subgroup_dvd_card
  have hthree : ¬ 3 ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := hS.exists_card_eq
    rw [hn]
    exact Nat.prime_three.coprime_iff_not_dvd.mp ((by decide : Nat.Coprime 3 2).pow_right n)
  have hx : Nat.card S ∈ Nat.divisors 6 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have he : Nat.divisors 6 = {1,2,3,6} := by decide
  rw [he] at hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with h | h | h | h
  · omega
  · omega
  · exact False.elim (hthree (h ▸ dvd_rfl))
  · exact False.elim (hthree (h ▸ (by decide : 3 ∣ 6)))

private theorem factor_commutator_le_of_two_subgroup {G : Type*} [Group G]
    {P H N K : Subgroup G} (n : MarkedFactor P H N K)
    (B E T : Subgroup G) (hBE : B ≤ E) (hEP : E ≤ P)
    (hE : IsPGroup 2 E) (hBK : ¬ B ≤ K) (hNT : N ≤ T)
    (hBT : ⁅H,B⁆ ≤ T) : ⁅H,E⁆ ≤ T := by
  let EB := (E.subgroupOf P).map n.val.projection
  let BB := (B.subgroupOf P).map n.val.projection
  have hsmall : Nat.card EB ≤ 2 := two_subgroup_card_le_two EB
    (hE.comap_subtype.map n.val.projection)
  have hn : BB ≠ ⊥ := by
    intro hh
    apply hBK
    have hk := (Subgroup.map_eq_bot_iff _).mp hh
    rw [n.property] at hk
    intro b hb
    exact hk (show (⟨b, hEP (hBE hb)⟩ : P) ∈ B.subgroupOf P from hb)
  have hl : 1 < Nat.card BB := (one_lt_card_iff_ne_bot BB).mpr hn
  have heq : BB = EB := eq_of_le_of_card_ge
    (map_mono (show B.subgroupOf P ≤ E.subgroupOf P from fun _ hx => hBE hx)) (by omega)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro e he x hx
  let a : P := ⟨e,hEP he⟩
  have ha : n.val.projection a ∈ BB := heq.symm ▸ mem_map_of_mem n.val.projection he
  obtain ⟨b,hb,hba⟩ := ha
  let u : H := ⟨x,hx⟩
  let ca : H := ⟨e*x*e⁻¹, (mem_normalizer_iff.mp (n.val.normalized a.property) _).mp hx⟩
  let cb : H := ⟨(b:G)*x*(b:G)⁻¹, (mem_normalizer_iff.mp (n.val.normalized b.property) _).mp hx⟩
  have hec : n.val.coordinates ca = n.val.coordinates cb := by
    apply Multiplicative.toAdd.injective
    rw [n.val.action a u ca rfl, n.val.action b u cb rfl, hba]
  have hk : (ca*u⁻¹)*(cb*u⁻¹)⁻¹ ∈ n.val.coordinates.ker := by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, hec, mul_inv_cancel]
  rw [n.val.kernel] at hk
  have hbt : ((cb*u⁻¹ : H):G) ∈ T :=
    (commutator_comm H B ▸ hBT) (commutator_mem_commutator hb hx)
  have ht := T.mul_mem (hNT hk) hbt
  change (e*x*e⁻¹*x⁻¹) * ((b:G)*x*(b:G)⁻¹*x⁻¹)⁻¹ *
    ((b:G)*x*(b:G)⁻¹*x⁻¹) ∈ T at ht
  simpa only [inv_mul_cancel_right, commutatorElement_def] using ht

private theorem index_two_generation {G : Type*} [Group G]
    (H B C N : Subgroup G) (hBN : B ≤ N) (hCH : C ≤ H)
    (hi : B.relIndex H = 2) (hnot : ¬ C ≤ N) : H ≤ C ⊔ N := by
  obtain ⟨a, _, _, hcosets⟩ := relIndex_eq_two_iff_exists_notMem_and.mp hi
  obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp hnot
  have hxa : x * a ∈ B := (hcosets x (hCH hx)).resolve_right (fun h => hxn (hBN h))
  have ha : a ∈ C ⊔ N := by
    have hh := (C ⊔ N).mul_mem ((C ⊔ N).inv_mem (mem_sup_left hx))
      (mem_sup_right (hBN hxa))
    simpa only [inv_mul_cancel_left] using hh
  intro y hy
  rcases hcosets y hy with hya | hyb
  · have hh := (C ⊔ N).mul_mem (mem_sup_right (hBN hya)) ((C ⊔ N).inv_mem ha)
    simpa only [mul_inv_cancel_right] using hh
  · exact mem_sup_right (hBN hyb)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The two natural X factors give the opposite-core containment, their
mutual commutator bound and the original center in the transported X. The
preceding central-layer containment remains an explicit hypothesis. -/
theorem middle_X_pair_of_center_le_second
    (source : LocalSource L R) (geometry : Geometry R) (hlarge : 2 < geometry.b R)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (moving : MovingFactor source i p.delta0) (x : XFactor source i p.delta0)
    (e : M) (he : flagIncident source i 1 e)
    (hcross : ¬ X source i p.delta0 ≤
      (localFlagKernel source (!i) e).map t.conjugation.toMonoidHom)
    (hcenter : Z R (alpha R) ≤
      (secondFlagLayer source i e).map t.conjugation.toMonoidHom) :
    (X source i e).map t.conjugation.toMonoidHom ≤ localFlagKernel source (!i) p.delta0 ∧
      ⁅X source i p.delta0, (X source i e).map t.conjugation.toMonoidHom⁆ ≤ Z R (alpha R) ∧
      Z R (alpha R) ≤ (X source i e).map t.conjugation.toMonoidHom := by
  let f := t.conjugation.toMonoidHom
  let A := X source i p.delta0
  let B := (X source i e).map f
  let E := (Y source i e).map f
  let T := (secondFlagLayer source i e).map f
  let P := (localFlagActor source (!i) e).map f
  let K := (localFlagKernel source (!i) e).map f
  have hQ : Q R (beta R) ≤ P :=
    (t.map_first_kernel source i hkernel).symm.le.trans
      (map_mono (Incident.flagKernel_le_incidentActor source i e he))
  have hAQ : A ≤ Q R (beta R) :=
    (X_le_second source geometry hlarge i p.delta0).trans
      ((secondFlagLayer_le_radius source i p.delta0).trans
        ((V_le_Q geometry hlarge _ rfl).trans (Q_le_adjacent_h R rfl (base_adjacent R))))
  have hAP : A ≤ P := hAQ.trans hQ
  have hEP : E ≤ localFlagActor source (!i) p.delta0 := by
    have hh : Y source i e ≤ Q R (beta R) :=
      (Y_le_radius source i e).trans
        ((V_le_Q geometry hlarge _ rfl).trans (Q_le_adjacent_h R rfl (base_adjacent R)))
    have hm := map_mono (f := f) hh
    change E ≤ (Q R (beta R)).map f at hm
    rw [t.map_Q_beta] at hm
    exact hm.trans (hkernel ▸ Incident.flagKernel_le_incidentActor source i p.delta0 p.delta0_neighbor)
  have hBE : B ≤ E := map_mono
    ((X_le_second source geometry hlarge i e).trans (second_le_Y source i e))
  have hpE : IsPGroup 2 E :=
    ((Q_isPGroup R source.two_group source.core_le (alpha R) rfl).to_le
      ((Y_le_radius source i e).trans (V_le_Q geometry hlarge _ rfl))).map f
  obtain ⟨me⟩ : Nonempty (MovingFactor source i e) := by
    simpa only [inv_mul_cancel_right] using
      movingFactor_conjugate source geometry hlarge i (e*p.delta0⁻¹) p.delta0 moving
  obtain ⟨xe⟩ : Nonempty (XFactor source i e) := by
    simpa only [inv_mul_cancel_right] using
      XFactor_conjugate source geometry hlarge i (e*p.delta0⁻¹) p.delta0 x
  have nm := markedFactorMap t.conjugation me
  have nx := markedFactorMap t.conjugation xe
  have hBK : B ≤ localFlagKernel source (!i) p.delta0 := by
    by_contra hn
    have hAB : ⁅A,B⁆ ≤ T :=
      (le_normalizer_iff_commutator_le_right.mp (hAP.trans nx.val.normalized)).trans
        (map_mono (X_le_second source geometry hlarge i e))
    have hAE : ⁅A,E⁆ ≤ T :=
      factor_commutator_le_of_two_subgroup x B E T hBE hEP hpE hn hcenter hAB
    apply hcross
    apply (markedFactor_commutator_iff nm A hAP).mp
    have hH : (⁅Y source i e, localFlagActor source (!i) e⁆ ⊔
        secondFlagLayer source i e).map f ≤ E :=
      map_mono (sup_le (le_normalizer_iff_commutator_le_left.mp (Y_normalized source i e))
        (second_le_Y source i e))
    exact (commutator_mono hH le_rfl).trans (commutator_comm A E ▸ hAE)
  have hAB : ⁅A,B⁆ ≤ Z R (alpha R) :=
    (markedFactor_commutator_iff x B (hBE.trans hEP)).mpr hBK
  have hnon : ¬ ⁅A,B⁆ ≤ Z R p.middle := by
    intro hh
    apply hcross
    apply (markedFactor_commutator_iff nx A hAP).mp
    simpa only [t.map_Z_alpha, commutator_comm] using hh
  have hZ : Z R (alpha R) ≤ ⁅A,B⁆ ⊔ Z R p.middle :=
    index_two_generation _ (Z R (beta R)) _ _
      (edge_Z_le p.middle (beta R) (by
        have hc := adjacent_color_ne R p.middle_neighbor
        have hb : color R (beta R) = true := rfl
        cases hc' : color R p.middle <;> simp_all) (adjacent_symm R p.middle_neighbor))
      hAB (early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R)) hnon
  refine ⟨hBK,hAB,hZ.trans (sup_le ?_ ?_)⟩
  · exact le_normalizer_iff_commutator_le_right.mp (hAP.trans nx.val.normalized)
  · rw [← t.map_Z_alpha]
    exact map_mono (show Z R (alpha R) ≤ X source i e from le_sup_right)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
