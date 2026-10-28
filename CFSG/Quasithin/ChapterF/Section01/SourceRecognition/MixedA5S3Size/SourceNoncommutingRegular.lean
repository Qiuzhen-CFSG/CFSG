module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceNoncommutingParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoBetaCore
public import Theory.GroupTheory.CentralBinaryCentralizerCard

/-!
# A sufficient bound for the mixed noncommuting Borel core

In the mixed A₅/S₃ distance-two branch the critical vertex is cubic and
its middle vertex is quintic. The natural center field is binary, while
the middle quotient is SL₂(4). The seed has index four in the adjacent
core intersection. Its commutator pairing with that intersection takes
values in the middle center of order two; its kernel on the seed is the
critical center of order four. The pairing bounds the seed by sixteen,
the middle core by 128, and the original Borel core by 512.

This bound covers both exceptional and regular seed branches. Together
with the mixed Sylow/Borel index it suffices for the Chapter 15 lower
bound 2048; a full regular-profile classification is unnecessary here.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(10.7), pp.158--159, and the central decomposition preceding (10.8),
pp.159--161; Aschbacher--Smith, F.1.9--12 and 15.2.6--8.
-/

public noncomputable section
open Subgroup
open scoped Pointwise commutatorElement IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.MixedDGS
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph

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

variable {G : Type*} [Group G] [Finite G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
local notation "F" => family P
variable {k W : Type*} [Field k] [Finite k] [CharP k 2]
  [AddCommGroup W] [Module (ZMod 2) W]
local instance : Algebra (ZMod 2) k := ZMod.algebra k 2

private theorem linear_four_middle_core_card_le
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
    (eβ : (graphLocalGroup F m ⧸ pCore 2 (graphLocalGroup F m)) ≃* SL(2,GaloisField 2 2))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → k)) (hk : Nat.card k = 2) :
    Nat.card (Q F m) ≤ 128 := by
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
  have hs := (c.linear_seed_eq_core_and_index h hB hSyl hS hb ht hne hnot eβ).1
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
  have hdec := d.decomposition h hS hb
  have hZD : Z F v ≤ D F m t := hdec ▸ le_sup_left
  have hDI : D F m t ≤ I := le_inf d.separated inf_le_left
  have hZI : Z F v ≤ centralizer (I : Set G) :=
    (le_centralizer_iff.mp (graph_Q_centralizes_Z h v)).trans (centralizer_le inf_le_left)
  have hZR : Z F v ≤ centralizer (d.residual : Set G) :=
    (le_centralizer_iff.mp (graph_Q_centralizes_Z h v)).trans (centralizer_le hRQ)
  have hC : D F m t ⊓ centralizer (I : Set G) = Z F v := by
    apply le_antisymm
    · intro x hx
      have hprod : x ∈ (Z F v : Set G) * (d.residual : Set G) := by
        rw [←coe_mul_of_left_le_normalizer_right _ _
          (hZR.trans (Subgroup.centralizer_le_normalizer _)),←hdec]
        exact hx.1
      obtain ⟨z,hz,r,hr,rfl⟩ := hprod
      have hrI : r ∈ centralizer (I : Set G) := by
        simpa only [inv_mul_cancel_left] using
          (centralizer (I : Set G)).mul_mem
            ((centralizer (I : Set G)).inv_mem (hZI hz)) hx.2
      have hr1 : r = 1 := mem_bot.mp (hfix ▸ ⟨hr,hrI⟩)
      change z * r ∈ Z F v
      rw [hr1,mul_one]
      exact hz
    · exact le_inf hZD hZI
  have hZbeta : Z F m ≤ Z F v :=
    center_le_of_central_neighbor h hB hSyl c.middle hcentral
  let := graph_Z_elementary h m
  have hDIcomm : ⁅D F m t,I⁆ ≤ Z F m :=
    (commutator_mono inf_le_left inf_le_right).trans
      (c.beta_core_frattini_eq h hB hSyl hb hactor hcentral ht hne hcomm).2.le
  have hZcomm : ⁅Z F m,I⁆ ≤ ⊥ := by
    rw [le_bot_iff,commutator_eq_bot_iff_le_centralizer]
    exact (le_centralizer_iff.mp (graph_Q_centralizes_Z h m)).trans (centralizer_le inf_le_right)
  have hZcard : Nat.card (Z F m) = 2 :=
    (c.central_middle_center_card h hB hSyl hb hactor hcentral E).trans hk
  have hcount := card_mul_card_centralizer_restrict_of_central_binary_pairing
    (D F m t) I (Z F m) (hZbeta.trans hZD) hDIcomm hZcomm hZcard
  have hright : (centralizer (I : Set G)).subgroupOf (D F m t) =
      (Z F v).subgroupOf (D F m t) := by
    ext x
    exact (show (x : G) ∈ centralizer (I : Set G) ↔ (x : G) ∈ Z F v from
      ⟨fun hx => hC ▸ ⟨x.property,hx⟩,fun hx => hZI hx⟩)
  rw [hright,Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv,
    c.central_center_card E hω,hk] at hcount
  have hindex : (D F m t).relIndex I = 4 := by
    exact (c.linear_seed_factor_index h hB hSyl hS hb ht hne hnot eβ).trans
      (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
  have hI := ((D F m t).subgroupOf I).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hDI).toEquiv] at hI
  change (D F m t).relIndex I * Nat.card (D F m t) = Nat.card I at hI
  rw [hindex] at hI
  have hsmall : Nat.card (D F m t) ≤ Nat.card ((centralizer (D F m t : Set G)).subgroupOf I) := by
    apply Nat.card_le_card_of_injective
      (fun x : D F m t => (⟨⟨x,hDI x.property⟩,(le_centralizer (D F m t)) x.property⟩ :
        (centralizer (D F m t : Set G)).subgroupOf I))
    intro x y he
    exact Subtype.ext (congrArg (fun z : (centralizer (D F m t : Set G)).subgroupOf I =>
      ((z : I) : G)) he)
  have hpos : 0 < Nat.card (D F m t) := Nat.card_pos
  have hDcard : Nat.card (D F m t) ≤ 16 := by nlinarith
  have hi := relIndex_ker (K := (Q F m).subgroupOf c.actor) c.quotient
  rw [c.kernel,relIndex_subgroupOf c.neighbor_core_le,c.neighbor_image] at hi
  have hiAlpha : (Q F v).relIndex (Q F m) = 2 := hi.trans
    ((Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 c.imageSylow).symm.toEquiv).trans hk)
  have hQb := (I.subgroupOf (Q F m)).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show I ≤ Q F m from inf_le_right)).toEquiv] at hQb
  change I.relIndex (Q F m) * Nat.card I = Nat.card (Q F m) at hQb
  have hi' : I.relIndex (Q F m) = 2 := by
    dsimp only [I]
    rw [inf_comm,inf_relIndex_left]
    exact hiAlpha
  rw [hi',←hI] at hQb
  omega

variable {K U S : Subgroup G}
local notation "F₀" => Reduction.reducedFamily ![K,U] S

/-- The actual noncommuting distance-two mixed pair has Borel core order
at most 512, without a regular-profile or exceptional-seed premise. -/
theorem noncommuting_two_borel_core_le_fivehundredtwelve
    (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {v m w t : Vertex F₀} (hc : IsCriticalPair F₀ v w)
    (hne : ⁅Z F₀ v,Z F₀ w⁆ ≠ ⊥) (hb : b F₀ = 2)
    (hvm : (graph F₀).Adj v m) (hmw : (graph F₀).Adj m w)
    (ht : (graph F₀).Adj v t) (htne : t ≠ m) :
    Nat.card (twoCore (commonBorel ![K,U] S)) ≤ 512 := by
  have H := Reduction.reduced_triple h
  obtain ⟨hv,hm⟩ := noncommuting_two_cubic_orientation h eK eU hc hne hb hvm hmw
  have hcentral := Reduction.reduced_bTwo_middle_central h hc hne hb hvm hmw
  have hcomm := (Reduction.reduced_bTwo_center_identities h hc hne hb hvm hmw).2.2.2
  obtain ⟨k,f,n,ch,a,c,hactor⟩ :=
    Reduction.reduced_bTwo_center_action_exists h hc hne hb hvm hmw
  let := f
  let := n
  let := ch
  have ha : a = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst a
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hk : Nat.card k = 2 := by
    simpa only [Nat.card_zmod] using source_action_field_card h hactor c.quotient c.onto c.kernel
      (graph_linear_two h eU v hv).some
  have hmiddle : Nat.card (Q F₀ m) ≤ 128 := linear_four_middle_core_card_le H
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hb c hactor hcentral ht htne hcomm
    (Reduction.reduced_graph_core_obstruction h v m hvm)
    (graph_linear_four h eK m hm).some (LinearEquiv.refl _ _) hk
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F₀ m
  rw [hm] at hg
  have hbase : Nat.card (Q F₀ (base F₀ false)) ≤ 128 := by
    rw [←hg,Q_translate,card_map_of_injective (MulAut.conj g).injective] at hmiddle
    exact hmiddle
  have hfirst : Nat.card (pCore 2 (parabolic ![K,U] S 0)) ≤ 128 := by
    have hmapped := congrArg (fun A : Subgroup G => Nat.card A)
      (NoncommutingProfile.reduced_base_Q_map h false)
    rw [card_map_of_injective (Reduction.G₀ ![K,U] S).subtype_injective] at hmapped
    change Nat.card (Q F₀ (base F₀ false)) = Nat.card (twoCore (parabolic ![K,U] S 0)) at hmapped
    have hcard : Nat.card (twoCore (parabolic ![K,U] S 0)) =
        Nat.card (pCore 2 (parabolic ![K,U] S 0)) :=
      card_map_of_injective (parabolic ![K,U] S 0).subtype_injective
    rw [hcard] at hmapped
    exact hmapped ▸ hbase
  calc
    _ = Nat.card (pCore 2 (commonBorel ![K,U] S)) :=
      card_map_of_injective (commonBorel ![K,U] S).subtype_injective
    _ = 4 * Nat.card (pCore 2 (parabolic ![K,U] S 0)) := h.mixed_borel_core_card eK eU
    _ ≤ 512 := by omega

end CFSG.Quasithin.ChapterF.Source.MixedDGS
