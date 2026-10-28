module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Continuation.Triple

/-!
# The Z-containment in the backward local product

For a moving pair, the common edge displacement has order four and is
U_start intersect Z_back. The fixed summand of Z_start lies in Z_back,
since it centralizes the neighbor's kernel and X_back = Z_back.

The commutator [Vcirc_back,Q_start] cannot lie in Z_back: Q_start escapes
Q_back, hence normally generates a subgroup containing the local residual.
Residual commutator idempotence would put Vcirc_back inside U_back and
force H_back = U_back to vanish. Thus, when the explicit backward bound
places this commutator inside Z_start, it supplies a vector outside the
common plane. The natural subgroup of order eight and its fixed summand
are consequently contained in Vcirc_back Z_back.

The backward commutator bound is an explicit intermediate premise; its
producer and the unconditional source-theorem assembly are separate.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the last paragraph of (4.3.2) on printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.Continuation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

private theorem moving_residual_idempotent (source : LocalSource L R)
    (hb : 2 < geometry.b R) (a : Vertex R) (ha : color R a = false) :
    ⁅Vcirc R a, Ltilde R a⁆ = Vcirc R a := by
  let S := stabilizer R a
  let := finite_stabilizer R a
  let A := (V R a).subgroupOf S
  let : A.Normal := normal_subgroupOf_of_le_normalizer (V_normalized a)
  have h := commutator_isPPerfect_idempotent (pResidual 2 S) A
    (isPPerfect_pResidual 2) (source.V_isPGroup geometry hb a ha).comap_subtype
    le_normalizer_of_normal
  have hh := congrArg (Subgroup.map S.subtype) h
  have hA : A.map S.subtype = V R a := map_subgroupOf_eq_of_le
    ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1))
  simpa only [map_commutator, hA, Vcirc, Ltilde, S] using hh

private theorem moving_commutator_not_le_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t d : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hd : d ∈ movingNeighbors geometry a) :
    ¬ ⁅Vcirc R d, Q R a⁆ ≤ Z R d := by
  have hdc := moving_color ha hd
  have hQa := Q_le_stabilizer_of_dist_two R a d ha hd.1
  have hCQ : Vcirc R d ≤ Q R d := (Vcirc_le_V d).trans (geometry.V_le_Q hb d hdc)
  have hCS := hCQ.trans (show Q R d ≤ stabilizer R d from fun _ hx => hx.1)
  have hQS : Q R d ≤ stabilizer R d := fun _ hx => hx.1
  have hnot : ¬ Q R a ≤ Q R d := by
    intro h
    have hz := le_bot_iff.mp ((commutator_mono (le_refl (Z R d)) h).trans
      (geometry.centralizes d hdc).le)
    have hc := FirstPairing.StepThree.moving_commutator_card_at p (by omega)
      initial bad a t d ha hat hdt hd
    rw [hz, card_bot] at hc
    omega
  intro hbound
  obtain ⟨o⟩ := facts.opposite d hdc
  let S := stabilizer R d
  let := finite_stabilizer R d
  let C := (Vcirc R d).subgroupOf S
  let N := (Z R d).subgroupOf S
  let J := (Q R a).subgroupOf S
  let : C.Normal := normal_subgroupOf_of_le_normalizer (Vcirc_normalized d)
  let : N.Normal := normal_subgroupOf_of_le_normalizer (Z_normalized R d)
  have hker : IsPGroup 2 o.projection.ker := by
    rw [o.kernel]
    exact (Q_isPGroup R source.two_group source.core_le d hdc).comap_subtype
  have hJ : ¬ J ≤ o.projection.ker := by
    intro h
    apply hnot
    intro x hx
    have hx' := h (show (⟨x, hQa hx⟩ : S) ∈ J from hx)
    rw [o.kernel] at hx'
    exact hx'
  have hc : ⁅C, J⁆ ≤ N := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hCS, map_subgroupOf_eq_of_le hQa]
    exact hbound
  have h := map_mono (f := S.subtype)
    (residual_commutator_bound o.projection o.surjective hker C N J
      ((Q_isPGroup R source.two_group source.core_le d hdc).to_le hCQ).comap_subtype hJ hc)
  dsimp only [C, N] at h
  rw [map_commutator, map_commutator, map_subgroupOf_eq_of_le hCS,
    map_subgroupOf_eq_of_le (Z_le_stabilizer R d)] at h
  change ⁅Vcirc R d, Ltilde R d⁆ ≤ U R d at h
  rw [moving_residual_idempotent source hb d hdc] at h
  have hz : H R d = ⊥ := le_bot_iff.mp
    ((commutator_mono (h.trans (U_le_Z d)) le_rfl).trans (geometry.centralizes d hdc).le)
  rw [facts.H_eq_U d hdc] at hz
  have hcard := modules.natural.card_at d hdc
  rw [hz, card_bot] at hcard
  omega

private theorem central_summand_le_neighbor_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    {a d : Vertex R} (ha : color R a = false) (hdc : color R d = false)
    (had : (cosetGraph R).dist a d = 2) :
    Z R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)) ≤ Z R d := by
  have hZd : Z R a ≤ Q R d := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a ha)
    rw [geometry.distance_constant a ha, had]
    exact hb
  have hQd : Q R d ≤ stabilizer R a := Q_le_stabilizer_of_dist_two R d a hdc
    (by rwa [SimpleGraph.dist_comm])
  rw [← modules.X_eq_Z d hdc]
  let := geometry.Z_elementary (show 0 < geometry.b R by omega) a ha
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hZd hx.1,
    elemPow_eq_one_of_isElementaryAbelian x hx.1, fun y hy => hx.2 y (hQd hy)⟩

/-- The Z-cover, conditional on the commutator bound for this actual choice. -/
theorem start_Z_le_backward_moving_sup_Z (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : BackwardChoice p)
    (hbound : ⁅Vcirc R choice.back, Q R p.a⁆ ≤ Z R p.a) :
    Z R p.a ≤ Vcirc R choice.back ⊔ Z R choice.back := by
  let a := p.a
  let d := choice.back
  let F := Z R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R))
  let K := Vcirc R d ⊔ Z R d
  let T := U R a ⊓ K
  have hd := moving_color p.color_a choice.moving
  have hrev := facts.moving_symmetric p.a d p.color_a choice.moving
  have hF : F ≤ Z R d := central_summand_le_neighbor_Z source hb modules
    p.color_a hd choice.moving.1
  let natural : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hsplit : Z R a = U R a ⊔ F := natural.decomposition_at a p.color_a
  have hdecomp : ∀ x ∈ Z R a, ∃ u ∈ U R a, ∃ f ∈ F, u * f = x := by
    let S := stabilizer R a
    let U₀ := (U R a).subgroupOf S
    let F₀ := F.subgroupOf S
    let : U₀.Normal := normal_subgroupOf_of_le_normalizer (U_normalized a)
    intro x hx
    have hx' : x ∈ (U₀ ⊔ F₀).map S.subtype := by
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le ((U_le_Z a).trans (Z_le_stabilizer R a)),
        map_subgroupOf_eq_of_le (show F ≤ S from inf_le_left.trans (Z_le_stabilizer R a)),
        ← hsplit]
      exact hx
    obtain ⟨y, hy, hxy⟩ := hx'
    obtain ⟨u, hu, f, hf, huf⟩ := mem_sup_of_normal_left.mp hy
    exact ⟨u, hu, f, hf, (congrArg Subtype.val huf).trans hxy⟩
  have heq : U R a ⊓ Z R d = edgeDisplacement a choice.edge := by
    rw [moving_natural_intersection source hb modules facts p initial bad hd
      choice.adjacent_back choice.adjacent_start hrev]
    exact facts.edge_eq a choice.edge d p.color_a choice.adjacent_start
      choice.adjacent_back choice.moving
  have heU : edgeDisplacement a choice.edge ≤ U R a :=
    Initial.edge_le_natural source a choice.edge p.color_a choice.adjacent_start
  have heD : edgeDisplacement a choice.edge ≤ Z R d := heq ▸ inf_le_right
  have heT : edgeDisplacement a choice.edge ≤ T := le_inf heU (heD.trans le_sup_right)
  have hcard := FirstPairing.StepThree.edge_card p (by omega) initial
    a choice.edge p.color_a choice.adjacent_start
  let : Finite (U R a) := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at a p.color_a]; decide)
  let : Finite T := Finite.of_injective (inclusion (show T ≤ U R a from inf_le_left))
    (inclusion_injective _)
  have hge : 4 ≤ Nat.card T := hcard ▸ card_le_of_le heT
  have hdvd : Nat.card T ∣ 8 := modules.natural.card_at a p.color_a ▸ card_dvd_of_le
    (show T ≤ U R a from inf_le_left)
  have hne : Nat.card T ≠ 4 := by
    intro hfour
    have hT : T = edgeDisplacement a choice.edge :=
      (eq_of_le_of_card_ge heT (by rw [hcard, hfour])).symm
    apply moving_commutator_not_le_Z source hb modules facts p initial bad p.color_a
      choice.adjacent_start choice.adjacent_back choice.moving
    intro x hx
    obtain ⟨u, hu, f, hf, rfl⟩ := hdecomp x (hbound hx)
    have hxK : u * f ∈ K := mem_sup_left
      (le_normalizer_iff_commutator_le_left.mp
        ((Q_le_stabilizer_of_dist_two R a d p.color_a choice.moving.1).trans
          (Vcirc_normalized d)) hx)
    have huK : u ∈ K := (K.mul_mem_cancel_right (mem_sup_right (hF hf))).mp hxK
    have huT : u ∈ T := ⟨hu, huK⟩
    rw [hT] at huT
    exact (Z R d).mul_mem (heD huT) (hF hf)
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hsize : Nat.card T = 8 := by omega
  have hT : T = U R a := eq_of_le_of_card_ge inf_le_left
    (by rw [hsize, modules.natural.card_at a p.color_a])
  rw [hsplit]
  exact sup_le (hT ▸ (show T ≤ K from inf_le_right)) (hF.trans le_sup_right)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.Continuation
