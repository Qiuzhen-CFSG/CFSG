module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Terminal.Reversal
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Kernel.Normality

/-!
# Radius-six noncommutation from the radius-five normality contradiction

Commutation with the third orbit layer propagates through both nonmoving
Z-joins. The kernel intersection then lies in Q_mu, and the earlier
order-four bounds put its commutator with Vcirc_mu inside V_alpha.
The proved symmetric radius-four join extends this bound to the whole
radius-six ball modulo the radius-four ball. The actual noncore actor and
marked SL3(2) quotient give the same bound for the local residual.

Consequently the radius-five span at the first edge is normal in G_alpha,
contrary to source characteristic faithfulness. This proves noncommutation
with the third orbit layer; no commutator or normality premise remains.

Source: Meierfrankenfeld--Stellmacher (1993), second full paragraph of
printed p.890, in the final contradiction for (4.3).
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Terminal
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Propagation Propagation.RadiusFour
open scoped commutatorElement Pointwise
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

private theorem backwardOfPropagation (h : PropagationFacts geometry) : BackwardFacts geometry where
  backward_bound := h.backward_bound
  product_normal := h.product_normal
  moving_symmetric := h.moving_symmetric
  far_not_moving := h.far_not_moving
  moving_radius_bound := h.moving_radius_bound

private theorem rigidityOfPropagation (h : PropagationFacts geometry) : RigidityFacts geometry where
  equal_Z := h.equal_Z
  moving_Z_unique := h.moving_Z_unique
  six_lt := h.six_lt

variable [Finite M]

/-- Commutation with the third layer passes through both actual nonmoving joins. -/
theorem intersection_le_first_kernel (source : LocalSource L R)
    (p : Counterexample geometry)
    {d t₃ t₅ s t₇ : Vertex R} (hd : Before p.a p.a' d 4)
    (h₃ : Before p.a p.a' t₃ 3) (hs : Before p.a p.a' s 6)
    (w : ThirdOrbitWitnesses p d t₃ t₅ s t₇)
    (hA : VBall R p.a 6 ≤ Q R s) (hc : ⁅VBall R p.a 6, Z R w.rho⁆ = ⊥) :
    VBall R p.a 6 ⊓ Q R d ≤ Q R w.earlier.mu := by
  have hdc : color R d = false := (hd.color (by decide)).trans p.end_color
  have hsc : color R s = false := (hs.color (by decide)).trans p.end_color
  have hμc : color R w.earlier.mu = false := by
    rw [← w.earlier.first_image, action_preserves_color, p.end_color]
  have hdist : (cosetGraph R).dist d w.earlier.mu ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (hd.adjacent (geometry := geometry) h₃))
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (adjacent_symm R w.earlier.first_adjacent))
    have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := t₃) (w := w.earlier.mu)
    omega
  have hClam : VBall R p.a 6 ≤ centralizer (Z R w.earlier.lam : Set (FreeAmalgam R)) := by
    apply le_centralizer_iff.mpr
    have hj : Z R w.earlier.lam ≤ Z R w.rho ⊔ Z R s := w.second_join.symm ▸ le_sup_left
    apply hj.trans
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
      ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes s hsc)).trans
        (centralizer_le hA))
  rw [← source.C_eq_Q geometry.radical_ne_bot w.earlier.mu hμc]
  refine le_inf (inf_le_right.trans (Q_le_stabilizer_of_dist_le_two d w.earlier.mu hdc hμc hdist)) ?_
  apply le_centralizer_iff.mpr
  have hj : Z R w.earlier.mu ≤ Z R w.earlier.lam ⊔ Z R d := w.first_join.symm ▸ le_sup_left
  apply hj.trans
  exact sup_le ((le_centralizer_iff.mp hClam).trans (centralizer_le inf_le_left))
    ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hdc)).trans
      (centralizer_le inf_le_right))

omit [Finite M] in
/-- The genuine first-conjugate actor lies in the starting local group. -/
theorem first_actor_local (propagation : PropagationFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ t : Vertex R} (hd : Before p.a p.a' d 4)
    (h₃ : Before p.a p.a' t₃ 3) (ht : Before p.a' p.a t 1)
    (w : PropagationWitnesses p d t₃ t₅) : Vcirc R w.mu ≤ stabilizer R p.a := by
  exact (Kernel.first_moving_le_ball p hd h₃ (centralWitness w)).trans
    (le_sup_left.trans (((propagation.radius_four p d hd).2.2 t ht).le.trans
      (show Q R t ≤ stabilizer R p.a from fun _ hx => hx.2 p.a
        (adjacent_symm R ht.endpoint_adjacent))))

/-- The kernel-intersection commutator is precisely controlled by the earlier
order-four lower bound at a newly constructed contrary critical pair. -/
theorem intersection_commutator_le_radius (source : LocalSource L R)
    (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (propagation : PropagationFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ t : Vertex R} (hd : Before p.a p.a' d 4)
    (h₃ : Before p.a p.a' t₃ 3) (ht : Before p.a' p.a t 1)
    (w : PropagationWitnesses p d t₃ t₅)
    (hI : VBall R p.a 6 ⊓ Q R d ≤ Q R w.mu) :
    ⁅VBall R p.a 6 ⊓ Q R d, Vcirc R w.mu⁆ ≤ V R p.a := by
  have hμc : color R w.mu = false := by
    rw [← w.first_image, action_preserves_color, p.end_color]
  have hnear : (cosetGraph R).dist p.a w.mu + 2 ≤ geometry.b R := by
    have hpath := h₃.2
    rw [p.distance_eq_b] at hpath
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr
      (adjacent_symm R w.first_adjacent))
    have htri := (cosetGraph_connected R).dist_triangle (u := p.a) (v := t₃) (w := w.mu)
    omega
  have hVaI : V R p.a ≤ VBall R p.a 6 ⊓ Q R d := by
    refine le_inf (VBall_mono R p.a (by decide : 2 ≤ 6)) ?_
    apply Backward.V_le_Q_of_dist_add_two_lt p.color_a
    have hpath := hd.2.trans p.distance_eq_b
    omega
  obtain ⟨q, hqa, hqc⟩ := Kernel.exists_counterexample_of_radius_not_le source
    p.color_a hμc hnear (hVaI.trans hI)
    (Kernel.first_radius_not_le source hb initial control (backwardOfPropagation propagation)
      p (centralWitness w))
  obtain ⟨hi⟩ := initial q
  have hlow : 4 ≤ Nat.card (⁅V R p.a, Vcirc R w.mu⁆ : Subgroup (FreeAmalgam R)) := by
    simpa only [hqa, hqc] using hi.radius_moving_card
  have hH := Kernel.H_card_four (by omega : 0 < geometry.b R) initial control
    (rigidityOfPropagation propagation) p w.mu t₃ hμc w.first_adjacent
  let : Finite (H R w.mu) := Nat.finite_of_card_ne_zero (by rw [hH]; decide)
  have hu : ⁅VBall R p.a 6 ⊓ Q R d, Vcirc R w.mu⁆ ≤ H R w.mu := by
    rw [commutator_comm]
    exact commutator_mono le_rfl hI
  let : Finite (⁅VBall R p.a 6 ⊓ Q R d, Vcirc R w.mu⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hu) (inclusion_injective _)
  have heq := eq_of_le_of_card_ge (commutator_mono hVaI (le_rfl (a := Vcirc R w.mu)))
    ((card_le_of_le hu).trans (by rw [hH]; exact hlow))
  rw [← heq]
  exact le_normalizer_iff_commutator_le_left.mp
    ((first_actor_local propagation p hd h₃ ht w).trans (V_normalized p.a))

/-- A normal supplement decomposes each ball element into its smaller-ball
part and a part in the kernel intersection. -/
private theorem commutator_le_of_supplement {G : Type*} [Group G]
    (A B D J : Subgroup G) (hBA : B ≤ A) (hA : A ≤ B ⊔ D)
    (hBD : B ≤ normalizer D) (hAB : A ≤ normalizer B)
    (hJB : J ≤ normalizer B) (hI : ⁅A ⊓ D, J⁆ ≤ B) : ⁅A, J⁆ ≤ B := by
  apply Subgroup.commutator_le.mpr
  intro a ha j hj
  have hp : a ∈ (D : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left D B hBD]
    exact (sup_comm B D ▸ hA ha)
  obtain ⟨d, hd, b, hb, rfl⟩ := hp
  have hdA : d ∈ A := by
    have hh := A.mul_mem ha (A.inv_mem (hBA hb))
    simpa only [mul_inv_cancel_right] using hh
  rw [commutatorElement_mul_left_eq_conj_mul]
  apply B.mul_mem
  · exact (mem_normalizer_iff.mp (hAB hdA) _).mp
      ((le_normalizer_iff_commutator_le_left.mp hJB) (commutator_mem_commutator hb hj))
  · exact hI (commutator_mem_commutator ⟨hdA, hd⟩ hj)

/-- The symmetric radius-four join extends the intersection displacement
bound to the whole radius-six ball. -/
theorem radius_six_actor_commutator (source : LocalSource L R) (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (propagation : PropagationFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ s t₇ t : Vertex R} (hd : Before p.a p.a' d 4)
    (h₃ : Before p.a p.a' t₃ 3) (h₅ : Before p.a p.a' t₅ 5)
    (hs : Before p.a p.a' s 6) (ht : Before p.a' p.a t 1)
    (w : ThirdOrbitWitnesses p d t₃ t₅ s t₇)
    (hA : VBall R p.a 6 ≤ Q R s) (hc : ⁅VBall R p.a 6, Z R w.rho⁆ = ⊥) :
    ⁅VBall R p.a 6, Vcirc R w.earlier.mu⁆ ≤ VBall R p.a 4 := by
  have hsc : color R s = false := (hs.color (by decide)).trans p.end_color
  have hs₅ := hs.adjacent (geometry := geometry) h₅
  have ht₅c : color R t₅ = true := by
    have hn := adjacent_color_ne R hs₅
    cases htc : color R t₅ <;> simp_all
  have hQT : Q R s ≤ Q R t₅ := Q_le_adjacent_h R ht₅c hs₅
  have hj := radius_four_join_symmetric source hb propagation p hd h₅ hs
  have hlarge := propagation.six_lt p
  apply commutator_le_of_supplement _ _ (Q R d) _ (VBall_mono R p.a (by decide : 4 ≤ 6))
    (by rw [hj]; exact hA.trans hQT)
  · exact (le_sup_left.trans (hj.le.trans
      (show Q R t₅ ≤ stabilizer R d from fun _ hx => hx.2 d
        (h₅.adjacent (geometry := geometry) hd)))) |>.trans (Q_normalized R d)
  · exact ((VBall_le_Q p.a p.color_a 6 hlarge).trans (fun _ hx => hx.1)).trans
      (VBall_normalized p.a 4)
  · exact (first_actor_local propagation p hd h₃ ht w.earlier).trans (VBall_normalized p.a 4)
  · exact (intersection_commutator_le_radius source hb initial control propagation p hd h₃ ht w.earlier
      (intersection_le_first_kernel source p hd h₃ hs w hA hc)).trans
      (VBall_mono R p.a (by decide : 2 ≤ 4))

/-- Normal generation by the noncore actor in the marked SL3(2) quotient
extends the radius-six displacement bound to the actual local residual. -/
theorem radius_six_residual_le_four (source : LocalSource L R)
    (hb : 6 < geometry.b R) (p : Counterexample geometry) (initial : InitialFacts p)
    (J : Subgroup (FreeAmalgam R)) (hJG : J ≤ stabilizer R p.a)
    (hJQ : ¬ J ≤ Q R p.a) (hc : ⁅VBall R p.a 6, J⁆ ≤ VBall R p.a 4) :
    ⁅VBall R p.a 6, Ltilde R p.a⁆ ≤ VBall R p.a 4 := by
  let S := stabilizer R p.a
  let := finite_stabilizer R p.a
  let W := (VBall R p.a 6).subgroupOf S
  let V₀ := (VBall R p.a 4).subgroupOf S
  let J₀ := J.subgroupOf S
  let π := initial.natural_section.projection
  have hWQ := VBall_le_Q p.a p.color_a 6 hb
  have hWG : VBall R p.a 6 ≤ S := hWQ.trans (fun _ hx => hx.1)
  have hVG : VBall R p.a 4 ≤ S := (VBall_mono R p.a (by decide : 4 ≤ 6)).trans hWG
  let : W.Normal := normal_subgroupOf_of_le_normalizer (VBall_normalized p.a 6)
  let : V₀.Normal := normal_subgroupOf_of_le_normalizer (VBall_normalized p.a 4)
  have hker : IsPGroup 2 π.ker := by
    rw [initial.natural_section.module_section.projection_kernel]
    exact (Q_isPGroup R source.two_group source.core_le p.a p.color_a).comap_subtype
  have hpW : IsPGroup 2 W :=
    ((Q_isPGroup R source.two_group source.core_le p.a p.color_a).to_le hWQ).comap_subtype
  have hJ : ¬ J₀ ≤ π.ker := by
    intro h
    apply hJQ
    intro z hz
    have hz' := h (show (⟨z, hJG hz⟩ : S) ∈ J₀ from hz)
    rw [initial.natural_section.module_section.projection_kernel] at hz'
    exact hz'
  have hc₀ : ⁅W, J₀⁆ ≤ V₀ := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hWG, map_subgroupOf_eq_of_le hJG]
    exact hc
  have h := map_mono (f := S.subtype)
    (PairingControl.Geometry.LocalProducts.residual_commutator_bound π
      initial.natural_section.module_section.projection_surjective hker W V₀ J₀ hpW hJ hc₀)
  dsimp only [W, V₀] at h
  have hbound : ⁅VBall R p.a 6, Ltilde R p.a⁆ ≤ ⁅VBall R p.a 4, Ltilde R p.a⁆ := by
    simpa only [map_commutator, map_subgroupOf_eq_of_le hWG,
      map_subgroupOf_eq_of_le hVG, Ltilde, S] using h
  exact hbound.trans (le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer p.a).trans (VBall_normalized p.a 4)))

/-- The residual commutator bound makes the actual radius-five span normal
at the first M-vertex; the local kernel supplies the second generator. -/
theorem radius_five_normal_of_residual (source : LocalSource L R)
    (p : Counterexample geometry) {t : Vertex R} (hat : Adjacent R p.a t)
    (hc : ⁅VBall R p.a 6, Ltilde R p.a⁆ ≤ VBall R p.a 4) :
    ((VBall R t 5).subgroupOf (stabilizer R p.a)).Normal := by
  have hdist : (cosetGraph R).dist p.a t = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
  have hsmall : VBall R p.a 4 ≤ VBall R t 5 := VBall_le_of_dist_add_le t p.a 4 5 (by rw [hdist])
  have hlarge : VBall R t 5 ≤ VBall R p.a 6 :=
    VBall_le_of_dist_add_le p.a t 5 6 (by rw [SimpleGraph.dist_comm, hdist])
  apply normal_subgroupOf_of_le_normalizer
  rw [← source.local_generation p.a p.color_a]
  apply sup_le
  · apply le_normalizer_iff_commutator_le_left.mpr
    exact (commutator_mono hlarge le_rfl).trans (hc.trans hsmall)
  · exact (show Q R p.a ≤ stabilizer R t from fun _ hx => hx.2 t hat).trans
      (VBall_normalized t 5)

omit [Finite M] in
/-- Characteristic faithfulness forbids a common normal radius-five span. -/
theorem radius_five_not_normal (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (hb : 6 < geometry.b R)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    ¬ ((VBall R t 5).subgroupOf (stabilizer R a)).Normal := by
  intro hnormal
  have hdist : (cosetGraph R).dist t a = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr (adjacent_symm R hat))
  have hQ : VBall R t 5 ≤ Q R a :=
    (VBall_le_of_dist_add_le a t 5 6 (by rw [hdist])).trans (VBall_le_Q a ha 6 hb)
  have hN := no_common_normal_at_edge R source.characteristic a t ha hat
    (VBall R t 5) (le_inf (hQ.trans (fun _ hx => hx.1))
      (hQ.trans (fun _ hx => hx.2 t hat))) hnormal
    (normal_subgroupOf_of_le_normalizer (VBall_normalized t 5))
  have hZ : Z R a ≤ VBall R t 5 := le_iSup_of_le a
    (le_iSup_of_le (show (cosetGraph R).dist a t ≤ 5 by
      rw [SimpleGraph.dist_comm, hdist]; omega) le_rfl)
  have hU : U R a = ⊥ := le_bot_iff.mp ((U_le_Z a).trans (hZ.trans hN.le))
  have hcard := modules.natural.card_at a ha
  rw [hU, card_bot] at hcard
  omega

/-- The noncommutation conclusion on printed p.890, with every commutator,
quotient-action, actor and normality premise constructed from earlier source facts. -/
theorem third_noncommutation (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (propagation : PropagationFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ s t₇ : Vertex R} (hd : Before p.a p.a' d 4)
    (h₃ : Before p.a p.a' t₃ 3) (h₅ : Before p.a p.a' t₅ 5)
    (hs : Before p.a p.a' s 6) (w : ThirdOrbitWitnesses p d t₃ t₅ s t₇) :
    ⁅VBall R p.a 6, Z R w.rho⁆ ≠ ⊥ := by
  intro hc
  have hlarge := propagation.six_lt p
  obtain ⟨t, hat, hdist⟩ := exists_adjacent_dist_sub_one R p.a p.a'
    (p.distance_eq_b.symm ▸ (show 0 < geometry.b R by omega))
  have ht : Before p.a' p.a t 1 := by
    constructor
    · rw [SimpleGraph.dist_comm]
      exact SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)
    · simpa only [SimpleGraph.dist_comm] using hdist
  have hJG := first_actor_local propagation p hd h₃ ht w.earlier
  have hJQ : ¬ Vcirc R w.earlier.mu ≤ Q R p.a := fun h =>
    Kernel.first_moving_not_le_product source hb initial control (backwardOfPropagation propagation)
      p (centralWitness w.earlier) (h.trans le_sup_right)
  obtain ⟨hi⟩ := initial p
  have hres := radius_six_residual_le_four source hlarge p hi (Vcirc R w.earlier.mu) hJG hJQ
    (radius_six_actor_commutator source hb initial control propagation p hd h₃ h₅ hs ht w
      (radius_six_le source hb propagation p hs) hc)
  exact radius_five_not_normal source modules hlarge p.a t p.color_a hat
    (radius_five_normal_of_residual source p hat hres)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Terminal
