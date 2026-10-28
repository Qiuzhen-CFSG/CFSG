module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Edges

/-!
# The normal-subgroup deduction in the local-product continuation

At a moving pair the common edge displacement has order four and equals
U_back intersected with Z_start. A subgroup of U_back normal in G_start
first centralizes Q_start, then lies in this proper edge subspace; natural
irreducibility forces it to vanish.

The backward product is normal by the residual-span bound. Since H_start
is U_start and centralizes Q_start, the second commutator of that product
is exactly the second commutator of Vcirc_back. It is consequently normal
in G_start. The remaining module-action premise is its containment in
U_back; this module does not assert that premise without proof.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2), printed p.885.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.Continuation
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}

private theorem normalized_commutator {G : Type*} [Group G] (S A B : Subgroup G)
    (hA : S ≤ normalizer (A : Set G)) (hB : S ≤ normalizer (B : Set G)) :
    S ≤ normalizer (⁅A, B⁆ : Subgroup G) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hA hg),
    mem_normalizer_iff_map_conj_eq.mp (hB hg)]

private theorem commutator_join {G : Type*} [Group G] (A B Q : Subgroup G)
    (hA : A ≤ Q) (hB : B ≤ Q) : ⁅A ⊔ B, Q⁆ = ⁅A, Q⁆ ⊔ ⁅B, Q⁆ := by
  have h := commutator_iSup_of_le (fun b : Bool => if b then A else B) Q
    (by intro b; cases b <;> assumption)
  simpa only [iSup_bool_eq, Bool.false_eq_true, if_false, if_true] using h

/-- Radius-two generators commute when b > 4, and are involutions. -/
theorem radius_elementary (hb : 4 < geometry.b R) {a : Vertex R}
    (ha : color R a = false) : IsElementaryAbelian 2 (V R a) := by
  have hc : V R a ≤ centralizer (V R a : Set (FreeAmalgam R)) :=
    V_centralizes_V_of_distance ha ha (by simpa using hb)
  let E : Subgroup (FreeAmalgam R) := {
    carrier := {x | x ∈ V R a ∧ x ^ 2 = 1}
    one_mem' := ⟨one_mem _, by simp⟩
    mul_mem' := by
      rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
      refine ⟨mul_mem hx hy, ?_⟩
      have hxy : Commute x y := hc hy x hx
      rw [hxy.mul_pow, hx2, hy2, one_mul]
    inv_mem' := by
      rintro x ⟨hx, hx2⟩
      exact ⟨inv_mem hx, by rw [inv_pow, hx2, inv_one]⟩ }
  have hE : V R a ≤ E := by
    apply V_le_of_m_ball ha
    intro d hd hdist x hx
    let := geometry.Z_elementary (by omega) d hd
    have hZV : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le hdist le_rfl)
    exact ⟨hZV hx,
      elemPow_eq_one_of_isElementaryAbelian x hx⟩
  refine { toIsMulCommutative := isMulCommutative_iff.mpr ?_, exponent_dvd_p := ?_ }
  · intro x y
    exact Subtype.ext (hc y.property x x.property)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    exact Subtype.ext (hE x.property).2

variable [Finite M]

omit [Finite M] in
/-- The common edge displacement makes the action on U_back quadratic.
The continuation still has to pass this fact to the actual dual section. -/
theorem moving_natural_quadratic (facts : ContraryLocalFacts geometry)
    (p : Counterexample geometry) (hb : 0 < geometry.b R)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t d : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hd : d ∈ movingNeighbors geometry a) : ⁅⁅U R d, Q R a⁆, Q R a⁆ = ⊥ := by
  have hcomm : ⁅U R d, Q R a⁆ ≤ edgeDisplacement a t := by
    rw [← facts.edge_eq a t d ha hat hdt hd,
      ← FirstPairing.StepThree.moving_commutator_eq_edge_at p hb
        initial bad a t d ha hat hdt hd]
    exact commutator_mono (U_le_Z d) le_rfl
  have hedge : edgeDisplacement a t ≤ Z R a :=
    le_normalizer_iff_commutator_le_left.mp
      ((show Q R t ≤ stabilizer R a from fun _ hx => hx.2 a (adjacent_symm R hat)).trans
        (Z_normalized R a))
  exact le_bot_iff.mp ((commutator_mono (hcomm.trans hedge) le_rfl).trans
    (geometry.centralizes a ha).le)

/-- This intersection uses step (3), before any later local-control theorem. -/
theorem moving_natural_intersection (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t d : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hd : d ∈ movingNeighbors geometry a) :
    U R d ⊓ Z R a = edgeDisplacement a t := by
  have hdc := moving_color ha hd
  have he := facts.edge_eq a t d ha hat hdt hd
  have hcomm := FirstPairing.StepThree.moving_commutator_eq_edge_at p (by omega)
    initial bad a t d ha hat hdt hd
  have hcard := FirstPairing.StepThree.edge_card p (by omega) initial a t ha hat
  have hU : edgeDisplacement a t ≤ U R d :=
    he ▸ Initial.edge_le_natural source d t hdc hdt
  have hZ : edgeDisplacement a t ≤ Z R a :=
    (Initial.edge_le_natural source a t ha hat).trans (U_le_Z a)
  let C := U R d ⊓ Z R a
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at d hdc]; decide)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ U R d from inf_le_left))
    (inclusion_injective _)
  have hle : edgeDisplacement a t ≤ C := le_inf hU hZ
  have hge : 4 ≤ Nat.card C := hcard ▸ card_le_of_le hle
  have hdvd : Nat.card C ∣ 8 := modules.natural.card_at d hdc ▸ card_dvd_of_le
    (show C ≤ U R d from inf_le_left)
  have hne : Nat.card C ≠ 8 := by
    intro hsize
    have hCU : C = U R d := eq_of_le_of_card_ge inf_le_left
      (by rw [hsize, modules.natural.card_at d hdc])
    have hUC : U R d ≤ centralizer (Q R a : Set (FreeAmalgam R)) :=
      (hCU ▸ (show C ≤ Z R a from inf_le_right)).trans
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha))
    have hQa : Q R a ≤ stabilizer R d := Q_le_stabilizer_of_dist_two R a d ha hd.1
    let s : BinaryNaturalStructure source :=
      ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
    have hZC : Z R d ≤ centralizer (Q R a : Set (FreeAmalgam R)) := by
      rw [s.decomposition_at d hdc]
      exact sup_le hUC (inf_le_right.trans (centralizer_le hQa))
    have hbot : edgeDisplacement a t = ⊥ := by
      rw [← he, ← hcomm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hZC
    rw [hbot, card_bot] at hcard
    omega
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hsize : Nat.card C = 4 := by omega
  exact (eq_of_le_of_card_ge hle (by rw [hcard, hsize])).symm

/-- The natural group at a moving neighbor has trivial G_start-normal core. -/
theorem normal_in_moving_natural_eq_bot (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {a t d : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hd : d ∈ movingNeighbors geometry a)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ U R d)
    (hn : stabilizer R a ≤ normalizer (K : Set (FreeAmalgam R))) : K = ⊥ := by
  have hdc := moving_color ha hd
  have hcomm : ⁅K, Q R a⁆ ≤ edgeDisplacement a t := by
    rw [← facts.edge_eq a t d ha hat hdt hd,
      ← FirstPairing.StepThree.moving_commutator_eq_edge_at p (by omega)
        initial bad a t d ha hat hdt hd]
    exact commutator_mono (hK.trans (U_le_Z d)) le_rfl
  have hzero := Selection.edge_normal_subgroup_eq_bot source hb modules facts ha hat
    ⁅K, Q R a⁆ hcomm (normalized_commutator _ _ _ hn (Q_normalized R a))
  have hKZ : K ≤ Z R a := by
    rw [← modules.X_eq_Z a ha]
    intro x hx
    apply mem_omegaCenter_iff.mpr
    have hKQ := (hK.trans (U_le_Z d)).trans
      ((moving_Z_le_V hd).trans (geometry.V_le_Q hb a ha))
    let := geometry.U_elementary (by omega) d hdc
    exact ⟨hKQ hx, elemPow_eq_one_of_isElementaryAbelian x (hK hx),
      commutator_eq_bot_iff_le_centralizer.mp hzero hx⟩
  apply Selection.edge_normal_subgroup_eq_bot source hb modules facts ha hat K _ hn
  rw [← moving_natural_intersection source hb modules facts p initial bad ha hat hdt hd]
  exact le_inf hK hKZ

/-- The source identity making the backward triple commutator normal. -/
theorem backward_triple_normalized (source : LocalSource L R)
    (facts : ContraryLocalFacts geometry) {p : Counterexample geometry}
    (choice : BackwardChoice p) (hlarge : 6 < geometry.b R)
    (hres : ⁅choice.W, Ltilde R p.a⁆ ≤ Vcirc R p.a) :
    stabilizer R p.a ≤ normalizer
      (⁅⁅Vcirc R choice.back, Q R p.a⁆, Q R p.a⁆ : Subgroup (FreeAmalgam R)) := by
  have hA : Vcirc R p.a ≤ Q R p.a :=
    (Vcirc_le_V p.a).trans (geometry.V_le_Q (by omega) p.a p.color_a)
  have hB : Vcirc R choice.back ≤ Q R p.a :=
    ((Vcirc_le_V choice.back).trans choice.back_le_W).trans (span_le_start_kernel choice hlarge)
  have hprod : Vcirc R p.a ⊔ Vcirc R choice.back ≤ stabilizer R p.a :=
    (sup_le hA hB).trans (fun _ hx => hx.1)
  have hn := (normal_subgroupOf_iff_le_normalizer hprod).mp
    (backward_product_normal source choice hres)
  have hU : ⁅Vcirc R p.a, Q R p.a⁆ = U R p.a := facts.H_eq_U p.a p.color_a
  have hcentral : ⁅U R p.a, Q R p.a⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono (U_le_Z p.a) le_rfl).trans (geometry.centralizes p.a p.color_a).le)
  have hid : ⁅⁅Vcirc R p.a ⊔ Vcirc R choice.back, Q R p.a⁆, Q R p.a⁆ =
      ⁅⁅Vcirc R choice.back, Q R p.a⁆, Q R p.a⁆ := by
    rw [commutator_join _ _ _ hA hB, hU,
      commutator_join _ _ _ ((U_le_Z p.a).trans ((Z_le_VBall R p.a 2).trans (geometry.V_le_Q (by omega) p.a p.color_a)))
        ((Subgroup.commutator_le_sup _ _).trans (sup_le hB le_rfl)), hcentral, bot_sup_eq]
  rw [← hid]
  exact normalized_commutator _ _ _
    (normalized_commutator _ _ _ hn (Q_normalized R p.a)) (Q_normalized R p.a)

/-- Normality finishes the triple calculation once the dual action bounds it by U_back. -/
theorem backward_triple_eq_bot_of_le_natural (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    (initial : ∀ r : Counterexample geometry, Nonempty (InitialFacts r))
    (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    (choice : BackwardChoice p) (hlarge : 6 < geometry.b R)
    (hres : ⁅choice.W, Ltilde R p.a⁆ ≤ Vcirc R p.a)
    (hquad : ⁅⁅Vcirc R choice.back, Q R p.a⁆, Q R p.a⁆ ≤ U R choice.back) :
    ⁅⁅Vcirc R choice.back, Q R p.a⁆, Q R p.a⁆ = ⊥ :=
  normal_in_moving_natural_eq_bot source hb modules facts p initial bad p.color_a
    choice.adjacent_start choice.adjacent_back choice.moving _ hquad
    (backward_triple_normalized source facts choice hlarge hres)

/-- The vanishing triple puts the elementary first commutator in X_start = Z_start. -/
theorem backward_commutator_le_Z_of_triple (source : LocalSource L R)
    (modules : ModuleFacts source geometry) {p : Counterexample geometry}
    (choice : BackwardChoice p) (hlarge : 6 < geometry.b R)
    (htriple : ⁅⁅Vcirc R choice.back, Q R p.a⁆, Q R p.a⁆ = ⊥) :
    ⁅Vcirc R choice.back, Q R p.a⁆ ≤ Z R p.a := by
  have hd := moving_color p.color_a choice.moving
  have hQa : Q R p.a ≤ stabilizer R choice.back :=
    Q_le_stabilizer_of_dist_two R p.a choice.back p.color_a choice.moving.1
  have hB : Vcirc R choice.back ≤ Q R p.a :=
    ((Vcirc_le_V choice.back).trans choice.back_le_W).trans (span_le_start_kernel choice hlarge)
  have hle : ⁅Vcirc R choice.back, Q R p.a⁆ ≤ V R choice.back :=
    (le_normalizer_iff_commutator_le_left.mp (hQa.trans (Vcirc_normalized choice.back))).trans
      (Vcirc_le_V choice.back)
  rw [← modules.X_eq_Z p.a p.color_a]
  let := radius_elementary (geometry := geometry) (by omega) hd
  intro x hx
  exact mem_omegaCenter_iff.mpr
    ⟨(Subgroup.commutator_le_sup _ _).trans (sup_le hB le_rfl) hx,
      elemPow_eq_one_of_isElementaryAbelian x (hle hx),
      commutator_eq_bot_iff_le_centralizer.mp htriple hx⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.LocalProducts.Continuation
