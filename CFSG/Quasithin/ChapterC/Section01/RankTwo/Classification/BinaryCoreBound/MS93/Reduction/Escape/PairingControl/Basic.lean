module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Basic

/-!
# The first reductions in MS93 (4.3.2)

The contrary commutator bound forces H and each moving-neighbor commutator
outside the fixed core, using (4.2)(ii) and the actual local conjugate span.
Conversely, the desired commutator bound implies all edge equalities in
(4.3.2)(ii). Indeed, the fixed core centralizes the local residual, while
Q normalizes each commutator. Together they generate the stabilizer, so
conjugate generation puts H inside each moving-neighbor commutator.

The natural decomposition removes the fixed summand of Z. Nilpotence of
the finite two-group Q then makes its commutator with the natural eight
proper, hence of order at most four. The earlier lower bound on H forces
equality. All normality and finiteness are local to a vertex stabilizer.

These results prove step (1) and the reduction (i) implies (ii), not the
remaining contradiction in steps (2)--(6).
Source: Meierfrankenfeld--Stellmacher (1993), printed p.883, (4.3.2).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

theorem conjugatesIn_eq_of_normalized {G : Type*} [Group G] (A K : Subgroup G)
    (hn : K ≤ normalizer (A : Set G)) : NormalizerTransfer.conjugatesIn A K = A := by
  apply le_antisymm
  · apply iSup_le
    intro k
    exact (mem_normalizer_iff_map_conj_eq.mp (hn (K.inv_mem k.property))).le
  · have h := le_iSup (fun k : K => NormalizerTransfer.rightConjugate A k) 1
    intro x hx
    apply h
    exact ⟨x, hx, by simp⟩

theorem commutator_conjugatesIn {G : Type*} [Group G] (A K Q : Subgroup G)
    (hA : A ≤ Q) (hK : K ≤ normalizer (Q : Set G)) :
    ⁅NormalizerTransfer.conjugatesIn A K, Q⁆ =
      NormalizerTransfer.conjugatesIn ⁅A, Q⁆ K := by
  unfold NormalizerTransfer.conjugatesIn
  rw [commutator_iSup_of_le]
  · apply iSup_congr
    intro k
    have hm : Q.map (MulAut.conj (k : G)⁻¹).toMonoidHom = Q :=
      mem_normalizer_iff_map_conj_eq.mp (hK (K.inv_mem k.property))
    simp only [NormalizerTransfer.rightConjugate, map_commutator, hm]
  · intro k
    change A.map (MulAut.conj (k : G)⁻¹).toMonoidHom ≤ Q
    rw [← mem_normalizer_iff_map_conj_eq.mp (hK (K.inv_mem k.property))]
    exact map_mono hA

theorem fixedCore_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (fixedCore R a : Set (FreeAmalgam R)) := by
  have hn : (fixedCore R a).subgroupOf (stabilizer R a) =
      (Q R a).subgroupOf (stabilizer R a) ⊓
        centralizer (pResidual 2 (stabilizer R a) : Set (stabilizer R a)) := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, ?_⟩
      intro l hl
      apply Subtype.ext
      exact hx.2 l (mem_map_of_mem (stabilizer R a).subtype hl)
    · rintro ⟨hx, hc⟩
      refine ⟨hx, ?_⟩
      rintro _ ⟨l, hl, rfl⟩
      exact congrArg Subtype.val (hc l hl)
  apply (normal_subgroupOf_iff_le_normalizer
    (show fixedCore R a ≤ stabilizer R a from inf_le_left.trans (fun _ hx => hx.1))).mp
  rw [hn]
  let := Q_normal R a
  infer_instance

theorem moving_color {a d : Vertex R} (ha : color R a = false)
    (hd : d ∈ movingNeighbors geometry a) : color R d = false := by
  have h := color_eq_of_dist_even R a d (by rw [hd.1]; decide)
  exact h.symm.trans ha

theorem moving_Z_le_V {a d : Vertex R} (hd : d ∈ movingNeighbors geometry a) :
    Z R d ≤ V R a := by
  apply le_iSup_of_le d
  apply le_iSup_of_le
    (show (cosetGraph R).dist d a ≤ 2 by rw [SimpleGraph.dist_comm, hd.1])
  exact le_rfl

variable [Finite M]

theorem H_le_conjugates_commutator (hb : 2 < geometry.b R)
    {p : Counterexample geometry} (initial : InitialFacts p)
    {d : Vertex R} (hd : d ∈ movingNeighbors geometry p.a) :
    H R p.a ≤ NormalizerTransfer.conjugatesIn ⁅Z R d, Q R p.a⁆ (stabilizer R p.a) := by
  rw [H, ← commutator_conjugatesIn _ _ _
    ((moving_Z_le_V hd).trans (geometry.V_le_Q hb p.a p.color_a)) (Q_normalized R p.a)]
  exact commutator_mono (initial.moving_generation d hd) le_rfl

omit [Finite M] in
theorem H_not_le_fixed (transfer : NormalizationTransfer R)
    {p : Counterexample geometry} (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) :
    ¬ H R p.a ≤ fixedCore R p.a :=
  fun h => bad (transfer p.a p.color_a (Q R p.a) le_rfl (Q_normal R p.a) h)

theorem moving_commutator_not_le_fixed (hb : 2 < geometry.b R)
    (transfer : NormalizationTransfer R) {p : Counterexample geometry}
    (initial : InitialFacts p) (bad : ¬ ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {d : Vertex R} (hd : d ∈ movingNeighbors geometry p.a) :
    ¬ ⁅Z R d, Q R p.a⁆ ≤ fixedCore R p.a := by
  intro h
  apply H_not_le_fixed transfer bad
  apply (H_le_conjugates_commutator hb initial hd).trans
  calc
    NormalizerTransfer.conjugatesIn ⁅Z R d, Q R p.a⁆ (stabilizer R p.a) ≤
        NormalizerTransfer.conjugatesIn (fixedCore R p.a) (stabilizer R p.a) :=
      iSup_mono fun _ => map_mono h
    _ = fixedCore R p.a := conjugatesIn_eq_of_normalized _ _ (fixedCore_normalized p.a)

theorem moving_commutator_normalized (source : LocalSource L R)
    {a d : Vertex R} (ha : color R a = false)
    (hc : ⁅Z R d, Q R a⁆ ≤ fixedCore R a) :
    stabilizer R a ≤ normalizer (⁅Z R d, Q R a⁆ : Subgroup (FreeAmalgam R)) := by
  rw [← source.local_generation a ha]
  apply sup_le _ (normalizer_commutator_ge_right _ _)
  exact ((le_centralizer_iff.mp (hc.trans inf_le_right)).trans
    (Subgroup.centralizer_le_normalizer _))

theorem H_le_moving_commutator (source : LocalSource L R) (hb : 2 < geometry.b R)
    {p : Counterexample geometry} (initial : InitialFacts p)
    (hfixed : ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a)
    {d : Vertex R} (hd : d ∈ movingNeighbors geometry p.a) :
    H R p.a ≤ ⁅Z R d, Q R p.a⁆ := by
  have hc := (commutator_mono (moving_Z_le_V hd) le_rfl).trans hfixed
  have hn := moving_commutator_normalized source p.color_a hc
  exact (H_le_conjugates_commutator hb initial hd).trans
    (conjugatesIn_eq_of_normalized _ _ hn).le

theorem moving_commutator_card_le_four (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    {a d : Vertex R} (ha : color R a = false) (hd : d ∈ movingNeighbors geometry a) :
    Nat.card (⁅Z R d, Q R a⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
  have hdcolor := moving_color ha hd
  have hQa : Q R a ≤ stabilizer R d := Q_le_stabilizer_of_dist_two R a d ha hd.1
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hUQ : U R d ≤ Q R a :=
    (U_le_Z d).trans ((moving_Z_le_V hd).trans (geometry.V_le_Q hb a ha))
  have hcomm : ⁅Z R d, Q R a⁆ = ⁅U R d, Q R a⁆ := by
    rw [commutator_comm (Z R d), commutator_comm (U R d)]
    symm
    apply commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (s.decomposition_at d hdcolor).symm)
    · exact inf_le_right.trans (centralizer_le hQa)
    · exact hUQ.trans (Q R a).le_normalizer
  have hnorm : Q R a ≤ normalizer (U R d : Set (FreeAmalgam R)) :=
    hQa.trans (U_normalized d)
  have hle : ⁅U R d, Q R a⁆ ≤ U R d :=
    le_normalizer_iff_commutator_le_left.mp hnorm
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by
    rw [modules.natural.card_at d hdcolor]; decide)
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  have hne : ⁅U R d, Q R a⁆ ≠ U R d := by
    intro heq
    have hbot : U R d ≤ ⊥ := le_of_le_sup_commutator_of_isNilpotent
      (Q R a) (U R d) ⊥ (Q R a)
      (Q_isPGroup R source.two_group source.core_le a ha).isNilpotent
      hUQ bot_le le_rfl le_normalizer_of_normal
      (by simpa only [bot_sup_eq, heq] using (le_refl (U R d)))
    have hc := modules.natural.card_at d hdcolor
    rw [le_bot_iff.mp hbot, card_bot] at hc
    omega
  have hcardne : Nat.card (⁅U R d, Q R a⁆ : Subgroup (FreeAmalgam R)) ≠ 8 := by
    intro hc
    exact hne (eq_of_le_of_card_ge hle (by rw [hc, modules.natural.card_at d hdcolor]))
  have hdiv := card_dvd_of_le hle
  rw [modules.natural.card_at d hdcolor] at hdiv
  have hdivs := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdivs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdivs
  rw [hcomm]
  omega

theorem localControl_of_commutator_le (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    {p : Counterexample geometry} (initial : InitialFacts p)
    (hfixed : ⁅V R p.a, Q R p.a⁆ ≤ fixedCore R p.a) : LocalControl p := by
  refine ⟨hfixed, ?_⟩
  intro t ht d hdt hd
  have hH := H_le_moving_commutator source hb initial hfixed hd
  have hcard := moving_commutator_card_le_four source hb modules p.color_a hd
  have hleU : ⁅Z R d, Q R p.a⁆ ≤ Z R d :=
    le_normalizer_iff_commutator_le_left.mp
      ((Q_le_stabilizer_of_dist_two R p.a d p.color_a hd.1).trans (Z_normalized R d))
  let := finite_stabilizer R d
  let : Finite (⁅Z R d, Q R p.a⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (hleU.trans (Z_le_stabilizer R d)))
      (inclusion_injective _)
  have heq : H R p.a = ⁅Z R d, Q R p.a⁆ :=
    eq_of_le_of_card_ge hH (hcard.trans initial.H_card)
  exact ⟨heq, heq.trans (initial.edge_commutator t ht d hdt hd)⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl
