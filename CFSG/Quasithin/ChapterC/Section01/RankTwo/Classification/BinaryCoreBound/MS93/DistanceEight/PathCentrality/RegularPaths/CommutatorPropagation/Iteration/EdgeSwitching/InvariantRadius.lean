module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.EdgeSwitching
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.LocalAction
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# Backward-edge switching from an invariant radius image

An escaping actor fixing a four-subgroup of the natural eight-group has
that subgroup as its full natural centralizer. If the radius image is normal
in the backward edge image, this plane is invariant under the backward edge
kernel. The quotient by the plane has order two, so the backward displacement
lies in the plane. Neighbor conjugacy and the seed's order-four consequence
then give the required edge equality.

The actual marked projection identifies image normalization with normalization
of A joined with Q at the switching vertex. This is quotient normalization;
no normalization of A itself, pointwise fixation of the entire backward edge,
or lower bound four on the radius image is assumed. In particular the argument
also covers a nontrivial normal radius image of order two.

The path application retains the literal failedSpanCommutator, the radius
centered at the original a, and the forward-edge and fixed-core induction
premises. It feeds Recurrence.source_recurrence. The radius-normalization
premise remains explicit and unproved from the source inputs: these conditional
results do not establish MS93 (4.4.4).

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the radius paragraph of (4.4.4), printed p.894.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.EdgeSwitching
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- An escaping local actor fixing a natural plane has precisely that fixed plane. -/
theorem plane_eq_natural_centralizer (common : CommonFacts R source geometry)
    {c : Vertex R} (hc : color R c = false)
    {K A : Subgroup (FreeAmalgam R)} (hK : K ≤ U R c) (hcard : Nat.card K = 4)
    (hA : A ≤ stabilizer R c) (hescape : ¬ A ≤ Q R c)
    (hcomm : ⁅K, A⁆ = ⊥) : K = U R c ⊓ centralizer (A : Set (FreeAmalgam R)) := by
  let F := U R c ⊓ centralizer (A : Set (FreeAmalgam R))
  have hKF : K ≤ F := le_inf hK (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  let : Finite (U R c) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at c hc]; decide)
  let : Finite F := Finite.of_injective (inclusion (show F ≤ U R c from inf_le_left))
    (inclusion_injective _)
  have hproper : F ≠ U R c := by
    intro h
    apply hescape
    rw [← common.natural.centralizer c hc]
    exact le_inf hA (le_centralizer_iff.mp (h ▸ (show F ≤ centralizer (A : Set (FreeAmalgam R)) from inf_le_right)))
  have hdiv := card_dvd_of_le (show F ≤ U R c from inf_le_left)
  rw [common.natural.card_at c hc] at hdiv
  have hd := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  have hnot8 : Nat.card F ≠ 8 := by
    intro h8
    exact hproper (eq_of_le_of_card_ge (show F ≤ U R c from inf_le_left)
      (by rw [common.natural.card_at c hc, h8]))
  have hsmall : Nat.card F ≤ 4 := by
    omega
  apply eq_of_le_of_card_ge hKF
  omega

/-- An invariant natural plane of order four equals the backward edge displacement.
The argument uses the trivial action on its quotient of order two. -/
theorem edge_switch_of_normalized_plane (common : CommonFacts R source geometry)
    {c s t : Vertex R} (hc : color R c = false)
    (hs : Adjacent R c s) (ht : Adjacent R c t)
    {K : Subgroup (FreeAmalgam R)}
    (hforward : K = edgeCommutator R c t) (hcard : Nat.card K = 4)
    (hnorm : Q R s ≤ normalizer (K : Set (FreeAmalgam R))) :
    K = edgeCommutator R c s := by
  have hKU : K ≤ U R c := by
    rw [hforward]
    exact Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) c t hc ht
  let : Finite (U R c) := Nat.finite_of_card_ne_zero
    (by rw [common.natural.card_at c hc]; decide)
  let : Finite K := Finite.of_injective (inclusion hKU) (inclusion_injective _)
  have hi : K.relIndex (U R c) = 2 := by
    have hh := (K.subgroupOf (U R c)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hKU).toEquiv,
      hcard, common.natural.card_at c hc] at hh
    change 4 * K.relIndex (U R c) = 8 at hh
    omega
  have hE : edgeCommutator R c s ≤ K := by
    rw [edgeCommutator, Escape.EdgeTransfer.edge_commutator_eq_natural
      common.large_distance (moduleFacts common) c s hc hs]
    apply commutator_le_of_normalized_index_two _ _ _ hKU hi _ hnorm
    exact (show Q R s ≤ stabilizer R c from fun _ hx => hx.2 c (adjacent_symm R hs)).trans
      (U_normalized c)
  obtain ⟨g, _, hg⟩ := exists_edge_conjugator ht hs
  have hEcard : Nat.card (edgeCommutator R c s) = 4 := by
    rw [← hg, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, ← hforward]
    exact hcard
  exact (eq_of_le_of_card_ge hE (by omega)).symm

/-- Setwise backward-kernel invariance is sufficient and necessary for switching.
Only invariance of K is required in this criterion. -/
theorem edge_switch_iff_normalized_plane (common : CommonFacts R source geometry)
    {c s t : Vertex R} (hc : color R c = false)
    (hs : Adjacent R c s) (ht : Adjacent R c t)
    {K : Subgroup (FreeAmalgam R)}
    (hforward : K = edgeCommutator R c t) (hcard : Nat.card K = 4) :
    K = edgeCommutator R c s ↔ Q R s ≤ normalizer (K : Set (FreeAmalgam R)) := by
  constructor
  · intro h
    rw [h]
    exact normalizer_commutator_ge_right _ _
  · exact edge_switch_of_normalized_plane common hc hs ht hforward hcard

/-- Normalization modulo the local kernel makes the fixed plane invariant.
This requires no lower bound on the nontrivial radius image. -/
theorem edge_switch_of_normalized_radius (common : CommonFacts R source geometry)
    {c s t : Vertex R} (hc : color R c = false)
    (hs : Adjacent R c s) (ht : Adjacent R c t)
    {K A : Subgroup (FreeAmalgam R)}
    (hforward : K = edgeCommutator R c t) (hcard : Nat.card K = 4)
    (hA : A ≤ Q R s) (hescape : ¬ A ≤ Q R c) (hcomm : ⁅K, A⁆ = ⊥)
    (hnorm : Q R s ≤ normalizer (A ⊔ Q R c : Subgroup (FreeAmalgam R))) :
    K = edgeCommutator R c s := by
  have hKU : K ≤ U R c := by
    rw [hforward]
    exact Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) c t hc ht
  have hS : Q R s ≤ stabilizer R c := fun _ hx => hx.2 c (adjacent_symm R hs)
  have hKQ : K ≤ centralizer (Q R c : Set (FreeAmalgam R)) :=
    (hKU.trans (U_le_Z R c)).trans
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes c hc))
  have hKJ : ⁅K, A ⊔ Q R c⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm))
      (le_centralizer_iff.mp hKQ)
  have he := plane_eq_natural_centralizer common hc hKU hcard
    (sup_le (hA.trans hS) (show Q R c ≤ stabilizer R c from fun _ hx => hx.1))
    (fun h => hescape (le_sup_left.trans h)) hKJ
  apply (edge_switch_iff_normalized_plane common hc hs ht hforward hcard).mpr
  rw [he]
  exact (le_inf (hS.trans (U_normalized c))
    (hnorm.trans (normalizer_le_normalizer_centralizer (A ⊔ Q R c)))).trans
      inf_normalizer_le_normalizer_inf

omit [Finite M] in
/-- The actual local projection identifies normalization of A joined with its
kernel with normalization of the literal quotient image of A. -/
theorem radius_normalized_iff_actorImage_normalized {c : Vertex R} (model : LocalModel c)
    {A B : Subgroup (FreeAmalgam R)} (hA : A ≤ stabilizer R c)
    (hB : B ≤ stabilizer R c) :
    B ≤ normalizer (A ⊔ Q R c : Subgroup (FreeAmalgam R)) ↔
      model.actorImage B ≤ normalizer (model.actorImage A : Set SL) := by
  have hQ : Q R c ≤ stabilizer R c := fun _ hx => hx.1
  have he : (model.actorImage A).comap model.projection =
      (A ⊔ Q R c).subgroupOf (stabilizer R c) := by
    rw [LocalModel.actorImage, comap_map_eq, model.kernel, subgroupOf_sup hA hQ]
  change B ≤ normalizer (A ⊔ Q R c : Subgroup (FreeAmalgam R)) ↔
    (B.subgroupOf (stabilizer R c)).map model.projection ≤ _
  rw [map_le_iff_le_comap, comap_normalizer_eq_of_surjective _ model.surjective, he,
    ← subgroupOf_normalizer_eq (sup_le hA hQ)]
  constructor
  · intro h x hx
    exact h hx
  · intro h x hx
    exact h (show (⟨x, hB hx⟩ : stabilizer R c) ∈ B.subgroupOf (stabilizer R c) from hx)

/-- The marked natural quotient supplies switching even for an order-two image,
provided that image is normalized by the backward edge image. -/
theorem edge_switch_of_normalized_image (common : CommonFacts R source geometry)
    {c s t : Vertex R} (model : LocalModel c) (hc : color R c = false)
    (hs : Adjacent R c s) (ht : Adjacent R c t)
    {K A : Subgroup (FreeAmalgam R)}
    (hforward : K = edgeCommutator R c t) (hcard : Nat.card K = 4)
    (hA : A ≤ Q R s) (hescape : ¬ A ≤ Q R c) (hcomm : ⁅K, A⁆ = ⊥)
    (hnorm : model.actorImage (Q R s) ≤ normalizer (model.actorImage A : Set SL)) :
    K = edgeCommutator R c s := by
  have hS : Q R s ≤ stabilizer R c := fun _ hx => hx.2 c (adjacent_symm R hs)
  exact edge_switch_of_normalized_radius common hc hs ht hforward hcard hA hescape hcomm
    ((radius_normalized_iff_actorImage_normalized model (hA.trans hS) hS).mpr hnorm)

/-- An explicit remaining proof target: the radius image is invariant in the
backward edge quotient. No assertion of this normalization is made here. -/
def BackwardRadiusNormalization {a a' : Vertex R} (p : CriticalPath R geometry a a')
    (K : Subgroup (FreeAmalgam R)) : Prop :=
  ∀ n : ℕ, 0 < n → 4 * n + 4 ≤ p.walk.length →
    K = edgeCommutator R (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n + 1)) →
    K ≤ fixedCore R (p.walk.getVert (p.walk.length - 4 * n + 2)) →
    Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
      normalizer (VBall R a (4 * n) ⊔ Q R (p.walk.getVert (p.walk.length - 4 * n)) :
        Subgroup (FreeAmalgam R))

/-- The conditional local calculation supplies the exact original switching
contract for the failed-span commutator and the ball centered at a. -/
theorem backwardEdgeSwitching_of_radius_normalized (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (seed : TerminalPropagationSeed p (failedSpanCommutator p g))
    (hnorm : BackwardRadiusNormalization p (failedSpanCommutator p g)) :
    BackwardEdgeSwitching p (failedSpanCommutator p g) := by
  intro n hn hlen hforward hfixed
  have heven : Even (p.walk.length - 4 * n) := by
    have he := geometry.even (alpha R) rfl
    change Even (geometry.b R) at he
    rw [← p.length_eq_b, Nat.even_iff] at he
    rw [Nat.even_iff]
    omega
  obtain ⟨hcomm, hescape, hA⟩ := switching_ball_facts common p hg heven
    (by omega) (by omega)
  have hs : Adjacent R (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n - 1)) := by
    apply adjacent_symm R
    have hh := p.walk.adj_getVert_succ (i := p.walk.length - 4 * n - 1) (by omega)
    rw [show p.walk.length - 4 * n - 1 + 1 = p.walk.length - 4 * n by omega] at hh
    exact (cosetGraph_adj R _ _).mp hh
  have ht : Adjacent R (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n + 1)) :=
    (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by omega))
  have hc := (p.vertex_color (by omega)).mpr heven
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) _ hc
  apply edge_switch_of_normalized_image common model hc
    hs ht hforward (seed_card_four common p seed) hA hescape hcomm
  have hS : Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
      stabilizer R (p.walk.getVert (p.walk.length - 4 * n)) :=
    fun _ hx => hx.2 _ (adjacent_symm R hs)
  apply (radius_normalized_iff_actorImage_normalized model (hA.trans hS) hS).mp
  simpa only [Nat.sub_sub_self (by omega : 4 * n ≤ p.walk.length)] using
    hnorm n hn hlen hforward hfixed

/-- Application to the original recurrence; the radius-normalization premise
still needs a source proof, and final source assembly remains incomplete. -/
theorem source_recurrence_of_radius_normalized (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hp : HasTurnConjugators R p)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (seed : TerminalPropagationSeed p (failedSpanCommutator p g))
    (hnorm : BackwardRadiusNormalization p (failedSpanCommutator p g))
    (n : ℕ) (hn : 0 < n) (hbound : 4 * n < geometry.b R - 2) :
    failedSpanCommutator p g = edgeCommutator R
      (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n + 1)) ∧
    failedSpanCommutator p g ≤ fixedCore R
      (p.walk.getVert (p.walk.length - 4 * n - 2)) :=
  source_recurrence source p hp seed
    (backwardEdgeSwitching_of_radius_normalized common p hg seed hnorm) n hn hbound

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.EdgeSwitching
