module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Iteration.EdgeSwitching.InvariantRadius
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.FiniteGeometry.Planes

/-!
# Reduction of backward switching to the radius image of order two

An escaping subgroup fixing a natural plane has image of order two or four
in the actual marked SL₃(2) quotient. An image of order four is normal in
any containing two-subgroup: that two-subgroup has order at most eight.
Its fixed plane is consequently invariant, which identifies the backward
edge with the source commutator plane.

The final theorem applies this calculation to the original failed-span
commutator and its radius group at every induction stage. Only normalization
in the order-two image case remains an explicit premise. This does not
assert that the remaining source normalization has been proved.

Source: Meierfrankenfeld--Stellmacher (1993), the radius-group step of
(4.4.4), printed p.894.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement
open PathCentrality.RegularPaths PathCentrality.RegularPaths.CommutatorPropagation
open Escape.Propagation.Backward.Products.Selection.Choices
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem four_normalized_in_two (A P : Subgroup SL) (hAP : A ≤ P)
    (hA : Nat.card A = 4) (hP : IsPGroup 2 P) : P ≤ normalizer A := by
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hPcard : Nat.card P ≤ 8 := by
    have h := Subgroup.card_le_of_le hS
    have hc : Nat.card (S : Subgroup SL) = 8 := by
      rw [S.card_eq_multiplicity, Matrix.PSL3Two.card_SL]
      decide +kernel
    exact hc ▸ h
  have hm := (A.subgroupOf P).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hAP).toEquiv, hA] at hm
  have hi : (A.subgroupOf P).index = 1 ∨ (A.subgroupOf P).index = 2 := by
    have hn := (A.subgroupOf P).index_ne_zero_of_finite
    omega
  rcases hi with hi | hi
  · have he : A = P := eq_of_le_of_card_ge hAP (by omega)
    rw [he]
    exact P.le_normalizer
  · have hn : (A.subgroupOf P).Normal := normal_of_index_eq_two hi
    exact (normal_subgroupOf_iff_le_normalizer hAP).mp hn

omit [Finite M] in
theorem actorImage_two_or_four_of_fixed_plane
    {c : Vertex R} (model : LocalModel c)
    {K A : Subgroup (FreeAmalgam R)} (hK : K ≤ U R c) (hcard : Nat.card K = 4)
    (hA : A ≤ stabilizer R c) (hescape : ¬ A ≤ Q R c) (hcomm : ⁅K,A⁆ = ⊥) :
    (Q R c).relIndex A = 2 ∨ (Q R c).relIndex A = 4 := by
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hle : model.actorImage A ≤ planeFixer (model.coordinates K) := by
    rintro _ ⟨g,hg,rfl⟩ _ ⟨u,hu,rfl⟩
    exact (model.action_fixed_iff g u).mpr (hcentral hu g hg)
  have hfix : Nat.card (planeFixer (model.coordinates K)) = 4 :=
    FiniteGeometry.planeFixer_card _ ((model.coordinates_card K hK).trans hcard)
  have hdiv := card_dvd_of_le hle
  rw [hfix] at hdiv
  have hne : model.actorImage A ≠ ⊥ := by
    intro he
    apply hescape
    intro x hx
    have hh : model.projection ⟨x,hA hx⟩ = 1 := by
      have hm := mem_map_of_mem model.projection
        (show (⟨x,hA hx⟩ : stabilizer R c) ∈ A.subgroupOf (stabilizer R c) from hx)
      change model.projection ⟨x,hA hx⟩ ∈ model.actorImage A at hm
      rwa [he,mem_bot] at hm
    have hk : (⟨x,hA hx⟩ : stabilizer R c) ∈ model.projection.ker := hh
    rwa [model.kernel] at hk
  have hpos := (one_lt_card_iff_ne_bot _).mpr hne
  have hd := Nat.mem_divisors.mpr ⟨hdiv,(by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = {1,2,4} by decide] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rw [model.actorImage_card A hA] at hd hpos
  omega

theorem edge_switch_of_image_four (common : CommonFacts R source geometry)
    {c s t : Vertex R} (model : LocalModel c) (hc : color R c = false)
    (hs : Adjacent R c s) (ht : Adjacent R c t)
    {K A : Subgroup (FreeAmalgam R)}
    (hforward : K = edgeCommutator R c t) (hcard : Nat.card K = 4)
    (hA : A ≤ Q R s) (hescape : ¬ A ≤ Q R c) (hcomm : ⁅K,A⁆ = ⊥)
    (hfour : (Q R c).relIndex A = 4) : K = edgeCommutator R c s := by
  apply Iteration.EdgeSwitching.edge_switch_of_normalized_image common model hc hs ht
    hforward hcard hA hescape hcomm
  have hS : Q R s ≤ stabilizer R c := fun _ hx => hx.2 c (adjacent_symm R hs)
  apply four_normalized_in_two _ _ (map_mono (comap_mono hA))
  · exact (model.actorImage_card A (hA.trans hS)).trans hfour
  · exact (Escape.EdgeTransfer.edge_kernel_two source c s hc hs).comap_subtype.map model.projection

/-- Only the order-two radius image needs a source normalization argument. -/
@[expose] def BackwardTwoImageNormalization {a a' : Vertex R}
    (p : CriticalPath R geometry a a') (K : Subgroup (FreeAmalgam R)) : Prop :=
  ∀ n : ℕ, 0 < n → 4 * n + 4 ≤ p.walk.length →
    K = edgeCommutator R (p.walk.getVert (p.walk.length - 4 * n))
      (p.walk.getVert (p.walk.length - 4 * n + 1)) →
    K ≤ fixedCore R (p.walk.getVert (p.walk.length - 4 * n + 2)) →
    (Q R (p.walk.getVert (p.walk.length - 4 * n))).relIndex
      (VBall R a (4 * n)) = 2 →
    Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
      normalizer (VBall R a (4 * n) ⊔ Q R (p.walk.getVert (p.walk.length - 4 * n)) :
        Subgroup (FreeAmalgam R))

theorem backwardEdgeSwitching_of_two_image_normalized
    (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (seed : TerminalPropagationSeed p (failedSpanCommutator p g))
    (hnorm : BackwardTwoImageNormalization p (failedSpanCommutator p g)) :
    Iteration.BackwardEdgeSwitching p (failedSpanCommutator p g) := by
  intro n hn hlen hforward hfixed
  have heven : Even (p.walk.length - 4 * n) := by
    have he := geometry.even (alpha R) rfl
    change Even (geometry.b R) at he
    rw [← p.length_eq_b, Nat.even_iff] at he
    rw [Nat.even_iff]
    omega
  obtain ⟨hcomm,hescape,hA⟩ := Iteration.switching_ball_facts common p hg heven
    (by omega) (by omega)
  have hind : p.walk.length - (p.walk.length - 4 * n) = 4 * n := by omega
  rw [hind] at hcomm hescape hA
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
  have hS : Q R (p.walk.getVert (p.walk.length - 4 * n - 1)) ≤
      stabilizer R (p.walk.getVert (p.walk.length - 4 * n)) :=
    fun _ hx => hx.2 _ (adjacent_symm R hs)
  have hcard := Iteration.EdgeSwitching.seed_card_four common p seed
  have hKU : failedSpanCommutator p g ≤ U R (p.walk.getVert (p.walk.length - 4 * n)) := by
    rw [hforward]
    exact Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) _ _ hc ht
  obtain ⟨model⟩ := localModel_nonempty source (moduleFacts common) _ hc
  rcases actorImage_two_or_four_of_fixed_plane model hKU hcard (hA.trans hS) hescape hcomm
    with htwo | hfour
  · exact Iteration.EdgeSwitching.edge_switch_of_normalized_radius common hc hs ht
      hforward hcard hA hescape hcomm (hnorm n hn hlen hforward hfixed htwo)
  · exact edge_switch_of_image_four common model hc hs ht hforward hcard hA hescape hcomm hfour

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement
