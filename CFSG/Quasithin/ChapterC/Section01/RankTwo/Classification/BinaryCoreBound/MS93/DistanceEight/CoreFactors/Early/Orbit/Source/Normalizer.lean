module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Obstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.RelativeNormalizer

/-!
# The corrected relative normality in MS93 (4.5.2)(i)

The actor is the normalizer of the incident kernel inside the other local
stabilizer. Its action on the seed Z-layer is realized in the holomorph
stabilizer, so its conjugate span lies in the original radius-two group.
Moving generation and the order-four edge calculation identify the seed
commutator with H at the other vertex. Centrality from (4.4) and the trivial
fixed subgroup of the natural layer force the span to centralize Q. The
identity X = Z then collapses that span to the original seed.

The local theorem retains the precise moving-neighbor hypothesis. The path
applications prove every needed forward and reflected instance on the same
supplied walk, including Z at index eight normal in the actor at (six,seven).
Containment and relative normality are both retained. The legacy OrbitFacts
and its edge-stabilizer obstruction are unchanged.

Source: Meierfrankenfeld--Stellmacher (1993), notation on printed p.881 and
(4.5.2)(i), printed p.897; standing path convention on pp.895--896.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R}

/-- The source actor G_(a,t) = N_(G_a)(Q_t), with Q_t representing T_t. -/
def relativeNormalizer (R : Subgroup M) (a t : Vertex R) : Subgroup (FreeAmalgam R) :=
  stabilizer R a ⊓ normalizer (Q R t : Set (FreeAmalgam R))

private theorem H_centralizes_local (earlier : Earlier R geometry)
    {a : Vertex R} (ha : color R a = false) :
    H R a ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
  intro x hx y hy
  obtain ⟨z, hz, rfl⟩ := H_le_localCenter_of_central R a (earlier.centrality a ha) hx
  exact congrArg Subtype.val (mem_center_iff.mp hz ⟨y, hy⟩)

private theorem conjugate_Z_le_radius [Finite M]
    (common : CommonFacts R source geometry) {a t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t)
    (g : FreeAmalgam R) (hg : g ∈ normalizer (Q R t : Set (FreeAmalgam R))) :
    rightConjugate (Z R a) g ≤ V R a := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hZQ : Z R a ≤ Q R t :=
    ((Z_le_VBall R a 2).trans (V_le_Q R ha common.large_distance)).trans
      (Q_le_adjacent_h R ht hat)
  obtain ⟨k, hk, he⟩ := Escape.Propagation.Backward.Products.holomorph_realizes t a ha hat
    g⁻¹ ((normalizer _).inv_mem hg)
  change (Z R a).map (MulAut.conj g⁻¹).toMonoidHom ≤ _
  rw [← Escape.Propagation.Backward.Products.map_conj_eq_of_agree hZQ he]
  have hkfix : act R k⁻¹ t = t := (stabilizer R t).inv_mem hk
  have hkat : Adjacent R (act R k⁻¹ a) t := by
    simpa only [hkfix] using (adjacent_act_iff R k⁻¹ a t).mpr hat
  have hd : (cosetGraph R).dist (act R k⁻¹ a) a ≤ 2 := by
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hkat)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hat))
    have htri := (cosetGraph_connected R).dist_triangle (u := act R k⁻¹ a) (v := t) (w := a)
    omega
  have hZ := Z_act R k⁻¹ a
  simp only [inv_inv] at hZ
  rw [← hZ]
  exact le_iSup_of_le _ (le_iSup_of_le hd le_rfl)

/-- Radius-two clearance gives containment in the actual relative normalizer. -/
theorem Z_le_relativeNormalizer [Finite M]
    (common : CommonFacts R source geometry) {a c t : Vertex R}
    (hc : color R c = false) (hct : Adjacent R c t)
    (hac : (cosetGraph R).dist a c ≤ 2) :
    Z R a ≤ relativeNormalizer R c t := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hct
    cases h : color R t <;> simp_all
  have hZQ : Z R a ≤ Q R c :=
    (le_iSup_of_le a (le_iSup_of_le hac le_rfl) : Z R a ≤ V R c).trans
      (V_le_Q R hc common.large_distance)
  exact hZQ.trans (le_inf (fun _ hx => hx.1)
    ((Q_le_adjacent_h R ht hct).trans (Q R t).le_normalizer))

/-- The moving seed displacement fills H at the opposite even vertex. -/
theorem moving_edge_displacement_eq_H [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a c t : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hmove : a ∈ Escape.movingNeighbors geometry c) :
    ⁅Z R a, Q R t⁆ = H R c := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hle : H R c ≤ ⁅Z R a, Q R t⁆ :=
    (H_le_displacement common earlier hc hmove).trans
      (commutator_mono le_rfl (Q_le_adjacent_h R ht hct))
  have hcard := First.Layer.edge_displacement_card common earlier ha hat
  let : Finite (⁅Z R a, Q R t⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  exact (eq_of_le_of_card_ge hle (by
    rw [hcard]
    exact First.Layer.H_card_lower common earlier c hc)).symm

/-- The V₀ argument of (4.5.2)(i), under the exact inherited moving condition. -/
theorem Z_normalized_by_relativeNormalizer_of_moving [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a c t : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hmove : a ∈ Escape.movingNeighbors geometry c) :
    relativeNormalizer R c t ≤ normalizer (Z R a : Set (FreeAmalgam R)) := by
  let P := relativeNormalizer R c t
  let V₀ := conjugatesIn (Z R a) P
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hZQ : Z R a ≤ Q R t :=
    ((Z_le_VBall R a 2).trans (V_le_Q R ha common.large_distance)).trans
      (Q_le_adjacent_h R ht hat)
  have hV : V₀ ≤ V R a := by
    apply iSup_le
    intro g
    exact conjugate_Z_le_radius common ha hat g g.property.2
  have hHnorm : P ≤ normalizer (H R c : Set (FreeAmalgam R)) :=
    (show P ≤ stabilizer R c from inf_le_left).trans
      ((le_centralizer_iff.mp (H_centralizes_local earlier hc)).trans
        (Subgroup.centralizer_le_normalizer _))
  have hcomm : ⁅V₀, Q R t⁆ = H R c := by
    rw [Escape.PairingControl.commutator_conjugatesIn _ _ _ hZQ
      (show P ≤ normalizer (Q R t : Set (FreeAmalgam R)) from inf_le_right),
      moving_edge_displacement_eq_H common earlier ha hc hat hct hmove]
    exact Escape.PairingControl.conjugatesIn_eq_of_normalized _ _ hHnorm
  have hzero : ⁅V₀, Q R a⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [← Escape.EdgeTransfer.U_fixed_eq_bot (LocalCommutator.moduleFacts common) a ha]
    apply le_inf
    · exact ((commutator_mono le_rfl (Q_le_adjacent_h R ht hat)).trans hcomm.le).trans
        (H_le_neighbor_U common earlier hc hmove)
    · intro x hx l hl
      obtain ⟨z, hz, rfl⟩ := earlier.centrality a ha (commutator_mono hV le_rfl hx)
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨l, Ltilde_le_stabilizer a hl⟩)
  have hVZ : V₀ ≤ Z R a := by
    rw [← common.X_eq_Z a ha]
    let := V_elementary_of_four_lt R ha (by rw [earlier.distance]; decide)
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨V_le_Q R ha common.large_distance (hV hx),
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V R a) x (hV hx),
      commutator_eq_bot_iff_le_centralizer.mp hzero hx⟩
  have heq : V₀ = Z R a := by
    apply le_antisymm hVZ
    intro x hx
    apply (le_iSup (fun g : P => rightConjugate (Z R a) g) 1)
    exact ⟨x, hx, by simp⟩
  rw [← heq]
  exact conjugatesIn_normalized _ _

/-- Both containment and normality inside the source actor, without ambient normality. -/
theorem Z_normal_in_relativeNormalizer_of_moving [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a c t : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    (hmove : a ∈ Escape.movingNeighbors geometry c) :
    Z R a ≤ relativeNormalizer R c t ∧
      ((Z R a).subgroupOf (relativeNormalizer R c t)).Normal := by
  exact ⟨Z_le_relativeNormalizer common hc hct (by rw [SimpleGraph.dist_comm]; exact hmove.1.le),
    normal_subgroupOf_of_le_normalizer
      (Z_normalized_by_relativeNormalizer_of_moving common earlier ha hc hat hct hmove)⟩

/-- All forward normality instances whose other even vertex is interior to this path. -/
theorem forward_normality [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi10 : i ≤ 10) :
    Z R (p.walk.getVert i) ≤ relativeNormalizer R (p.walk.getVert (i + 2))
      (p.walk.getVert (i + 1)) ∧
    ((Z R (p.walk.getVert i)).subgroupOf
      (relativeNormalizer R (p.walk.getVert (i + 2)) (p.walk.getVert (i + 1)))).Normal := by
  have hc : Even (i + 2) := hi.add (by decide)
  apply Z_normal_in_relativeNormalizer_of_moving common earlier
    (p.even_color hi (by omega)) (p.even_color hc (by omega))
    (p.adjacent (by omega))
  · exact adjacent_symm R (by
      simpa only [Nat.add_assoc] using p.adjacent (i := i + 1) (by omega))
  · simpa only [Nat.add_sub_cancel] using
      (p.moving_neighbors source common earlier hc (by omega) (by omega)).1

/-- Reflected normality on this very walk, obtained from its backward moving neighbor. -/
theorem backward_normality [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi14 : i ≤ 14) :
    Z R (p.walk.getVert i) ≤ relativeNormalizer R (p.walk.getVert (i - 2))
      (p.walk.getVert (i - 1)) ∧
    ((Z R (p.walk.getVert i)).subgroupOf
      (relativeNormalizer R (p.walk.getVert (i - 2)) (p.walk.getVert (i - 1)))).Normal := by
  have hc : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  apply Z_normal_in_relativeNormalizer_of_moving common earlier
    (p.even_color hi hi14) (p.even_color hc (by omega))
  · exact adjacent_symm R (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using p.adjacent (i := i - 1) (by omega))
  · simpa only [show i - 2 + 1 = i - 1 by omega] using
      p.adjacent (i := i - 2) (by omega)
  · simpa only [Nat.sub_add_cancel (by omega : 2 ≤ i)] using
      (p.moving_neighbors source common earlier hc (by omega) (by omega)).2

/-- Literal (4.5.2)(i) at the central vertex of the supplied path. -/
theorem center_normality [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) :
    Z R a ≤ relativeNormalizer R (p.walk.getVert 6) (p.walk.getVert 5) ∧
      ((Z R a).subgroupOf
        (relativeNormalizer R (p.walk.getVert 6) (p.walk.getVert 5))).Normal := by
  simpa only [p.center_eq] using forward_normality common earlier p (i := 4)
    (by decide) (by decide)

/-- The same-path input used by the higher replacement consumer at (eight,six,seven). -/
theorem reflected_normality [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) :
    Z R (p.walk.getVert 8) ≤ relativeNormalizer R (p.walk.getVert 6) (p.walk.getVert 7) ∧
      ((Z R (p.walk.getVert 8)).subgroupOf
        (relativeNormalizer R (p.walk.getVert 6) (p.walk.getVert 7))).Normal :=
  backward_normality common earlier p (i := 8) (by decide) (by decide) (by decide)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source
