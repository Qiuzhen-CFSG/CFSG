module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Span

/-!
# Actual local centrality from the earlier escape control

The fixed core only centralizes the residual. Edge displacement also
centralizes the adjacent kernel, and the residual and kernel generate the
local group. Keeping these two arguments separate places R₀ in the actual
center at the vertex two before the endpoint; fixedCore is not substituted
for that center.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)--(4.3.3), and their
use in (4.3.6)--(4.3.8), printed pp.883--888.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Membership in the actual local center includes local containment. -/
theorem le_localCenter_iff (a : Vertex R) (A : Subgroup (FreeAmalgam R)) :
    A ≤ localCenter a ↔ A ≤ stabilizer R a ∧
      A ≤ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
  constructor
  · intro h
    constructor
    · exact h.trans (map_subtype_le _)
    · intro x hx y hy
      obtain ⟨z, hz, rfl⟩ := h hx
      exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)
  · rintro ⟨hlocal, hcentral⟩ x hx
    refine ⟨⟨x, hlocal hx⟩, ?_, rfl⟩
    change (⟨x, hlocal hx⟩ : stabilizer R a) ∈ center (stabilizer R a)
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact hcentral hx y y.property

variable [Finite M]

/-- Fixed-core containment and kernel centrality together give the actual
local center, using the source generation by the residual and kernel. -/
theorem le_localCenter_of_fixedCore (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) (A : Subgroup (FreeAmalgam R))
    (hfixed : A ≤ fixedCore R a)
    (hQ : A ≤ centralizer (Q R a : Set (FreeAmalgam R))) : A ≤ localCenter a := by
  apply (le_localCenter_iff a A).mpr
  refine ⟨hfixed.trans (inf_le_left.trans (fun _ hx => hx.1)), ?_⟩
  apply le_centralizer_iff.mpr
  rw [← source.local_generation a ha]
  exact sup_le (le_centralizer_iff.mp (hfixed.trans inf_le_right))
    (le_centralizer_iff.mp hQ)

private theorem generator_commutator_centralizes_Q (p : Counterexample geometry)
    (hb : 2 < geometry.b R)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (a : Vertex R) (ha : color R a = false) (d : Vertex R)
    (hd : (cosetGraph R).dist d a ≤ 2) :
    ⁅Z R d, Q R a⁆ ≤ centralizer (Q R a : Set (FreeAmalgam R)) := by
  by_cases hzero : (cosetGraph R).dist d a = 0
  · have hda := (cosetGraph_connected R).dist_eq_zero_iff.mp hzero
    subst d
    rw [geometry.centralizes a ha]
    exact bot_le
  by_cases hone : (cosetGraph R).dist d a = 1
  · have had : Adjacent R a d := adjacent_symm R
      ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp hone))
    apply (commutator_mono (EdgeTransfer.edge_Z_le a d ha had) le_rfl).trans
    rw [geometry.centralizes a ha]
    exact bot_le
  have htwo : (cosetGraph R).dist a d = 2 := by rw [SimpleGraph.dist_comm]; omega
  have hdcol : color R d = false :=
    (color_eq_of_dist_even R a d (htwo.symm ▸ (by decide : Even 2))).symm.trans ha
  obtain ⟨t, hat, hdt⟩ := exists_common_neighbor_of_dist_two R a d htwo
  have htcol : color R t = true := by
    have hn := adjacent_color_ne R hat
    rw [ha] at hn
    cases h : color R t <;> simp_all
  have hQ : Q R a ≤ Q R t := Q_le_adjacent_h R htcol hat
  have hZ : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [Z, if_neg (by rw [htcol]; decide)]
    intro x hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  exact (commutator_mono le_rfl hQ).trans
    ((edge_le_Z p hb control edge d t hdcol hdt).trans
      (hZ.trans (centralizer_le hQ)))

/-- The edge calculation proves kernel centrality for the full radius
commutator, including the nonmoving generators. -/
theorem radius_kernel_commutator_centralizes (p : Counterexample geometry)
    (hb : 2 < geometry.b R)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (a : Vertex R) (ha : color R a = false) :
    ⁅V R a, Q R a⁆ ≤ centralizer (Q R a : Set (FreeAmalgam R)) := by
  have hV := geometry.V_le_Q hb a ha
  have hZ (d : Vertex R) (hd : (cosetGraph R).dist d a ≤ 2) : Z R d ≤ Q R a :=
    (show Z R d ≤ V R a from le_iSup_of_le d (le_iSup_of_le hd le_rfl)).trans hV
  change ⁅⨆ d, ⨆ (_ : (cosetGraph R).dist d a ≤ 2), Z R d, Q R a⁆ ≤ _
  rw [commutator_iSup_of_le _ _ (fun d => iSup_le (hZ d))]
  apply iSup_le
  intro d
  rw [commutator_iSup_of_le _ _ (hZ d)]
  exact iSup_le (generator_commutator_centralizes_Q p hb control edge a ha d)

/-- Global central control follows from genuine transport, the earlier
fixed-core bound, and the edge calculation. -/
theorem radius_kernel_commutator_le_center (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (a : Vertex R) (ha : color R a = false) : ⁅V R a, Q R a⁆ ≤ localCenter a :=
  le_localCenter_of_fixedCore source a ha _
    (commutator_le_fixed_at p (by omega) control a ha)
    (radius_kernel_commutator_centralizes p hb control edge a ha)

/-- R₀ already centralizes the kernel at c by its genuine endpoint edge
description and (4.3.3). -/
theorem radius_centralizes_before_kernel (p : Counterexample geometry)
    (hb : 2 < geometry.b R) (initial : InitialFacts p)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry) :
    radiusCommutator p.a p.a' ≤ centralizer (Q R p.c : Set (FreeAmalgam R)) := by
  obtain ⟨s, hs⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  have hcs : Adjacent R p.c s := p.before.adjacent (geometry := geometry) hs
  have hscol : color R s = true := by
    have hn := adjacent_color_ne R hs.endpoint_adjacent
    rw [p.end_color] at hn
    cases h : color R s <;> simp_all
  have hZ : Z R s ≤ centralizer (Q R s : Set (FreeAmalgam R)) := by
    rw [Z, if_neg (by rw [hscol]; decide)]
    intro x hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  rw [initial.radius_eq_edge s hs]
  exact (edge_le_Z p hb control edge p.a' s p.end_color hs.endpoint_adjacent).trans
    (hZ.trans (centralizer_le (Q_le_adjacent_h R hscol hcs)))

/-- The local fixed-core bound applies at c by actual counterexample
transport. R₀ is a commutator of a subgroup of Q_c with one of V_c. -/
theorem radius_le_before_fixedCore (p : Counterexample geometry)
    (hb : 0 < geometry.b R)
    (control : ∀ q : Counterexample geometry, LocalControl q) :
    radiusCommutator p.a p.a' ≤ fixedCore R p.c := by
  have hZ : Z R p.a' ≤ V R p.c := by
    apply le_iSup_of_le p.a'
    apply le_iSup_of_le (show (cosetGraph R).dist p.a' p.c ≤ 2 by
      rw [SimpleGraph.dist_comm, p.before.1])
    exact le_rfl
  rw [radiusCommutator, commutator_comm]
  exact (commutator_mono hZ p.trapped).trans
    (commutator_le_fixed_at p hb control p.c p.before_color)

/-- The centrality at c used throughout the backward argument. This
derivation needs only preceding stages, and no radius-four conclusion. -/
theorem radius_le_before_center (source : LocalSource L R) (p : Counterexample geometry)
    (hb : 2 < geometry.b R) (initial : InitialFacts p)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry) :
    radiusCommutator p.a p.a' ≤ localCenter p.c :=
  le_localCenter_of_fixedCore source p.c p.before_color _
    (radius_le_before_fixedCore p (by omega) control)
    (radius_centralizes_before_kernel p hb initial control edge)

/-- The first geometric step of (4.3.6). A genuine local conjugator moves
the endpoint to the intervening edge. Centrality at c fixes R₀, and the
supplied (4.3.4) rigidity identifies the new Z-layer with the backward one.
The moving-neighbor assertion is deliberately not inferred from this equality. -/
theorem noncentral_backward_edge (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (initial : InitialFacts p)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (d t : Vertex R)
    (hd : Before p.a p.a' d 4) (ht : Before p.a p.a' t 3)
    (hn : ¬ radiusCommutator p.a p.a' ≤ localCenter d) :
    ∃ g ∈ stabilizer R p.c, Adjacent R (act R g p.a') t ∧
      Z R (act R g p.a') = Z R d ∧
      radiusCommutator p.a p.a' = edgeDisplacement (act R g p.a') t ∧
      radiusCommutator p.a p.a' = edgeDisplacement d t := by
  obtain ⟨s, hs⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  have hcs : Adjacent R p.c s := p.before.adjacent (geometry := geometry) hs
  have hct : Adjacent R p.c t := adjacent_symm R (ht.adjacent (geometry := geometry) p.before)
  obtain ⟨g, hg, hgs⟩ := stabilizer_transitive_neighbors R p.c hcs hct
  have hμt : Adjacent R (act R g p.a') t := by
    rw [← hgs]
    exact (adjacent_act_iff R g _ _).mpr hs.endpoint_adjacent
  have hcentral := ((le_localCenter_iff p.c _).mp
    (radius_le_before_center source p hb initial control edge)).2
  have hmap : (radiusCommutator p.a p.a').map (MulAut.conj g⁻¹).toMonoidHom =
      radiusCommutator p.a p.a' := by
    have hfix (x : FreeAmalgam R) (hx : x ∈ radiusCommutator p.a p.a') :
        (MulAut.conj g⁻¹) x = x := by
      change g⁻¹ * x * (g⁻¹)⁻¹ = x
      rw [hcentral hx g⁻¹ ((stabilizer R p.c).inv_mem hg)]
      simp only [mul_assoc, inv_mul_cancel, mul_one, inv_inv]
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change (MulAut.conj g⁻¹) x ∈ radiusCommutator p.a p.a'
      rw [hfix x hx]
      exact hx
    · intro x hx
      exact ⟨x, hx, hfix x hx⟩
  have hR : radiusCommutator p.a p.a' = edgeDisplacement (act R g p.a') t := by
    rw [← hgs, PairingControl.FirstPairing.edgeDisplacement_act,
      ← initial.radius_eq_edge s hs, hmap]
  have hμcol : color R (act R g p.a') = false :=
    (action_preserves_color R g p.a').trans p.end_color
  have hdcol : color R d = false := (hd.color (by decide)).trans p.end_color
  have hdt : Adjacent R d t := hd.adjacent (geometry := geometry) ht
  have hRU : radiusCommutator p.a p.a' ≤ U R (act R g p.a') := by
    rw [hR]
    exact EdgeTransfer.edge_commutator_le_natural hb modules _ t hμcol hμt
  have hRZ : radiusCommutator p.a p.a' ≤ Z R d := by
    rw [hR]
    exact (edge_le_Z p hb control edge _ t hμcol hμt).trans
      (EdgeTransfer.edge_Z_le d t hdcol hdt)
  obtain ⟨q, hqa, hqt⟩ := counterexample_at_edge p (by omega) d t hdcol hdt
  have hZd : Z R (act R g p.a') = Z R d :=
    rigidity.equal_Z q t hqt _ d hμt hdt (fun h => hn ((le_inf hRU hRZ).trans h))
  refine ⟨g, hg, hμt, hZd, hR, ?_⟩
  simpa only [edgeDisplacement, hZd] using hR

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
