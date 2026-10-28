module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators.Algebra
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators.Statements
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Generation

/-!
# Same-path sharpening and the second hat commutator

The forward and reversed local windows use the actual indexed vertices,
critical endpoints, and reflected products supplied by firstFactsOnPath.
Their turns extend the first-hat bounds to both directions at centers four
through ten. Conjugate generation then proves the three forward and three
backward second-hat bounds needed by the higher consumers.

The final SourceOrbitFacts application constructs both requested bounds,
normality, generation and the ordered first-hat product. Its first identity
and preliminary displacement record are explicit: the latter still needs
its source producer, and this module does not assert unconditional (4.5.3).

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.3)(ii--iii), printed p.898.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
open PathCentrality NormalizerTransfer
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem path_Z_le_Q (earlier : Earlier R geometry) {a : Vertex R}
    (p : SourcePath R a) {i j : ℕ} (hi : Even i)
    (hi14 : i ≤ 14) (hj14 : j ≤ 14) (hij : (i - j) + (j - i) < 8) :
    Z R (p.walk.getVert i) ≤ Q R (p.walk.getVert j) := by
  apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ (p.even_color hi hi14))
  rw [geometry.distance_constant _ (p.even_color hi hi14)]
  change _ < geometry.b R
  rw [earlier.distance]
  rcases le_total i j with h | h
  · rw [p.distance (geometry := geometry) h hj14]
    omega
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) h hi14]
    omega

/-- The forward sharpening window needs the reflected first product at i+4
and the critical endpoint i+8, hence precisely these guards. -/
theorem forward_sharp (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) (identity : HatIdentitiesOnPath R p)
    (preliminary : PreliminaryOnPath p) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6) :
    ⁅hatV R (p.walk.getVert i) (p.walk.getVert (i + 2)),
      Q R (p.walk.getVert (i + 2))⁆ ≤ Z R (p.walk.getVert (i + 2)) := by
  have hc := hi.add (by decide : Even 2)
  have hd := hi.add (by decide : Even 4)
  have hf := hi.add (by decide : Even 8)
  have hproduct := (firstFactsOnPath source common earlier p).backward (i + 4) hd (by omega) (by omega)
  have hprod : (hatW R (p.walk.getVert (i + 4)) (p.walk.getVert (i + 2)) (p.walk.getVert i) :
      Set (FreeAmalgam R)) * (Q R (p.walk.getVert i) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert (i + 1)) : Set (FreeAmalgam R)) := by
    simpa only [show i + 4 - 2 = i + 2 by omega, Nat.add_sub_cancel,
      show i + 4 - 3 = i + 1 by omega] using hproduct.hatW_product
  apply sharpen common earlier (p.even_color hi (by omega)) (p.even_color hc (by omega))
    (p.even_color hd (by omega)) (p.even_color hf (by omega))
    (f := p.walk.getVert (i + 8)) (t := p.walk.getVert (i + 1))
  · exact p.adjacent (by omega)
  · exact adjacent_symm R (by simpa only [Nat.add_assoc] using p.adjacent (i := i + 1) (by omega))
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · exact path_Z_le_Q earlier p hf (by omega) (by omega) (by omega)
  · exact (common.critical_reverse _ (p.even_color hi (by omega)) _
      (p.even_color hf (by omega)) (p.critical_pair earlier hi hi6)).2
  · exact identity.forward i hi (by omega) (by omega)
  · exact hprod
  · exact preliminary.forward i hi (by omega) (by omega)
  · have hp := preliminary.forward (i + 2) hc (by omega) (by omega)
    rw [← backward_hatV_eq_forward p hc (by omega) (by omega)] at hp
    simpa only [Nat.add_assoc, Nat.add_sub_cancel] using hp

/-- The reversed window retains the original indices and its endpoint i-8. -/
theorem backward_sharp (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) (identity : HatIdentitiesOnPath R p)
    (preliminary : PreliminaryOnPath p) {i : ℕ}
    (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10) :
    ⁅hatV R (p.walk.getVert i) (p.walk.getVert (i - 2)),
      Q R (p.walk.getVert (i - 2))⁆ ≤ Z R (p.walk.getVert (i - 2)) := by
  have hc : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  have hd : Even (i - 4) := by rw [Nat.even_iff] at hi ⊢; omega
  have hf : Even (i - 8) := by rw [Nat.even_iff] at hi ⊢; omega
  have hproduct := (firstFactsOnPath source common earlier p).forward (i - 4) hd (by omega) (by omega)
  have hprod : (hatW R (p.walk.getVert (i - 4)) (p.walk.getVert (i - 2)) (p.walk.getVert i) :
      Set (FreeAmalgam R)) * (Q R (p.walk.getVert i) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert (i - 1)) : Set (FreeAmalgam R)) := by
    simpa only [show i - 4 + 2 = i - 2 by omega, Nat.sub_add_cancel (by omega : 4 ≤ i),
      show i - 4 + 3 = i - 1 by omega] using hproduct.hatW_product
  apply sharpen common earlier (p.even_color hi (by omega)) (p.even_color hc (by omega))
    (p.even_color hd (by omega)) (p.even_color hf (by omega))
    (f := p.walk.getVert (i - 8)) (t := p.walk.getVert (i - 1))
  · exact adjacent_symm R (by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using
        (p.adjacent (i := i - 1) (by omega)))
  · simpa only [show i - 2 + 1 = i - 1 by omega] using p.adjacent (i := i - 2) (by omega)
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · exact path_Z_le_Q earlier p hf (by omega) (by omega) (by omega)
  · simpa only [Nat.sub_add_cancel hi8] using (p.critical (i - 8) hf (by omega)).2
  · exact identity.backward hi (by omega) (by omega)
  · exact hprod
  · exact preliminary.backward hi (by omega) (by omega)
  · have hp := preliminary.backward (i := i - 2) hc (by omega) (by omega)
    rw [backward_hatV_eq_forward p hc (by omega) (by omega)] at hp
    simpa only [Nat.sub_sub, Nat.sub_add_cancel (by omega : 2 ≤ i)] using hp


omit [Finite M] in
private theorem transport_bound {v b c : Vertex R} {A : Subgroup (FreeAmalgam R)}
    (hn : stabilizer R v ≤ normalizer (A : Set (FreeAmalgam R)))
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R v) (hgb : act R g b = c)
    (h : ⁅A, Q R b⁆ ≤ Z R b) : ⁅A, Q R c⁆ ≤ Z R c := by
  have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h
  have hmap : A.map (MulAut.conj g⁻¹).toMonoidHom = A :=
    mem_normalizer_iff_map_conj_eq.mp (hn ((stabilizer R v).inv_mem hg))
  rwa [map_commutator, hmap, ← Q_act, ← Z_act, hgb] at hm

/-- Both first-layer bounds at every center with the necessary critical
and product windows. Reflection only conjugates the supplied turn. -/
theorem first_bounds (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) (identity : HatIdentitiesOnPath R p)
    (preliminary : PreliminaryOnPath p) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi10 : i ≤ 10) :
    (⁅hatV R (p.walk.getVert i) (p.walk.getVert (i + 2)),
      Q R (p.walk.getVert (i + 2))⁆ ≤ Z R (p.walk.getVert (i + 2))) ∧
    (⁅hatV R (p.walk.getVert i) (p.walk.getVert (i - 2)),
      Q R (p.walk.getVert (i - 2))⁆ ≤ Z R (p.walk.getVert (i - 2))) := by
  obtain ⟨g, hg, ht⟩ := p.turns i hi (by omega) (by omega)
  have heq := backward_hatV_eq_forward p hi (by omega) (by omega)
  by_cases hsmall : i ≤ 6
  · have h := forward_sharp common earlier p identity preliminary hi hi4 hsmall
    refine ⟨h, ?_⟩
    rw [heq]
    exact transport_bound (hatV_normalized R _ _) hg ht h
  · have hi8 : 8 ≤ i := by rw [Nat.even_iff] at hi; omega
    have h := backward_sharp common earlier p identity preliminary hi hi8 hi10
    refine ⟨?_, h⟩
    rw [← heq]
    apply transport_bound (hatV_normalized R _ _) ((stabilizer R _).inv_mem hg) _ h
    rw [← ht, ← act_mul, mul_inv_cancel, act_one]

omit [Finite M] in
/-- The final symmetry on p.898 is a conjugate-span calculation with Q_a
normal in G_a and Z_a invariant. -/
theorem second_bound_of_first (earlier : Earlier R geometry)
    {a c d : Vertex R} (hc : color R c = false)
    (hca : (cosetGraph R).dist c a = 2) (hdc : (cosetGraph R).dist d c = 2)
    (hfirst : ⁅hatV R c d, Q R a⁆ ≤ Z R a) :
    ⁅hatW R a c d, Q R a⁆ ≤ Z R a := by
  have hseed : hatV R c d ≤ Q R a := (hatV_le_radius R hdc.le).trans
    (V_le_Q_of_dist_add_two_lt R hc (by rw [hca, earlier.distance]; decide))
  rw [hatW, Escape.PairingControl.commutator_conjugatesIn _ _ _ hseed (Q_normalized R a)]
  apply iSup_le
  intro g
  exact (map_mono hfirst).trans
    (mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized R a ((stabilizer R a).inv_mem g.property))).le

/-- All three forward second-layer estimates used at indices four, six,
and eight. The midpoint turn identifies the exact opposite seed. -/
theorem forward_second_bound (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) (identity : HatIdentitiesOnPath R p)
    (preliminary : PreliminaryOnPath p) {i : ℕ}
    (hi : Even i) (hi4 : 4 ≤ i) (hi8 : i ≤ 8) :
    ⁅hatW R (p.walk.getVert i) (p.walk.getVert (i + 2)) (p.walk.getVert (i + 4)),
      Q R (p.walk.getVert i)⁆ ≤ Z R (p.walk.getVert i) := by
  have hc := hi.add (by decide : Even 2)
  apply second_bound_of_first earlier (p.even_color hc (by omega))
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · rw [SimpleGraph.dist_comm, p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · have h := (first_bounds common earlier p identity preliminary hc (by omega) (by omega)).2
    rw [backward_hatV_eq_forward p hc (by omega) (by omega)] at h
    simpa only [Nat.add_assoc, Nat.add_sub_cancel] using h

/-- The reflected second-layer estimates at six, eight and ten use the
same walk, with all subtraction guards explicit. -/
theorem backward_second_bound (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) (identity : HatIdentitiesOnPath R p)
    (preliminary : PreliminaryOnPath p) {i : ℕ}
    (hi : Even i) (hi6 : 6 ≤ i) (hi10 : i ≤ 10) :
    ⁅hatW R (p.walk.getVert i) (p.walk.getVert (i - 2)) (p.walk.getVert (i - 4)),
      Q R (p.walk.getVert i)⁆ ≤ Z R (p.walk.getVert i) := by
  have hc : Even (i - 2) := by rw [Nat.even_iff] at hi ⊢; omega
  apply second_bound_of_first earlier (p.even_color hc (by omega))
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · rw [p.distance (geometry := geometry) (by omega) (by omega)]; omega
  · have h := (first_bounds common earlier p identity preliminary hc (by omega) (by omega)).1
    rw [← backward_hatV_eq_forward p hc (by omega) (by omega)] at h
    simpa only [Nat.sub_sub, Nat.sub_add_cancel (by omega : 2 ≤ i)] using h

/-- A genuine application of the new sharpening and second-layer arguments.
The identity and preliminary displacement records remain explicit source
obligations until their producers are discharged by the assembly owner. -/
theorem sourceOrbitFacts_of_identity_and_preliminary (source : LocalSource L R)
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {a : Vertex R} (p : SourcePath R a) (identity : HatIdentitiesOnPath R p)
    (preliminary : PreliminaryOnPath p) : SourceOrbitFacts R p where
  Z_le_pair := (center_normality common earlier p).1
  Z_normal_pair := (center_normality common earlier p).2
  local_generation := local_generation source common earlier p
  reflected_Z_le_pair := (reflected_normality common earlier p).1
  reflected_Z_normal_pair := (reflected_normality common earlier p).2
  hatV_eq := identity.center
  hatV_product := hatV_product_of_eq common
    (by simpa only [p.center_eq] using p.even_color (i := 4) (by decide) (by decide)) identity.center
  hatV_commutator := by
    simpa only [p.center_eq] using (first_bounds common earlier p identity preliminary
      (i := 4) (by decide) (by decide) (by decide)).1
  hatW_commutator := by
    simpa only [p.center_eq] using forward_second_bound common earlier p identity preliminary
      (i := 4) (by decide) (by decide) (by decide)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatCommutators
