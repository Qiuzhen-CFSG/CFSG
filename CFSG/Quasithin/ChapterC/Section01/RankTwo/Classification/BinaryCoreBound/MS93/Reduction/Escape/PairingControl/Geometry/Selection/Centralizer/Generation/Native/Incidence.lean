module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.NativeSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Complement.FixedComparison.FullRadius

/-!
# Native intersections and their edge annihilators

Each neighboring radius group is fixed modulo B_c by its edge kernel:
moving Z-generators have the common edge displacement, and nonmoving
ones already lie in B_c. The proved early-input equality Vcirc_c ∩ B_c = U_c
then gives fixation on the actual moving quotient. Evaluation against its
compatible natural coordinates annihilates [U_c,Q_s] = [Z_c,Q_s].

Thus a nonzero intersection image is already an incident dual vector;
no additional annihilator assumption is needed. Existence of a nonzero
intersection remains separate from this calculation.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.2)(3) and the generation
display immediately before (4), printed p.884. The imported full-radius
intersection theorem uses only the supplied natural and opposite sections.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : MS93.Geometry R}

private noncomputable def evaluationMap {c : Vertex R} (o : OppositeSectionAt c) (v : Space) :
    U R c →* Multiplicative (ZMod 2) where
  toFun d := Multiplicative.ofAdd (pairing v (naturalEquiv o d))
  map_one' := by simp [pairing]
  map_mul' x y := by simp [pairing, dotProduct_add]

/-- Fixation modulo the exact moving kernel annihilates actual natural
commutators, retaining the common quotient marking. -/
theorem fixed_annihilates_natural_commutator {c : Vertex R} (o : OppositeSectionAt c)
    (hC : Vcirc R c ≤ stabilizer R c) (A : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R c) (x : Vcirc R c)
    (hfixed : ∀ a ∈ A, ⁅a, (x : FreeAmalgam R)⁆ ∈ U R c) :
    ∀ d : U R c, (d : FreeAmalgam R) ∈ ⁅U R c, A⁆ →
      pairing (movingCoordinates o hC x) (naturalEquiv o d) = 0 := by
  let k := evaluationMap o (movingCoordinates o hC x)
  have hcomm : ⁅U R c, A⁆ ≤ k.ker.map (U R c).subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    let a₀ : stabilizer R c := ⟨a, hA ha⟩
    let u₀ : U R c := ⟨u, hu⟩
    let u₁ : U R c := ⟨a * u * a⁻¹,
      le_normalizer_iff.mp (U_normalized c) a (hA ha) u hu⟩
    let y : Vcirc R c := ⟨a⁻¹ * (x : FreeAmalgam R) * a,
      by simpa using (le_normalizer_iff.mp (Vcirc_normalized c) a⁻¹
        ((stabilizer R c).inv_mem (hA ha)) (x : FreeAmalgam R) x.property)⟩
    have hy : y * x⁻¹ ∈ (movingCoordinates o hC).ker := by
      rw [movingCoordinates_kernel]
      change a⁻¹ * (x : FreeAmalgam R) * a * (x : FreeAmalgam R)⁻¹ ∈ U R c
      simpa only [commutatorElement_def, inv_inv] using hfixed a⁻¹ (A.inv_mem ha)
    have he : movingCoordinates o hC y = movingCoordinates o hC x := by
      apply mul_inv_eq_one.mp
      simpa only [MonoidHom.mem_ker, map_mul, map_inv] using hy
    have hact := movingCoordinates_conjugation o hC a₀⁻¹ x y (by
      simp only [coe_inv, inv_inv]; rfl)
    rw [he] at hact
    simp only [map_inv, inv_inv] at hact
    refine ⟨u₁ * u₀⁻¹, ?_, rfl⟩
    change k (u₁ * u₀⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
    change Multiplicative.ofAdd
      (dotProduct (movingCoordinates o hC x).toAdd (naturalEquiv o u₁).toAdd) =
      Multiplicative.ofAdd
        (dotProduct (movingCoordinates o hC x).toAdd (naturalEquiv o u₀).toAdd)
    congr 1
    rw [naturalEquiv_conjugation o a₀ u₀ u₁ rfl, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose, ← hact]
  intro d hd
  obtain ⟨w, hw, he⟩ := hcomm hd
  have hwd : w = d := Subtype.ext he
  rw [hwd] at hw
  exact hw

-- Elementary graph argument from Propagation/Edges, without its later inputs.
private theorem neighbor_distance_two {a t d : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hne : a ≠ d) : (cosetGraph R).dist a d = 2 := by
  have hd : color R d = false := by
    have h₁ := adjacent_color_ne R hat
    have h₂ := adjacent_color_ne R hdt
    cases ht : color R t <;> cases hd : color R d <;> simp_all
  have hlow := (cosetGraph_connected R).one_lt_dist_of_ne_of_not_adj hne (by
    intro h
    exact (adjacent_color_ne R ((cosetGraph_adj R _ _).mp h)) (ha.trans hd.symm))
  have hupp := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := d)
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat),
    SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdt))] at hupp
  omega

variable [Finite M]

/-- Every native neighboring radius group is fixed by its own edge kernel
modulo the central vertex's fixed preimage. -/
theorem neighbor_fixed_mod_B (source : LocalSource L R) (hb : 2 < geometry.b R)
    (facts : ContraryLocalFacts geometry) {c s : Vertex R}
    (hc : color R c = false) (hcs : Adjacent R c s) :
    ⁅V R s, Q R s⁆ ≤ B R c (geometry.Z_normal c) := by
  let Bc := B R c (geometry.Z_normal c)
  have hQ : Q R s ≤ stabilizer R c := fun _ hx => hx.2 c (adjacent_symm R hcs)
  have hn : Q R s ≤ normalizer (Bc : Set (FreeAmalgam R)) :=
    hQ.trans (fixedPreimage_normalized hb c hc)
  have hV : V R s ≤ stabilizer R c := (neighbor_V_le hc hcs).trans
    ((geometry.V_le_Q hb c hc).trans (fun _ hx => hx.1))
  have hgen : V R s ≤ commutatorPreimage (stabilizer R c) (Q R s) Bc := by
    apply Initial.Consequences.V_le_of_h_neighbors hc hcs
    intro d hds
    have hdV : Z R d ≤ V R s := le_iSup_of_le d (le_iSup_of_le
      (show (cosetGraph R).dist d s ≤ 2 from
        (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hds)).le.trans
          (by decide)) le_rfl)
    apply le_commutatorPreimage (hdV.trans hV)
    by_cases hdB : Z R d ≤ Bc
    · exact (commutator_mono hdB le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hn)
    by_cases hdc : d = c
    · subst d
      exact (hdB (EdgeTransfer.Z_le_B hb c hc)).elim
    have hd : d ∈ movingNeighbors geometry c :=
      ⟨neighbor_distance_two hc hcs hds (Ne.symm hdc), hdB⟩
    change edgeDisplacement d s ≤ Bc
    rw [facts.edge_eq c s d hc hcs hds hd]
    exact ((Initial.edge_le_natural source c s hc hcs).trans (U_le_Z c)).trans
      (EdgeTransfer.Z_le_B hb c hc)
  exact (commutator_mono hgen le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ (fixedPreimage_normalized hb c hc))

/-- On the moving intersection, fixation modulo B is fixation modulo U. -/
theorem native_intersection_fixed (source : LocalSource L R) (hb : 2 < geometry.b R)
    (facts : ContraryLocalFacts geometry) {c s : Vertex R}
    (hc : color R c = false) (hcs : Adjacent R c s)
    (sectionAt : NaturalSectionAt c (V R c) (Z R c)) (o : OppositeSectionAt c)
    (x : Vcirc R c) (hx : (x : FreeAmalgam R) ∈ V R s) :
    ∀ a ∈ Q R s, ⁅a, (x : FreeAmalgam R)⁆ ∈ U R c := by
  intro a ha
  rw [← Six.Complement.FixedComparison.moving_inf_fixed source hb hc sectionAt o]
  constructor
  · exact le_normalizer_iff_commutator_le_right.mp
      ((show Q R s ≤ stabilizer R c from
        fun _ hz => hz.2 c (adjacent_symm R hcs)).trans (Vcirc_normalized c))
      (commutator_mem_commutator ha x.property)
  · have h := neighbor_fixed_mod_B source hb facts hc hcs
    rw [commutator_comm] at h
    exact h (commutator_mem_commutator ha hx)

/-- The geometric obligation, with no coordinate or selected-span premise:
some actual neighboring radius group meets Vcirc beyond U. -/
@[expose] def NativeIncidence (c : Vertex R) : Prop :=
  ∃ s : Vertex R, Adjacent R c s ∧ ¬ Vcirc R c ⊓ V R s ≤ U R c

/-- Actual nonzero native intersections satisfy the required annihilator
relation automatically, under only the earlier contrary local facts. -/
theorem exists_native_lift_of_incidence (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry) {c : Vertex R} (hc : color R c = false)
    (sectionAt : NaturalSectionAt c (V R c) (Z R c))
    (o : OppositeSectionAt c) (hC : Vcirc R c ≤ stabilizer R c)
    (incidence : NativeIncidence c) :
    ∃ v : Space, v ≠ 1 ∧ Nonempty (NativeNeighborLift o hC v) := by
  obtain ⟨s, hcs, hnot⟩ := incidence
  obtain ⟨x, hx, hxu⟩ := SetLike.not_le_iff_exists.mp hnot
  let x₀ : Vcirc R c := ⟨x, hx.1⟩
  let v := movingCoordinates o hC x₀
  have hv : v ≠ 1 := by
    intro he
    have hk : x₀ ∈ (movingCoordinates o hC).ker := he
    rw [movingCoordinates_kernel] at hk
    exact hxu hk
  refine ⟨v, hv, ⟨{
    neighbor := s
    adjacent := hcs
    vector := x₀
    in_neighbor := hx.2
    coordinates := rfl
    annihilates := ?_ }⟩⟩
  intro d hd
  apply fixed_annihilates_natural_commutator o hC (Q R s)
    (fun _ hz => hz.2 c (adjacent_symm R hcs)) x₀
    (native_intersection_fixed source hb facts hc hcs sectionAt o x₀ hx.2) d
  rw [← Initial.edge_eq_natural_commutator source hb modules c s hc hcs]
  exact hd

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
