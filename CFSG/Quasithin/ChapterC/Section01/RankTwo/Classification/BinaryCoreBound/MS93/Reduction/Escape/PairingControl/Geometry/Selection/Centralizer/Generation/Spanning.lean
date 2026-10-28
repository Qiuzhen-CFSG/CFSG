module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.NativeSource

/-!
# Generation from native dual-line lifts

Choose a nonidentity vector u of U_c fixed by Q_t. Every dual vector v
with v(u)=1 has a native neighboring lift whose displacement plane omits u.
That plane and u generate U_c, so its relative centralizer in Q_t is Q_c.
The affine hyperplane v(u)=1 spans the full binary dual space: adding any
one of its vectors expresses every vector in its kernel as a sum of two
such vectors. Thus the selected span surjects onto Vcirc_c/U_c.

The earlier kernel and radius-decomposition lemmas lift this surjectivity
to the required V_c containment. Native neighbor realization remains an
explicit premise, to be supplied by the source-geometric proof.

Source: Meierfrankenfeld--Stellmacher (1993), the local generation display
before (4.3.2)(4), printed p.884.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation

private theorem pairing_mul (v w u : Space) : pairing (v * w) u = pairing v u + pairing w u :=
  add_dotProduct _ _ _

/-- The affine hyperplane defined by evaluation one spans the binary
three-space. This uses group addition, with no finite matrix certificate. -/
theorem eq_top_of_pairing_one (u : Space) (hu : u ≠ 1) (K : Subgroup Space)
    (hK : ∀ v, pairing v u = 1 → v ∈ K) : K = ⊤ := by
  classical
  have hi : ∃ i, u.toAdd i ≠ 0 := by
    by_contra! h
    apply hu
    apply Multiplicative.toAdd.injective
    exact funext h
  obtain ⟨i, hi⟩ := hi
  have hi1 : u.toAdd i = 1 := by
    have h := (u.toAdd i).val_lt
    have hv : (u.toAdd i).val = 1 := by
      have hn : (u.toAdd i).val ≠ 0 := by simpa using hi
      omega
    exact Fin.ext hv
  let w : Space := Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))
  have hw : pairing w u = 1 := by
    change dotProduct (Pi.single i (1 : ZMod 2)) u.toAdd = 1
    simpa only [single_dotProduct, one_mul] using hi1
  apply top_unique
  intro v _
  by_cases hv : pairing v u = 1
  · exact hK v hv
  · have hz : pairing v u = 0 := by
      have h := (pairing v u).val_lt
      have hn : (pairing v u).val ≠ 1 := fun h => hv (Fin.ext h)
      apply Fin.ext
      change (pairing v u).val = 0
      omega
    have hm : pairing (w * v) u = 1 := by rw [pairing_mul, hw, hz, add_zero]
    simpa only [inv_mul_cancel_left] using K.mul_mem (K.inv_mem (hK w hw)) (hK _ hm)

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- Native lifts give the exact surjectivity needed in the dual moving
quotient. The selected neighbors and their centralizer equalities are derived. -/
theorem selectedMovingImage_eq_top_of_native_lifts (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry) {c t : Vertex R}
    (hc : color R c = false) (hct : Adjacent R c t)
    (o : OppositeSectionAt c) (hC : Vcirc R c ≤ stabilizer R c)
    (lifts : NativeNeighborLifts o hC) : selectedMovingImage o hC t = ⊤ := by
  obtain ⟨u, hu, hfix, hne⟩ := exists_fixed_natural_element source hb modules hc hct
  let u₀ : U R c := ⟨u, hu⟩
  have hu₀ : naturalEquiv o u₀ ≠ 1 := by
    intro h
    have hh : u₀ = 1 := (naturalEquiv o).injective (h.trans (map_one _).symm)
    exact hne (congrArg Subtype.val hh)
  apply eq_top_of_pairing_one (naturalEquiv o u₀) hu₀
  intro v hv
  have hvne : v ≠ 1 := by
    intro h
    subst v
    change dotProduct (0 : Fin 3 → ZMod 2) (naturalEquiv o u₀).toAdd = 1 at hv
    rw [zero_dotProduct] at hv
    exact zero_ne_one hv
  obtain ⟨lift⟩ := lifts v hvne
  have hout : u ∉ edgeDisplacement c lift.neighbor := by
    intro h
    have hz := lift.annihilates u₀ h
    rw [hv] at hz
    exact one_ne_zero hz
  have heq := centralizer_eq_of_fixed_outside source modules initial p (by omega)
    hc hct lift.adjacent hu hfix hout
  have hmem : lift.vector ∈
      (centralizingNeighborSpan c t).subgroupOf (Vcirc R c) :=
    neighbor_le_span lift.adjacent heq lift.in_neighbor
  rw [← lift.coordinates]
  exact mem_map_of_mem (movingCoordinates o hC) hmem

/-- All remaining linear and centralizer steps of the source generation
identity, conditional only on native dual-vector realization. -/
theorem le_span_of_native_lifts (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t)
    (o : OppositeSectionAt c) (hC : Vcirc R c ≤ stabilizer R c)
    (lifts : NativeNeighborLifts o hC) : V R c ≤ centralizingNeighborSpan c t :=
  (le_span_iff_moving_image source hb modules initial facts p hc hct o hC).mpr
    (selectedMovingImage_eq_top_of_native_lifts source hb modules initial p hc hct o hC lifts)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
