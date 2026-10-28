module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.TensorPointResidual
public import Theory.Representation.OrthogonalFourPlusMatrix.NonsingularPointGeneration

/-!
The fixed subgroup of the actual diagonal point residual is precisely the
field-four line through its nonsingular vector. Surjectivity of the residual
onto the matrix stabilizer transfers the scalar-commutant calculation to the
original full module. In particular every containing component has at most
four fixed vectors in that module, the centralizer bound used at the start
of the quasisimple exclusion in source 9.4.1.

Source: Aschbacher--Smith 9.1.2(4) and 9.4.1, printed pp.729 and 735.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The fixed vectors of the literal point residual form its field line. -/
theorem tensorPointResidual_fixed_iff (v w : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    (w : G) ∈ centralizer (m.tensorPointResidual v : Set G) ↔
      (m.sectionData.coordinates w).toAdd ∈
        Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V) := by
  constructor
  · intro hc
    apply mem_span_of_pointStabilizer_le _ _ hv
    intro g hg
    obtain ⟨a,ha⟩ := m.tensorPointResidualQuotient_surjective v hv ⟨g,hg⟩
    have hq : m.quotient ⟨a,m.tensorPointResidual_le_orbit v a.property⟩ = g :=
      congrArg Subtype.val ha
    rw [←hq]
    apply (m.tensorPointCentralizer_coordinates w _).mp
    exact ⟨m.tensorPointResidual_le_orbit v a.property,
      mem_centralizer_singleton_iff.mpr (hc a a.property)⟩
  · intro hw a ha
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hw
    let b : localOrbit T L := ⟨a,m.tensorPointResidual_le_orbit v ha⟩
    have hfix := (m.tensorPointCentralizer_coordinates v b).mp (m.tensorPointResidual_le v ha)
    have hwfix : m.quotient b ∈ pointStabilizer (m.sectionData.coordinates w).toAdd := by
      rw [mem_pointStabilizer,←hc,LinearEquiv.map_smul]
      exact congrArg (c • ·) hfix
    exact mem_centralizer_singleton_iff.mp
      (((m.tensorPointCentralizer_coordinates w b).mpr hwfix).2)

/-- The fixed field line in the original module has exactly four elements. -/
theorem tensorPointResidual_fixed_card (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0) :
    Nat.card (D.fullModule ⊓ centralizer (m.tensorPointResidual v : Set G) : Subgroup G) = 4 := by
  let C := D.fullModule ⊓ centralizer (m.tensorPointResidual v : Set G)
  let W := Submodule.span Binary.F ({(m.sectionData.coordinates v).toAdd} : Set Binary.V)
  let f : C → W := fun w => ⟨(m.sectionData.coordinates ⟨w,w.property.1⟩).toAdd,
    (m.tensorPointResidual_fixed_iff v ⟨w,w.property.1⟩ hv).mp w.property.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      have h := m.coordinates_injective (Multiplicative.toAdd.injective (congrArg Subtype.val hab))
      exact congrArg (fun x : D.fullModule => (x : G)) h
    · intro w
      obtain ⟨a,ha⟩ := m.sectionData.onto (Multiplicative.ofAdd w.val)
      have hc : (a : G) ∈ centralizer (m.tensorPointResidual v : Set G) := by
        apply (m.tensorPointResidual_fixed_iff v a hv).mpr
        change (m.sectionData.coordinates a).toAdd ∈ W
        rw [ha]
        exact w.property
      exact ⟨⟨a,a.property,hc⟩,Subtype.ext (congrArg Multiplicative.toAdd ha)⟩
  have hn : (m.sectionData.coordinates v).toAdd ≠ 0 := by
    intro hz
    exact hv (hz ▸ Matrix.det_zero)
  calc
    Nat.card C = Nat.card W := Nat.card_congr (Equiv.ofBijective f hf)
    _ = 4 := by
      rw [Module.natCard_eq_pow_finrank (K := Binary.F),finrank_span_singleton hn,
        pow_one,Nat.card_eq_fintype_card]
      exact Representation.SL2FourNatural.card_field

/-- The actual normal overcomponent in 9.4.1 has at most four fixed vectors. -/
theorem tensorPoint_containing_fixed_card_le (v : D.fullModule)
    (hv : ((m.sectionData.coordinates v).toAdd).det ≠ 0)
    {I : Subgroup G} (hLI : m.tensorPointResidual v ≤ I) :
    Nat.card (D.fullModule ⊓ centralizer (I : Set G) : Subgroup G) ≤ 4 := by
  rw [←m.tensorPointResidual_fixed_card v hv]
  exact card_le_of_le (inf_le_inf le_rfl (centralizer_le hLI))

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
