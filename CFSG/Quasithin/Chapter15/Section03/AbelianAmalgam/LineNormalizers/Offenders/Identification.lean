module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Identification.BinaryPlane
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SmallModels.CubicField
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.SourceAssembly

/-!
# Identifying the marked action after the offender reduction

The original 3-prime normalizer condition, transported through the actual
section kernel, excludes the cubic fixing the marker in each SL₃ or S₅
alternative. The B.4 normalizer comparison restricts the remaining SL₂ field
to two elements. Explicit matrix/permutation coordinates then give both the
two-dimensional commutator space and the index-three marker stabilizer.

The consumer uses the same temporary Thompson actor and the exact quotient
and marker of `TemporarySource`. Its preceding marker facts and the earlier
classification remain explicit here. Returning to original I₀, and proving
those marker facts from the source V, are separate source-assembly steps.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed pp.1153–1154, and 15.3.49(5).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Identification
open BestReduction SmallModels
variable {D W : Type*} [Group D] [Finite D]
  [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {J : Subgroup D}

/-- Once the field degree has been proved to be one, the original central
quotient is the actual S₃ plane with compatible actor coordinates. -/
noncomputable def binary_plane_coordinates
    {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
    (c : CentralQuotientCoordinates ρ
      (HigherFieldBorelFixedSpaces.binaryNatural (F := F) 2))
    (hF : Nat.card F = 2) : CentralQuotientCoordinates ρ SymmetricThree.natural := by
  let := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := (ZMod.ringEquiv F
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  refine {
    actor := (c.actor.trans (Atlas.fieldEquivSL 2 e)).trans BinaryPlane.actor
    coordinates := (c.coordinates.trans (BinaryPlane.fieldCoordinates e)).trans BinaryPlane.coordinates
    intertwines := ?_ }
  intro g v
  simp only [LinearEquiv.trans_apply, MulEquiv.trans_apply]
  rw [c.intertwines, BinaryPlane.fieldCoordinates_action, BinaryPlane.coordinates_action]

omit [Finite D] in
private theorem no_cubic (P : Submodule (ZMod 2) W)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ P ⊤)))
    (hc : ∃ g : D, orderOf g = 3 ∧ ∀ v ∈ P, ρ g v = v) : False := by
  obtain ⟨g, hg, hfix⟩ := hc
  let a : subspaceKernel ρ P ⊤ := ⟨g, mem_top _, hfix⟩
  have ha : orderOf a = 3 := (Subgroup.orderOf_coe a).symm.trans hg
  have hd : 3 ∣ Nat.card (subspaceKernel ρ P ⊤) := ha ▸ orderOf_dvd_natCard a
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hP) hd

/-- The full unreduced field alternatives give S₃, dimension two and the
literal marker stabilizer. The excluded alternatives retain their actual
nonsplit central quotient and use a genuine cubic fixing its marker. -/
theorem marked_identification
    (a : UnreducedAlternative ρ J) (d : MarkedNormalizer ρ J)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ d.marker ⊤))) :
    Nonempty (D ≃* Equiv.Perm (Fin 3)) ∧
      Module.finrank (ZMod 2) (Coinvariants.ker ρ) = 2 ∧
      SymmetricThree.markerStabilizer ρ d.marker = (d.sylow : Subgroup D) ∧
      (SymmetricThree.markerStabilizer ρ d.marker).index = 3 := by
  cases a with
  | linearTwo F n hn hc c hB =>
    have hF : Nat.card F = 2 := by
      rw [hc, linearTwo_field_degree_eq_one d c hn hc hB, pow_one]
    let c' := binary_plane_coordinates c hF
    exact ⟨⟨c'.actor⟩, SymmetricThree.marked_conclusions d c'⟩
  | linearThree F n hn ho hc c hB =>
    exact (no_cubic d.marker hP (marked_cubic_of_model d c
      (SL3BinaryCubic.klein (F := F)) SL3BinaryCubic.klein_two
      SL3BinaryCubic.cycle SL3BinaryCubic.cycle_pow SL3BinaryCubic.cycle_ne_one
      SL3BinaryCubic.cycle_fixes_natural)).elim
  | doubleLinearThree F n hn ho hc c hB =>
    exact (no_cubic d.marker hP (marked_cubic_of_model d c
      (SL3BinaryCubic.klein (F := F)) SL3BinaryCubic.klein_two
      SL3BinaryCubic.cycle SL3BinaryCubic.cycle_pow SL3BinaryCubic.cycle_ne_one
      SL3BinaryCubic.cycle_fixes_double)).elim
  | symmetricFive c =>
    exact (no_cubic d.marker hP (symmetricFive_marked_cubic d c)).elim

open BestReduction.SourceAssembly BestReduction.FullCoreTransfer Replacement.Transvections
  ChapterB.SourceInduction
open scoped IsMulCommutative
universe u
variable {G L X : Type u} [Group G] [Finite G] [Group L]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  {K : GroupClass.{u}} {Y T V E : Subgroup G} [IsMulCommutative V]
  [(Replacement.Transvections.localSpan T V E).Normal]
  [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)]
  {σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) X}

/-- The source 15.3.49(5) input excludes the two cubic alternatives in the
actual faithful image. The original temporary I is separately best-generated;
it is never identified with its faithful image. -/
theorem temporary_identification
    (d : TemporarySource K Y T V E L σ)
    (classify : AdequateClassificationInput.{u,u} K)
    (a : UnreducedAlternative (imageRepresentation (σ.comp (thompsonImage T V E).subtype))
      (TemporarySource.imageThompson (σ := σ) (T := T) (V := V) (E := E))) :
    offenderSubgroup (σ.comp (thompsonImage T V E).subtype) = ⊤ ∧
    Nonempty (actionImage (σ.comp (thompsonImage T V E).subtype) ≃* Equiv.Perm (Fin 3)) ∧
    Module.finrank (ZMod 2)
      (Coinvariants.ker (imageRepresentation (σ.comp (thompsonImage T V E).subtype))) = 2 ∧
    SymmetricThree.markerStabilizer
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) d.marker =
        (d.imageMarked.sylow : Subgroup _) ∧
    (SymmetricThree.markerStabilizer
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) d.marker).index = 3 := by
  have hEU : localLine T V E ≤ Replacement.Transvections.localSpan T V E :=
    comap_mono (d.temporary.line_le.trans (le_conjugateSpanBy V (lineNormalizer E)))
  let : IsElementaryAbelian 2 (localLine T V E) := IsElementaryAbelian.of_le hEU
  have hP := temporary_markerCentralizer_coprime_three Y T V E d.Z d.temporary
    d.Z_le d.Z_normalizer σ d.marker d.marker_centralizer
  exact ⟨d.generated classify,
    marked_identification a d.imageMarked
      (image_markerCentralizer_coprime_three _ d.marker hP)⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Identification
