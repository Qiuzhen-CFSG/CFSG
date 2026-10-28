module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.Reduction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.OrderObstruction
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.DiagonalSelection.Transport

/-!
# Ambient rigidity of a realized full diagonal

Pairs in the two SL₂(4) factors that are realized on a long frame form a
subgroup. The existing order-seventeen word excludes the mixed upper/lower
shear, so this subgroup is proper. A full diagonal in a product of two simple
groups is maximal: its overgroup has either trivial or full second kernel.
Consequently any realized full diagonal contains the frame's graph reflection.

The consumer in `InverterCoset` applies this to the literal J₂ dihedral
centralizer. This uses the actual Leech quotient order, and does not infer
uniqueness from a common S₃. Source context: Aschbacher, *Sporadic Groups*
(1994), Lemma 49.5, pp.283–284. The order certificate is reused from
`LocalA5.DiagonalSelection.Transport`.
-/

open Matrix Atlas.Conway
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.InverterCoset
open OctonionLocals
open PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight

private theorem realizes_mul {L : LongFrame} {g h : LeechCentralQuotient}
    {a b : LinearGroup}
    (ha : ∀ v, quotientModTwoRepresentation g (L.coordinates v) = L.coordinates (a v))
    (hb : ∀ v, quotientModTwoRepresentation h (L.coordinates v) = L.coordinates (b v)) :
    ∀ v, quotientModTwoRepresentation (g*h) (L.coordinates v) = L.coordinates ((a*b) v) := by
  intro v
  simp only [map_mul, LinearEquiv.mul_apply]
  rw [hb, ha]

/-- Matrix pairs realized by actual elements on the specified coordinates. -/
def realizedPairs (L : LongFrame) : Subgroup (SL(2,F) × SL(2,F)) where
  carrier := {p | ∃ g : LeechCentralQuotient, ∀ v,
    quotientModTwoRepresentation g (L.coordinates v) = L.coordinates (pairRepresentation p v)}
  one_mem' := ⟨1, by intro v; simp⟩
  mul_mem' := by
    rintro p q ⟨g, hg⟩ ⟨h, hh⟩
    exact ⟨g*h, by simpa only [map_mul] using realizes_mul hg hh⟩
  inv_mem' := by
    rintro p ⟨g, hg⟩
    refine ⟨g⁻¹, fun v => ?_⟩
    apply (quotientModTwoRepresentation g).injective
    rw [hg]
    simp

theorem flip_mem_realizedPairs (L : LongFrame) : (flip,flip) ∈ realizedPairs L := by
  refine ⟨L.swap, fun v => ?_⟩
  rw [graph_action]
  exact equivariant_of_single _ _ _ L.on_swap v

/-- The existing order-seventeen certificate excludes the mixed shear. -/
theorem mixedShear_not_mem (L : LongFrame) :
    (shear, DiagonalSelection.lowerShear) ∉ realizedPairs L := by
  rintro ⟨k, hk⟩
  let e := DiagonalSelection.fieldEquiv.toRingHom
  let block (A : SL(3,DiagonalSelection.K)) := L.long (Matrix.SpecialLinearGroup.map e A)
  let step (A : SL(3,DiagonalSelection.K)) := k * L.swap * block A
  let g := step DiagonalSelection.Certificate.A0 * step DiagonalSelection.Certificate.A1 *
    step DiagonalSelection.Certificate.A2 * step DiagonalSelection.Certificate.A3
  have hg : ∀ v, quotientModTwoRepresentation L.swap (L.coordinates v) =
      L.coordinates (action graph v) := equivariant_of_single _ _ _ L.on_swap
  have hl (A : SL(3,DiagonalSelection.K)) : ∀ v,
      quotientModTwoRepresentation (block A) (L.coordinates v) =
      L.coordinates (action (BlockRealization.blockHom (Matrix.SpecialLinearGroup.map e A)) v) :=
    L.intertwines_long _
  have hs (A : SL(3,DiagonalSelection.K)) := realizes_mul (realizes_mul hk hg) (hl A)
  have hw : ∀ v, quotientModTwoRepresentation g (L.coordinates v) =
      L.coordinates (DiagonalSelection.coordinateWord e v) :=
    realizes_mul (realizes_mul (realizes_mul (hs DiagonalSelection.Certificate.A0)
      (hs DiagonalSelection.Certificate.A1)) (hs DiagonalSelection.Certificate.A2))
      (hs DiagonalSelection.Certificate.A3)
  have hsq : ∀ v, quotientModTwoRepresentation (g^2) (L.coordinates v) =
      L.coordinates ((DiagonalSelection.coordinateWord e ^ 2) v) := by
    simpa only [pow_two] using realizes_mul hw hw
  exact no_order_seventeen L (g^2) (DiagonalSelection.coordinateWord e ^ 2) hsq
    (DiagonalSelection.coordinateWord_order e)

private theorem eq_graph_of_proper {S : Type*} [Group S] [IsSimpleGroup S]
    (H : Subgroup (S × S)) (φ : S ≃* S)
    (hφ : ∀ a, (a, φ a) ∈ H) (hproper : H ≠ ⊤)
    {a b : S} (hab : (a,b) ∈ H) : φ a = b := by
  let N : Subgroup S := H.comap (MonoidHom.inr S S)
  have hmem (s : S) : s ∈ N ↔ (1,s) ∈ H := Iff.rfl
  let : N.Normal := ⟨by
    intro n hn s
    have hs : (φ.symm s,s) ∈ H := by simpa using hφ (φ.symm s)
    have hh := H.mul_mem (H.mul_mem hs hn) (H.inv_mem hs)
    exact (hmem _).mpr (by simpa using hh)⟩
  rcases (inferInstance : N.Normal).eq_bot_or_eq_top with hn | hn
  · have hm : (φ a)⁻¹ * b ∈ N := by
      apply (hmem _).mpr
      simpa using H.mul_mem (H.inv_mem (hφ a)) hab
    rw [hn, Subgroup.mem_bot] at hm
    exact inv_mul_eq_one.mp hm
  · exfalso
    apply hproper
    apply top_unique
    rintro ⟨x,y⟩ _
    have hm : (1,(φ x)⁻¹*y) ∈ H := (hmem _).mp (hn ▸ Subgroup.mem_top _)
    simpa [mul_assoc] using H.mul_mem (hφ x) hm

/-- An actual full diagonal must contain the frame's graph reflection.
Otherwise it and that reflection generate both factors, contradicting the
ambient order certificate. -/
theorem twist_flip_of_realized (L : LongFrame) (φ : SL(2,F) ≃* SL(2,F))
    (hφ : ∀ a, (a, φ a) ∈ realizedPairs L) : φ flip = flip := by
  let : IsSimpleGroup (SL(2,F)) := alternatingEquiv.isSimpleGroup
  apply eq_graph_of_proper (realizedPairs L) φ hφ
  · intro h
    exact mixedShear_not_mem L (h ▸ Subgroup.mem_top _)
  · exact flip_mem_realizedPairs L

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.InverterCoset
