module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary.Recognition
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates

/-!
# Natural quotient coordinates on the lifted hexad radical

Restrict the literal central projection to the radical, retaining its image
in the native pointwise hexad kernel. The published native coordinates then
give a surjection onto the four-dimensional natural module with kernel Z(K).
Conjugation agrees with the native action, including its comparison marking.
These are the quotient inputs for augmentation-core recognition in I.2.2(6).

Source: Aschbacher–Smith I.2.2(6), printed p.412.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
variable {K : Type*} [Group K]
noncomputable section

/-- The actual radical projects onto the native pointwise hexad kernel. -/
def kernelProjection (e : (K ⧸ center K) ≃* M22) (B : Finset (Fin 22)) :
    hexadRadical e B →* (m22SetAction B).ker :=
  ((localProjection e (MulAction.stabilizer M22 B)).comp
    (Subgroup.inclusion (hexadRadical_le e B))).codRestrict _ (fun r => by
      change Subgroup.inclusion (hexadRadical_le e B) r ∈
        (m22SetAction B).ker.comap (localProjection e (MulAction.stabilizer M22 B))
      rw [← hexadRadical_subgroupOf]
      exact r.property)

theorem kernelProjection_surjective (e : (K ⧸ center K) ≃* M22) (B : Finset (Fin 22)) :
    Function.Surjective (kernelProjection e B) := by
  intro n
  obtain ⟨g, hg⟩ := localProjection_surjective e (MulAction.stabilizer M22 B) n.val
  have hr : g ∈ (hexadRadical e B).subgroupOf (hexadPreimage e B) := by
    rw [hexadRadical_subgroupOf]
    change localProjection e (MulAction.stabilizer M22 B) g ∈ (m22SetAction B).ker
    rw [hg]
    exact n.property
  exact ⟨⟨g.val, hr⟩, Subtype.ext hg⟩

theorem kernelProjection_ker (e : (K ⧸ center K) ≃* M22) (B : Finset (Fin 22)) :
    (kernelProjection e B).ker = (center K).subgroupOf (hexadRadical e B) := by
  ext r
  change kernelProjection e B r = 1 ↔ r.val ∈ center K
  rw [Subtype.ext_iff, Subtype.ext_iff]
  exact (show projection e r.val = 1 ↔ r.val ∈ (projection e).ker from Iff.rfl).trans
    (by rw [projection_ker])

theorem kernelProjection_conjugation (e : (K ⧸ center K) ≃* M22)
    (B : Finset (Fin 22)) (g : hexadPreimage e B) (r : hexadRadical e B) :
    kernelProjection e B (hexadConjugation e B g r) =
      MulAut.conjNormal (localProjection e (MulAction.stabilizer M22 B) g)
        (kernelProjection e B r) := by
  apply Subtype.ext
  apply Subtype.ext
  change projection e (g.val * r.val * g.val⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  rfl

/-- The natural quotient, with the original central projection retained. -/
def naturalMap (e : (K ⧸ center K) ≃* M22) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    hexadRadical e B →* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  (m22HexadNaturalCoordinates hB).toMonoidHom.comp (kernelProjection e B)

theorem naturalMap_surjective (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) : Function.Surjective (naturalMap e hB) :=
  (m22HexadNaturalCoordinates hB).surjective.comp (kernelProjection_surjective e B)

theorem naturalMap_ker (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (naturalMap e hB).ker = (center K).subgroupOf (hexadRadical e B) :=
  (MonoidHom.ker_mulEquiv_comp _ (m22HexadNaturalCoordinates hB)).trans
    (kernelProjection_ker e B)

/-- The actual native section removes precisely the displayed actor twist. -/
theorem naturalMap_conjugation (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (s : alternatingGroup (Fin 6) →* hexadPreimage e B)
    (hs : (localProjection e (MulAction.stabilizer M22 B)).comp s = m22HexadSection hB)
    (a : alternatingGroup (Fin 6)) (r : hexadRadical e B) :
    (naturalMap e hB (hexadConjugation e B (s a) r)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) a.val (naturalMap e hB r).toAdd := by
  change (m22HexadNaturalCoordinates hB
    (kernelProjection e B (hexadConjugation e B (s a) r))).toAdd = _
  have hs' : localProjection e (MulAction.stabilizer M22 B) (s a) = m22HexadSection hB a :=
    DFunLike.congr_fun hs a
  rw [kernelProjection_conjugation, hs']
  exact m22HexadNaturalCoordinates_section hB a (kernelProjection e B r)

end
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary
