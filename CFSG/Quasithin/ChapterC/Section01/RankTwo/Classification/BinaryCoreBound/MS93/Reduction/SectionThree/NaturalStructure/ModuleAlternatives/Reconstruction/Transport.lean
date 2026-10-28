module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Reconstruction.Linear
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.MovingLayer
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# Moving-layer reconstruction from edge fixed-space generation

If the actual Z equals the sum of the fixed and commutator spaces of X,
perfectness proves that U=[Z,Ltilde] is the commutator module of X. The proof
then constructs genuine multiplicative coordinates and surjections on U,
retaining the common quotient marking and the exact fixed kernel. All
statements keep the still-needed edge-generation identity explicit.
Source: Meierfrankenfeld–Stellmacher (1993), (3.2), printed p.863.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Reconstruction
open CentralAttachments
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
local instance : IsElementaryAbelian 2 (X R (alpha R)) := X_elementary R (alpha R)

/-- The literal commutator of X corresponds to the abstract moving module. -/
theorem moving_space (source : LocalSource L R) :
    space ⁅X R (alpha R), Ltilde R (alpha R)⁆ =
      (moving (Offenders.linearize (xAction source))).toSubmodule := by
  rw [space_commutator source _ le_rfl (X_normalized R (alpha R))]
  have ht : space (X R (alpha R)) = ⊤ := by
    change lattice ((X R (alpha R)).subgroupOf _) = ⊤
    rw [subgroupOf_self, lattice.map_top]
  rw [ht, ← moving_eq]

private theorem centralSum_commutator {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL V) :
    subspaceCommutator ρ (centralSum ρ) ⊤ = (moving ρ).toSubmodule := by
  have he := subspaceCommutator_map_embedding ρ (moving ρ).toRepresentation
    (MonoidHom.id SL) (moving ρ).toSubmodule.subtype (fun _ _ => rfl) ⊤ ⊤
  simp only [Subgroup.map_id, Submodule.map_top, Submodule.range_subtype,
    moving_full] at he
  apply le_antisymm
  · exact (subspaceCommutator_mono_left ρ le_top ⊤).trans_eq (moving_eq ρ).symm
  · rw [← he]
    exact subspaceCommutator_mono_left ρ le_sup_right ⊤

/-- Once edge fixed-space generation is known, the actual U is the full
commutator module of X. This implication does not identify them by definition. -/
theorem space_U_of_space_Z (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source))) :
    space (U R (alpha R)) = (moving (Offenders.linearize (xAction source))).toSubmodule := by
  change space ⁅Z R (alpha R), Ltilde R (alpha R)⁆ = _
  rw [space_commutator source _ (geometry.omega_bound (alpha R) rfl hb)
    (Z_normalized R (alpha R)), hZ, centralSum_commutator]

theorem X_commutator_eq_U_of_space_Z (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source))) :
    ⁅X R (alpha R), Ltilde R (alpha R)⁆ = U R (alpha R) := by
  apply space_injective (commutator_le_X _ le_rfl)
    ((U_le_Z _).trans (geometry.omega_bound (alpha R) rfl hb))
  rw [moving_space source, space_U_of_space_Z source geometry hb hZ]

theorem Z_eq_fixed_sup_U_of_space_Z (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source))) :
    Z R (alpha R) = fixedPart R ⊔ U R (alpha R) := by
  have hUX := (U_le_Z (alpha R)).trans (geometry.omega_bound (alpha R) rfl hb)
  apply space_injective (geometry.omega_bound (alpha R) rfl hb) (sup_le inf_le_left hUX)
  rw [space_sup inf_le_left hUX]
  change space (Z R (alpha R)) = space (fixedPart R) ⊔ space (U R (alpha R))
  rw [space_fixed source, space_U_of_space_Z source geometry hb hZ]
  exact hZ

/-- Actual multiplicative coordinates identify U with the linear moving space. -/
noncomputable def movingEquiv (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source))) :
    U R (alpha R) ≃* Multiplicative (moving (Offenders.linearize (xAction source))).toSubmodule where
  toFun u := Multiplicative.ofAdd ⟨Additive.ofMul
    ⟨u.val, (U_le_Z (alpha R)).trans (geometry.omega_bound (alpha R) rfl hb) u.property⟩,
    by rw [← space_U_of_space_Z source geometry hb hZ]; exact u.property⟩
  invFun v := ⟨v.toAdd.val.toMul,
    (space_U_of_space_Z source geometry hb hZ).ge v.toAdd.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem movingEquiv_action (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source)))
    (g : M) (u v : U R (alpha R))
    (hv : (v : FreeAmalgam R) = embedM R g * (u : FreeAmalgam R) * (embedM R g)⁻¹) :
    (movingEquiv source geometry hb hZ v).toAdd =
      (moving (Offenders.linearize (xAction source))).toRepresentation (source.projection g)
        (movingEquiv source geometry hb hZ u).toAdd := by
  apply Subtype.ext
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hv.trans (layerAction_apply source (X R (alpha R)) (X_normalized R (alpha R))
    (Q_le_centralizer_X R (alpha R)) g
    ⟨u.val, (U_le_Z (alpha R)).trans (geometry.omega_bound (alpha R) rfl hb) u.property⟩).symm

theorem movingEquiv_fixed (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source)))
    (u : U R (alpha R)) :
    (movingEquiv source geometry hb hZ u).toAdd ∈
      fixedSpace (moving (Offenders.linearize (xAction source))).toRepresentation ⊤ ↔
      (u : FreeAmalgam R) ∈ fixedPart R := by
  let v := (movingEquiv source geometry hb hZ u).toAdd
  have he : v ∈ fixedSpace (moving (Offenders.linearize (xAction source))).toRepresentation ⊤ ↔
      v.val ∈ fixedSpace (Offenders.linearize (xAction source)) ⊤ := by
    constructor
    · intro h g
      exact congrArg Subtype.val (h g)
    · intro h g
      exact Subtype.ext (h g)
  rw [he, ← space_fixed source]
  rfl

noncomputable def quotientOnU (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source)))
    {m : ℕ} (q : AbelianCore.QuotientRecognition.ModuleQuotient
      (moving (Offenders.linearize (xAction source))).toRepresentation m) :
    MovingQuotient source m where
  marking := q.marking
  projection := q.projection.toAddMonoidHom.toMultiplicative.comp
    (movingEquiv source geometry hb hZ).toMonoidHom
  onto := q.surjective.comp (movingEquiv source geometry hb hZ).surjective
  kernel := by
    ext u
    change q.projection (movingEquiv source geometry hb hZ u).toAdd = 0 ↔ _
    change (movingEquiv source geometry hb hZ u).toAdd ∈ q.projection.ker ↔ _
    rw [q.kernel]
    exact movingEquiv_fixed source geometry hb hZ u
  action := by
    intro g u v hv i
    change q.projection (movingEquiv source geometry hb hZ v).toAdd i = _
    rw [movingEquiv_action source geometry hb hZ g u v hv]
    exact q.equivariant _ _ i

noncomputable def copiesOnU (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R)
    (hZ : space (Z R (alpha R)) = centralSum (Offenders.linearize (xAction source)))
    {m : ℕ} (e : Copies (moving (Offenders.linearize (xAction source))).toRepresentation m) :
    MovingCopies source m where
  marking := e.marking
  equiv := (movingEquiv source geometry hb hZ).trans e.equiv.toAddEquiv.toMultiplicative
  action := by
    intro g u v hv i
    change e.equiv (movingEquiv source geometry hb hZ v).toAdd i = _
    rw [movingEquiv_action source geometry hb hZ g u v hv]
    exact e.equivariant _ _ i

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.Reconstruction
