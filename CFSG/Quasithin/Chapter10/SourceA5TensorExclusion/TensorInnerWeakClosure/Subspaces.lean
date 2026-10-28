module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Normalizer
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.Intrinsic

/-!
# Literal subgroups from tensor-coordinate subspaces

The faithful tensor coordinates identify every binary subspace with an
actual subgroup of the original full module, preserving its order. Fixed
spaces and linear displacement therefore give literal centralizers and
commutator containments. These transfers are used by the singular-plane
argument in Aschbacher–Smith 9.4.4–5, printed pp.736–737.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

def tensorCoordinateSubgroup (U : Submodule (ZMod 2) Binary.V) : Subgroup G :=
  (U.toAddSubgroup.toSubgroup.comap m.sectionData.coordinates).map D.fullModule.subtype

theorem tensorCoordinateSubgroup_le (U : Submodule (ZMod 2) Binary.V) :
    m.tensorCoordinateSubgroup U ≤ D.fullModule := map_subtype_le _

theorem mem_tensorCoordinateSubgroup (U : Submodule (ZMod 2) Binary.V) (v : D.fullModule) :
    (v : G) ∈ m.tensorCoordinateSubgroup U ↔ (m.sectionData.coordinates v).toAdd ∈ U := by
  constructor
  · rintro ⟨w,hw,hwe⟩
    exact (Subtype.ext hwe : w = v) ▸ hw
  · intro hv
    exact ⟨v,hv,rfl⟩

theorem card_tensorCoordinateSubgroup (U : Submodule (ZMod 2) Binary.V) :
    Nat.card (m.tensorCoordinateSubgroup U) = Nat.card U := by
  let f : m.tensorCoordinateSubgroup U → U := fun v =>
    ⟨(m.sectionData.coordinates ⟨v,m.tensorCoordinateSubgroup_le U v.property⟩).toAdd,
      (m.mem_tensorCoordinateSubgroup U _).mp v.property⟩
  apply Nat.card_congr (Equiv.ofBijective f ?_)
  constructor
  · intro v w h
    have hh := m.coordinates_injective (Multiplicative.toAdd.injective
      (congrArg Subtype.val h))
    exact Subtype.ext (congrArg (fun x : D.fullModule => (x : G)) hh)
  · intro u
    obtain ⟨v,hv⟩ := m.sectionData.onto (Multiplicative.ofAdd u.val)
    have hcoord : (m.sectionData.coordinates v).toAdd = u.val := congrArg Multiplicative.toAdd hv
    have hvU : (v : G) ∈ m.tensorCoordinateSubgroup U :=
      (m.mem_tensorCoordinateSubgroup U v).mpr (hcoord ▸ u.property)
    exact ⟨⟨v,hvU⟩,Subtype.ext hcoord⟩

theorem tensorCoordinateSubgroup_fixed (U : Submodule (ZMod 2) Binary.V)
    (a : D.maximalLocal) (hf : ∀ u ∈ U, m.maximalAction a u = u) :
    (a : G) ∈ centralizer (m.tensorCoordinateSubgroup U : Set G) := by
  intro v hv
  let w : D.fullModule := ⟨v,m.tensorCoordinateSubgroup_le U hv⟩
  have hw := (m.mem_tensorCoordinateSubgroup U w).mp hv
  have he := m.maximalAction_coordinates a w
  rw [hf _ hw] at he
  have hh := congrArg (fun x : D.fullModule => (x : G))
    (m.coordinates_injective (Multiplicative.toAdd.injective he.symm))
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

theorem tensorCoordinateSubgroup_commutator {A : Subgroup G}
    (hAM : A ≤ D.maximalLocal) (U S : Submodule (ZMod 2) Binary.V)
    (hmove : ∀ a : A, ∀ u ∈ U,
      m.maximalAction ⟨a,hAM a.property⟩ u - u ∈ S) :
    ⁅A,m.tensorCoordinateSubgroup U⁆ ≤ m.tensorCoordinateSubgroup S := by
  apply commutator_le.mpr
  intro a ha v hv
  let aM : D.maximalLocal := ⟨a,hAM ha⟩
  let vV : D.fullModule := ⟨v,m.tensorCoordinateSubgroup_le U hv⟩
  let w := D.fullModule.normalizerMonoidHom
    ⟨aM,D.maximalLocal_normalizes_fullModule aM.property⟩ vV
  have hcoord := m.maximalAction_coordinates aM vV
  have hh := hmove ⟨a,ha⟩ _ ((m.mem_tensorCoordinateSubgroup U vV).mp hv)
  rw [hcoord] at hh
  apply (m.mem_tensorCoordinateSubgroup S (w * vV⁻¹)).mpr
  rw [map_mul,map_inv]
  change (m.sectionData.coordinates w).toAdd + -(m.sectionData.coordinates vV).toAdd ∈ S
  simpa only [sub_eq_add_neg] using hh

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
