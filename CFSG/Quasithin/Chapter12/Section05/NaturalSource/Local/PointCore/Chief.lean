module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.PointCore.Movement
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.PointChief

/-!
# The literal middle chief interval in the original module

Exterior coordinates identify any subgroup of the elementary V with a binary
subspace. Surjectivity of the original point-parabolic actor transports the
irreducibility of V₇/V₁ and V/V₇ to their ambient subgroup intervals under
N_L(V₁). This is the irreducibility input for the G.2.2 point-core argument;
it concerns the original V and the original quotient action.

Source: Aschbacher--Smith, 12.5.2(1) and 12.5.8(1), pp.817 and 820.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation Representation.SL5ExteriorSquare
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace ExteriorMarking
variable (a : ExteriorMarking D)

private def coordinateSubspace (A : Subgroup G) : Submodule (ZMod 2) SL5ExteriorSquare.V :=
  (AddSubgroup.toZModSubmodule 2)
    (AddSubgroup.toSubgroup.symm ((A.subgroupOf V).map a.coordinates.toMonoidHom))

private theorem mem_coordinateSubspace (A : Subgroup G) (v : V) :
    (a.coordinates v).toAdd ∈ a.coordinateSubspace A ↔ (v : G) ∈ A := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact a.coordinates.injective he ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

private theorem coordinateSubspace_subspace (W : Submodule (ZMod 2) SL5ExteriorSquare.V) :
    a.coordinateSubspace (a.subspace W) = W := by
  ext w
  let v := a.coordinates.symm (Multiplicative.ofAdd w)
  have he := (a.mem_coordinateSubspace (a.subspace W) v).trans (a.mem_subspace W v)
  simpa only [v, MulEquiv.apply_symm_apply, toAdd_ofAdd] using he

private theorem coordinateSubspace_mono : Monotone a.coordinateSubspace := by
  intro A B h v hv
  obtain ⟨x, hx, rfl⟩ := hv
  exact ⟨x, h hx, rfl⟩

private theorem coordinateSubspace_injective {A B : Subgroup G} (hA : A ≤ V) (hB : B ≤ V)
    (he : a.coordinateSubspace A = a.coordinateSubspace B) : A = B := by
  apply le_antisymm
  · intro x hx
    apply (a.mem_coordinateSubspace B ⟨x, hA hx⟩).mp
    rw [← he]
    exact (a.mem_coordinateSubspace A ⟨x, hA hx⟩).mpr hx
  · intro x hx
    apply (a.mem_coordinateSubspace A ⟨x, hB hx⟩).mp
    rw [he]
    exact (a.mem_coordinateSubspace B ⟨x, hB hx⟩).mpr hx

private theorem coordinateSubspace_invariant (A : Subgroup G)
    (hn : L ⊓ a.Gi 1 ≤ normalizer (A : Set G)) :
    ∀ g : parabolic 2, ∀ v ∈ a.coordinateSubspace A,
      SL5TenDimensional.exteriorAction 2 g v ∈ a.coordinateSubspace A := by
  let W := a.coordinateSubspace A
  intro g w hw
  obtain ⟨l, hl⟩ := a.localActor_surjective 1 (Or.inl rfl) g
  let v := a.coordinates.symm (Multiplicative.ofAdd w)
  have hvA : (v : G) ∈ A := by
    apply (a.mem_coordinateSubspace A v).mp
    simpa only [v, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hw
  have hln : (l : G) ∈ normalizer (A : Set G) :=
    hn l.property
  have he := a.equivariant ⟨l, l.property.1⟩ v
  have hag : a.componentActor ⟨l, l.property.1⟩ = (g : SL5TenDimensional.Group) :=
    congrArg Subtype.val hl
  have hm := (a.mem_coordinateSubspace A
    ⟨(l : G) * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (D.normalizes l.property.1) v).mp v.property⟩).mpr
    ((mem_normalizer_iff.mp hln v).mp hvA)
  rw [he] at hm
  change SL5TenDimensional.exteriorAction 2 (a.componentActor ⟨l, l.property.1⟩)
    (a.coordinates v).toAdd ∈ W at hm
  simpa only [hag, v, MulEquiv.apply_symm_apply, toAdd_ofAdd] using hm

/-- The actual invariant interval V₇/V₁ under N_L(V₁) is irreducible. -/
theorem point_middle_invariant_interval_of_component (A : Subgroup G)
    (h1 : a.Vi 1 ≤ A) (h7 : A ≤ a.Vi 7)
    (hn : L ⊓ a.Gi 1 ≤ normalizer (A : Set G)) : A = a.Vi 1 ∨ A = a.Vi 7 := by
  let W := a.coordinateSubspace A
  have hW1 : V₁ ≤ W := by
    rw [← a.coordinateSubspace_subspace V₁]
    exact a.coordinateSubspace_mono h1
  have hW7 : W ≤ V₇ := by
    rw [← a.coordinateSubspace_subspace V₇]
    exact a.coordinateSubspace_mono h7
  have hWV : A ≤ V := h7.trans (a.subspace_le _)
  have hact := a.coordinateSubspace_invariant A hn
  rcases SL5ExteriorSquare.point_middle_invariant_interval W hW1 hW7 hact with he | he
  · left
    apply a.coordinateSubspace_injective hWV (a.subspace_le _)
    exact he.trans (a.coordinateSubspace_subspace V₁).symm
  · right
    apply a.coordinateSubspace_injective hWV (a.subspace_le _)
    exact he.trans (a.coordinateSubspace_subspace V₇).symm

/-- The last chief factor is the actual upper invariant interval. -/
theorem point_upper_invariant_interval_of_component (A : Subgroup G)
    (h7 : a.Vi 7 ≤ A) (hV : A ≤ V)
    (hn : L ⊓ a.Gi 1 ≤ normalizer (A : Set G)) : A = a.Vi 7 ∨ A = V := by
  let W := a.coordinateSubspace A
  have hW7 : V₇ ≤ W := by
    rw [← a.coordinateSubspace_subspace V₇]
    exact a.coordinateSubspace_mono h7
  have hact := a.coordinateSubspace_invariant A hn
  rcases SL5ExteriorSquare.point_upper_invariant_interval W hW7 hact with he | he
  · left
    apply a.coordinateSubspace_injective hV (a.subspace_le _)
    exact he.trans (a.coordinateSubspace_subspace V₇).symm
  · right
    apply a.coordinateSubspace_injective hV le_rfl
    exact he.trans ((a.coordinateSubspace_subspace ⊤).symm.trans
      (congrArg a.coordinateSubspace a.subspace_top))


end ExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
