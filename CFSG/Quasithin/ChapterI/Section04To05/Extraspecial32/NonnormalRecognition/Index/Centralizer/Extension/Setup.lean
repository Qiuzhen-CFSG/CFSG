module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Index.Centralizer.Comparison

/-!
# Literal subgroup maps for the marked centralizer extension

The local subgroup K ∩ L is identified with C_L(t), then with C_A₈(t8).
Its inclusion in the A₉ centralizer is the fixed `eightToNine` map. The
residual transport keeps both original inclusions, so transfer gives
O²(K) ∩ (K ∩ L) = O²(K ∩ L) inside K.

The model residual below is the actual O²(C_A₉(t9)). Its concrete geometry
is an explicit obligation, separate from the gluing construction.
Source: Aschbacher, “A 2-local characterization of M12”, Proposition 3.3,
printed p.38.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
namespace Extension

/-- The literal inclusion of the eight-point centralizer. -/
def modelLocalEmbedding : Centralizer t8 →* Centralizer t9 where
  toFun a := ⟨eightToNine a.val, by
    apply mem_centralizer_singleton_iff.mpr
    have h := congrArg eightToNine (mem_centralizer_singleton_iff.mp a.property)
    simpa only [map_mul, eightToNine_t8] using h⟩
  map_one' := Subtype.ext (map_one eightToNine)
  map_mul' a b := Subtype.ext (map_mul eightToNine a.val b.val)

theorem modelLocalEmbedding_injective : Function.Injective modelLocalEmbedding := by
  intro a b h
  exact Subtype.ext (eightToNine_injective (congrArg Subtype.val h))

/-- The actual two-residual in the nine-point centralizer. -/
abbrev modelResidual := pResidual 2 (Centralizer t9)

/-- The actual two-residual of the eight-point centralizer, embedded there. -/
abbrev modelLocalResidual : Subgroup (Centralizer t8) :=
  (pResidual 2 (Centralizer t8))

/-- Concrete model obligations for the extension. No ambient-group conclusion
or fusion assertion is included here. -/
structure ModelGeometry where
  residual_equiv : modelResidual ≃* alternatingGroup (Fin 5)
  local_card : Nat.card modelLocalResidual = 12
  local_intersection : modelResidual.comap modelLocalEmbedding = modelLocalResidual
  generation : modelResidual ⊔ modelLocalEmbedding.range = ⊤

variable {G : Type*} [Group G] {z : G} {L : Subgroup G}

/-- Changing only the subgroup type identifies K ∩ L with C_L(t). -/
def localCentralizerEquiv (d : InvolutionData z L) :
    d.M ≃* centralizer ({d.t} : Set L) where
  toFun a := ⟨⟨a.val.val, a.property⟩, by
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp a.val.property)⟩
  invFun a := ⟨⟨a.val.val, by
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp a.property)⟩, a.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The marked local equivalence, including its centralizing equation. -/
def localModelEquiv (d : InvolutionData z L) : d.M ≃* Centralizer t8 where
  toFun a := ⟨d.equiv ⟨a.val.val, a.property⟩, by
    apply mem_centralizer_singleton_iff.mpr
    have h := congrArg d.equiv (mem_centralizer_singleton_iff.mp
      (localCentralizerEquiv d a).property)
    change d.equiv ⟨a.val.val, a.property⟩ * t8 =
      t8 * d.equiv ⟨a.val.val, a.property⟩
    have heq : ((localCentralizerEquiv d a : centralizer ({d.t} : Set L)) : L) =
        (⟨a.val.val, a.property⟩ : L) := by rfl
    rw [heq] at h
    simpa only [map_mul, InvolutionData.t, d.equiv.apply_symm_apply] using h⟩
  invFun a := (localCentralizerEquiv d).symm ⟨d.equiv.symm a, by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul, InvolutionData.t] using
      congrArg d.equiv.symm (mem_centralizer_singleton_iff.mp a.property)⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    simp [localCentralizerEquiv]
  right_inv a := by
    apply Subtype.ext
    exact d.equiv.apply_symm_apply _
  map_mul' x y := by
    apply Subtype.ext
    change d.equiv ((⟨x.val.val, x.property⟩ : L) * ⟨y.val.val, y.property⟩) = _
    rw [map_mul]
    rfl

/-- The prescribed local map whose extension is required by the source. -/
def localEmbedding (d : InvolutionData z L) : d.M →* Centralizer t9 :=
  modelLocalEmbedding.comp (localModelEquiv d).toMonoidHom

theorem localEmbedding_injective (d : InvolutionData z L) :
    Function.Injective (localEmbedding d) :=
  modelLocalEmbedding_injective.comp (localModelEquiv d).injective

theorem localEmbedding_coe (d : InvolutionData z L) (a : d.M) :
    (localEmbedding d a : Nine) = eightToNine (d.equiv ⟨a.val.val, a.property⟩) := by
  dsimp [localEmbedding, modelLocalEmbedding]
  change eightToNine (localModelEquiv d a).val = _
  change eightToNine (d.equiv ⟨a.val.val, a.property⟩) = _
  rfl

/-- The residual with its original K-subgroup type is the actual ambient J. -/
noncomputable def residualEquiv (d : InvolutionData z L) : pResidual 2 d.K ≃* d.J :=
  (pResidual 2 d.K).equivMapOfInjective d.K.subtype d.K.subtype_injective

variable [Finite G]

theorem residual_sup_local (d : InvolutionData z L)
    (hz : orderOf z = 2) (hCL : Centralizer z ≤ L) :
    pResidual 2 d.K ⊔ d.M = ⊤ := by
  obtain ⟨T, hT⟩ := d.exists_sylow_K_le_M hz hCL
  exact top_unique ((pResidual_sup_sylow_eq_top T).ge.trans (sup_le_sup_left hT _))

/-- Transport of the local residual uses both original ambient inclusions. -/
theorem localResidual_map (d : InvolutionData z L) :
    ((pResidual 2 d.M).map d.M.subtype).map d.K.subtype = d.X := by
  have h := map_pResidual_of_surjective 2 (localCentralizerEquiv d).toMonoidHom
    (localCentralizerEquiv d).surjective
  rw [InvolutionData.X, ← h, map_map, map_map, map_map]
  rfl

/-- Transfer identifies the actual intersection inside K with the local residual. -/
theorem residual_inf_local (d : InvolutionData z L) (htransfer : d.J ⊓ L = d.X) :
    pResidual 2 d.K ⊓ d.M = (pResidual 2 d.M).map d.M.subtype := by
  apply map_injective d.K.subtype_injective
  rw [map_inf _ _ _ d.K.subtype_injective, localResidual_map]
  change d.J ⊓ d.M.map d.K.subtype = d.X
  have hm : d.M.map d.K.subtype = L ⊓ d.K := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, a.property⟩
    · rintro ⟨hxL, hxK⟩
      exact ⟨⟨x, hxK⟩, hxL, rfl⟩
  rw [hm, ← inf_assoc, ← htransfer]
  exact inf_eq_left.mpr (inf_le_left.trans d.J_le_K)

end Extension
end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Index
end
