module
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.FactorCarrier
public import Theory.Representation.SubrepresentationLattice
/-!
# A proper factor subspace in its literal centralizer quotient

A normal embedded factor has an actual normal binary subgroup of the local
subgroup. Pulling a proper ambient subspace through its carrier equivalence
preserves invariance under the factor image and the original Sylow image.
This transports the proper-span contradiction to the E9 extension action.

Source: Aschbacher--Smith 15.1.2, printed p.1085.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.RatioDecomposition.Factor
variable {G D : Type*} [Group G] [Group D]
  {M V : Subgroup G} (hVM : V ≤ M) [IsElementaryAbelian 2 V]
  (ρ : Representation (ZMod 2) D (Additive V))
  (q : M →* D) (hq : Function.Surjective q)
  (hact : ∀ (m : M) (v : Additive V), ((ρ (q m) v).toMul : G) = (m:G) * v.toMul * (m:G)⁻¹)
  (F : Factor ρ) [F.actor.Normal]

include hact in
theorem internal_not_irreducible_of_proper_subspace
    (S : Subgroup M) (B : Submodule (ZMod 2) (Additive V))
    (hB0 : B ≠ ⊥) (hB : B < F.space)
    (hstable : F.actor ⊔ (S.map q ⊓ subspaceStabilizer ρ F.space) ≤ subspaceStabilizer ρ B) :
    letI := F.internalSubgroup_normal hVM ρ q hact
    let W := F.internalSubgroup hVM
    let r := F.internalProjection hVM ρ q hq hact
    let σ := NormalElementaryQuotient.representation W (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    ¬ IsIrreducible (σ.comp ((F.actor.map r) ⊔ S.map (QuotientGroup.mk' _)).subtype) := by
  let := F.internalSubgroup_normal hVM ρ q hact
  let W := F.internalSubgroup hVM
  let r := F.internalProjection hVM ρ q hq hact
  let σ := NormalElementaryQuotient.representation W (QuotientGroup.mk' _)
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  change ¬ IsIrreducible (σ.comp ((F.actor.map r) ⊔ S.map (QuotientGroup.mk' _)).subtype)
  let e := F.internalSpaceEquiv hVM ρ
  let φ := F.embedding.spaceMap.comp e.symm.toLinearMap
  have hφ (w : Additive W) : ((φ w).toMul : G) = ((w.toMul : M) : G) := by
    obtain ⟨v,rfl⟩ := e.surjective w
    change ((F.embedding.spaceMap (e.symm (e v))).toMul : G) = _
    rw [e.symm_apply_apply]
    rfl
  have heq (m : M) (w : Additive W) :
      φ (σ (QuotientGroup.mk' _ m) w) = ρ (q m) (φ w) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hφ,hact,NormalElementaryQuotient.representation_apply]
    rw [hφ]
    rfl
  have hφrange : φ.range = F.space := by
    change (F.embedding.spaceMap.comp e.symm.toLinearMap).range = F.embedding.spaceMap.range
    rw [LinearMap.range_comp,LinearEquiv.range,Submodule.map_top]
  let C := B.comap φ
  have hC0 : C ≠ ⊥ := by
    intro hz
    apply hB0
    apply bot_unique
    intro v hv
    obtain ⟨w,rfl⟩ := hφrange ▸ hB.le hv
    have hw : w ∈ C := hv
    rw [hz] at hw
    rw [(Submodule.mem_bot (R := ZMod 2)).mp hw,map_zero]
    exact Submodule.zero_mem _
  have hC1 : C ≠ ⊤ := by
    intro hz
    apply hB.ne
    apply le_antisymm hB.le
    intro v hv
    obtain ⟨w,rfl⟩ := hφrange ▸ hv
    exact (show w ∈ C from hz ▸ Submodule.mem_top)
  have hspace : (⊤ : Subgroup D) ≤ subspaceStabilizer ρ F.space := by
    rw [F.space_eq_support]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) le_normalizer_of_normal
  have hBa : F.actor ≤ subspaceStabilizer ρ B := le_sup_left.trans hstable
  have hBs : S.map q ⊓ subspaceStabilizer ρ F.space ≤ subspaceStabilizer ρ B :=
    le_sup_right.trans hstable
  have hC : F.actor.map r ⊔ S.map (QuotientGroup.mk' _) ≤ subspaceStabilizer σ C := by
    apply sup_le
    · rintro g ⟨a,ha,rfl⟩ w
      obtain ⟨m,hm⟩ := hq a
      change φ (σ (r a) w) ∈ B ↔ φ w ∈ B
      rw [←hm,F.internalProjection_apply hVM ρ q hq hact,heq]
      simpa only [hm] using hBa ha (φ w)
    · rintro g ⟨m,hm,rfl⟩ w
      change φ (σ (QuotientGroup.mk' _ m) w) ∈ B ↔ φ w ∈ B
      rw [heq]
      exact hBs ⟨mem_map_of_mem q hm,hspace (mem_top _)⟩ (φ w)
  intro hi
  let A : Subrepresentation (σ.comp ((F.actor.map r) ⊔ S.map (QuotientGroup.mk' _)).subtype) := {
    toSubmodule := C
    apply_mem_toSubmodule := fun g v hv => (hC g.property v).2 hv }
  rcases hi.eq_bot_or_eq_top A with hh | hh
  · exact hC0 (congrArg Subrepresentation.toSubmodule hh)
  · exact hC1 (congrArg Subrepresentation.toSubmodule hh)
end CFSG.Quasithin.ChapterD.RatioDecomposition.Factor
