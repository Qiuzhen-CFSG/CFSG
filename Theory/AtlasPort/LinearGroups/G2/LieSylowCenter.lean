module

public import Theory.AtlasPort.LinearGroups.G2.LieParabolicSetup
/-!
# Centers in the even-characteristic G₂ root pair

Commuting with four root elements forces all but the highest-root coordinate
to vanish. This identifies the centers of both the Sylow subgroup and the
first five-root subgroup with the additive field, and proves the source
numbering convention: the first local group centralizes the whole Sylow center.

Source: Aschbacher--Smith, F.1.11--12, printed pp. 262--264.
-/

@[expose] public section

open Atlas.G2 Atlas.G2.Explicit
namespace Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F]
private theorem central_parameters [CharP F 2] (t : Fin 6 → F)
    (ht : ∀ j : Fin 6, j ≠ 5 →
      unipotentProductParameters (Pi.single j 1) t =
      unipotentProductParameters t (Pi.single j 1)) :
    t = ![t 0,0,0,0,0,0] := by
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hthree : (3 : F) = 1 := by linear_combination htwo
  have he5 := congrFun (ht 4 (by decide)) 3
  have h5 : t 5 = 0 := by
    simpa [unipotentProductParameters, Pi.single_apply] using he5.symm
  have he4 := congrFun (ht 1 (by decide)) 0
  have h4 : t 4 = 0 := by
    simpa [unipotentProductParameters, Pi.single_apply, h5] using he4.symm
  have he3 := congrFun (ht 2 (by decide)) 0
  have h3 : t 3 = 0 := by
    simpa [unipotentProductParameters, Pi.single_apply, h5, hthree] using he3.symm
  have he2 := congrFun (ht 3 (by decide)) 0
  have h2 : t 2 = 0 := by
    simpa [unipotentProductParameters, Pi.single_apply, h5, hthree] using he2
  have he1 := congrFun (ht 4 (by decide)) 0
  have h1 : t 1 = 0 := by
    simpa [unipotentProductParameters, Pi.single_apply, h5] using he1
  ext i
  fin_cases i <;> simp [h1,h2,h3,h4,h5]

/-- The additive highest-root group, embedded in the actual octonion automorphisms. -/
def highestRootHom : Multiplicative F →* Model F where
  toFun a := rootA a.toAdd
  map_one' := by simp
  map_mul' a b := (rootA_add _ _).symm

def highestRoot : Subgroup (Model F) := highestRootHom.range

theorem highestRootHom_injective : Function.Injective (highestRootHom (F := F)) :=
  fun _ _ h => Multiplicative.toAdd.injective (rootA_injective h)

noncomputable def highestRootEquiv : Multiplicative F ≃* highestRoot (F := F) :=
  MonoidHom.ofInjective highestRootHom_injective

theorem card_highestRoot : Nat.card (highestRoot (F := F)) = Nat.card F :=
  Nat.card_congr highestRootEquiv.toEquiv.symm

theorem rootA_mem_radical₁ (a : F) : rootA a ∈ radical₁ (F := F) :=
  ⟨![a,0,0,0,0,0], rfl, by simp [unipotentProduct]⟩

variable [CharP F 2]

/-- Every intermediate subgroup between the five-root radical and the positive
roots has precisely the highest-root group as its center. -/
theorem center_map_eq_highestRoot (H : Subgroup (Model F))
    (hlo : radical₁ ≤ H) (hhi : H ≤ unipotent) :
    (Subgroup.center H).map H.subtype = highestRoot := by
  apply le_antisymm
  · rintro _ ⟨g,hg,rfl⟩
    have hgu := hhi g.prop
    rw [unipotent_eq_range] at hgu
    obtain ⟨t,ht⟩ := hgu
    have hp : t = ![t 0,0,0,0,0,0] := by
      apply central_parameters
      intro j hj
      apply unipotentProduct_injective
      rw [← unipotentProduct_mul, ← unipotentProduct_mul, ht]
      have hjmem : unipotentProduct (Pi.single j 1) ∈ radical₁ (F := F) :=
        ⟨Pi.single j 1, by simp [Ne.symm hj], rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hg
        ⟨unipotentProduct (Pi.single j 1), hlo hjmem⟩)
    refine ⟨Multiplicative.ofAdd (t 0), ?_⟩
    change rootA (t 0) = g.val
    rw [← ht, hp]
    simp [unipotentProduct]
  · rintro _ ⟨a,rfl⟩
    refine ⟨⟨rootA a.toAdd, hlo (rootA_mem_radical₁ _)⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro g
    apply Subtype.ext
    have hgu := hhi g.prop
    rw [unipotent_eq_range] at hgu
    obtain ⟨t,ht⟩ := hgu
    change g.val * rootA a.toAdd = rootA a.toAdd * g.val
    rw [← ht]
    exact (unipotentProduct_commute_rootA _ _).eq

noncomputable def centerEquivHighestRoot (H : Subgroup (Model F))
    (hlo : radical₁ ≤ H) (hhi : H ≤ unipotent) :
    Subgroup.center H ≃* Multiplicative F :=
  ((Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
    (MulEquiv.subgroupCongr (center_map_eq_highestRoot H hlo hhi))).trans
      highestRootEquiv.symm

theorem card_center_radical₁ : Nat.card (Subgroup.center (radical₁ (F := F))) = Nat.card F :=
  Nat.card_congr (centerEquivHighestRoot radical₁ le_rfl
    (fiveRootSubgroup_le_unipotent _ _)).toEquiv

theorem unipotent_center :
    (Subgroup.center (unipotent (K := F))).map unipotent.subtype = highestRoot :=
  center_map_eq_highestRoot _ (fiveRootSubgroup_le_unipotent _ _) le_rfl

theorem local₁_centralizes_sylow_center [Finite F]
    (g : Model F) (hg : g ∈ local₁)
    (z : Subgroup.center (sylow (F := F) : Subgroup (Model F))) :
    Commute g z.val.val := by
  have hz : z.val.val ∈ highestRoot (F := F) := by
    rw [← unipotent_center]
    exact ⟨z.val, z.prop, rfl⟩
  obtain ⟨a,ha⟩ := hz
  rw [← ha]
  exact Subgroup.mem_centralizer_singleton_iff.mp (local₁_le_centralizer_rootA a.toAdd hg)

end Atlas.G2.LieParabolicSetup
