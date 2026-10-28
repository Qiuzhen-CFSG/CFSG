module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Span
public import Theory.Representation.AlternatingSevenFiveRestriction.DeletedMoved
public import Theory.Representation.BinaryConjugationSection.CommutatorImage

/-!
# The moved five-letter core in an ordinary seven-letter chart

A chart transports subgroup commutators to linear moved spaces. For an A₅
subgroup normalized by a Sylow 2-subgroup of A₇, the moved space is the simple
binary five-letter core. Thus every nonzero invariant subgroup of that moved
space is the whole space. This is the module identification used in
Aschbacher–Smith, *The Classification of Quasithin Groups*, 4.3.7, p. 616.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open BinaryPermutation
namespace BinaryPermutation.SevenParabolic.Ordinary.Chart
variable {G : Type*} [Group G] {J C U : Subgroup G} (d : Chart J C U)

private def conjugationSection (hUJ : U ≤ J) : BinaryConjugationSection J U ⊥
    ((coreRepresentation (Fin 7)).comp d.actor) where
  section_le := hUJ
  kernel_le := bot_le
  normalized := d.normalized
  coordinates := d.moduleEquiv.toMonoidHom
  onto := d.moduleEquiv.surjective
  kernel_eq := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr d.moduleEquiv.injective]
    simp only [bot_subgroupOf]
  equivariant := d.equivariant

/-- Whole-module coordinates carry the literal subgroup commutator to the
linear moved space for the actual actor image. -/
theorem image_commutator (hUJ : U ≤ J) (L : Subgroup G) (hLJ : L ≤ J) :
    d.image ⁅U,L⁆ = subspaceCommutator (coreRepresentation (Fin 7)) ⊤
      ((L.subgroupOf J).map d.actor) := by
  have htop : (d.conjugationSection hUJ).imageSpace U = ⊤ := by
    apply top_unique
    intro v _
    exact ((d.conjugationSection hUJ).mem_imageSpace_iff _ _).mpr
      ⟨d.lift v,(d.lift v).property,d.coordinate_lift v⟩
  change (d.conjugationSection hUJ).imageSpace ⁅U,L⁆ = _
  rw [commutator_comm,(d.conjugationSection hUJ).imageSpace_commutator L U hLJ le_rfl,htop,
    subspaceCommutator_comp_map]

/-- The nonzero invariant part of the moved A₅ core is its whole moved space. -/
theorem five_moved_eq (hUJ : U ≤ J) (L W : Subgroup G) (hLJ : L ≤ J)
    (B : Subgroup (alternatingGroup (Fin 7))) (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hSB : (S : Subgroup (alternatingGroup (Fin 7))) ≤
      normalizer (B : Set (alternatingGroup (Fin 7))))
    (himage : (L.subgroupOf J).map d.actor = B.map (alternatingGroup (Fin 7)).subtype)
    (hW : W ≤ ⁅U,L⁆) (hne : W ≠ ⊥) (hn : L ≤ normalizer (W : Set G)) :
    ⁅U,L⁆ = W := by
  have hUL : ⁅U,L⁆ ≤ U := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp (hLJ.trans d.normalized)
  have hWU := hW.trans hUL
  have hmove : d.image ⁅U,L⁆ =
      subspaceCommutator (alternatingCoreRepresentation (Fin 7)) ⊤ B := by
    rw [d.image_commutator hUJ L hLJ,himage]
    exact (subspaceCommutator_comp_map _ _ _ _).symm
  obtain ⟨eB,j,hj,hact,hrange⟩ := exists_five_core_moved_embedding B e S hSB
  let M := d.image W
  have hM : M ≤ j.range := by
    rw [hrange,←hmove]
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨u,hW hu,rfl⟩
  have hinv (b : B) (v : core (Fin 7)) (hv : v ∈ M) :
      coreRepresentation (Fin 7) b.val.val v ∈ M := by
    have hb : b.val.val ∈ (L.subgroupOf J).map d.actor := by
      rw [himage]
      exact mem_map_of_mem _ b.property
    obtain ⟨l,hl,hlb⟩ := hb
    rw [←hlb,d.mem_image_lift,d.lift_action]
    exact le_normalizer_iff.mp hn l hl (d.lift v) ((d.mem_image_lift W v).mp hv)
  have hp : ∀ a : alternatingGroup (Fin 5), ∀ v ∈ M.comap j,
      coreRepresentation (Fin 5) a.val v ∈ M.comap j := by
    intro a v hv
    change j (coreRepresentation (Fin 5) a.val v) ∈ M
    rw [←eB.apply_symm_apply a,hact]
    exact hinv (eB.symm a) (j v) hv
  have hfull : M = j.range := by
    rcases SevenPointChiefFactor.fiveCore_simple (M.comap j) hp with hz | ht
    · exfalso
      apply hne
      apply bot_unique
      intro w hw
      let u : U := ⟨w,hWU hw⟩
      have hu : (d.moduleEquiv u).toAdd ∈ M := (d.mem_image W u).mpr hw
      obtain ⟨v,hv⟩ := hM hu
      have hv0 : v = 0 := by
        have hvm : v ∈ M.comap j := by
          change j v ∈ M
          rwa [hv]
        rwa [hz,Submodule.mem_bot] at hvm
      have he : d.moduleEquiv u = 1 := by
        apply Multiplicative.toAdd.injective
        change (d.moduleEquiv u).toAdd = 0
        rw [←hv,hv0,map_zero]
      have hu1 : u = 1 := d.moduleEquiv.injective (he.trans d.moduleEquiv.map_one.symm)
      exact congrArg Subtype.val hu1
    · apply le_antisymm hM
      rintro _ ⟨v,rfl⟩
      have hv : v ∈ M.comap j := by rw [ht]; trivial
      exact hv
  apply le_antisymm _ hW
  intro u hu
  apply (d.mem_image W ⟨u,hUL hu⟩).mp
  change (d.moduleEquiv ⟨u,hUL hu⟩).toAdd ∈ M
  rw [hfull,hrange,←hmove]
  exact (d.mem_image ⁅U,L⁆ ⟨u,hUL hu⟩).mpr hu
end BinaryPermutation.SevenParabolic.Ordinary.Chart
