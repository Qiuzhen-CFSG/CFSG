module
public import Theory.Representation.SL2NaturalOffenders.Ratios.FixedLine
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Natural fixed lines in the epsilon-two critical branch

Every nontrivial subgroup of a natural SL₂ Sylow has the same fixed and
commutator line. Quadraticity bounds its displacements above; one nonidentity
matrix and rank-nullity give the matching lower bound. Literal conjugation
coordinates then identify the original group commutator when the central
section kernel vanishes. The quotient actor and both subgroup embeddings are
retained. `CenterCommutators` applies this to the source edge two-core.

Source: DGS, *Groups and Graphs* (1985), (7.4)(c--d), p.128, using the
natural-module properties on p.113. These lemmas do not assert the distance bound.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
variable {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "N" => Representation.SL2NaturalOffenders.NoStrong.natural (F := F)

private theorem matrix_sylow_facts (T : Sylow 2 SL(2,F)) :
    IsQuadratic N T ∧
    Module.finrank (ZMod 2) (fixedSpace N T) = Module.finrank (ZMod 2) F := by
  let e : (⊤ : Subgroup SL(2,F)) ≃* SL(2,F) := Subgroup.topEquiv
  let P := T.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have he : (P : Subgroup (⊤ : Subgroup SL(2,F))).map (⊤ : Subgroup SL(2,F)).subtype = T := by
    change ((T : Subgroup SL(2,F)).map e.symm.toMonoidHom).map _ = _
    rw [map_map]
    change (T : Subgroup SL(2,F)).map (MonoidHom.id _) = _
    exact map_id _
  have hq := SL2NaturalOffenders.Ratios.sylowImage_quadratic ⊤ e N (fun _ _ => rfl) P
  have hd := SL2NaturalOffenders.Ratios.sylowImage_fixedCodim ⊤ e N (fun _ _ => rfl) P
  rw [he] at hq hd
  have hf := fixedCodim_add_finrank N (T : Subgroup SL(2,F))
  have hdim : Module.finrank (ZMod 2) (Fin 2 → F) = 2 * Module.finrank (ZMod 2) F := by
    simp [Module.finrank_pi_fintype,two_mul]
  exact ⟨hq,by omega⟩

/-- Every nontrivial subgroup of a natural Sylow has the same fixed and moved line. -/
theorem natural_subgroup_fixed_moved (T : Sylow 2 SL(2,F)) (A : Subgroup SL(2,F))
    (hAT : A ≤ T) (hne : A ≠ ⊥) :
    fixedSpace N A = fixedSpace N T ∧
    subspaceCommutator N ⊤ A = fixedSpace N T := by
  obtain ⟨hq,hfd⟩ := matrix_sylow_facts T
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hz := zpowers_le.mpr ha
  have hcard := SL2NaturalOffenders.fixedSpace_card_le_of_le ⊤
    (Subgroup.topEquiv : (⊤ : Subgroup SL(2,F)) ≃* SL(2,F)) N
    (fun _ _ => rfl) (zpowers_ne_bot.mpr ha1) le_top
  have hk : Module.finrank (ZMod 2) (fixedSpace N (zpowers a)) ≤ Module.finrank (ZMod 2) F := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F),Nat.card_zmod] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hcard
  have hm : subspaceCommutator N ⊤ A ≤ fixedSpace N T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,v,_,rfl⟩ y
    exact hq y y.property x (hAT hx) v
  have hr : LinearMap.range (N a - LinearMap.id) ≤ subspaceCommutator N ⊤ A := by
    rintro _ ⟨v,rfl⟩
    exact Submodule.subset_span ⟨a,ha,v,Submodule.mem_top,rfl⟩
  have hdim : Module.finrank (ZMod 2) (Fin 2 → F) = 2 * Module.finrank (ZMod 2) F := by
    simp [Module.finrank_pi_fintype,two_mul]
  have hadd := fixedCodim_add_finrank N (zpowers a)
  rw [fixedCodim_zpowers_eq_displacement_rank] at hadd
  have hl := Submodule.finrank_mono hr
  refine ⟨?_,Submodule.eq_of_le_of_finrank_le hm (by omega)⟩
  apply (Submodule.eq_of_le_of_finrank_le (fixedSpace_antitone N hAT) ?_).symm
  have hh := Submodule.finrank_mono (fixedSpace_antitone N hz)
  omega

variable {G : Type*} [Group G]

/-- Fixed-line coordinates identify the original group commutator, with trivial kernel. -/
theorem natural_section_commutator (L Z : Subgroup G) (π : L →* SL(2,F))
    (d : BinaryConjugationSection L Z ⊥ ((N).comp π))
    (A S : Subgroup G) (hAL : A ≤ L) (hSL : S ≤ L)
    (T : Sylow 2 SL(2,F)) (hT : (S.subgroupOf L).map π = T)
    (hAS : A ≤ S) (hne : (A.subgroupOf L).map π ≠ ⊥) :
    ⁅Z,A⁆ = Z ⊓ centralizer (S : Set G) := by
  have hi : Function.Injective d.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [d.kernel_eq,bot_subgroupOf]
  have hAZ : ⁅Z,A⁆ ≤ Z := le_normalizer_iff_commutator_le_left.mp (hAL.trans d.normalized)
  have hm : d.imageSpace ⁅Z,A⁆ = fixedSpace N T := by
    rw [commutator_comm Z A,d.imageSpace_commutator A Z hAL le_rfl,
      d.imageSpace_self,subspaceCommutator_comp_map]
    apply (natural_subgroup_fixed_moved T _ ?_ hne).2
    rw [←hT]
    exact map_mono (subgroupOf_mono L hAS)
  have hf (z : Z) : (d.coordinates z).toAdd ∈ fixedSpace N T ↔
      (z : G) ∈ centralizer (S : Set G) := by
    rw [←hT,←fixedSpace_comp_map]
    constructor
    · intro hz s hs
      have hfix := hz ⟨⟨s,hSL hs⟩,hs⟩
      have he := d.equivariant ⟨s,hSL hs⟩ z
      have hc := congrArg Subtype.val (hi (Multiplicative.toAdd.injective (he.trans hfix)))
      change s * (z : G) * s⁻¹ = z at hc
      exact mul_inv_eq_iff_eq_mul.mp hc
    · intro hz s
      have he := d.equivariant s.val z
      have hc : (⟨(s.val : G) * z * (s.val : G)⁻¹,
          (mem_normalizer_iff.mp (d.normalized s.val.property) z).mp z.property⟩ : Z) = z := by
        apply Subtype.ext
        change (s.val : G) * (z : G) * (s.val : G)⁻¹ = z
        rw [hz s.val s.property,mul_inv_cancel_right]
      rw [hc] at he
      exact he.symm
  apply le_antisymm
  · intro z hz
    refine ⟨hAZ hz,(hf ⟨z,hAZ hz⟩).mp ?_⟩
    rw [←hm]
    exact (d.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le _).mpr hz
  · intro z hz
    apply (d.coordinates_mem_imageSpace_iff_of_kernel_le _ bot_le ⟨z,hz.1⟩).mp
    rw [hm]
    exact (hf ⟨z,hz.1⟩).mpr hz.2

end CFSG.Quasithin.ChapterF.Source.DGS85.Noncommuting
