module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.RootPairEnvelope
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.Representation.BinaryOffender.PermutationConjugacy
/-!
# Residual noncentrality of the root-pair envelope

The first basis vector is fixed by the upper root pair but moved by the
opposite first root in its rank-one envelope. The strict natural fixed-index
gap lifts through a full two-kernel using the exact indices on the original
module. A residual/Sylow factorization then forces the two-residual to move
the entire Sylow fixed subgroup. Inner conjugation treats arbitrary root
pairs without changing the field or removing central attachments.

Source: MS93 (5.1), printed p.913, clause (iii). The actual Thompson central
omega application is in NonbinarySymplectic.CriticalReduction.RootProductMovement.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Subgroup Matrix Representation
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open BinaryOffender
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.RootEnvelope
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]
local notation "τ" => restrictScalars (k := ZMod 2) (symplecticNatural (k := F) 2)
local notation "v₀" => (Pi.single (Sum.inl (0 : Fin 2)) (1 : F) : Fin 2 ⊕ Fin 2 → F)

private theorem first_vector_fixed (b : Bool) : v₀ ∈ fixedSpace τ (sylowImage (F := F) b) := by
  have hfix : sylowImage (F := F) b ≤ MulAction.stabilizer (Sp F) v₀ := by
    apply sup_le
    · intro x hx
      obtain ⟨t,rfl⟩ := (first_root_mem_iff x).mp hx
      change (rootElement 0 t).val *ᵥ v₀ = v₀
      ext i
      rcases i with i | i <;> fin_cases i <;>
        simp [rootElement,rootMatrix,Matrix.fromBlocks,Matrix.single,Matrix.mulVec, dotProduct,
          Fintype.sum_sum_type,Fin.sum_univ_two,Pi.single_apply]
    · cases b with
      | false => exact bot_le
      | true =>
        intro x hx
        obtain ⟨t,rfl⟩ := (second_root_mem_iff x).mp hx
        change (rootElement 2 t).val *ᵥ v₀ = v₀
        ext i
        rcases i with i | i <;> fin_cases i <;>
          simp [rootElement,rootMatrix,Matrix.fromBlocks,Matrix.single,Matrix.mulVec,dotProduct,
            Fintype.sum_sum_type,Fin.sum_univ_two,Pi.single_apply]
  intro x
  exact hfix x.property

omit [CharP F 2] [Finite F] [Algebra (ZMod 2) F] in
private theorem lower_mem (b : Bool) : rootElement 1 (1:F) ∈ group (F := F) b := by
  refine ⟨((Matrix.SpecialLinearGroup.transvection (i := (1:Fin 2)) (j := 0) one_ne_zero 1),1),?_⟩
  change OppositeLongRootPair.embedding _ * rootElement 2 (0:F) = _
  rw [OppositeLongRootPair.embedding_lower,RootSubgroup.element_zero,mul_one]

omit [CharP F 2] [Finite F] in
private theorem first_vector_not_fixed (b : Bool) : v₀ ∉ fixedSpace τ (group (F := F) b) := by
  intro hv
  have hh := congrFun (hv ⟨rootElement 1 (1:F),lower_mem b⟩) (.inr 0)
  change ((rootElement 1 (1:F)).val *ᵥ v₀) (.inr 0) = v₀ (.inr 0) at hh
  simp [rootElement,rootMatrix,Matrix.fromBlocks,Matrix.single,Matrix.mulVec,dotProduct,
    Fintype.sum_sum_type,Fin.sum_univ_two,Pi.single_apply] at hh

/-- The rank-one envelope strictly decreases the fixed space of its full root Sylow. -/
theorem fixedCodim_sylow_lt_group (b : Bool) :
    fixedCodim τ (sylowImage (F := F) b) < fixedCodim τ (group (F := F) b) := by
  obtain ⟨S,hS,_⟩ := exists_envelope (F := F) b
  have hle : sylowImage (F := F) b ≤ group (F := F) b := hS ▸ map_subtype_le _
  have hlt : fixedSpace τ (group (F := F) b) < fixedSpace τ (sylowImage (F := F) b) :=
    lt_of_le_not_ge (fixedSpace_antitone τ hle)
      (fun h => first_vector_not_fixed b (h (first_vector_fixed b)))
  have hd := Submodule.finrank_lt_finrank_of_lt hlt
  have h₁ := fixedCodim_add_finrank τ (sylowImage (F := F) b)
  have h₂ := fixedCodim_add_finrank τ (group (F := F) b)
  omega

/-- A fixed-index gap forces the prime residual to move the original Sylow fixed subgroup. -/
theorem residual_moves_fixed_of_index_lt
    {G : Type*} [Group G] [Finite G] (U I J : Subgroup G)
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = J)
    (hi : (centralizer (J : Set G)).relIndex U < (centralizer (I : Set G)).relIndex U) :
    ⁅U ⊓ centralizer (J : Set G), (pResidual 2 I).map I.subtype⁆ ≠ ⊥ := by
  intro hc
  have hgen := congrArg (Subgroup.map I.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup,hS,←MonoidHom.range_eq_map,range_subtype] at hgen
  have hCI : U ⊓ centralizer (J : Set G) ≤ centralizer (I : Set G) := by
    apply le_centralizer_iff.mpr
    rw [←hgen]
    exact sup_le
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
      (le_centralizer_iff.mp (show U ⊓ centralizer (J : Set G) ≤ centralizer (J : Set G) from inf_le_right))
  have hle : U ⊓ centralizer (J : Set G) ≤ U ⊓ centralizer (I : Set G) := le_inf inf_le_left hCI
  have he : U ⊓ centralizer (I : Set G) = U ⊓ centralizer (J : Set G) :=
    le_antisymm (inf_le_inf_left U (centralizer_le (hS ▸ map_subtype_le _))) hle
  rw [←inf_relIndex_left U (centralizer (J : Set G)),
    ←inf_relIndex_left U (centralizer (I : Set G)),he] at hi
  exact hi.false

/-- The full preimage envelope moves the Sylow fixed subgroup through its
prime residual. Its original kernel and the exact natural indices are retained. -/
theorem exists_moving_preimage_envelope
    {G : Type*} [Group G] [Finite G]
    (f : G →* Sp F) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (U J : Subgroup G) (hkJ : f.ker ≤ J) (b : Bool) (hJ : J.map f = sylowImage b)
    (hindex : ∀ A : Subgroup G, (centralizer (A : Set G)).relIndex U =
      2 ^ fixedCodim τ (A.map f)) :
    ∃ I : Subgroup G, J ≤ I ∧ I.map f = group b ∧
      ∃ S : Sylow 2 I, (S : Subgroup I).map I.subtype = J ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
        ⁅U ⊓ centralizer (J : Set G), (pResidual 2 I).map I.subtype⁆ ≠ ⊥ := by
  obtain ⟨P,hP,⟨eP⟩⟩ := exists_envelope (F := F) b
  let I := (group (F := F) b).comap f
  let q : I →* group (F := F) b := (f.comp I.subtype).codRestrict (group (F := F) b) (fun x => x.property)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y,hy⟩ := hf x.val
    exact ⟨⟨y,by change f y ∈ group (F := F) b; rw [hy]; exact x.property⟩,Subtype.ext hy⟩
  have hqk : IsPGroup 2 q.ker := by
    have he : q.ker = f.ker.comap I.subtype := by
      ext x
      change q x=1 ↔ f x.val=1
      exact Subtype.ext_iff
    rw [he]
    exact hk.comap_subtype
  have hJI : J ≤ I := by
    intro x hx
    change f x ∈ group (F := F) b
    exact (hP ▸ map_subtype_le (P : Subgroup (group (F := F) b))) (hJ ▸ mem_map_of_mem f hx)
  let S := P.comapOfKerIsPGroup q hqk (by
    rw [MonoidHom.range_eq_top_of_surjective q hq]; exact le_top)
  have hs : (S : Subgroup I) = J.subgroupOf I := by
    ext x
    change q x ∈ (P : Subgroup (group (F := F) b)) ↔ x.val ∈ J
    have hx : q x ∈ (P : Subgroup (group (F := F) b)) ↔ f x.val ∈ sylowImage b := by
      rw [←hP]
      exact (mem_map_iff_mem (group (F := F) b).subtype_injective).symm
    rw [hx,←hJ]
    change x.val ∈ (J.map f).comap f ↔ _
    rw [comap_map_eq_self hkJ]
  have hSm : (S : Subgroup I).map I.subtype = J := by
    rw [hs,map_subgroupOf_eq_of_le hJI]
  have hIm : I.map f = group b := map_comap_eq_self_of_surjective hf _
  refine ⟨I,hJI,hIm,S,hSm,⟨(q.pCoreQuotientEquiv hq hqk).trans eP⟩,?_⟩
  apply residual_moves_fixed_of_index_lt U I J S hSm
  rw [hindex,hindex,hJ,hIm]
  exact pow_lt_pow_right₀ (by decide : 1 < 2) (fixedCodim_sylow_lt_group b)

/-- Arbitrary full root pairs retain the residual noncentrality after
conjugating the quotient marking inside the original symplectic group. -/
theorem exists_moving_root_pair_envelope
    {G : Type*} [Group G] [Finite G]
    (f : G →* Sp F) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (U J : Subgroup G) (hkJ : f.ker ≤ J) (s t : Option F)
    (hJ : J.map f = rootImage s ⊔ rootImage t)
    (hindex : ∀ A : Subgroup G, (centralizer (A : Set G)).relIndex U =
      2 ^ fixedCodim τ (A.map f)) :
    ∃ I : Subgroup G, J ≤ I ∧
      ∃ S : Sylow 2 I, (S : Subgroup I).map I.subtype = J ∧
        Nonempty ((I ⧸ pCore 2 I) ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
        ⁅U ⊓ centralizer (J : Set G), (pResidual 2 I).map I.subtype⁆ ≠ ⊥ := by
  obtain ⟨g,hg⟩ := rootPair_standard_first s t
  let f' := (MulAut.conj g).toMonoidHom.comp f
  have hf' : Function.Surjective f' := (MulAut.conj g).surjective.comp hf
  have hker : f'.ker = f.ker := by
    ext x
    change (MulAut.conj g) (f x)=1 ↔ f x=1
    exact (MulAut.conj g).map_eq_one_iff
  have hm : J.map f' = (rootImage s ⊔ rootImage t).map (MulAut.conj g).toMonoidHom := by
    rw [←Subgroup.map_map,hJ]
  have hi : ∀ A : Subgroup G, (centralizer (A : Set G)).relIndex U =
      2 ^ fixedCodim τ (A.map f') := by
    intro A
    rw [←Subgroup.map_map,fixedCodim_map_conj]
    exact hindex A
  have hh (b : Bool) (hb : J.map f' = sylowImage b) :=
    exists_moving_preimage_envelope f' hf' (hker ▸ hk) U J (hker ▸ hkJ) b hb hi
  rcases hg with hg | hg
  · obtain ⟨I,hJI,_,S,hS,he,hn⟩ := hh false
      (by simpa only [sylowImage,Bool.false_eq_true,↓reduceIte,sup_bot_eq] using hm.trans hg)
    exact ⟨I,hJI,S,hS,he,hn⟩
  · obtain ⟨I,hJI,_,S,hS,he,hn⟩ := hh true
      (by simpa only [sylowImage,↓reduceIte] using hm.trans hg)
    exact ⟨I,hJI,S,hS,he,hn⟩

end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.SmallMovers.RootEnvelope
