module

public import Theory.GroupAction.NormalPChiefSeries
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.Representation.BinaryConjugationSection
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Binary representations on actual noncentral chief sections

Every chief interval below a finite normal two-subgroup is elementary abelian,
even when the containing interval is nonabelian. Its literal conjugation action
is an irreducible binary representation. The two-core acts trivially; when the
actual two-core quotient is simple, every noncentral descended action is faithful.
Consequently each element outside the two-core moves every noncentral factor.

The ambient adapter retains the original subgroup inclusion and quotient map.
It supplies the chief-section input to the final paragraph of Aschbacher–Smith,
*The Classification of Quasithin Groups*, 13.8.28, printed pp.965–966.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace NoncentralChiefRefinement
variable {H : Type*} [Group H] [Finite H] (A B : NormalNode H)

theorem chief_elementary (hc : A ⋖ B) (hp : IsPGroup 2 B.val) :
    IsElementaryAbelian 2 (Section A B) := by
  obtain ⟨s, hs0, hsA⟩ := exists_chiefSeries (⊥ : NormalNode H) A bot_le
  have hstep : s.last ⋖ B := hsA ▸ hc
  let t : SeriesOn B.val := ⟨s.snoc B hstep,
    (RelSeries.head_snoc _ _ _).trans hs0, RelSeries.last_snoc _ _ _⟩
  have h := t.factor_elementary hp (Fin.last s.length)
  have hlo : t.lower (Fin.last s.length) = A :=
    (RelSeries.snoc_castSucc s B hstep (Fin.last s.length)).trans hsA
  have hhi : t.upper (Fin.last s.length) = B := RelSeries.last_snoc' s B hstep
  change IsElementaryAbelian 2 (Section (t.lower (Fin.last s.length))
    (t.upper (Fin.last s.length))) at h
  rw [hlo, hhi] at h
  exact h

omit [Finite H] in
theorem chief_irreducible (hc : A ⋖ B) (D : Subgroup (Section A B))
    (hd : ∀ h x, x ∈ D → sectionAction A B h x ∈ D) : D = ⊥ ∨ D = ⊤ := by
  have hchief := (covBy_iff_isChief A B).mp hc
  apply quotient_conjugation_irreducible_of_maximal ⊤ B.val A.val hc.le
    (by rw [normalizer_eq_top]) inferInstance
    (fun L hAL hLB hL => ?_) ((sectionAction A B).comp (⊤ : Subgroup H).subtype)
    (fun _ _ => rfl) D (fun h x hx => hd h x hx)
  have hnL : L.Normal := normalizer_eq_top_iff.mp (top_unique hL)
  rcases hchief.minimal L hnL hAL hLB.le with he | he
  · exact he
  · exact (hLB.ne he).elim

@[expose] noncomputable def binarySectionRepresentation [IsElementaryAbelian 2 (Section A B)] :
    Representation (ZMod 2) H (Additive (Section A B)) where
  toFun h := (sectionAction A B h).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext x
    change sectionAction A B 1 x.toMul = x.toMul
    rw [map_one]
    rfl
  map_mul' h k := by
    ext x
    change sectionAction A B (h * k) x.toMul = _
    rw [map_mul]
    rfl

omit [Finite H] in
theorem binarySection_irreducible [IsElementaryAbelian 2 (Section A B)] (hc : A ⋖ B) :
    Representation.IsIrreducible (binarySectionRepresentation A B) := by
  let _ := ((covBy_iff_isChief A B).mp hc).quotient_nontrivial B.val A.val
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, ?_⟩
  intro W
  let D : Subgroup (Section A B) := AddSubgroup.toSubgroup' W.toSubmodule.toAddSubgroup
  rcases chief_irreducible A B hc D (fun h x hx => W.apply_mem_toSubmodule h hx) with he | he
  · left
    apply bot_unique
    intro x hx
    have hh : x.toMul ∈ D := hx
    rwa [he] at hh
  · right
    apply top_unique
    intro x _
    have hh : x.toMul ∈ D := by rw [he]; trivial
    exact hh

omit [Finite H] in
theorem binarySection_trivial_iff [IsElementaryAbelian 2 (Section A B)] :
    binarySectionRepresentation A B = 1 ↔ IsCentral A B := by
  rw [isCentral_iff_action]
  constructor
  · intro h g x
    exact congrArg (fun ρ : Representation (ZMod 2) H (Additive (Section A B)) =>
      (ρ g (Additive.ofMul x)).toMul) h
  · intro h
    ext g x
    exact h g x.toMul

theorem binarySection_exists_faithful [IsElementaryAbelian 2 (Section A B)]
    [IsSimpleGroup (H ⧸ pCore 2 H)] (hc : A ⋖ B) (hn : ¬ IsCentral A B) :
    ∃ σ : Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive (Section A B)),
      Representation.IsIrreducible σ ∧ Function.Injective σ ∧
      σ.comp (QuotientGroup.mk' (pCore 2 H)) = binarySectionRepresentation A B := by
  let ρ := binarySectionRepresentation A B
  let _ := binarySection_irreducible A B hc
  have hk : pCore 2 H ≤ ρ.ker := normal_p_subgroup_le_ker ρ _ pCore_isPGroup
  let σ := quotientOfLEKer ρ (pCore 2 H) hk
  refine ⟨σ, (quotientOfLEKer_irreducible_iff ρ _ hk).mpr inferInstance, ?_, rfl⟩
  apply (MonoidHom.ker_eq_bot_iff σ).mp
  apply (inferInstance : σ.ker.Normal).eq_bot_or_eq_top.resolve_right
  intro he
  apply hn
  apply (binarySection_trivial_iff A B).mp
  apply MonoidHom.ext
  intro h
  exact (show QuotientGroup.mk' (pCore 2 H) h ∈ σ.ker from he ▸ mem_top _)
end NoncentralChiefRefinement

namespace NoncentralChiefRefinement
open scoped commutatorElement
variable {H : Type*} [Group H] [Finite H] (A B : NormalNode H)
theorem exists_moving_commutator [IsSimpleGroup (H ⧸ pCore 2 H)]
    (hc : A ⋖ B) (hp : IsPGroup 2 B.val) (hn : ¬ IsCentral A B)
    (a : H) (ha : a ∉ pCore 2 H) : ∃ b ∈ B.val, ⁅a, b⁆ ∉ A.val := by
  let _ := chief_elementary A B hc hp
  obtain ⟨σ, _, hf, hσ⟩ := binarySection_exists_faithful A B hc hn
  by_contra! hall
  apply ha
  apply (QuotientGroup.eq_one_iff a).mp
  apply hf
  rw [map_one]
  have he : σ (QuotientGroup.mk' (pCore 2 H) a) = binarySectionRepresentation A B a :=
    congrArg (fun ρ : Representation (ZMod 2) H (Additive (Section A B)) => ρ a) hσ
  change σ (QuotientGroup.mk' (pCore 2 H) a) = 1
  rw [he]
  ext x
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x.toMul
  change sectionAction A B a x.toMul = x.toMul
  rw [← hb, sectionAction_mk]
  apply QuotientGroup.eq_iff_div_mem.mpr
  change a * (b : H) * a⁻¹ / (b : H) ∈ A.val
  simpa only [commutatorElement_def, div_eq_mul_inv] using hall b b.property
end NoncentralChiefRefinement

namespace NoncentralChiefRefinement
variable {G : Type*} [Group G] (H : Subgroup G) (A B : NormalNode H)
private def fromMapped (B : NormalNode H) : (B.val.map H.subtype) ≃* B.val where
  toFun b := ⟨⟨b, map_subtype_le B.val b.property⟩,
    (mem_map_iff_mem H.subtype_injective).mp b.property⟩
  invFun b := ⟨b, mem_map_of_mem H.subtype b.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

noncomputable def ambientBinarySection [IsElementaryAbelian 2 (Section A B)] (hAB : A ≤ B) :
    BinaryConjugationSection H (B.val.map H.subtype) (A.val.map H.subtype)
      (binarySectionRepresentation A B) where
  section_le := map_subtype_le _
  kernel_le := map_mono hAB
  normalized := by
    have hh := B.val.le_normalizer_map H.subtype
    rw [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh
  coordinates := {
    toFun := fun b => Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk' (A.val.subgroupOf B.val) (fromMapped H B b)))
    map_one' := map_one ((QuotientGroup.mk' (A.val.subgroupOf B.val)).comp
      (fromMapped H B).toMonoidHom)
    map_mul' := fun _ _ => map_mul ((QuotientGroup.mk' (A.val.subgroupOf B.val)).comp
      (fromMapped H B).toMonoidHom) _ _ }
  onto := by
    intro x
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (A.val.subgroupOf B.val) x.toAdd.toMul
    exact ⟨(fromMapped H B).symm b, hb⟩
  kernel_eq := by
    ext b
    change QuotientGroup.mk' (A.val.subgroupOf B.val) (fromMapped H B b) = 1 ↔ _
    exact (QuotientGroup.eq_one_iff (fromMapped H B b)).trans
      (mem_map_iff_mem H.subtype_injective).symm
  equivariant _ _ := rfl
end NoncentralChiefRefinement
