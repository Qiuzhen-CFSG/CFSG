module

public import CFSG.Quasithin.ChapterG.Section03.CoreFreeBlockModels
public import CFSG.Quasithin.ChapterG.Section03.Decomposition.InternalProducts
public import Theory.Representation.BinaryTransvectionGroups.TransvectionGenerators

/-!
# The fixed complement of a core-free binary root decomposition

Faithful full block actions lift a dimension-sized transvection generating
family to the original space. The common fixed-space codimension is therefore
at most the sum of the block dimensions. The independent full-action blocks
have no common fixed vector, so their literal span complements the fixed space
of their literal generated subgroup.

This proves the splitting calculation in Aschbacher--Smith 12.7.18,
printed p.845, without a spanning assumption on the original root orbit.
-/

public noncomputable section
open Subgroup BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {H : Subgroup (BinaryLinear.GL V)} [Finite H] {Δ : Set V}

omit [FiniteDimensional (ZMod 2) V] in
private theorem conjugate_isTransvection (g : BinaryLinear.GL V)
    {t : BinaryLinear.GL V} (ht : BinaryLinear.OuterCyclic.IsTransvection t) :
    BinaryLinear.OuterCyclic.IsTransvection (g * t * g⁻¹) := by
  obtain ⟨x, f, hx, hf, hfx, rfl⟩ := ht
  refine ⟨g x, f.comp g.symm.toLinearMap, ?_, ?_, ?_, ?_⟩
  · exact fun hz => hx (g.injective (by simp [hz]))
  · intro hz
    apply hf
    ext v
    have h := congrArg (fun F : V →ₗ[ZMod 2] ZMod 2 => F (g v)) hz
    simpa using h
  · simpa using hfx
  · ext v
    simp [BinaryLinear.transvection]

omit [FiniteDimensional (ZMod 2) V] in
private theorem block_transvection_seed
    (h : Hypotheses H Δ) (hcore : pCore 2 H = ⊥) (i : OrbitBlock H Δ) :
    ∃ s : blockGroup H Δ i,
      BinaryLinear.OuterCyclic.IsTransvection s.val ∧
      BinaryLinear.OuterCyclic.IsTransvection (spanAction H i.val s) := by
  obtain ⟨x, hxΔ, hi⟩ := i.property
  have hx : x ∈ i.val := hi ▸ MulAction.mem_orbit_self x
  have hx0 := h.nonzero x hxΔ
  have hc := Reduced.source_large_roots h hxΔ
  let : Nontrivial (rootGroup H x) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : rootGroup H x)
  obtain ⟨_, f, hfx, he⟩ := (mem_rootGroup_iff hx0).mp a.property
  have hf : f ≠ 0 := by
    intro hz
    apply ha
    apply Subtype.ext
    rw [he]
    ext v
    simp [BinaryLinear.transvection, hz]
  let s : blockGroup H Δ i := ⟨a.val, rootGroup_le_generated H hx a.property⟩
  let W := blockSpace H Δ i
  let xW : W := ⟨x, Submodule.subset_span hx⟩
  have hrestrict : spanAction H i.val s =
      BinaryLinear.transvection xW (f.comp W.subtype) hfx := by
    ext w
    change a.val w = (w : V) + f w • x
    rw [he]
    rfl
  have hfW : f.comp W.subtype ≠ 0 := by
    intro hz
    have hs : spanAction H i.val s = 1 := by
      rw [hrestrict]
      apply LinearEquiv.ext
      intro w
      change w + (f.comp W.subtype) w • xW = w
      simp [hz]
    have hs1 := Reduced.blockAction_injective h hcore i (hs.trans (map_one _).symm)
    have ha1 : a.val = 1 := congrArg (fun u : blockGroup H Δ i => u.val) hs1
    exact ha (Subtype.ext ha1)
  exact ⟨s, ⟨x, f, hx0, hf, hfx, he⟩,
    ⟨xW, f.comp W.subtype, fun hz => hx0 (congrArg Subtype.val hz), hfW, hfx, hrestrict⟩⟩

private theorem block_fixed_codimension_le
    (h : Hypotheses H Δ) (hcore : pCore 2 H = ⊥) (hf : FullAction H Δ)
    (i : OrbitBlock H Δ) :
    Module.finrank (ZMod 2) (V ⧸ fixedSpace (blockGroup H Δ i)) ≤
      Module.finrank (ZMod 2) (blockSpace H Δ i) := by
  classical
  let e : blockGroup H Δ i ≃* BinaryLinear.GL (blockSpace H Δ i) :=
    MulEquiv.ofBijective (spanAction H i.val)
    ⟨Reduced.blockAction_injective h hcore i, hf.surjective i⟩
  obtain ⟨s, hs, hse⟩ := block_transvection_seed h hcore i
  have hlift (t : BinaryLinear.GL (blockSpace H Δ i))
      (ht : BinaryLinear.OuterCyclic.IsTransvection t) :
      BinaryLinear.OuterCyclic.IsTransvection ((e.symm t).val) := by
    obtain ⟨c, hc⟩ := BinaryLinear.OuterCyclic.transvections_conjugate hse ht
    let b := e.symm c
    have he : e (b * s * b⁻¹) = t := by
      change e b * e s * (e b)⁻¹ = t
      rw [show e b = c from e.apply_symm_apply c]
      exact hc
    have hu : b * s * b⁻¹ = e.symm t := e.injective (he.trans (e.apply_symm_apply t).symm)
    rw [← hu]
    exact conjugate_isTransvection b.val hs
  obtain ⟨t, ht, hgen⟩ := BinaryLinear.exists_transvection_generators (hf.dimension_ge_two i)
  let f := (blockGroup H Δ i).subtype.comp e.symm.toMonoidHom
  have hclosure : Subgroup.closure (Set.range (fun j => f (t j))) = blockGroup H Δ i := by
    calc
      Subgroup.closure (Set.range (fun j => f (t j))) =
          (Subgroup.closure (Set.range t)).map f := by
        rw [MonoidHom.map_closure, Set.range_comp']
      _ = blockGroup H Δ i := by
        rw [hgen]
        ext g
        constructor
        · rintro ⟨q, _, rfl⟩
          exact (e.symm q).property
        · intro hg
          refine ⟨e ⟨g, hg⟩, Subgroup.mem_top _, ?_⟩
          change (e.symm (e ⟨g, hg⟩)).val = g
          rw [e.symm_apply_apply]
  have hb := BinaryLinear.fixedSpace_codimension_le_generators
    (fun j => f (t j)) (fun j => hlift (t j) (ht j))
  rw [← hclosure]
  simpa only [Fintype.card_fin] using hb

/-- Each original block has its actual common fixed space as a complement. -/
theorem core_free_block_isCompl_fixedSpace
    (h : Hypotheses H Δ) (hcore : pCore 2 H = ⊥) (hf : FullAction H Δ)
    (i : OrbitBlock H Δ) :
    IsCompl (blockSpace H Δ i) (fixedSpace (blockGroup H Δ i)) := by
  have hd : Disjoint (blockSpace H Δ i) (fixedSpace (blockGroup H Δ i)) := by
    apply Submodule.disjoint_def.mpr
    intro v hv hfix
    exact congrArg Subtype.val
      (DecompositionProof.block_fixed_zero hf i ⟨v, hv⟩ hfix)
  have hb := block_fixed_codimension_le h hcore hf i
  have hdim := (fixedSpace (blockGroup H Δ i)).finrank_quotient_add_finrank
  exact ⟨hd, codisjoint_iff.mpr (Submodule.eq_top_of_disjoint _ _ (by omega) hd)⟩

/-- The original root span complements the actual common fixed space of the
root-generated subgroup, with no spanning premise on the ambient module. -/
theorem core_free_span_isCompl_fixedSpace
    (h : Hypotheses H Δ) (hcore : pCore 2 H = ⊥) (hf : FullAction H Δ)
    (hd : Decomposition H Δ) :
    IsCompl (Submodule.span (ZMod 2) Δ) (fixedSpace (generated H Δ)) := by
  classical
  let : Finite (OrbitBlock H Δ) := DecompositionProof.finite_blocks h
  let : Fintype (OrbitBlock H Δ) := Fintype.ofFinite _
  obtain ⟨e, he⟩ := hd.space_equiv
  have heval (u : ∀ i : OrbitBlock H Δ, blockSpace H Δ i) :
      (e u : V) = ∑ i, (u i : V) := by
    have hu := congrArg (fun w => (e w : V)) (Finset.univ_sum_single u)
    simp only [map_sum, Submodule.coe_sum] at hu
    rw [← hu]
    apply Finset.sum_congr rfl
    intro i _
    exact he i (u i)
  have hdis : Disjoint (Submodule.span (ZMod 2) Δ) (fixedSpace (generated H Δ)) := by
    apply Submodule.disjoint_def.mpr
    intro v hv hfix
    let u := e.symm ⟨v, hv⟩
    have hvsum : ∑ i, (u i : V) = v := by
      rw [← heval]
      exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)
    have hu0 (i : OrbitBlock H Δ) : u i = 0 := by
      apply DecompositionProof.block_fixed_zero hf i
      intro g hg
      have hs : ∑ j, (g (u j) - (u j : V)) = 0 := by
        rw [Finset.sum_sub_distrib, ← map_sum, hvsum,
          hfix g (blockGroup_le_generated h i hg), sub_self]
      have hsingle : ∑ j, (g (u j) - (u j : V)) = g (u i) - (u i : V) := by
        apply Finset.sum_eq_single i
        · intro j _ hji
          rw [hd.cross_fix i j hji.symm g hg (u j) (u j).property, sub_self]
        · simp
      exact sub_eq_zero.mp (hsingle.symm.trans hs)
    rw [← hvsum]
    simp [hu0]
  have hfixed : fixedSpace (generated H Δ) =
      ⨅ i : OrbitBlock H Δ, fixedSpace (blockGroup H Δ i) := by
    ext v
    constructor
    · intro hv
      exact (Submodule.mem_iInf _).mpr fun i g hg => hv g (blockGroup_le_generated h i hg)
    · intro hv
      have hle : generated H Δ ≤ MulAction.stabilizer (BinaryLinear.GL V) v := by
        rw [← hd.group_join]
        exact iSup_le fun i g hg => (Submodule.mem_iInf _).mp hv i g hg
      exact fun g hg => hle hg
  have hbound : Module.finrank (ZMod 2) (V ⧸ fixedSpace (generated H Δ)) ≤
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) Δ) := by
    rw [hfixed]
    calc
      _ ≤ ∑ i : OrbitBlock H Δ,
          Module.finrank (ZMod 2) (V ⧸ fixedSpace (blockGroup H Δ i)) :=
        Submodule.finrank_quotient_iInf_le_sum _
      _ ≤ ∑ i : OrbitBlock H Δ, Module.finrank (ZMod 2) (blockSpace H Δ i) :=
        Finset.sum_le_sum fun i _ => block_fixed_codimension_le h hcore hf i
      _ = Module.finrank (ZMod 2) (Submodule.span (ZMod 2) Δ) := by
        rw [← Module.finrank_pi_fintype]
        exact e.finrank_eq
  have hdim := (fixedSpace (generated H Δ)).finrank_quotient_add_finrank
  exact ⟨hdis, codisjoint_iff.mpr (Submodule.eq_top_of_disjoint _ _ (by omega) hdis)⟩

end CFSG.Quasithin.ChapterG.Section03
