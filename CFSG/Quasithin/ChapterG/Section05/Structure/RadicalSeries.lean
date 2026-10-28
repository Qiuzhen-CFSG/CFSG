module

public import CFSG.Quasithin.ChapterG.Section05.Structure.Defs
public import Theory.Representation.BinaryPermutationNaturalDuality
public import Theory.Representation.SimpleHeadQuotient
public import Theory.Representation.FirstCohomologyDuality.SimpleCover
public import Theory.Representation.CentralCoverSelfDualFlag

set_option maxHeartbeats 1000000

/-!
# The radical and chief series in G.5.3

The invariant dot product makes the even duad module self-dual, and transitivity
on the odd number of duads gives zero fixed space. A simple fixed-point-free
module maps trivially to either nontrivial perfect central cover, so the natural
four-space is the unique simple submodule of the core. Orthogonal complements
and the dimensions of the two literal quotients classify its invariant spaces.
Their strict flag is the series of intersections of maximal subrepresentations.

The only conditional input is the published `MiddleCoverData`, constructed by
the independent middle-cover argument. The fourth layer is identified using
`naturalCopy` and the actual perpendicular-complement vectors.

Source: Aschbacher--Smith, G.5.3(2)--(5), printed pp.344--345.
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation BinaryDuadModule
open Representation Representation.OneCohomology

namespace CFSG.Quasithin.ChapterG.Section05.Structure

open BinaryDuadStructure

noncomputable section

/-! The invariant dot product on the even core. -/

noncomputable def corePairing :
    LinearMap.BilinForm (ZMod 2) (core Duad) :=
  (dotProductEquiv (ZMod 2) Duad).toLinearMap.compl₁₂
    (core Duad).subtype (core Duad).subtype

theorem corePairing_apply (v w : core Duad) :
    corePairing v w = ∑ i, v.val i * w.val i := rfl

theorem corePairing_symm (v w : core Duad) :
    corePairing v w = corePairing w v := by
  exact dotProduct_comm v.val w.val

theorem corePairing_injective : Function.Injective corePairing := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  have hconst (i : Duad) : v.val i = v.val 0 := by
    let w : core Duad := ⟨Pi.single i 1 + Pi.single 0 1, by
      simp [mem_core, Finset.sum_add_distrib, CharTwo.add_self_eq_zero]⟩
    have h : corePairing v w = 0 := LinearMap.congr_fun hv w
    rw [corePairing_apply] at h
    change dotProduct v.val (Pi.single i 1 + Pi.single 0 1) = 0 at h
    simp only [dotProduct_add, dotProduct_single, mul_one] at h
    simpa only [CharTwo.neg_eq] using eq_neg_of_add_eq_zero_left h
  apply Subtype.ext
  apply Submodule.disjoint_def.mp
    (core_isCompl_constants Duad (by decide)).disjoint v.val v.property
  exact Submodule.mem_span_singleton.mpr ⟨v.val 0, funext fun i => by
    simpa only [Pi.smul_apply, allOne, smul_eq_mul, mul_one] using
      (hconst i).symm⟩

theorem corePairing_nondegenerate : corePairing.Nondegenerate := by
  constructor
  · intro v hv
    apply corePairing_injective
    exact LinearMap.ext (by simpa using hv)
  · intro v hv
    apply corePairing_injective
    exact LinearMap.ext (by
      simpa only [corePairing_symm, map_zero, LinearMap.zero_apply] using hv)

theorem corePairing_invariant (g : A6) (v w : core Duad) :
    corePairing (coreAction g v) w = corePairing v (coreAction g⁻¹ w) := by
  change (∑ i : Duad, v.val (g⁻¹ • i) * w.val i) =
    ∑ i : Duad, v.val i * w.val (g • i)
  simpa using Equiv.sum_comp (MulAction.toPerm g⁻¹)
    (fun i : Duad => v.val i * w.val (g • i))

/-- The literal even core is self-dual for its actual `A₆` action. -/
noncomputable def coreSelfDual : coreAction.Equiv coreAction.dual :=
  Representation.BinaryCoverSocle.selfDualOfPairing coreAction corePairing
    corePairing_injective corePairing_invariant

theorem coreSelfDual_equiv : Nonempty (coreAction.Equiv coreAction.dual) :=
  ⟨coreSelfDual⟩

/-! A fixed vector in the even core is constant, hence zero. -/

theorem core_fixed_eq_bot :
    fixed coreAction = (⊥ : Submodule (ZMod 2) (core Duad)) := by
  apply le_antisymm _ bot_le
  intro v hv
  have hconst (i : Duad) : v.val i = v.val 0 := by
    obtain ⟨g, hg⟩ := a6_duad_transitive i 0
    have h := congrArg (fun z : core Duad => z.val 0) (hv g)
    change v.val (g⁻¹ • (0 : Duad)) = v.val 0 at h
    rw [show g⁻¹ • (0 : Duad) = i from (inv_smul_eq_iff.mpr hg.symm)] at h
    exact h
  apply Subtype.ext
  apply Submodule.disjoint_def.mp
    (core_isCompl_constants Duad (by decide)).disjoint v.val v.property
  exact Submodule.mem_span_singleton.mpr ⟨v.val 0, funext fun i => by
    simpa only [Pi.smul_apply, allOne, smul_eq_mul, mul_one] using
      (hconst i).symm⟩

/-! The elementary one-dimensional-kernel cover calculation. -/

theorem cover_subrepresentation_cases
    {k H V W : Type*} [Field k] [Group H]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W]
    (σ : Representation k H V) (ρ : Representation k H W)
    (p : σ.IntertwiningMap ρ)
    (hp : Representation.OneCohomology.IsCover p)
    (hirr : ρ.IsIrreducible)
    (hker : Module.finrank k p.toLinearMap.ker = 1)
    (S : Subrepresentation σ) :
    S = ⊥ ∨ S = p.ker ∨ S = ⊤ := by
  let N : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule.map p.toLinearMap
    apply_mem_toSubmodule g := by
      rintro _ ⟨v, hv, rfl⟩
      refine ⟨σ g v, S.apply_mem_toSubmodule g hv, ?_⟩
      exact LinearMap.congr_fun (p.isIntertwining' g) v }
  have hNall := @IsSimpleOrder.eq_bot_or_eq_top
    (Subrepresentation ρ) _ _ hirr N
  rcases hNall with hN | hN
  · have hle : S ≤ p.ker := by
      intro v hv
      have hmem : p v ∈ N := ⟨v, hv, rfl⟩
      rw [hN] at hmem
      exact hmem
    by_cases hS : S = ⊥
    · exact Or.inl hS
    right; left
    apply Subrepresentation.toSubmodule_injective
    have hpos : 0 < Module.finrank k S.toSubmodule := by
      by_contra hh
      apply hS
      apply Subrepresentation.toSubmodule_injective
      exact Submodule.finrank_eq_zero.mp (by omega)
    have hmono := Submodule.finrank_mono hle
    have hk : Module.finrank k (IntertwiningMap.ker σ ρ p).toSubmodule = 1 := hker
    rw [hk] at hmono
    apply Submodule.eq_of_le_of_finrank_eq hle
    rw [hk]
    omega
  · right; right
    apply Subrepresentation.toSubmodule_injective
    apply Representation.OneCohomology.invariant_eq_top_of_cover_image_eq_top
      p hp S.toSubmodule (fun g _ hq => S.apply_mem_toSubmodule g hq)
    exact congrArg Subrepresentation.toSubmodule hN

/-! Literal quotient maps for the middle section. -/

noncomputable def middleQuotientMap :
    BinaryDuadModule.lineComplementSubrepresentation.toRepresentation.IntertwiningMap
      middleAction :=
  { toLinearMap := MiddleRelations.mkQ
    isIntertwining' := by intro g; rfl }

noncomputable def middleMap (d : MiddleCoverData) :
    BinaryDuadModule.lineComplementSubrepresentation.toRepresentation.IntertwiningMap
      d.oppositeAction :=
  d.projection.comp middleQuotientMap

theorem middle_projection_kernel_finrank (d : MiddleCoverData) :
    Module.finrank (ZMod 2) d.projection.toLinearMap.ker = 1 := by
  have h := d.projection.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr d.isCover.1, middleQuotient_finrank] at h
  rw [finrank_top, Theory.SpecificGroups.SymmetricSix.naturalModule_finrank] at h
  omega

theorem middle_subrepresentation_cases (d : MiddleCoverData)
    (S : Subrepresentation
      middleAction) :
    S = ⊥ ∨ S = d.projection.ker ∨ S = ⊤ := by
  exact cover_subrepresentation_cases _ _ d.projection d.isCover d.irreducible
    (middle_projection_kernel_finrank d) S

end
end CFSG.Quasithin.ChapterG.Section05.Structure

set_option backward.isDefEq.respectTransparency false

namespace CFSG.Quasithin.ChapterG.Section05.Structure
open Theory.SpecificGroups.SymmetricSix BinaryPermutation BinaryDuadModule
open Representation BinaryDuadStructure Representation.BinaryCoverSocle
noncomputable section

/-- The embedded natural four-space viewed inside the literal even core. -/
def coreNatural : Subrepresentation coreAction :=
  restrict naturalSubmodule coreSubrepresentation

/-- The line-complement nine-space viewed inside the literal even core. -/
def coreLines : Subrepresentation coreAction :=
  restrict lineComplementSubrepresentation coreSubrepresentation

theorem coreNatural_finrank : Module.finrank (ZMod 2) coreNatural.toSubmodule = 4 := by
  exact (Submodule.comapSubtypeEquivOfLe
    (natural_le_lines_le_core.1.trans natural_le_lines_le_core.2)).finrank_eq.trans
      layer_finranks.2.2

theorem coreLines_finrank : Module.finrank (ZMod 2) coreLines.toSubmodule = 9 := by
  exact (Submodule.comapSubtypeEquivOfLe natural_le_lines_le_core.2).finrank_eq.trans
    layer_finranks.2.1

theorem coreNatural_le_coreLines : coreNatural ≤ coreLines := by
  intro v hv
  exact natural_le_lines_le_core.1 hv

/-- The perpendicular-complement map with its codomain restricted to the even core. -/
def coreNaturalMap : Representation.IntertwiningMap naturalAction coreAction where
  toLinearMap := complementMap.codRestrict (core Duad) (fun v =>
    natural_le_lines_le_core.2 (natural_le_lines_le_core.1 ⟨v, rfl⟩))
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact complementMap_equivariant g.val v

theorem coreNaturalMap_range : coreNaturalMap.range = coreNatural := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨v, rfl⟩
  · intro v hv
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, Subtype.ext hw⟩

/-- The natural copy is simple for the actual restricted action. -/
theorem coreNatural_isAtom : IsAtom coreNatural := by
  refine ⟨?_, ?_⟩
  · intro h
    have hd := coreNatural_finrank
    rw [h, finrank_bottom] at hd
    omega
  intro S hS
  let P : Subrepresentation naturalAction := {
    toSubmodule := S.toSubmodule.comap coreNaturalMap.toLinearMap
    apply_mem_toSubmodule g v hv := by
      change coreNaturalMap (naturalAction g v) ∈ S
      rw [coreNaturalMap.isIntertwining]
      exact S.apply_mem_toSubmodule g hv }
  have hi := @IsSimpleOrder.eq_bot_or_eq_top _ _ _ alternatingNaturalAction_irreducible P
  rcases hi with hP | hP
  · apply le_antisymm _ bot_le
    intro v hv
    have hvC : v ∈ coreNaturalMap.range := coreNaturalMap_range ▸ hS.le hv
    obtain ⟨w, rfl⟩ := hvC
    have hp : w ∈ P := hv
    rw [hP] at hp
    change w = 0 at hp
    change coreNaturalMap w = 0
    simp only [hp, map_zero]
  · exfalso
    apply hS.ne
    apply le_antisymm hS.le
    rw [← coreNaturalMap_range]
    rintro _ ⟨v, rfl⟩
    exact (show v ∈ P from hP ▸ Submodule.mem_top)

/-- Every restricted submodule of the core has zero fixed space. -/
theorem core_submodule_fixed_eq_bot (S : Subrepresentation coreAction) :
    OneCohomology.fixed S.toRepresentation = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  have h : v.val ∈ OneCohomology.fixed coreAction := by
    intro g
    exact congrArg Subtype.val (hv g)
  rw [core_fixed_eq_bot] at h
  exact Subtype.ext h

def coreQuotientMap : coreAction.IntertwiningMap coreQuotientAction where
  toLinearMap := CoreRelations.mkQ
  isIntertwining' _ := rfl

theorem core_projection_kernel_finrank :
    Module.finrank (ZMod 2) coreNaturalProjection.toLinearMap.ker = 1 := by
  have h := coreNaturalProjection.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr coreNaturalProjection_isCover.1,
    finrank_top, naturalModule_finrank] at h
  have hd : Module.finrank (ZMod 2) CoreQuotient = 5 :=
    quotient_finranks.1
  omega

/-- The natural four-space is the unique simple submodule of the core. -/
theorem core_atom_eq_natural (d : MiddleCoverData)
    (S : Subrepresentation coreAction) (hS : IsAtom S) : S = coreNatural := by
  let : IsIrreducible S.toRepresentation :=
    (Subrepresentation.irreducible_iff_isAtom S).mpr hS
  let : IsIrreducible naturalAction := alternatingNaturalAction_irreducible
  let f : S.toRepresentation.IntertwiningMap coreQuotientAction := {
    toLinearMap := CoreRelations.mkQ.comp S.toSubmodule.subtype
    isIntertwining' _ := rfl }
  have hker : coreNaturalProjection.toLinearMap.ker ≠ ⊥ := by
    intro he
    have := core_projection_kernel_finrank
    rw [he, finrank_bot] at this
    omega
  have hf : f = 0 := simple_map_to_cover_eq_zero
    coreNaturalProjection coreNaturalProjection_isCover hker f
    (core_submodule_fixed_eq_bot S)
  have hSD : S ≤ coreLines := by
    intro v hv
    have hz := congrArg (fun q : S.toRepresentation.IntertwiningMap coreQuotientAction =>
      q ⟨v, hv⟩) hf
    exact (Submodule.Quotient.mk_eq_zero CoreRelations).mp hz
  let f' : S.toRepresentation.IntertwiningMap middleAction := {
    toLinearMap := MiddleRelations.mkQ.comp
      ((core Duad).subtype.comp S.toSubmodule.subtype |>.codRestrict lineComplementSpan
        (fun v => hSD v.property))
    isIntertwining' _ := rfl }
  let : IsIrreducible d.oppositeAction := d.irreducible
  have hker' : d.projection.toLinearMap.ker ≠ ⊥ := by
    intro he
    have := middle_projection_kernel_finrank d
    rw [he, finrank_bot] at this
    omega
  have hf' : f' = 0 := simple_map_to_cover_eq_zero d.projection d.isCover hker' f'
    (core_submodule_fixed_eq_bot S)
  have hSC : S ≤ coreNatural := by
    intro v hv
    have hz := congrArg (fun q : S.toRepresentation.IntertwiningMap middleAction =>
      q ⟨v, hv⟩) hf'
    exact (Submodule.Quotient.mk_eq_zero MiddleRelations).mp hz
  rcases eq_or_lt_of_le hSC with he | hl
  · exact he
  · exact False.elim (hS.1 (coreNatural_isAtom.2 S hl))

/-- The actual natural copy lies in every nonzero invariant subspace of the core. -/
theorem coreNatural_le_of_ne_bot (d : MiddleCoverData)
    (S : Subrepresentation coreAction) (hS : S ≠ ⊥) : coreNatural ≤ S := by
  obtain ⟨A, hA, hAS⟩ := (eq_bot_or_exists_atom_le S).resolve_left hS
  exact core_atom_eq_natural d A hA ▸ hAS

end
end CFSG.Quasithin.ChapterG.Section05.Structure

namespace CFSG.Quasithin.ChapterG.Section05.Structure
open Theory.SpecificGroups.SymmetricSix BinaryPermutation BinaryDuadModule
open Representation BinaryDuadStructure Representation.BinaryCoverSocle
noncomputable section

/-- Dimensions in the literal interval from the natural copy to the line span. -/
theorem core_middle_interval_finrank (d : MiddleCoverData)
    (S : Subrepresentation coreAction) (hCS : coreNatural ≤ S) (hSD : S ≤ coreLines) :
    Module.finrank (ZMod 2) S.toSubmodule = 4 ∨
    Module.finrank (ZMod 2) S.toSubmodule = 5 ∨
    Module.finrank (ZMod 2) S.toSubmodule = 9 := by
  let f : S.toRepresentation.IntertwiningMap middleAction := {
    toLinearMap := MiddleRelations.mkQ.comp
      ((core Duad).subtype.comp S.toSubmodule.subtype |>.codRestrict lineComplementSpan
        (fun v => hSD v.property))
    isIntertwining' _ := rfl }
  have hk : f.toLinearMap.ker = coreNatural.toSubmodule.comap S.toSubmodule.subtype := by
    ext v
    exact Submodule.Quotient.mk_eq_zero MiddleRelations
  have hdim := f.toLinearMap.finrank_range_add_finrank_ker
  rw [hk, (Submodule.comapSubtypeEquivOfLe hCS).finrank_eq, coreNatural_finrank] at hdim
  have hc := middle_subrepresentation_cases d f.range
  rcases hc with hc | hc | hc
  · have hh : Module.finrank (ZMod 2) f.toLinearMap.range = 0 := by
      change Module.finrank (ZMod 2) f.range.toSubmodule = 0
      rw [hc]
      exact finrank_bot _ _
    omega
  · have hh : Module.finrank (ZMod 2) f.toLinearMap.range = 1 := by
      change Module.finrank (ZMod 2) f.range.toSubmodule = 1
      rw [hc]
      exact middle_projection_kernel_finrank d
    omega
  · have hh : Module.finrank (ZMod 2) f.toLinearMap.range = 5 := by
      change Module.finrank (ZMod 2) f.range.toSubmodule = 5
      rw [hc]
      exact (finrank_top _ _).trans middleQuotient_finrank
    omega

/-- Dimensions in the literal interval from the line span to the whole core. -/
theorem core_upper_interval_finrank
    (S : Subrepresentation coreAction) (hDS : coreLines ≤ S) :
    Module.finrank (ZMod 2) S.toSubmodule = 9 ∨
    Module.finrank (ZMod 2) S.toSubmodule = 10 ∨
    Module.finrank (ZMod 2) S.toSubmodule = 14 := by
  let f : S.toRepresentation.IntertwiningMap coreQuotientAction := {
    toLinearMap := CoreRelations.mkQ.comp S.toSubmodule.subtype
    isIntertwining' _ := rfl }
  have hk : f.toLinearMap.ker = coreLines.toSubmodule.comap S.toSubmodule.subtype := by
    ext v
    exact Submodule.Quotient.mk_eq_zero CoreRelations
  have hdim := f.toLinearMap.finrank_range_add_finrank_ker
  rw [hk, (Submodule.comapSubtypeEquivOfLe hDS).finrank_eq, coreLines_finrank] at hdim
  have hc := cover_subrepresentation_cases coreQuotientAction naturalAction
    coreNaturalProjection coreNaturalProjection_isCover alternatingNaturalAction_irreducible
    core_projection_kernel_finrank f.range
  rcases hc with hc | hc | hc
  · have hh : Module.finrank (ZMod 2) f.toLinearMap.range = 0 := by
      change Module.finrank (ZMod 2) f.range.toSubmodule = 0
      rw [hc]
      exact finrank_bot _ _
    omega
  · have hh : Module.finrank (ZMod 2) f.toLinearMap.range = 1 := by
      change Module.finrank (ZMod 2) f.range.toSubmodule = 1
      rw [hc]
      exact core_projection_kernel_finrank
    omega
  · have hh : Module.finrank (ZMod 2) f.toLinearMap.range = 5 := by
      change Module.finrank (ZMod 2) f.range.toSubmodule = 5
      rw [hc]
      exact (finrank_top _ _).trans quotient_finranks.1
    omega

/-- All invariant subspaces of the even duad module, conditionally on the
published middle covering. -/
theorem core_subrepresentation_cases (d : MiddleCoverData)
    (S : Subrepresentation coreAction) :
    S = ⊥ ∨ S = coreNatural ∨ S = perp coreSelfDual coreLines ∨
      S = coreLines ∨ S = perp coreSelfDual coreNatural ∨ S = ⊤ := by
  apply Representation.SelfDualFiveFlag.cases_of_rank_data
    (fun S : Subrepresentation coreAction => Module.finrank (ZMod 2) S.toSubmodule)
    (fun _ _ h => Submodule.finrank_lt_finrank_of_lt h)
    (finrank_bot _ _) ((finrank_top _ _).trans core_finrank)
    (fun S T => Submodule.finrank_sup_add_finrank_inf_eq S.toSubmodule T.toSubmodule)
    (perp coreSelfDual) (perp_antitone coreSelfDual)
    (perp_perp coreSelfDual corePairing_symm)
    (fun S => (perp_finrank coreSelfDual S).trans core_finrank)
    coreNatural coreLines coreNatural_finrank coreLines_finrank coreNatural_le_coreLines
    (coreNatural_le_of_ne_bot d) (core_middle_interval_finrank d)
    core_upper_interval_finrank

end
end CFSG.Quasithin.ChapterG.Section05.Structure

namespace CFSG.Quasithin.ChapterG.Section05.Structure
open Theory.SpecificGroups.SymmetricSix BinaryPermutation BinaryDuadModule
open Representation BinaryDuadStructure Representation.BinaryCoverSocle
noncomputable section

def coreMiddleMap (d : MiddleCoverData) :
    coreLines.toRepresentation.IntertwiningMap d.oppositeAction :=
  d.projection.comp {
    toLinearMap := MiddleRelations.mkQ.comp
      ((core Duad).subtype.comp coreLines.toSubmodule.subtype |>.codRestrict lineComplementSpan
        (fun v => v.property))
    isIntertwining' _ := rfl }

theorem coreMiddleMap_surjective (d : MiddleCoverData) :
    Function.Surjective (coreMiddleMap d) := by
  intro v
  obtain ⟨w, rfl⟩ := d.isCover.1 v
  obtain ⟨u, rfl⟩ := MiddleRelations.mkQ_surjective w
  exact ⟨⟨⟨u.val, lineComplementSpan_le_core u.property⟩, u.property⟩, rfl⟩

theorem coreLines_perp_finrank :
    Module.finrank (ZMod 2) (perp coreSelfDual coreLines).toSubmodule = 5 := by
  have h := perp_finrank coreSelfDual coreLines
  rw [coreLines_finrank, core_finrank] at h
  omega

theorem coreNatural_perp_finrank :
    Module.finrank (ZMod 2) (perp coreSelfDual coreNatural).toSubmodule = 10 := by
  have h := perp_finrank coreSelfDual coreNatural
  rw [coreNatural_finrank, core_finrank] at h
  omega

/-- The middle head kernel realizes the five-space required for the strict flag. -/
theorem coreMiddleMap_kernel (d : MiddleCoverData) :
    embed coreLines (coreMiddleMap d).ker = perp coreSelfDual coreLines := by
  have hd : Module.finrank (ZMod 2) (coreMiddleMap d).ker.toSubmodule = 5 := by
    change Module.finrank (ZMod 2) (coreMiddleMap d).toLinearMap.ker = 5
    have h := (coreMiddleMap d).toLinearMap.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (coreMiddleMap_surjective d), finrank_top,
      naturalModule_finrank, coreLines_finrank] at h
    omega
  have hr : Module.finrank (ZMod 2) (embed coreLines (coreMiddleMap d).ker).toSubmodule = 5 :=
    (embed_finrank coreLines (coreMiddleMap d).ker).trans hd
  rcases core_subrepresentation_cases d (embed coreLines (coreMiddleMap d).ker) with
    he | he | he | he | he | he
  · rw [he, finrank_bottom] at hr; omega
  · rw [he, coreNatural_finrank] at hr; omega
  · exact he
  · rw [he, coreLines_finrank] at hr; omega
  · rw [he, coreNatural_perp_finrank] at hr; omega
  · rw [he, finrank_whole, core_finrank] at hr; omega

theorem coreLines_perp_le (d : MiddleCoverData) : perp coreSelfDual coreLines ≤ coreLines := by
  rw [← coreMiddleMap_kernel d]
  exact embed_le _ _

theorem core_proper_le_natural_perp (d : MiddleCoverData)
    (S : Subrepresentation coreAction) (hS : S ≠ ⊤) : S ≤ perp coreSelfDual coreNatural := by
  have hn : perp coreSelfDual S ≠ ⊥ := by
    intro he
    have h := perp_finrank coreSelfDual S
    rw [he, finrank_bottom, core_finrank, add_zero] at h
    apply hS
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.eq_top_of_finrank_eq (h.trans core_finrank.symm)
  have h := perp_antitone coreSelfDual (coreNatural_le_of_ne_bot d _ hn)
  simpa only [perp_perp coreSelfDual corePairing_symm] using h

def coreFlag : Fin 6 → Subrepresentation coreAction :=
  ![⊤, perp coreSelfDual coreNatural, coreLines, perp coreSelfDual coreLines, coreNatural, ⊥]

theorem coreFlag_strictAnti (d : MiddleCoverData) : StrictAnti coreFlag := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  have lt_of_rank {S T : Subrepresentation coreAction} (h : S ≤ T)
      (hd : Module.finrank (ZMod 2) S.toSubmodule < Module.finrank (ZMod 2) T.toSubmodule) :
      S < T := lt_of_le_of_ne h (by intro he; rw [he] at hd; omega)
  have hD : coreLines ≠ ⊤ := by
    intro he
    have h := coreLines_finrank
    rw [he, finrank_whole, core_finrank] at h
    omega
  have hK : perp coreSelfDual coreLines ≠ ⊥ := by
    intro he
    have h := coreLines_perp_finrank
    rw [he, finrank_bottom] at h
    omega
  fin_cases i
  · apply lt_of_rank le_top
    change Module.finrank (ZMod 2) (perp coreSelfDual coreNatural).toSubmodule <
      Module.finrank (ZMod 2) (⊤ : Subrepresentation coreAction).toSubmodule
    rw [coreNatural_perp_finrank, finrank_whole, core_finrank]
    decide
  · apply lt_of_rank (core_proper_le_natural_perp d coreLines hD)
    rw [coreLines_finrank, coreNatural_perp_finrank]
    decide
  · apply lt_of_rank (coreLines_perp_le d)
    rw [coreLines_perp_finrank, coreLines_finrank]
    decide
  · apply lt_of_rank (coreNatural_le_of_ne_bot d _ hK)
    rw [coreNatural_finrank, coreLines_perp_finrank]
    decide
  · apply lt_of_rank bot_le
    change Module.finrank (ZMod 2) (⊥ : Subrepresentation coreAction).toSubmodule <
      Module.finrank (ZMod 2) coreNatural.toSubmodule
    rw [finrank_bottom, coreNatural_finrank]
    decide

/-- The six source spaces as subrepresentations of the original permutation module. -/
def sourceFlag (i : Fin 6) : Subrepresentation action :=
  embed coreSubrepresentation (coreFlag i)

theorem sourceFlag_zero : sourceFlag 0 = coreSubrepresentation := embed_top _
theorem sourceFlag_two : sourceFlag 2 = lineComplementSubrepresentation :=
  embed_restrict _ _ lineComplementSpan_le_core
theorem sourceFlag_four : sourceFlag 4 = naturalSubmodule :=
  embed_restrict _ _ (natural_le_lines_le_core.1.trans natural_le_lines_le_core.2)
theorem sourceFlag_five : sourceFlag 5 = ⊥ := embed_bot _

theorem sourceFlag_strictAnti (d : MiddleCoverData) : StrictAnti sourceFlag := by
  intro i j hij
  have h := coreFlag_strictAnti d hij
  exact ⟨embed_mono _ h.le, fun hji => h.not_ge ((embed_le_iff _ _ _).mp hji)⟩

theorem sourceFlag_exhaustive (d : MiddleCoverData) (S : Subrepresentation action)
    (hS : S ≤ sourceFlag 0) : ∃ i, S = sourceFlag i := by
  rw [sourceFlag_zero] at hS
  have he := embed_restrict S coreSubrepresentation hS
  rcases core_subrepresentation_cases d (restrict S coreSubrepresentation) with
    h | h | h | h | h | h
  · exact ⟨5, he.symm.trans (congrArg (embed coreSubrepresentation) h)⟩
  · exact ⟨4, he.symm.trans (congrArg (embed coreSubrepresentation) h)⟩
  · exact ⟨3, he.symm.trans (congrArg (embed coreSubrepresentation) h)⟩
  · exact ⟨2, he.symm.trans (congrArg (embed coreSubrepresentation) h)⟩
  · exact ⟨1, he.symm.trans (congrArg (embed coreSubrepresentation) h)⟩
  · exact ⟨0, he.symm.trans (congrArg (embed coreSubrepresentation) h)⟩

theorem radicalLayer_eq_sourceFlag (d : MiddleCoverData) (n : ℕ) (hn : n < 6) :
    radicalLayer n = sourceFlag ⟨n, hn⟩ := by
  induction n with
  | zero => exact sourceFlag_zero.symm
  | succ n ih =>
    change ModuleRadical.within (radicalLayer n) = _
    rw [ih (by omega)]
    exact within_flag sourceFlag (sourceFlag_strictAnti d) (sourceFlag_exhaustive d)
      ⟨n, by omega⟩

/-- G.5.3(3): the second literal radical is the span of the line complements. -/
theorem radicalLayer_two (d : MiddleCoverData) :
    radicalLayer 2 = lineComplementSubrepresentation :=
  (radicalLayer_eq_sourceFlag d 2 (by decide)).trans sourceFlag_two

/-- G.5.3(4): the fourth literal radical is the perpendicular-complement copy. -/
theorem radicalLayer_four (d : MiddleCoverData) : radicalLayer 4 = naturalSubmodule :=
  (radicalLayer_eq_sourceFlag d 4 (by decide)).trans sourceFlag_four

theorem radicalLayer_five (d : MiddleCoverData) : radicalLayer 5 = ⊥ :=
  (radicalLayer_eq_sourceFlag d 5 (by decide)).trans sourceFlag_five

/-- G.5.3(2): every adjacent pair is a strict cover in the invariant-subspace lattice. -/
theorem radicalLayer_covBy (d : MiddleCoverData) (i : ℕ) (hi : i < 5) :
    CovBy (radicalLayer (i + 1)) (radicalLayer i) := by
  rw [radicalLayer_eq_sourceFlag d (i + 1) (by omega),
    radicalLayer_eq_sourceFlag d i (by omega)]
  exact flag_covBy sourceFlag (sourceFlag_strictAnti d) (sourceFlag_exhaustive d) ⟨i, hi⟩

/-- The source's vector description of the fourth radical. -/
theorem mem_radicalLayer_four (d : MiddleCoverData) (u : U) :
    u ∈ radicalLayer 4 ↔ u = 0 ∨ ∃ x : Omega, u = pointComplement x := by
  rw [radicalLayer_four d]
  exact mem_complementSubrepresentation u

end
end CFSG.Quasithin.ChapterG.Section05.Structure

namespace CFSG.Quasithin.ChapterG.Section05.Structure
open Theory.SpecificGroups.SymmetricSix Representation

/-- The fourth radical carries the marked natural action through `naturalCopy`. -/
theorem radicalLayer_four_equiv (d : MiddleCoverData) :
    Nonempty (Representation.Equiv naturalAction (radicalLayer 4).toRepresentation) := by
  rw [radicalLayer_four d]
  exact ⟨Representation.Equiv.mk naturalCopy
    (fun g => LinearMap.ext (naturalCopy_equivariant g))⟩

/-- The radical and chief-series part of G.5.3, with only the independent
published middle-cover input left conditional. -/
theorem radical_chief_series (d : MiddleCoverData) :
    radicalLayer 2 = BinaryDuadModule.lineComplementSubrepresentation ∧
    radicalLayer 4 = naturalSubmodule ∧ radicalLayer 5 = ⊥ ∧
    (∀ i < 5, CovBy (radicalLayer (i + 1)) (radicalLayer i)) ∧
    Nonempty (Representation.Equiv naturalAction (radicalLayer 4).toRepresentation) :=
  ⟨radicalLayer_two d, radicalLayer_four d, radicalLayer_five d,
    radicalLayer_covBy d, radicalLayer_four_equiv d⟩

end CFSG.Quasithin.ChapterG.Section05.Structure
