module
public import CFSG.Quasithin.ChapterG.Section05.Structure.RadicalSeries
public import CFSG.Quasithin.ChapterG.Section05.Structure.OppositeCover
public import Theory.Representation.BinaryDuadStructure.QuotientClassification
public import Theory.Representation.BinaryPermutation.SixPairsQuadratic
public import Theory.Representation.BinaryPermutationSixCover.Universal
public import Theory.Representation.BinaryPermutation.SixPolar
public import Theory.Representation.BinaryDuadModule.SmallDisplacement

/-!
# Marked nonzero quotients of the fifteen-pair permutation module

Full movement makes the map from the even duad core surjective. Its proved
invariant-subspace flag then gives either the marked natural four-space or
an equivariant quotient onto the five-dimensional perfect cover. The latter
is identified with the actual six-letter augmentation core, including its
constant line, using the universal perfect-cover map and equal dimensions.
The possible quotient dimensions are 4, 5, 9, 10 and 14.

The final comparison retains any supplied faithful six-letter actor marking.
Its original U_L/V application is in Chapter13 Section08, OriginalWholeComparison.
Source: Aschbacher--Smith, G.5.3, printed pp.344--345, and the proof of
13.8.33, printed p.967. No small-displacement premise is assumed here.
-/

public section
open Representation BinaryPermutation BinaryDuadModule BinaryDuadStructure
open Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.ChapterG.Section05.Structure

private theorem factor_map
    {X Y Z : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] [AddCommGroup Z] [Module (ZMod 2) Z]
    {α : Representation (ZMod 2) A6 X} {β : Representation (ZMod 2) A6 Y}
    {γ : Representation (ZMod 2) A6 Z}
    (f : α.IntertwiningMap β) (hf : Function.Surjective f)
    (g : α.IntertwiningMap γ) (hg : Function.Surjective g)
    (hk : f.ker ≤ g.ker) : ∃ q : β.IntertwiningMap γ, Function.Surjective q := by
  let E := f.toLinearMap.quotKerEquivOfSurjective hf
  let q := (f.toLinearMap.ker.liftQ g.toLinearMap hk).comp E.symm.toLinearMap
  have he (x : X) : q (f x) = g x := by
    change (f.toLinearMap.ker.liftQ g.toLinearMap hk)
      ((f.toLinearMap.quotKerEquivOfSurjective hf).symm (f.toLinearMap x)) = g x
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    rfl
  refine ⟨q.intertwiningMap_of_isIntertwiningMap _ _ ?_, ?_⟩
  · intro a y
    obtain ⟨x,rfl⟩ := hf y
    rw [← f.isIntertwining, he, he, g.isIntertwining]
  · intro z
    obtain ⟨x,rfl⟩ := hg z
    exact ⟨f x,he x⟩

/-- The exact nonzero quotient alternatives for the generated duad core. -/
theorem duad_core_quotient_comparison
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Nontrivial X]
    (ρ : Representation (ZMod 2) A6 X)
    (f : coreAction.IntertwiningMap ρ) (hf : Function.Surjective f) :
    (Nonempty (Representation.Equiv alternatingNaturalAction ρ) ∨
      ∃ q : ρ.IntertwiningMap coreQuotientAction, Function.Surjective q) ∧
    (Module.finrank (ZMod 2) X = 4 ∨ Module.finrank (ZMod 2) X = 5 ∨
      Module.finrank (ZMod 2) X = 9 ∨ Module.finrank (ZMod 2) X = 10 ∨
      Module.finrank (ZMod 2) X = 14) := by
  have hnt : f.ker ≠ ⊤ := by
    intro he
    obtain ⟨x,hx⟩ := exists_ne (0 : X)
    obtain ⟨v,rfl⟩ := hf x
    exact hx (show f v = 0 from (show v ∈ f.ker from he ▸ Submodule.mem_top))
  have hdim := f.toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top,
    CFSG.Quasithin.ChapterG.Section05.core_finrank] at hdim
  have hcases := core_subrepresentation_cases middleCoverData f.ker
  have hcomp : f.ker ≤ coreLines ∨ coreLines ≤ f.ker := by
    rcases hcases with he | he | he | he | he | he
    · exact Or.inl (he ▸ bot_le)
    · exact Or.inl (he ▸ coreNatural_le_coreLines)
    · exact Or.inl (he ▸ coreLines_perp_le middleCoverData)
    · exact Or.inl he.le
    · exact Or.inr (he ▸ (coreFlag_strictAnti middleCoverData (by decide : (1 : Fin 6) < 2)).le)
    · exact (hnt he).elim
  have hQ : Function.Surjective coreQuotientMap := CoreRelations.mkQ_surjective
  have hQker : coreQuotientMap.ker = coreLines := by
    ext v
    exact Submodule.Quotient.mk_eq_zero CoreRelations
  constructor
  · rcases hcomp with hk | hk
    · right
      exact factor_map f hf coreQuotientMap hQ (hQker.symm ▸ hk)
    · obtain ⟨q,hq⟩ := factor_map coreQuotientMap hQ f hf (hQker ▸ hk)
      let q' := q.comp coreLineRepresentationEquiv.symm.toIntertwiningMap
      have hq' : Function.Surjective q' := hq.comp coreLineRepresentationEquiv.symm.toLinearEquiv.surjective
      rcases BinaryDuadStructure.nonzero_quotient_alternatives ρ q' hq' with hn | hn
      · exact Or.inl hn
      · obtain ⟨E⟩ := hn
        exact Or.inr ⟨(coreLineRepresentationEquiv.trans E).symm.toIntertwiningMap,
          (coreLineRepresentationEquiv.trans E).symm.toLinearEquiv.surjective⟩
  · have hd : Module.finrank (ZMod 2) f.ker.toSubmodule =
        Module.finrank (ZMod 2) f.toLinearMap.ker := rfl
    rcases hcases with he | he | he | he | he | he
    · rw [he, Representation.BinaryCoverSocle.finrank_bottom] at hd; omega
    · rw [he, coreNatural_finrank] at hd; omega
    · rw [he, coreLines_perp_finrank] at hd; omega
    · rw [he, coreLines_finrank] at hd; omega
    · rw [he, coreNatural_perp_finrank] at hd; omega
    · exact (hnt he).elim

private noncomputable def pairTable : Duad ≃ SixPairsQuadratic.Pair :=
  _root_.Equiv.ofBijective (fun d => ⟨duadSet d, duad_is_duad d⟩)
    ⟨fun _ _ h => duadSet_injective (congrArg Subtype.val h), by
      intro ⟨s,hs⟩
      obtain ⟨d,hd⟩ := duadSet_complete s hs
      exact ⟨d,Subtype.ext hd⟩⟩

private theorem pairTable_equivariant (g : S6) (d : Duad) :
    pairTable (g • d) = SixPairsQuadratic.pairPerm g (pairTable d) := by
  apply Subtype.ext
  change duadSet (g • d) = (duadSet d).map g.toEmbedding
  rw [duadSet_smul, Finset.map_eq_image]
  rfl

/-- Reindexing by the literal table of unordered pairs. -/
noncomputable def pairCoordinates : Full Duad ≃ₗ[ZMod 2] Full SixPairsQuadratic.Pair :=
  LinearEquiv.funCongrLeft (ZMod 2) (ZMod 2) pairTable.symm

/-- The duad-table coordinates preserve the full symmetric action. -/
theorem pairCoordinates_equivariant (g : S6) (v : Full Duad) :
    pairCoordinates (pointAction g v) = SixPairsQuadratic.action g (pairCoordinates v) := by
  ext p
  change v (g⁻¹ • pairTable.symm p) = v (pairTable.symm ((SixPairsQuadratic.pairPerm g).symm p))
  congr 1
  apply pairTable.injective
  rw [pairTable_equivariant, pairTable.apply_symm_apply, pairTable.apply_symm_apply]
  rfl

/-- Full movement makes the restriction to the even core surjective. -/
theorem symmetric_pair_core_surjection
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) S6 X)
    (f : SixPairsQuadratic.action.IntertwiningMap ρ) (hf : Function.Surjective f)
    (hgen : Coinvariants.ker ρ = ⊤) :
    ∃ q : SmallDisplacement.symmetricCoreAction.IntertwiningMap ρ, Function.Surjective q := by
  let q : SmallDisplacement.symmetricCoreAction.IntertwiningMap ρ := {
    toLinearMap := f.toLinearMap.comp (pairCoordinates.toLinearMap.comp (core Duad).subtype)
    isIntertwining' := by
      intro g
      ext v
      change f (pairCoordinates (pointAction g v.val)) = ρ g (f (pairCoordinates v.val))
      rw [pairCoordinates_equivariant, f.isIntertwining] }
  refine ⟨q, LinearMap.range_eq_top.mp ?_⟩
  apply top_unique
  rw [← hgen]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,x⟩,rfl⟩
  obtain ⟨v,rfl⟩ := hf x
  let w := pairCoordinates.symm v
  have hw : pointAction g w - w ∈ core Duad := by
    rw [mem_core]
    change (∑ d : Duad, (w (g⁻¹ • d) - w d)) = 0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (_root_.Equiv.sum_comp (MulAction.toPerm g⁻¹) w)
  refine ⟨⟨pointAction g w - w,hw⟩,?_⟩
  change f (pairCoordinates (pointAction g w - w)) = _
  rw [map_sub, map_sub, pairCoordinates_equivariant, f.isIntertwining]
  simp only [w, LinearEquiv.apply_symm_apply]

/-- Full movement makes the restriction to the even core surjective. -/
theorem pair_core_surjection
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) S6 X)
    (f : SixPairsQuadratic.action.IntertwiningMap ρ) (hf : Function.Surjective f)
    (hgen : Coinvariants.ker ρ = ⊤) :
    ∃ q : coreAction.IntertwiningMap (ρ.comp A6.subtype), Function.Surjective q := by
  obtain ⟨q,hq⟩ := symmetric_pair_core_surjection ρ f hf hgen
  exact ⟨q.toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (fun a v => IntertwiningMap.isIntertwining _ _ q a.val v),hq⟩

/-- The literal duad cover is equivariantly the five-dimensional six-letter
augmentation core, including its constant line. -/
theorem duad_cover_coordinates :
    Nonempty (Representation.Equiv coreQuotientAction
      (alternatingCoreRepresentation (Fin 6))) := by
  let P : coreQuotientAction.IntertwiningMap (alternatingNaturalRepresentation (Fin 6)) :=
    (PolarNatural.equiv.toLinearMap.comp coreNaturalProjection.toLinearMap).intertwiningMap_of_isIntertwiningMap
      _ _ (fun g v => by
        change PolarNatural.equiv (coreNaturalProjection (coreQuotientAction g v)) = _
        rw [coreNaturalProjection.isIntertwining]
        exact PolarNatural.equiv_action g.val _)
  have hP : Representation.OneCohomology.IsCover P := by
    refine ⟨PolarNatural.equiv.surjective.comp coreNaturalProjection_isCover.1,?_,coreQuotient_generated⟩
    intro v hv g
    have hz : coreNaturalProjection v = 0 := PolarNatural.equiv.injective
      (hv.trans (map_zero PolarNatural.equiv).symm)
    exact coreNaturalProjection_isCover.2.1 hz g
  obtain ⟨f,hf,he,_⟩ := BinaryPermutation.SixCover.core_quotient_of_alternating_cover
    coreQuotientAction P hP
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [finrank_core, CFSG.Quasithin.ChapterG.Section05.quotient_finranks.1]
      rfl)).mpr hf
  let f' : (alternatingCoreRepresentation (Fin 6)).IntertwiningMap coreQuotientAction :=
    f.intertwiningMap_of_isIntertwiningMap _ _ he
  exact ⟨(f'.ofBijective ⟨hi,hf⟩).symm⟩

private noncomputable def duadNaturalCoordinates :
    Representation.Equiv alternatingNaturalAction (alternatingNaturalRepresentation (Fin 6)) :=
  Representation.Equiv.mk PolarNatural.equiv (fun g => LinearMap.ext (PolarNatural.equiv_action g.val))

/-- Transport the comparison through a specified faithful six-letter actor.
The module and the supplied actor marking remain unchanged. -/
theorem marked_pair_comparison
    {A X : Type*} [Group A] [AddCommGroup X] [Module (ZMod 2) X] [Nontrivial X]
    (ρ : Representation (ZMod 2) A X) (e : A ≃* S6)
    (f : Representation.IntertwiningMap (SixPairsQuadratic.action.comp e.toMonoidHom) ρ)
    (hf : Function.Surjective f) (hgen : Coinvariants.ker ρ = ⊤) :
    let σ : Representation (ZMod 2) A6 X := ρ.comp (e.symm.toMonoidHom.comp A6.subtype)
    (Nonempty (Representation.Equiv (alternatingNaturalRepresentation (Fin 6)) σ) ∨
      ∃ q : σ.IntertwiningMap (alternatingCoreRepresentation (Fin 6)), Function.Surjective q) ∧
    (Module.finrank (ZMod 2) X = 4 ∨ Module.finrank (ZMod 2) X = 5 ∨
      Module.finrank (ZMod 2) X = 9 ∨ Module.finrank (ZMod 2) X = 10 ∨
      Module.finrank (ZMod 2) X = 14) := by
  let τ : Representation (ZMod 2) S6 X := ρ.comp e.symm.toMonoidHom
  let f' : SixPairsQuadratic.action.IntertwiningMap τ := {
    toLinearMap := f.toLinearMap
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro v
      change f (SixPairsQuadratic.action g v) = ρ (e.symm g) (f v)
      have he := IntertwiningMap.isIntertwining _ _ f (e.symm g) v
      change f (SixPairsQuadratic.action (e (e.symm g)) v) = ρ (e.symm g) (f v) at he
      rwa [e.apply_symm_apply] at he }
  have hg : Coinvariants.ker τ = ⊤ := by
    apply top_unique
    rw [← hgen]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    have he : τ (e g) v = ρ g v := by
      change ρ (e.symm (e g)) v = _
      rw [e.symm_apply_apply]
    change ρ g v - v ∈ Coinvariants.ker τ
    rw [← he]
    exact Coinvariants.sub_mem_ker _ _
  obtain ⟨q,hq⟩ := pair_core_surjection τ f' hf hg
  obtain ⟨hc,hd⟩ := duad_core_quotient_comparison (τ.comp A6.subtype) q hq
  refine ⟨?_,hd⟩
  rcases hc with hnat | hquot
  · obtain ⟨E⟩ := hnat
    exact Or.inl ⟨duadNaturalCoordinates.symm.trans E⟩
  · obtain ⟨q,hq⟩ := hquot
    obtain ⟨E⟩ := duad_cover_coordinates
    exact Or.inr ⟨E.toIntertwiningMap.comp q,E.toLinearEquiv.surjective.comp hq⟩

end CFSG.Quasithin.ChapterG.Section05.Structure
