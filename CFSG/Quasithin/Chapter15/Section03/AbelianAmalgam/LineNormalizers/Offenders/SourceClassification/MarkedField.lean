module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceClassification.Coordinates
public import Theory.Representation.SL2NaturalOffenders.Internal
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# The marked SL₂ Sylow and its field

The normalizer-fixed, orbit-generating marker and faithfulness make the literal
image of J(S_E) nontrivial. A maximum elementary subgroup of S_E therefore has
a nontrivial faithful image. The source maximum-family comparison places it
in the ordinary-offender theorem for C_H(E); the odd action kernel and the
whole central quotient preserve that inequality. On the natural SL₂ module
this offender fills a Sylow two-subgroup. Its containment in the marked image
identifies that image with the compatible Sylow I intersect q(S_E).

Conjugating both the actor and module coordinates carries this same Sylow to
the upper unipotent subgroup. Its Borel normalizer fixes the marker, whereas
for a larger field the natural Borel fixed space is zero. The field thus has
degree one. The concluding consumer applies this to the whole-fixed-quotient
coordinates supplied by the full earlier classifier; that classifier remains
an input owned by the source-classification assembly.

Source: Aschbacher–Smith, proof of 15.3.67, printed pp.1153–1154,
and B.4.2(1), printed p.86 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceClassification.MarkedField
open BestReduction BestReduction.SourceAssembly ChapterB.QuasisimpleSource
open Replacement.Transvections BestReduction.FullCoreTransfer
universe u v
variable {D : Type u} [Group D] {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {J : Subgroup D}

private theorem marked_ne_bot [Nontrivial D]
    (m : MarkedNormalizer ρ J) (hf : Function.Injective ρ) : J ≠ ⊥ := by
  intro hz
  have hfix (g : D) (v : W) (hv : v ∈ m.marker) : ρ g v = v := by
    apply m.normalizer_fixes g _ v hv
    rw [hz, Subgroup.normalizer_eq_top]
    trivial
  have hs : Submodule.span (ZMod 2)
      {w | ∃ (g : D) (v : W), v ∈ m.marker ∧ ρ g v = w} ≤ ρ.invariants := by
    apply Submodule.span_le.mpr
    rintro w ⟨g, v, hv, rfl⟩
    rw [hfix g v hv]
    exact fun a => hfix a v hv
  rw [m.orbit_span] at hs
  obtain ⟨g, hg⟩ := exists_ne (1 : D)
  apply hg
  apply hf
  ext v
  simpa only [map_one, Module.End.one_apply] using
    hs (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) W)) g

private theorem quotient_offender [FiniteDimensional (ZMod 2) W]
    (F : BinaryField) (c : CentralQuotientCoordinates ρ (linearNatural F 2))
    {A : Subgroup D} (hA : IsOffender ρ A) :
    IsOffender (linearNatural F 2) (A.map c.actor.toMonoidHom) := by
  let q := c.coordinates.toLinearMap.comp ρ.invariants.mkQ
  have hq : Function.Surjective q := c.coordinates.surjective.comp ρ.invariants.mkQ_surjective
  have hcod := fixedCodim_le_of_equivariant_surjection ρ
    ((linearNatural F 2).comp c.actor.toMonoidHom) q hq c.intertwines A
  exact IsOffender.map_equivariant _ _ c.actor.toMonoidHom c.actor.injective
    (LinearEquiv.refl (ZMod 2) (Fin 2 → F.Carrier)) (fun _ _ => rfl)
    ⟨hA.1, hcod.trans hA.2⟩

private theorem offender_eq_sylow [Finite D] [FiniteDimensional (ZMod 2) W]
    (F : BinaryField) (c : CentralQuotientCoordinates ρ (linearNatural F 2))
    {A : Subgroup D} (hA : IsOffender ρ A) (P : Sylow 2 D)
    (hAP : A ≤ (P : Subgroup D)) : A = (P : Subgroup D) := by
  obtain ⟨Q, hQ⟩ := SL2NaturalOffenders.exists_sylow_of_le
    ⊤ Subgroup.topEquiv (linearNatural F 2) (fun _ _ => rfl)
    (quotient_offender F c hA) le_top
  let Q' := Q.mapSurjective
    (f := (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F.Carrier)).subtype)
    (fun x => ⟨⟨x, mem_top _⟩, rfl⟩)
  let P' := P.mapSurjective (f := c.actor.toMonoidHom) c.actor.surjective
  have hQ' : (Q' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F.Carrier)) =
      A.map c.actor.toMonoidHom := hQ
  have hle : (Q' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F.Carrier)) ≤
      (P' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F.Carrier)) := by
    rw [hQ']
    exact map_mono hAP
  have he := Q'.is_maximal' P'.isPGroup' hle
  apply Subgroup.map_injective (f := c.actor.toMonoidHom) c.actor.injective
  exact (he.trans hQ').symm

/-- Inner transport changes both the actor and the natural-module coordinates. -/
private noncomputable def conjugateCoordinates (F : BinaryField)
    (c : CentralQuotientCoordinates ρ (linearNatural F 2))
    (g : Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :
    CentralQuotientCoordinates ρ (linearNatural F 2) where
  actor := c.actor.trans (MulAut.conj g)
  coordinates := c.coordinates.trans
    (LinearMap.GeneralLinearGroup.toLinearEquiv ((linearNatural F 2).asGroupHom g))
  intertwines a v := by
    change linearNatural F 2 g (c.coordinates (ρ.invariants.mkQ (ρ a v))) =
      linearNatural F 2 (g * c.actor a * g⁻¹)
        (linearNatural F 2 g (c.coordinates (ρ.invariants.mkQ v)))
    rw [c.intertwines]
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

private theorem exists_standard_coordinates [Finite D]
    (m : MarkedNormalizer ρ J) (hJ : J = (m.sylow : Subgroup D))
    (F : BinaryField) (c : CentralQuotientCoordinates ρ (linearNatural F 2)) :
    ∃ c' : CentralQuotientCoordinates ρ (linearNatural F 2),
      J.map c'.actor.toMonoidHom = Matrix.SpecialLinearGroup.upperUnipotent F.Carrier := by
  let P := m.sylow.mapSurjective (f := c.actor.toMonoidHom) c.actor.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
    (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) P
      (Matrix.SpecialLinearGroup.upperUnipotentSylow F.Carrier 2)
  refine ⟨conjugateCoordinates F c g, ?_⟩
  change J.map ((MulAut.conj g).toMonoidHom.comp c.actor.toMonoidHom) = _
  rw [← Subgroup.map_map, hJ]
  change ((g • P : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) F.Carrier)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) F.Carrier)) = _
  rw [hg]
  rfl

variable {G L X : Type u} [Group G] [Finite G] [Group L]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  {K : GroupClass.{u}} {Y T V E : Subgroup G} [IsMulCommutative V]
  [(Replacement.Transvections.localSpan T V E).Normal]
  [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)]
  {σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) X}

omit [Finite G] [FiniteDimensional (ZMod 2) X] in
private theorem exists_maximum_image_ne_bot
    (d : TemporarySource K Y T V E L σ)
    (hne : TemporarySource.imageThompson (σ := σ) (T := T) (V := V) (E := E) ≠ ⊥) :
    ∃ A ∈ Stellmacher.elementaryAbelianMaxSubgroups (centralizerSylow T V E),
      actionSubgroup (σ.comp (thompsonImage T V E).subtype)
        ((A.map (QuotientGroup.mk' (localCore T V E))).subgroupOf (thompsonImage T V E)) ≠ ⊥ := by
  classical
  by_contra! h
  apply hne
  apply (Subgroup.map_eq_bot_iff _).mpr
  apply (Subgroup.map_le_map_iff_of_injective (thompsonImage T V E).subtype_injective).mp
  rw [d.markedThompson_map]
  apply Subgroup.map_le_iff_le_comap.mpr
  apply sSup_le
  intro A hA
  apply Subgroup.map_le_iff_le_comap.mp
  have hAI : A.map (QuotientGroup.mk' (localCore T V E)) ≤ thompsonImage T V E :=
    map_mono (le_sSup (d.maximum_comparison A hA))
  rw [← Subgroup.map_subgroupOf_eq_of_le hAI]
  exact map_mono ((Subgroup.map_eq_bot_iff _).mp (h A hA))

/-- The actual image of J(S_E) fills the compatible Sylow intersection. -/
theorem imageThompson_eq_sylow (d : TemporarySource K Y T V E L σ)
    (F : BinaryField)
    (c : CentralQuotientCoordinates
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) (linearNatural F 2)) :
    TemporarySource.imageThompson (σ := σ) (T := T) (V := V) (E := E) =
      (d.imageMarked.sylow : Subgroup _) := by
  let ρ := σ.comp (thompsonImage T V E).subtype
  let : Nontrivial (Matrix.SpecialLinearGroup (Fin 2) F.Carrier) :=
    (Matrix.SpecialLinearGroup.upperUnipotentHom_injective F.Carrier).nontrivial
  let : Nontrivial (actionImage ρ) := c.actor.symm.injective.nontrivial
  have hne := marked_ne_bot d.imageMarked (imageRepresentation_injective ρ)
  obtain ⟨A, hA, hAn⟩ := exists_maximum_image_ne_bot d hne
  let q := QuotientGroup.mk' (localCore T V E)
  let B := (A.map q).subgroupOf (thompsonImage T V E)
  have hAI : A.map q ≤ thompsonImage T V E :=
    map_mono (le_sSup (d.maximum_comparison A hA))
  have hAq : A.map q ≠ ⊥ := by
    intro hz
    apply hAn
    change actionSubgroup ρ ((A.map q).subgroupOf (thompsonImage T V E)) = ⊥
    rw [hz, Subgroup.bot_subgroupOf]
    exact Subgroup.map_bot _
  have hO := FullCoreTransfer.temporary_maximum_images_ordinary Y T V E d.temporary
    d.action d.surjective d.kernel d.geometry σ d.paired d.maximum_exists
    A (d.maximum_comparison A hA) hAq
  have hB : IsOffender ρ B := hO.subgroupOf σ hAI
  have hBim := hB.actionImage_of_odd_kernel ρ d.odd_kernel
  have hBJ : actionSubgroup ρ B ≤
      TemporarySource.imageThompson (σ := σ) (T := T) (V := V) (E := E) := by
    apply map_mono
    exact comap_mono (map_mono (le_sSup hA))
  have he := offender_eq_sylow F c hBim d.imageMarked.sylow
    (hBJ.trans d.imageMarked.subgroup_le_sylow)
  exact le_antisymm d.imageMarked.subgroup_le_sylow (he ▸ hBJ)

/-- Sylow conjugacy carries the literal marked Thompson image to the standard
upper unipotent subgroup, transporting the natural module at the same time. -/
theorem temporary_standard_coordinates (d : TemporarySource K Y T V E L σ)
    (F : BinaryField)
    (c : CentralQuotientCoordinates
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) (linearNatural F 2)) :
    ∃ c' : CentralQuotientCoordinates
        (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) (linearNatural F 2),
      (TemporarySource.imageThompson (σ := σ) (T := T) (V := V) (E := E)).map
        c'.actor.toMonoidHom = Matrix.SpecialLinearGroup.upperUnipotent F.Carrier :=
  exists_standard_coordinates d.imageMarked (imageThompson_eq_sylow d F c) F c

/-- The source normalizer fixes its orbit-generating marker. After the literal
Sylow comparison, the natural Borel fixed-space calculation forces degree one. -/
theorem temporary_field_degree_eq_one (d : TemporarySource K Y T V E L σ)
    (F : BinaryField)
    (c : CentralQuotientCoordinates
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) (linearNatural F 2)) :
    F.degree = 1 := by
  obtain ⟨c', hc'⟩ := temporary_standard_coordinates d F c
  apply linearTwo_field_degree_eq_one d.imageMarked c' F.degree_pos F.card_eq
  rw [hc']

/-- Apply the field restriction to the actual full-classifier coordinates.
Only the universal earlier classifier remains an explicit source input. -/
theorem temporary_degree_one_coordinates (d : TemporarySource K Y T V E L σ)
    (classify : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} K) :
    ∃ F : BinaryField, F.degree = 1 ∧ Nonempty (CentralQuotientCoordinates
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) (linearNatural F 2)) := by
  obtain ⟨F, ⟨c⟩⟩ := temporary_linearTwo_coordinates d classify
  exact ⟨F, temporary_field_degree_eq_one d F c, ⟨c⟩⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceClassification.MarkedField
