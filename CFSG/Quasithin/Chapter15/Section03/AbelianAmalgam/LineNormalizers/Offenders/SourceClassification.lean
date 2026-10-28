module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.SourceAssembly
public import Theory.Representation.SpecialLinearNatural.CubicFixedSpace
public import Theory.Representation.BinaryPermutation.CubicFixedSpace.Five

/-!
# Eliminating the cubic families before the whole-quotient comparison

The full earlier classifier supplies central sections for the same faithful
Thompson image. In the SL₃ and S₅ families, a concrete cubic fixes the entire
fixed space of the specified Sylow subgroup, even when either extension around
the section is nonsplit. It therefore fixes the source marker. The source
prime-to-three condition on its pointwise stabilizer excludes these families.

Only a natural SL₂ section remains, over an arbitrary positive binary field
degree. This does not yet assert coordinates on the whole quotient by the
fixed space, nor a Borel comparison for the literal image of J(S_E). Those
are separate remaining steps in the source classification assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.1 and
B.5.6, printed pp.99–105, and proof of 15.3.67, printed pp.1153–1154.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceClassification
open BestReduction BestReduction.FullCoreTransfer ChapterB.QuasisimpleSource
universe u v
variable {D : Type u} [Group D] {W : Type v}
  [AddCommGroup W] [Module (ZMod 2) W]

/-- The remaining natural section, with unrestricted positive field degree.
It retains both extension orientations and the actual actor equivalence. -/
structure LinearTwoSection (ρ : Representation (ZMod 2) D W) where
  field : BinaryField
  actor : D ≃* Matrix.SpecialLinearGroup (Fin 2) field.Carrier
  sectionData : ModelSection ρ actor.symm.toMonoidHom (linearNatural field 2)

private theorem no_cubic {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ d.marker ⊤)))
    (c : D) (hc : c ∉ d.sylow) (hp : c ^ 3 = 1)
    (hfix : ∀ v ∈ fixedSpace ρ (d.sylow : Subgroup D), ρ c v = v) : False := by
  let a : subspaceKernel ρ d.marker ⊤ :=
    ⟨c, mem_top _, fun v hv => hfix v (d.sylow_fixes hv)⟩
  have ho : orderOf c = 3 := orderOf_eq_prime hp (fun h => hc (h ▸ d.sylow.one_mem))
  have ha : orderOf a = 3 := (Subgroup.orderOf_coe a).symm.trans ho
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hP) (ha ▸ orderOf_dvd_natCard a)

private theorem repeated_cycle_fixes (F : BinaryField) (r : ℕ) :
    ∀ v ∈ fixedSpace (repeated (linearNatural F 3) r)
      (SL3BinaryCubic.klein (F := F.Carrier)),
      repeated (linearNatural F 3) r (SL3BinaryCubic.cycle (F := F.Carrier)) v = v := by
  intro v hv
  funext i
  apply SL3BinaryCubic.cycle_fixes_natural
  intro g
  exact congrFun (hv g) i

/-- An embedded alternating-five natural section contradicts the source
marker bound. Neither extension around the section is assumed split. -/
theorem no_alternatingFive_section [Finite D]
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ d.marker ⊤)))
    (f : alternatingGroup (Fin 5) →* D) (hf : Function.Injective f)
    (s : ModelSection ρ f (alternatingNatural 5)) : False := by
  obtain ⟨c, hc, hp, hfix⟩ :=
    BinaryPermutation.CubicFixedSpace.Five.centralSection_enlargement
      ρ f hf s.space s.projection s.intertwines s.kernel_fixed s.quotient_trivial d.sylow
  exact no_cubic d hP c hc hp hfix

/-- An embedded repeated natural SL₃ section contradicts the same bound,
over every binary field. The identical actor acts on every copy. -/
theorem no_linearThree_section [Finite D]
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ d.marker ⊤)))
    (F : BinaryField) (r : ℕ)
    (f : Matrix.SpecialLinearGroup (Fin 3) F.Carrier →* D) (hf : Function.Injective f)
    (s : ModelSection ρ f (repeated (linearNatural F 3) r)) : False := by
  let A := SL3BinaryCubic.klein (F := F.Carrier)
  let c := SL3BinaryCubic.cycle (F := F.Carrier)
  have hfix : ∀ v ∈ fixedSpace (ρ.comp f) A, (ρ.comp f) c v = v :=
    cubic_fixedSpace_of_central_section (ρ.comp f)
      (repeated (linearNatural F 3) r) A c SL3BinaryCubic.cycle_pow
      SL3BinaryCubic.cycle_normalizes s.space s.projection s.intertwines
      s.kernel_fixed s.quotient_trivial (repeated_cycle_fixes F r)
  obtain ⟨g, hg, hp, hv⟩ := sylow_fixedSpace_enlargement_of_embedded_cubic
    ρ f hf A SL3BinaryCubic.klein_two c SL3BinaryCubic.cycle_pow
      SL3BinaryCubic.cycle_ne_one hfix d.sylow
  exact no_cubic d hP g hg hp hv

/-- The source's 3-prime marker stabilizer eliminates both higher-rank
families directly on their nonsplit sections, before any field restriction. -/
theorem linearTwo_section_of_rankOne [Finite D]
    {ρ : Representation (ZMod 2) D W} {J : Subgroup D}
    (d : MarkedNormalizer ρ J)
    (hP : Nat.Coprime 3 (Nat.card (subspaceKernel ρ d.marker ⊤)))
    (h : RankOneModel ρ) : Nonempty (LinearTwoSection ρ) := by
  cases h with
  | linearTwo F actor s => exact ⟨⟨F, actor, s⟩⟩
  | symmetricFive actor s =>
    let f := actor.symm.toMonoidHom.comp (alternatingGroup (Fin 5)).subtype
    have hf : Function.Injective f := actor.symm.injective.comp Subtype.val_injective
    exact (no_alternatingFive_section d hP f hf s).elim
  | linearThree F _ r _ actor s =>
    exact (no_linearThree_section d hP F r actor.symm.toMonoidHom actor.symm.injective s).elim

open BestReduction.SourceAssembly Replacement.Transvections ChapterB.SourceInduction
open scoped IsMulCommutative
variable {G L X : Type u} [Group G] [Finite G] [Group L]
  [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
  {K : GroupClass.{u}} {Y T V E : Subgroup G} [IsMulCommutative V]
  [(Replacement.Transvections.localSpan T V E).Normal]
  [IsElementaryAbelian 2 (Replacement.Transvections.localSpan T V E)]
  {σ : Representation (ZMod 2) ((temporaryLineNormalizer T V E) ⧸ localCore T V E) X}

omit [FiniteDimensional (ZMod 2) X] in
/-- The original Z-normalizer assumption gives the prime-to-three bound on
the literal source marker in the faithful action image. -/
theorem temporary_marker_coprime (d : TemporarySource K Y T V E L σ) :
    Nat.Coprime 3 (Nat.card (subspaceKernel
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype)) d.marker ⊤)) := by
  have hEU : localLine T V E ≤ Replacement.Transvections.localSpan T V E :=
    comap_mono (d.temporary.line_le.trans (le_conjugateSpanBy V (lineNormalizer E)))
  let : IsElementaryAbelian 2 (localLine T V E) := IsElementaryAbelian.of_le hEU
  exact image_markerCentralizer_coprime_three _ d.marker
    (temporary_markerCentralizer_coprime_three Y T V E d.Z d.temporary
      d.Z_le d.Z_normalizer σ d.marker d.marker_centralizer)

/-- Apply the cubic exclusion to the full earlier alternatives on the same
temporary image. No reduced list, quotient coordinates or Borel containment
is assumed. The universal earlier classifier remains explicit. -/
theorem temporary_linearTwo_section (d : TemporarySource K Y T V E L σ)
    (classify : AdequateClassificationInput.{u,u} K) :
    Nonempty (LinearTwoSection
      (imageRepresentation (σ.comp (thompsonImage T V E).subtype))) :=
  linearTwo_section_of_rankOne d.imageMarked (temporary_marker_coprime d)
    (d.unreduced_models classify)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceClassification
