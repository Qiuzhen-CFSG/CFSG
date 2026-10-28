module
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldParityOddSeed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceIrreducible
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition

/-!
# The natural marking in odd field degree

Odd degree fixes the original chosen seed under T. Residual nonfaithfulness
removes its fixed vectors; its original Irr⁺ condition therefore makes the
faithful orbit action irreducible. The proved guarded cubic estimate and
quasisimple actor structure supply Chapter K's hypotheses. K.3.1 recognizes
a natural or Hermitian action, and oddness excludes the Hermitian degree.
The quotient marking and binary coordinates are then transported back to
the original FSU module using its actual inclusions and conjugation action.

The private import of Actor.Orbit is an intentional internal continuation
for its unexposed orbitComponentHom and orbitComponentQuotientHom bodies.
Their conjugation formula is verified here without changing public visibility.
Source: Aschbacher–Smith, 5.1.17, printed p.640, using K.3.1, p.454
(refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)
include D

/-- In odd degree the literal chosen module is already the entire Sylow orbit. -/
theorem rankOne_sourceOrbit_eq_of_odd
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hodd : Odd n) :
    D.sourceOrbit = V := by
  have he := fundamental_module_eq_seed_of_odd (D.fundamentalSetup h)
    D.sylow_normalizes_component hpsl hodd
  rwa [D.fundamentalSetup_module, D.fundamentalSetup_seed, ← D.sourceOrbit_eq] at he

omit [Group G] [Finite G] D in
private theorem irreducible_restricted_congr {A E : Type*} [Group A]
    [AddCommGroup E] [Module (ZMod 2) E] (ρ : Representation (ZMod 2) A E)
    (X : Subgroup A) {I J : Submodule (ZMod 2) E} (he : I = J)
    (hi : Representation.IsIrreducible
      ((subspaceImageRepresentation ρ J).comp (restrictedSubgroup ρ J X).subtype)) :
    Representation.IsIrreducible
      ((subspaceImageRepresentation ρ I).comp (restrictedSubgroup ρ I X).subtype) := by
  subst I
  exact hi

/-- The original orbit action satisfies Chapter K before selecting a model. -/
theorem rankOne_odd_chapterK
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hodd : Odd n) :
    ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent := by
  have hWV := D.rankOne_sourceOrbit_eq_of_odd h.toHypothesis1221 hpsl hodd
  have hFV : (D.fundamentalSetup h.toHypothesis1221).moduleSubgroup = V := by
    rw [D.fundamentalSetup_module, ← D.sourceOrbit_eq, hWV]
  have hc : V ⊓ centralizer (L : Set G) = ⊥ := by
    rw [← hFV]
    exact D.rankOne_fundamental_fixed_eq_bot h hmany hH hlinear _
  have he : D.orbitSpace = D.space := ReducedNormal.subspaceImage_injective
    (L ⊔ (T : Subgroup G)) (hWV.trans D.image_eq.symm)
  have hi := irreducible_restricted_congr (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G))) he (D.seed_irreducible hc)
  exact ⟨D.sourceOrbit_sqtk h.toHypothesis1221, D.orbit_fitting h.toHypothesis1221,
    D.orbitComponent_quasisimple h.toHypothesis1221, subspaceImageRepresentation_injective _ _,
    hi, D.sourceOrbit_cubic_le_two_of_many h hmany⟩

/-- Recognition produces an actual natural action on the original selected module. -/
theorem rankOne_natural_of_odd
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hodd : Odd n) : Chapter6.Source.IsNaturalModule L V n := by
  have hs := D.rankOne_odd_chapterK h hmany hpsl hH hlinear hodd
  have hWV := D.rankOne_sourceOrbit_eq_of_odd h.toHypothesis1221 hpsl hodd
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let eL := e.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let q := D.orbitComponentQuotientHom h.toHypothesis1221
  have hz : center (L ⧸ pCore 2 L) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    apply e.injective
    rw [map_one]
    have hx' : e x ∈ center PSL(2,F) := by
      rw [mem_center_iff]
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)
    simpa only [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot, mem_bot] using hx'
  let := h.toHypothesis1221.quasisimple
  have hq : Function.Injective q := by
    apply q.ker_eq_bot_iff.mp
    rcases IsQuasisimple.normal_le_center_or_eq_top q.ker with hc | ht
    · exact bot_unique (hc.trans hz.le)
    · exfalso
      obtain ⟨x,hx⟩ := exists_ne (1 : D.orbitComponent)
      obtain ⟨y,rfl⟩ := D.orbitComponentQuotientHom_surjective h.toHypothesis1221 x
      exact hx (ht.ge (mem_top y))
  let a := MulEquiv.ofBijective q ⟨hq,D.orbitComponentQuotientHom_surjective h.toHypothesis1221⟩
  let ea := a.symm.trans eL
  obtain ⟨_,hm | ⟨s,he,_,_,_,_⟩⟩ := hs.binary_recognition ea n (by omega) hF
  · obtain ⟨M⟩ := hm.2
    let f : V ≃* Multiplicative (Fin 2 → F) :=
      (MulEquiv.subgroupCongr hWV).symm.trans
        (D.sourceOrbitCoordinates.symm.trans M.coordinates).toAddEquiv.toMultiplicative
    refine ⟨F,inferInstance,inferInstance,inferInstance,hF,a.trans M.groupEquiv,f,?_⟩
    intro l v
    let w := D.sourceOrbitCoordinates.symm (Additive.ofMul ((MulEquiv.subgroupCongr hWV).symm v))
    have hmark : (a.trans M.groupEquiv) (QuotientGroup.mk' (pCore 2 L) l) =
        M.groupEquiv (D.orbitComponentHom l) := rfl
    have hh := M.intertwines (D.orbitComponentHom l) w
    change M.coordinates (D.orbitRepresentation (D.orbitComponentHom l).val w) =
      (M.groupEquiv (D.orbitComponentHom l)).val.mulVec (f v).toAdd at hh
    change (f.symm (Multiplicative.ofAdd
      (((a.trans M.groupEquiv) (QuotientGroup.mk' (pCore 2 L) l)).val.mulVec (f v).toAdd)) : G) = _
    rw [hmark, ← hh]
    change ((D.sourceOrbitCoordinates (M.coordinates.symm
      (M.coordinates (D.orbitRepresentation (D.orbitComponentHom l).val w)))).toMul : G) = _
    rw [LinearEquiv.symm_apply_apply]
    have hw : ((D.sourceOrbitCoordinates w).toMul : G) = (v : G) := by
      dsimp only [w]
      rw [LinearEquiv.apply_symm_apply]
      rfl
    rw [sourceOrbitCoordinates_apply] at hw ⊢
    change (l : G) * w.val.toMul.val.val * (l : G)⁻¹ = _
    rw [hw]
  · exact ((Nat.not_even_iff_odd.mpr hodd) ⟨s,by omega⟩).elim

/-- The literal FSU required by 5.1.17 now has its natural marking. -/
theorem rankOne_odd_natural_fundamental_exists
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hodd : Odd n) :
    ∃ F : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L,
      F.moduleSubgroup = V ∧ Chapter6.Source.IsNaturalModule L F.moduleSubgroup n := by
  have he : (D.fundamentalSetup h.toHypothesis1221).moduleSubgroup = V := by
    rw [D.fundamentalSetup_module, ← D.sourceOrbit_eq,
      D.rankOne_sourceOrbit_eq_of_odd h.toHypothesis1221 hpsl hodd]
  exact ⟨D.fundamentalSetup h.toHypothesis1221,he,he.symm ▸
    D.rankOne_natural_of_odd h hmany hn hpsl hH hlinear hodd⟩

/-- The parity seed now needs only the global point and F.8 geometry. -/
theorem rankOne_odd_seed_of_chosen_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {A B : Subgroup G} (c : CartanPair T L H A B) (hodd : Odd n)
    (hf : (setup T L V H A).Hypothesis)
    (hti : ∀ g : G,
      (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁) :
    Nonempty (Seed T L H A n) := by
  obtain ⟨F,he,hnat⟩ := D.rankOne_odd_natural_fundamental_exists h hmany hn hpsl hH hlinear hodd
  exact D.rankOne_odd_seed_of_fundamental_geometry h hmany hn hpsl hH hlinear c hodd
    F hnat (he.symm ▸ hf) (he.symm ▸ hti)

/-- Parity assembly with the natural-module obligation fully discharged. -/
theorem rankOne_even_exponent_of_chosen_geometry_and_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hgeometry : ∀ A B : Subgroup G, CartanPair T L H A B → Odd n →
      (setup T L V H A).Hypothesis ∧
        ∀ g : G,
          (setup T L V H A).V₁ ⊓ (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = ⊥ ∨
            (setup T L V H A).V₁.map (MulAut.conj g).toMonoidHom = (setup T L V H A).V₁)
    (hlower : DisplacementSource T L H n) : Even n := by
  apply D.rankOne_even_exponent_of_seed_and_displacement h hn hpsl hH hgen ?_ hlower
  intro A B c hodd
  obtain ⟨hf,hti⟩ := hgeometry A B c hodd
  exact D.rankOne_odd_seed_of_chosen_geometry h hmany hn hpsl hH hlinear c hodd hf hti

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
