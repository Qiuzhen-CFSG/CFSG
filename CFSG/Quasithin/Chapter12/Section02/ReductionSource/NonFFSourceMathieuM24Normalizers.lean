module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Equality
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrioNormalizers
-- Internal proof continuation: unfold the original component-action map only.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# The original M24 cocode fixed-space normalizer and its residual

For each original w-offender, use its proved trio marking to coordinatize
U=C_W(A) by the actual native affine-plane three-space. L already induces all
of M24 on W, so N_L(U) acts on U as the full GL(3,2), with kernel C_{N_L(U)}(U).
The intrinsic solvable residual also induces this full action, and the
conjugates of every nontrivial subgroup of U under that residual generate U.
This gives the natural action in the M24 cocode row of source 8.2.6(2), with
the literal original subgroup and conjugation action preserved.

The only external premise is the precise central-two-cover rigidity owned by
qt-model-j4-two-primary-covers, used by the preceding point-control theorem.
The owner qt-d-1222-nonff-mathieu retains its discharge, the remaining Mathieu
branches, component and two-core recognition, and the ambient J4 isomorphism;
qt-d-1222-normalized-nonff also retains the model premise in final assembly.
Source: Aschbacher--Smith 8.1.3, 8.2.5--6, printed pp.713,716--717,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode MathieuCode.TrioCalculation
open CFSG.Quasithin.ChapterE
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The actual component normalizer of the offender fixed three-space acts
as the full binary linear three-group, in the original trio coordinates. -/
theorem sourceOrbit_m24_fixedPlane_normalizer_action
    (hcover : ∀ (K : Type u) [Group K] [Finite K] [Group.IsPerfect K],
      (K ⧸ center K) ≃* Janko4.Model → IsPGroup 2 (center K) → center K = ⊥)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    ∃ (c : M24) (e : U ≃* Multiplicative Vector)
      (π : (L ⊓ normalizer (U : Set G) : Subgroup G) →* BinaryLinear.GL Vector),
      Function.Surjective π ∧
      Function.Surjective (π.comp (solvableResidual
        (L ⊓ normalizer (U : Set G) : Subgroup G)).subtype) ∧
      π.ker = (centralizer (U : Set G)).subgroupOf (L ⊓ normalizer (U : Set G)) ∧
      (∀ u : U, standardPlaneMap (e u).toAdd =
        cocodeRepresentation c (E (Additive.ofMul (inclusion inf_le_left u)))) ∧
      (∀ (l : (L ⊓ normalizer (U : Set G) : Subgroup G)) (u : U),
        (e (U.normalizerMonoidHom ⟨l,l.property.2⟩ u)).toAdd = π l (e u).toAdd) ∧
      ∀ B : Subgroup G, B ≤ U → B ≠ ⊥ →
        conjugateSpanBy B ((solvableResidual
          (L ⊓ normalizer (U : Set G) : Subgroup G)).map
            (L ⊓ normalizer (U : Set G) : Subgroup G).subtype) = U := by
  let W := D.sourceOrbit
  let A := offenderNormalizer W g
  let U := W ⊓ centralizer (A : Set G)
  obtain ⟨_,_,_,_,_,c,hc,hp,_,_⟩ :=
    D.sourceOrbit_m24_cocode_geometry_of_janko_two_cover hcover h hmany hV hq hnon a E hE hg
  let C := LinearMap.GeneralLinearGroup.toLinearEquiv (cocodeRepresentation.asGroupHom c)
  let F := E.trans C
  let q : L →* M24 := (MulAut.conj c).toMonoidHom.comp
    (a.toMonoidHom.comp D.mathieuComponentAutomizer)
  have hqsur : Function.Surjective q := (MulAut.conj c).surjective.comp
    (a.surjective.comp (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (Or.inr hq)))
  have hF (l : L) (w : W) :
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,D.sourceOrbit_component_normalizes l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)) := by
    change cocodeRepresentation c
        (E (automizerRepresentation W (D.mathieuComponentAutomizer l) (Additive.ofMul w))) =
      cocodeRepresentation (c * a (D.mathieuComponentAutomizer l) * c⁻¹)
        (cocodeRepresentation c (E (Additive.ofMul w)))
    rw [hE]
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  have hplane (w : W) : (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range := by
    rw [←hp]
    constructor
    · intro hw
      exact ⟨E (Additive.ofMul w),⟨Additive.ofMul w,
        (mem_fixedSpace_inducedAutomizer W A inf_le_right _).mpr hw.2,rfl⟩,rfl⟩
    · rintro ⟨v,⟨y,hy,rfl⟩,he⟩
      have hyw : y = Additive.ofMul w := F.injective he
      rw [hyw] at hy
      exact ⟨w.property,(mem_fixedSpace_inducedAutomizer W A inf_le_right _).mp hy⟩
  obtain ⟨e,π,hπ,hker,he,hact⟩ := MathieuTrio.plane_normalizer_action W L U
    D.sourceOrbit_component_normalizes inf_le_left q hqsur F hF hplane
  exact ⟨c,e,π,hπ,MathieuTrio.residual_surjective π hπ,hker,he,hact,
    fun B hBU hB => MathieuTrio.plane_residual_conjugateSpan U _ inf_le_right e π hπ hact B hBU hB⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
