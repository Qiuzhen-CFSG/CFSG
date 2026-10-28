module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24CodeFixed
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeRank.Marking

/-!
# Rank saturation of the original M24 code offender

The whole-automizer marking transports the original offender's corank-one
fixed space to the native code. The checked near-offender calculation excludes
ranks four and five, so the actor has rank six and its fixed subgroup rank four. The native sextet marking also proves
normality of the fixed subgroup inside the original Sylow group.
The selected pair, orbit and full centralizer kernel are retained.
Source: Aschbacher--Smith 8.2.5, printed pp.716--717, using H.16.5.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Sporadic.Mathieu MathieuCode
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The canonical offender on the original M24 code has rank six and a
native sextet marking. Its four-dimensional fixed subgroup is the original
conjugate intersection and is normal inside the original Sylow subgroup. -/
theorem sourceOrbit_m24_code_rank_six_pair_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      let A := offenderNormalizer D.sourceOrbit i.val⁻¹
      let U := D.sourceOrbit ⊓ centralizer (A : Set G)
      let B := inducedAutomizer D.sourceOrbit A
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S ∧
      globalW D.sourceOrbit (T : Subgroup G) = 1 ∧
      IsWOffenderAt D.sourceOrbit T i.val⁻¹ ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = A ⊓ centralizer (D.sourceOrbit : Set G) ∧
      I ≤ centralizer (U : Set G) ∧
      rank B = 6 ∧ rank U = 4 ∧ subgroupCorank D.sourceOrbit U = 7 ∧
      (U.subgroupOf T).Normal ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      ∃ c : M24, (B.map a.toMonoidHom).map (MulAut.conj c).toMonoidHom =
        M24LocalGeometry.SextetCore.core := by
  obtain ⟨I,i,S,s,hw,hOff,hfix,hker,hcentral,hfour,hsix,hcor,hsum⟩ :=
    D.sourceOrbit_m24_code_fixed_pair_of_many h hmany hV hq hnon a E hE hH
  let B := inducedAutomizer D.sourceOrbit (offenderNormalizer D.sourceOrbit i.val⁻¹)
  let : IsElementaryAbelian 2 B := offender_inducedAutomizer_elementary D.sourceOrbit i.val⁻¹
  let : IsElementaryAbelian 2 (B.map a.toMonoidHom) := IsElementaryAbelian.map _
  change 4 ≤ rank B at hfour
  change rank B ≤ 6 at hsix
  change subgroupCorank D.sourceOrbit
    (D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)) =
      1 + rank B at hcor
  change rank (D.sourceOrbit ⊓ centralizer
    (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)) + rank B = 10 at hsum
  have hc := fixedCodim_inducedAutomizer D.sourceOrbit
    (offenderNormalizer D.sourceOrbit i.val⁻¹) (show
      offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ normalizer (D.sourceOrbit : Set G) from inf_le_right)
  have ht := fixedCodim_map_equivariant (automizerRepresentation D.sourceOrbit)
    codeRepresentation a.toMonoidHom E hE B
  have hm := rank_map_injective a.toMonoidHom a.injective B
  have hr := NormalizedShadowRows.CodeRank.rank_six (B.map a.toMonoidHom)
    (by rw [hm]; exact hfour) (by rw [hm]; exact hsix) (by
      rw [← ht,hc,hm]
      simpa only [Nat.add_comm] using hcor.le)
  rw [hm] at hr
  have hnear : fixedCodim codeRepresentation (B.map a.toMonoidHom) ≤ 7 := by
    rw [← ht,hc,hcor,hr]
  have hmark := NormalizedShadowRows.CodeRank.sextet_marking (B.map a.toMonoidHom)
    (hm.trans hr) hnear
  have hAT := (selected_offender_of_parameter_bound s D.sourceOrbit_weakClosure_setup
    (by rw [hw]; rfl)).2.2.2.1
  let P := inducedAutomizer D.sourceOrbit (T : Subgroup G)
  have hp : IsPGroup 2 P := T.2.comap_subtype.map _
  have hBP : B ≤ P := map_mono (comap_mono hAT)
  have hn := NormalizedShadowRows.CodeRank.normalized_in_two_group
    (B.map a.toMonoidHom) (P.map a.toMonoidHom) (hp.map a.toMonoidHom)
    (map_mono hBP) (hm.trans hr) hnear
  have hnormalize : P ≤ normalizer (B : Set (Automizer D.sourceOrbit)) := by
    intro b hb
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.map_injective (f := a.toMonoidHom) a.injective
    change (B.map (MulAut.conj b).toMonoidHom).map a.toMonoidHom = B.map a.toMonoidHom
    rw [map_map]
    have heq : a.toMonoidHom.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj (a b)).toMonoidHom.comp a.toMonoidHom := by
      ext x
      simp [MulAut.conj_apply]
    rw [heq,← map_map]
    exact mem_normalizer_iff_map_conj_eq.mp (hn (mem_map_of_mem a.toMonoidHom hb))
  have hT := D.sourceOrbit_weakClosure_setup
  refine ⟨I,i,S,s,hw,hOff,hfix,hker,hcentral,hr,?_,?_,
    fixed_normal_in_sylow D.sourceOrbit _ T hT.le_sylow inf_le_right hT.normalizes hnormalize,
    fixed_normalized_of_image_normalized D.sourceOrbit _ T inf_le_right hT.normalizes hnormalize,
    hmark⟩ <;> omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
