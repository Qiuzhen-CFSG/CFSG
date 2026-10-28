module

public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.SextetGeometry.Native
public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.LinearSteps
public import CFSG.Quasithin.ChapterH.Section13To16.CodeLocal.Spaces
public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# The sextet argument in Lemma K.4.2

For the native code, the earlier H.16 sextet facts give a four-dimensional
fixed space V₄ and a rank-one displacement on the quotient by V₄. A noncentral
involution has displacement rank five, so rank-nullity puts V₄ in its image.
Quadraticity then forces the whole subgroup to fix V₄ pointwise. The ambient
stabilizer places it in the sextet stabilizer, and its two-group property kills
the order-three part of the tetrad kernel, placing it in the actual two-core.
The native hexacode calculation in `Native` bounds its order by four.

The coordinate-paired duality transfers quadraticity to the cocode. Combining
both bounds with the exhaustive native involution classification supplies the
central-class selection step immediately before K.4.3.

This is the conditional K.4.2 implication: `CodeSextetFacts` retains only the
specified earlier H.16 flag, action, and stabilizer facts. Their construction
belongs to the earlier-source assembly. It contains no noncentral-subgroup
bound or quadratic-subgroup placement. The hexacode field line, the concrete
quotient action needed from H.14.1(2), and noncentral sextet placement are proved
in `Native` using the actual native-to-hexacode coordinate identification.
In particular the entire pointwise centralizer of V₄ is not assumed to be a
2-group: its order-three part is removed in the proof.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemma K.4.2 and
the selection before K.4.3, printed pp.458–459 (PDF pp.469–470); H.16.1,
printed p.402, and H.14.1(2), printed pp.396–397.
-/

@[expose] public section

open Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open MathieuCode.CocodeOctad.Involutions
noncomputable section
namespace CFSG.Quasithin.ChapterK.Mathieu.SextetGeometry
/-- The literal code fixed space C_U(K_S) for the standard sextet. -/
abbrev V4 := ChapterH.Section13To16.codeSextetFixed standardSextet

/-- The earlier sextet facts used in K.4.2, all on the native code and maps.

The quotient image is taken with the actual quotient map by V₄. The final
field expresses faithfulness of the natural action of the six-tetrad quotient
on V₄; it does not identify its pointwise kernel with the two-core. -/
structure CodeSextetFacts : Prop where
  /-- H.16.1(1): the actual fixed space has dimension four. -/
  four_rank : Module.finrank (ZMod 2) V4 = 4
  /-- H.16.1(3): each nonidentity kernel element induces a transvection. -/
  quotient_rank : ∀ x ∈ SextetCore.core, x ≠ 1 →
    Module.finrank (ZMod 2)
      (LinearMap.range (V4.mkQ.comp (displacement codeRepresentation x))) = 1
  /-- The ambient setwise stabilizer of the four-space. -/
  stabilizer : subspaceStabilizer codeRepresentation V4 = sextetStabilizer standardSextet
  /-- H.16.1(2): a pointwise fixer acts trivially on the six tetrads. -/
  action_kernel : ∀ g : sextetStabilizer standardSextet,
    (∀ v ∈ V4, codeRepresentation g.val v = v) → SextetCore.columnHom g = 1

private theorem subspace_le_of_quotient_rank {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (W I : Submodule (ZMod 2) V)
    (hW : Module.finrank (ZMod 2) W = 4)
    (hI : Module.finrank (ZMod 2) I = 5)
    (hQ : Module.finrank (ZMod 2) (I.map W.mkQ) = 1) : W ≤ I := by
  let f := W.mkQ.comp I.subtype
  have hr : LinearMap.range f = I.map W.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : f.ker.map I.subtype = W ⊓ I := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.map_comap_subtype, inf_comm]
  have hd := f.finrank_range_add_finrank_ker
  rw [hr, hQ, hI] at hd
  have he := Submodule.finrank_map_subtype_eq I f.ker
  rw [hk] at he
  have heq : W ⊓ I = W := Submodule.eq_of_le_of_finrank_eq inf_le_left (by omega)
  exact inf_eq_left.mp heq

/-- The rank-five noncentral image contains the source four-space. -/
theorem four_le_displacement (h : CodeSextetFacts) {x : M24}
    (hx : x ∈ SextetCore.core) (ht : IsConj t x) :
    V4 ≤ LinearMap.range (displacement codeRepresentation x) := by
  apply subspace_le_of_quotient_rank V4 _ h.four_rank
  · exact (fixedCodim_zpowers_eq_displacement_rank codeRepresentation x).symm.trans
      ((code_cocode_fixedCodim_cyclic (Subgroup.zpowers x)).trans
        (fixedCodim_of_isConj_t x ht))
  · rw [← LinearMap.range_comp]
    apply h.quotient_rank x hx
    intro hx1
    exact noncentral_fixedPointFree ht 0 (by rw [hx1, one_smul])

private theorem two_subgroup_of_column_kernel (D : Subgroup M24)
    (hp : IsPGroup 2 D) (hD : D ≤ sextetStabilizer standardSextet)
    (hc : ∀ g : sextetStabilizer standardSextet, g.val ∈ D → SextetCore.columnHom g = 1) :
    D ≤ SextetCore.core := by
  let A := D.subgroupOf (sextetStabilizer standardSextet)
  have hA : IsPGroup 2 A := hp.comap_subtype
  have hm : A.map SextetCore.sextetEquiv.toMonoidHom ≤ Atlas.Codes.sextetCoordinateHom.ker := by
    rintro _ ⟨g, hg, rfl⟩
    exact hc g hg
  have hk := SextetCore.atlas_two_subgroup_le_kernel _
    (hA.map SextetCore.sextetEquiv.toMonoidHom) hm
  intro g hg
  refine ⟨⟨g,hD hg⟩, ?_, rfl⟩
  rw [← SextetCore.quotientHom_ker]
  exact hk ⟨⟨g,hD hg⟩, hg, rfl⟩

/-- Once a noncentral element is placed in K_S, quadraticity places D in K_S. -/
theorem quadratic_le_core (h : CodeSextetFacts) (D : Subgroup M24)
    (hp : IsPGroup 2 D) (hq : IsQuadratic codeRepresentation D)
    {x : M24} (hxD : x ∈ D) (hxK : x ∈ SextetCore.core) (ht : IsConj t x) :
    D ≤ SextetCore.core := by
  have hfix : ∀ d ∈ D, ∀ v ∈ V4, codeRepresentation d v = v := by
    intro d hd v hv
    obtain ⟨w, rfl⟩ := four_le_displacement h hxK ht hv
    exact hq d hd x hxD w
  have hD : D ≤ sextetStabilizer standardSextet := by
    rw [← h.stabilizer]
    apply le_subspaceStabilizer
    intro d hd v hv
    rwa [hfix d hd v hv]
  exact two_subgroup_of_column_kernel D hp hD (fun g hg => h.action_kernel g (hfix g hg))

private theorem quadratic_conj {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    {D : Subgroup G} (hq : IsQuadratic ρ D) (g : G) :
    IsQuadratic ρ (D.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
  have hh := congrArg (ρ g) (hq a ha b hb (ρ g⁻¹ v))
  simpa only [map_mul, Module.End.mul_apply, map_sub, ρ.inv_self_apply,
    ρ.self_inv_apply] using hh

/-- Lemma K.4.2 for the native code, conditional only on the earlier sextet facts. -/
theorem code_noncentral_rank_le_two (h : CodeSextetFacts) (D : Subgroup M24)
    (hD : D ∈ quadraticSubgroups codeRepresentation)
    (hclass : ∀ x ∈ D, x ≠ 1 → IsConj t x) : rank D ≤ 2 := by
  let : IsElementaryAbelian 2 D := hD.1.2
  obtain ⟨x,hx,hx1⟩ := D.bot_or_exists_ne_one.resolve_left hD.1.1
  obtain ⟨g,hg⟩ := noncentral_sextet_placement (hclass x hx hx1)
  let E := D.map (MulAut.conj g).toMonoidHom
  have hE : IsPGroup 2 E := (hD.1.2.isPGroup 2 D).map _
  have hq : IsQuadratic codeRepresentation E := quadratic_conj _ hD.2.2 g
  have hr : representative ∈ E := hg ▸ Subgroup.mem_map_of_mem _ hx
  have hle := quadratic_le_core h E hE hq hr representative_mem representative_isConj
  have hcl : ∀ y ∈ E, y ≠ 1 → IsConj t y := by
    rintro _ ⟨d,hd,rfl⟩ hn
    have hd1 : d ≠ 1 := by
      intro he
      apply hn
      rw [he, map_one]
    exact (hclass d hd hd1).trans (isConj_iff.mpr ⟨g,rfl⟩)
  have hb := core_noncentral_rank_le_two E hle hcl
  rwa [rank_map_injective _ (MulAut.conj g).injective] at hb

/-- Quadraticity agrees on the actual coordinate-paired code and cocode. -/
theorem code_quadratic_iff_cocode (D : Subgroup M24) :
    IsQuadratic codeRepresentation D ↔ IsQuadratic cocodeRepresentation D := by
  constructor
  · intro h
    apply (quadratic_iff_dual cocodeRepresentation D).mpr
    exact quadratic_of_equivariant_surjection codeRepresentation cocodeRepresentation.dual
      codeDuality.toLinearMap codeDuality.toLinearEquiv.surjective
      (fun g v => LinearMap.congr_fun (codeDuality.isIntertwining' g) v) D h
  · intro h
    apply (quadratic_iff_dual codeRepresentation D).mpr
    exact quadratic_of_equivariant_surjection cocodeRepresentation codeRepresentation.dual
      cocodeDuality.toLinearMap cocodeDuality.toLinearEquiv.surjective
      (fun g v => LinearMap.congr_fun (cocodeDuality.isIntertwining' g) v) D h

/-- Lemma K.4.2 for the native cocode, through the genuine duality. -/
theorem cocode_noncentral_rank_le_two (h : CodeSextetFacts) (D : Subgroup M24)
    (hD : D ∈ quadraticSubgroups cocodeRepresentation)
    (hclass : ∀ x ∈ D, x ≠ 1 → IsConj t x) : rank D ≤ 2 :=
  code_noncentral_rank_le_two h D
    ⟨hD.1,hD.2.1,(code_quadratic_iff_cocode D).mpr hD.2.2⟩ hclass

private theorem exists_central_of_not_all_noncentral (D : Subgroup M24)
    (he : IsElementaryAbelian 2 D)
    (hn : ¬ ∀ x ∈ D, x ≠ 1 → IsConj t x) : ∃ x ∈ D, IsConj z x := by
  classical
  push Not at hn
  obtain ⟨x,hx,hx1,hxt⟩ := hn
  let := he
  have ho : orderOf x = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian _ hx) hx1
  exact ⟨x,hx,(M24InvolutionCentralizers.involution_classes x ho).resolve_right hxt⟩

/-- The code selection step for the octad application immediately before K.4.3. -/
theorem code_rank_gt_two_contains_central (h : CodeSextetFacts) (D : Subgroup M24)
    (hD : D ∈ quadraticSubgroups codeRepresentation) (hr : 2 < rank D) :
    ∃ x ∈ D, IsConj z x := by
  apply exists_central_of_not_all_noncentral D hD.1.2
  intro hc
  exact (not_le_of_gt hr) (code_noncentral_rank_le_two h D hD hc)

/-- The cocode selection step for that same octad application. -/
theorem cocode_rank_gt_two_contains_central (h : CodeSextetFacts) (D : Subgroup M24)
    (hD : D ∈ quadraticSubgroups cocodeRepresentation) (hr : 2 < rank D) :
    ∃ x ∈ D, IsConj z x := by
  apply exists_central_of_not_all_noncentral D hD.1.2
  intro hc
  exact (not_le_of_gt hr) (cocode_noncentral_rank_le_two h D hD hc)

end CFSG.Quasithin.ChapterK.Mathieu.SextetGeometry
