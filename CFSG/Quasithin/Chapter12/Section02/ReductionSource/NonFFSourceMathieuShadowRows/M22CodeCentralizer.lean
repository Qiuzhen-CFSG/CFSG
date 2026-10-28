module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.Automizer
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeCentralizerCover
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeCentralizer
public import Theory.GroupTheory.SolvableResidual.TwoKernel
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetResidual
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
-- Evaluate only the literal original orbit maps on representatives.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# The original M22-code involution centralizer

A nonzero vector in the original orbit fixed by the original Sylow has a
native hexad marking. Its literal L-centralizer covers the full hexad
stabilizer, with the original action map, entire kernel and full preimage
identity retained. Factoring through L/O₂(L) constructs a quasisimple
point-residual quotient with projective model A₆; its possible central
covering kernel is retained.

The full hexad preimage in L/O₂(L) is perfect by transfer at index 77.
The remaining kernel is a two-group, so the printed O²(C_L(z)) equals the
constructed perfect residual. Relative normality and source 1.2.4 place
this same residual in a normal C-component of the actual C_G(z).
The last theorem chooses an original involution centralized by both T and
the original H-star subgroup and returns this literal two-residual.

The exact A₆ quotient, containing-component restrictions, Xi placement and
the dihedral/semidihedral contradiction are still needed to remove the
inside-core branch. No unconditional M22 exclusion or M24 selection is
asserted here. Source: Aschbacher--Smith 8.2.2(1), printed p.715,
using H.13, I.1.3(4) and 1.2.4, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The same nonzero original Sylow-fixed vector has an actual hexad marking. -/
theorem sourceOrbit_m22_code_central_hexad
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ B : Finset (Fin 22), ∃ hB : B ∈ m22Blocks,
      (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
        (Additive.ofMul z) = m22HexadVector hB := by
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
  let q := d.componentEquiv.toMonoidHom.comp D.orbitComponentHom
  have hq : Function.Surjective q := d.componentEquiv.surjective.comp D.orbitComponentHom_surjective
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hPT : (P : Subgroup L).map L.subtype ≤ (T : Subgroup G) := by
    rw [hP]
    exact inf_le_left.trans (by
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le
        (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)])
  let S := P.mapSurjective hq
  have hfix : E (Additive.ofMul z) ∈ fixedSpace m22CodeRepresentation S := by
    intro b
    obtain ⟨l,hl,hb⟩ := b.property
    change m22CodeRepresentation b.val (E (Additive.ofMul z)) = E (Additive.ofMul z)
    rw [←hb]
    change m22CodeRepresentation (d.componentEquiv (D.orbitComponentHom l)) _ = _
    rw [←D.sourceOrbit_m22_component_coordinates m22CodeRepresentation
      m22OuterCodeRepresentation rfl d]
    apply congrArg E
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G)*(z : G)*(l : G)⁻¹=(z : G)
    rw [hz l (hPT (mem_map_of_mem L.subtype hl)),mul_inv_cancel_right]
  have hv : E (Additive.ofMul z) ≠ 0 := by
    intro he
    exact hne (congrArg Additive.toMul (E.injective (he.trans E.map_zero.symm)))
  exact NormalizedShadowRows.sylow_fixed_code_vector S _ hv hfix

private theorem code_restriction :
    m22OuterCodeRepresentation.comp m22ToPairStabilizer = m22CodeRepresentation := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  exact m22OuterCodeRepresentation_restrict g v

omit [Finite G] in
private theorem code_centralizer_mem_iff
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hzB : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul z) = m22HexadVector hB) (l : L) :
    d.componentEquiv (D.orbitComponentHom l) ∈ MulAction.stabilizer M22 B ↔
      l.val ∈ centralizer ({(z : G)} : Set G) := by
  let E := D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv
  let g := d.componentEquiv (D.orbitComponentHom l)
  let a := automizerRepresentation D.sourceOrbit (D.sourceOrbit.normalizerMonoidHom.rangeRestrict
    (inclusion D.sourceOrbit_component_normalizes l))
  have he : E (a (Additive.ofMul z)) = m22CodeRepresentation g (E (Additive.ofMul z)) :=
    D.sourceOrbit_m22_component_coordinates m22CodeRepresentation
      m22OuterCodeRepresentation code_restriction d l (Additive.ofMul z)
  have hfix : m22CodeRepresentation g (E (Additive.ofMul z)) = E (Additive.ofMul z) ↔
      l.val ∈ centralizer ({(z : G)} : Set G) := by
    constructor
    · intro hh
      have hv := congrArg (fun v : Additive D.sourceOrbit => (v.toMul : G))
        (E.injective (he.trans hh))
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hv)
    · intro hh
      have hv : a (Additive.ofMul z) = Additive.ofMul z := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change l.val*z.val*l.val⁻¹=z.val
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hh)
      exact he.symm.trans (congrArg E hv)
  have hmark := congrArg (fun v : M22Code => m22CodeRepresentation g v = v) hzB
  exact (NormalizedShadowRows.code_hexad_vector_fixed_iff hB g).symm.trans
    (hmark.symm.to_iff.trans hfix)

omit [Finite G] in
private theorem code_centralizer_cover_of_hexad
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hzB : (D.sourceOrbitCoordinates.symm.trans d.equivalence.toLinearEquiv)
      (Additive.ofMul z) = m22HexadVector hB) :
    ∃ c : (L ⊓ centralizer ({(z : G)} : Set G) : Subgroup G) →* MulAction.stabilizer M22 B,
      Function.Surjective c ∧
      (∀ l, (c l).val = d.componentEquiv (D.orbitComponentHom ⟨l,l.property.1⟩)) ∧
      c.ker = D.orbitComponentHom.ker.comap (inclusion (show
        L ⊓ centralizer ({(z : G)} : Set G) ≤ L from inf_le_left)) ∧
      (L ⊓ centralizer ({(z : G)} : Set G)).subgroupOf L =
        (MulAction.stabilizer M22 B).comap
          (d.componentEquiv.toMonoidHom.comp D.orbitComponentHom) := by
  let q : L →* M22 := d.componentEquiv.toMonoidHom.comp D.orbitComponentHom
  let C := L ⊓ centralizer ({(z : G)} : Set G)
  let S := MulAction.stabilizer M22 B
  let j : C →* L := inclusion inf_le_left
  have hf (l : L) : q l ∈ S ↔ l.val ∈ centralizer ({(z : G)} : Set G) :=
    D.code_centralizer_mem_iff d z hB hzB l
  let c : C →* S := (q.comp j).codRestrict S (fun l => (hf (j l)).mpr l.property.2)
  refine ⟨c,?_,fun _ => rfl,?_,?_⟩
  · intro y
    obtain ⟨l,hl⟩ := (d.componentEquiv.surjective.comp D.orbitComponentHom_surjective) y.val
    change q l = y.val at hl
    have hc : l.val ∈ C := ⟨l.property,(hf l).mp (hl.symm ▸ y.property)⟩
    exact ⟨⟨l,hc⟩,Subtype.ext hl⟩
  · ext l
    change c l = 1 ↔ D.orbitComponentHom (j l) = 1
    exact Subtype.ext_iff.trans d.componentEquiv.map_eq_one_iff
  · ext l
    change (l.val ∈ L ∧ l.val ∈ centralizer ({(z : G)} : Set G)) ↔ q l ∈ S
    exact ⟨fun hl => (hf l).mpr hl.2,fun hl => ⟨l.property,(hf l).mp hl⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- The full centralizer covers the actual hexad stabilizer, retaining the
original action map and its whole kernel. -/
theorem sourceOrbit_m22_code_centralizer_cover
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ B : Finset (Fin 22), ∃ _hB : B ∈ m22Blocks,
      ∃ c : (L ⊓ centralizer ({(z : G)} : Set G) : Subgroup G) →* MulAction.stabilizer M22 B,
        Function.Surjective c ∧
        (∀ l, (c l).val = d.componentEquiv (D.orbitComponentHom ⟨l,l.property.1⟩)) ∧
        c.ker = D.orbitComponentHom.ker.comap (inclusion (show
          L ⊓ centralizer ({(z : G)} : Set G) ≤ L from inf_le_left)) ∧
        (L ⊓ centralizer ({(z : G)} : Set G)).subgroupOf L =
          (MulAction.stabilizer M22 B).comap
            (d.componentEquiv.toMonoidHom.comp D.orbitComponentHom) := by
  have hex := @sourceOrbit_m22_code_central_hexad G _ _ T L V D d z hz hne
  rcases hex with ⟨B,hB,hzB⟩
  refine ⟨B,hB,?_⟩
  exact @code_centralizer_cover_of_hexad G _ T L V D d z B hB hzB

/-- The perfect residual of the original point centralizer has a genuine
quasisimple two-core quotient with projective model A₆. -/
theorem sourceOrbit_m22_code_centralizer_projective
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    IsQuasisimple (localResidual L z ⧸ pCore 2 (localResidual L z)) ∧
      Nonempty (((localResidual L z ⧸ pCore 2 (localResidual L z)) ⧸
        center (localResidual L z ⧸ pCore 2 (localResidual L z))) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨B,hB,f,hf,hval,_,_⟩ := D.sourceOrbit_m22_code_centralizer_cover d z hz hne
  let C := L ⊓ centralizer ({(z : G)} : Set G)
  let q := (QuotientGroup.mk' (pCore 2 L)).comp (inclusion (show C ≤ L from inf_le_left))
  have hq : IsPGroup 2 q.ker := by
    rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective _)
  let k := d.componentEquiv.toMonoidHom.comp (D.orbitComponentQuotientHom h)
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let : IsQuasisimple D.orbitComponent := D.orbitComponent_quasisimple h
  let : IsQuasisimple M22 := IsQuasisimple.of_mulEquiv d.componentEquiv
  let c : Covering (L ⧸ pCore 2 L) M22 :=
    { toMonoidHom := k
      surjective := d.componentEquiv.surjective.comp (D.orbitComponentQuotientHom_surjective h) }
  let a := NormalizedShadowRows.code_hexad_core_equiv hB
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (MulAction.stabilizer M22 B ⧸ pCore 2 (MulAction.stabilizer M22 B)) :=
    IsQuasisimple.of_mulEquiv a.symm
  let : Group.IsPerfect (MulAction.stabilizer M22 B) := m22HexadStabilizer_isPerfect hB
  obtain ⟨hR,⟨e⟩⟩ := Chapter8.MathieuShadowRows.residual_core_central_quotient_of_factorization
    q hq k c.ker_le_center f hf (MulAction.stabilizer M22 B).subtype
    (MulAction.stabilizer M22 B).subtype_injective (fun x => (hval x).symm)
  let b : solvableResidual C ≃* localResidual L z :=
    (solvableResidual C).equivMapOfInjective C.subtype C.subtype_injective
  let bq := QuotientGroup.congr _ _ b.symm (pCore_map_iso 2 b.symm)
  let := hR
  refine ⟨IsQuasisimple.of_mulEquiv bq.symm,⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ bq (FixedElementary.map_center bq)).trans
    (e.trans ((QuotientGroup.congr _ _ a (FixedElementary.map_center a)).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
        QuotientGroup.quotientBot)))

/-- The printed two-residual equals the constructed perfect point residual.
The full hexad preimage is perfect by transfer at index 77; only the actual
two-core kernel is removed in the comparison. -/
theorem sourceOrbit_m22_code_two_residual_eq
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    (pResidual 2 (L ⊓ centralizer ({(z : G)} : Set G) : Subgroup G)).map
      (L ⊓ centralizer ({(z : G)} : Set G)).subtype = localResidual L z := by
  obtain ⟨B,hB,c,hc,hval,hker,hpre⟩ := D.sourceOrbit_m22_code_centralizer_cover d z hz hne
  let C := L ⊓ centralizer ({(z : G)} : Set G)
  let q := QuotientGroup.mk' (pCore 2 L)
  let k := d.componentEquiv.toMonoidHom.comp (D.orbitComponentQuotientHom h)
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let : IsQuasisimple D.orbitComponent := D.orbitComponent_quasisimple h
  let : IsQuasisimple M22 := IsQuasisimple.of_mulEquiv d.componentEquiv
  let cf : Covering (L ⧸ pCore 2 L) M22 := {
    toMonoidHom := k
    surjective := d.componentEquiv.surjective.comp (D.orbitComponentQuotientHom_surjective h) }
  let P := (MulAction.stabilizer M22 B).comap k
  let : Group.IsPerfect P := NormalizedShadowRows.code_hexad_preimage_perfect
    (PerfectCentralCovering.ofCovering cf) hB
  have he : C.subgroupOf L = P.comap q := hpre
  let e : C ≃* P.comap q := (subgroupOfEquivOfLe (show C ≤ L from inf_le_left)).symm.trans
    (MulEquiv.subgroupCongr he)
  let f := q.subgroupComap P
  have hf : Function.Surjective f :=
    q.subgroupComap_surjective_of_surjective P (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    have hfk : f.ker = q.ker.subgroupOf (P.comap q) := by
      ext a
      change f a = 1 ↔ q a = 1
      exact Subtype.ext_iff
    rw [hfk,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have hk' : IsPGroup 2 (f.comp e.toMonoidHom).ker := by
    rw [←MonoidHom.comap_ker]
    exact hk.comap_of_injective _ e.injective
  rw [pResidual_eq_solvableResidual_of_perfect_image (f.comp e.toMonoidHom)
    (hf.comp e.surjective) hk']
  rfl

/-- Relative normality and the actual core quotient make the original
perfect point residual a C-component, normalized by the same Sylow. -/
theorem sourceOrbit_m22_code_centralizer_component
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ((localResidual L z).subgroupOf
      (normalizer (L : Set G) ⊓ centralizer ({(z : G)} : Set G))).IsCComponent ∧
      (T : Subgroup G) ≤ normalizer (localResidual L z : Set G) := by
  let R := localResidual L z
  let M := normalizer (L : Set G) ⊓ centralizer ({(z : G)} : Set G)
  have hRM : R ≤ M := (localResidual_le L z).trans (inf_le_inf_right _ L.le_normalizer)
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer
    (MathieuSextet.residual_normalized L z)
  let : Group.IsPerfect R := Group.IsPerfect.map _
  let : IsQuasisimple (R ⧸ pCore 2 R) :=
    (D.sourceOrbit_m22_code_centralizer_projective h d z hz hne).1
  have hp : IsPPerfect 2 R := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (R ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (R ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (R ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (R ⧸ N) inferInstance
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 R) (pCore_isPGroup (p := 2)) hp
  have htop : (⊤ : Subgroup (R.subgroupOf M)).IsCComponent := by
    simpa using ht.map_equiv (subgroupOfEquivOfLe hRM).symm
  refine ⟨?_,?_⟩
  · simpa only [←MonoidHom.range_eq_map,range_subtype] using
      htop.map_subtype (inferInstance : (R.subgroupOf M).Normal).isSubnormal
  · apply le_trans (le_inf D.sylow_normalizes_component ?_)
      (MathieuSextet.residual_normalized L z)
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hz t ht)

/-- Source 1.2.4 places the same original residual in a normal C-component
of the actual involution centralizer; the original Sylow is retained. -/
theorem sourceOrbit_m22_code_centralizer_containing_component
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ K : Subgroup G, K ≤ centralizer ({(z : G)} : Set G) ∧
      (K.subgroupOf (centralizer ({(z : G)} : Set G))).IsCComponent ∧
      localResidual L z ≤ K ∧
      centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G) := by
  obtain ⟨hR,hTR⟩ := D.sourceOrbit_m22_code_centralizer_component h d z hz hne
  let R := localResidual L z
  let C := centralizer ({(z : G)} : Set G)
  let M := normalizer (L : Set G) ⊓ C
  let U := zpowers (z : G)
  have hTC : (T : Subgroup G) ≤ C := fun t ht =>
    mem_centralizer_singleton_iff.mpr (hz t ht)
  have hUW : U ≤ D.sourceOrbit := zpowers_le.mpr z.property
  have hUne : U ≠ ⊥ := by
    intro he
    exact hne (Subtype.ext (mem_bot.mp (he ▸ mem_zpowers (z : G))))
  have hUC : U ≤ C := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)
  have hCU : C ≤ normalizer (U : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer (U : Set G))
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro c hc
    exact mem_centralizer_singleton_iff.mp hc
  have hU2 : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW
  have hRC : R ≤ C := (localResidual_le L z).trans inf_le_right
  have hRM : R ≤ M := (localResidual_le L z).trans (inf_le_inf_right _ L.le_normalizer)
  have hRTM : R ⊔ (T : Subgroup G) ≤ M := sup_le hRM
    (le_inf D.sylow_normalizes_component hTC)
  have hlocal : R ∈ Chapter1.L G (T : Subgroup G) := by
    refine ⟨hR.subgroupOf_of_le le_sup_left hRTM,?_,?_⟩
    · exact ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
    · have hUQ := le_pCoreIn_of_normalizes hU2
        ((hUW.trans D.sourceOrbit_weakClosure_setup.le_sylow).trans
          (show (T : Subgroup G) ≤ R ⊔ (T : Subgroup G) from le_sup_right))
        ((sup_le hRC hTC).trans hCU)
      exact ne_bot_of_le_ne_bot hUne hUQ
  let P := T.subtype hTC
  have hloc : R.subgroupOf C ∈ Chapter1.L C (P : Subgroup C) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTC hRC).mp ⟨hRC,hlocal⟩
  have hPN : (P : Subgroup C) ≤ normalizer (R.subgroupOf C : Set C) := by
    rw [←subgroupOf_normalizer_eq hRC]
    exact comap_mono hTR
  have hCH : C ∈ Chapter1.H G := ne_bot_of_le_ne_bot hUne
    (le_pCoreIn_of_normalizes hU2 hUC hCU)
  obtain ⟨K,⟨hK,hRK,hn⟩,_⟩ := Chapter1.Section02.lemma_1_2_4_containment_normality_source
    (Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hCH) P hloc hPN
  let K' := K.map C.subtype
  have hKC : K' ≤ C := map_subtype_le _
  have hsub : K'.subgroupOf C = K := comap_map_eq_self_of_injective C.subtype_injective _
  refine ⟨K',hKC,hsub.symm ▸ hK,?_,?_⟩
  · intro x hx
    let y : C := ⟨x,hRC hx⟩
    exact mem_map_of_mem C.subtype (hRK (show y ∈ R.subgroupOf C from hx))
  · exact (normal_subgroupOf_iff_le_normalizer hKC).mp (hsub.symm ▸ hn)

/-- The original H-star subgroup and Sylow centralize an actual involution
of the unchanged code orbit. Its point residual has the full projective
A₆ marking and a normal containing component in that same centralizer. -/
theorem sourceOrbit_m22_code_exists_centralizer_component
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ z : D.sourceOrbit, z ≠ 1 ∧ orderOf (z : G) = 2 ∧
      (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G) ∧
      H ≤ centralizer ({(z : G)} : Set G) ∧
      let R := (pResidual 2 (L ⊓ centralizer ({(z : G)} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({(z : G)} : Set G)).subtype
      IsQuasisimple (R ⧸ pCore 2 R) ∧
      Nonempty (((R ⧸ pCore 2 R) ⧸ center (R ⧸ pCore 2 R)) ≃*
        alternatingGroup (Fin 6)) ∧
      ∃ K : Subgroup G, K ≤ centralizer ({(z : G)} : Set G) ∧
        (K.subgroupOf (centralizer ({(z : G)} : Set G))).IsCComponent ∧
        R ≤ K ∧
        centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G) := by
  have hZ : D.sourceOrbit ⊓ centralizer (T : Set G) ≠ ⊥ :=
    inf_centralizer_ne_bot_of_pGroups (T : Subgroup G) D.sourceOrbit T.isPGroup'
      (IsElementaryAbelian.isPGroup 2 D.sourceOrbit)
      D.sourceOrbit_weakClosure_setup.normalizes D.sourceOrbit_weakClosure_setup.nontrivial
  obtain ⟨z,hzne⟩ := ne_bot_iff_exists_ne_one.mp hZ
  let w : D.sourceOrbit := ⟨z,z.property.1⟩
  have hne : w ≠ 1 := fun he => hzne (Subtype.ext
    (show (z : G) = 1 from congrArg (fun x : D.sourceOrbit => (x : G)) he))
  have hz : (w : G) ∈ centralizer (T : Set G) := z.property.2
  have h2 : (w : G)^2=1 := elemPow_eq_one_of_isElementaryAbelian _ w.property
  have ho : orderOf (w : G)=2 := orderOf_eq_prime h2
    (fun he => hne (Subtype.ext he))
  have hwO : (w : G) ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) :=
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨D.sourceOrbit_weakClosure_setup.le_sylow w.property,h2,hz⟩
  have hHC : H ≤ centralizer ({(w : G)} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      ((D.sourceOrbit_hstar_centralizes_omega h hnon hH hx w hwO).symm)
  obtain ⟨hq,he⟩ := D.sourceOrbit_m22_code_centralizer_projective h d w hz hne
  refine ⟨w,hne,ho,(fun t ht => mem_centralizer_singleton_iff.mpr (hz t ht)),hHC,?_⟩
  rw [D.sourceOrbit_m22_code_two_residual_eq h d w hz hne]
  exact ⟨hq,he,D.sourceOrbit_m22_code_centralizer_containing_component h d w hz hne⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
