module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Block
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetResidual
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# The original M24 cocode involution centralizer

The cocode marking sends every nonzero original T-fixed vector to the
common tetrad class of a concrete native sextet. Its literal centralizer
in L maps onto that sextet stabilizer with two-group kernel. Restricting
to the perfect residual and dividing by its full two-core gives the
actual nonsplit triple cover 3.A₆. Relative normality yields a C-component
of C_{N_G(L)}(z), and source 1.2.4 places this same residual in a normal
C-component of C_G(z), with the original Sylow subgroup retained. The
residual marking has exactly V∩L_z as kernel, and its full two-core maps
onto all native sextet translations. These are literal actions for the
commutator-space calculation, without an assumed containment V≤L_z.

The completed cocode block theorem supplies the order-two subgroup
Ω₁Z(T) and hence its generator. No point marking, residual quotient,
or containing-component callback remains. The cocode representation
marking is still the earlier module-classification input. This proves
source 8.2.11(1), its group quotient in (2), and the component placement
used in 8.2.13. The module sections, normal closure, remaining Mathieu
branches and ambient J4 recognition stay with qt-d-1222-nonff-mathieu.
Source: Aschbacher–Smith H.15.3, 8.2.11 and 8.2.13, printed pp.400,722,
refs/quasithin.pdf. The lower native model retains its ATLAS attribution.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry MathieuCode
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Stellmacher
open Chapter8.Section02.Centralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
set_option backward.isDefEq.respectTransparency false

/-- A nontrivial original T-fixed vector is the tetrad vector of an actual
native sextet under the original cocode marking. -/
theorem sourceOrbit_m24_central_sextet
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ S : Sextet, E (Additive.ofMul z) = sextetVector S := by
  have hsur := D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
    (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (.inr hq)
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have hPT : (P : Subgroup L).map L.subtype ≤ (T : Subgroup G) := by
    rw [hP]
    exact inf_le_left.trans (by
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le
        (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)])
  let f := a.toMonoidHom.comp D.mathieuComponentAutomizer
  let Q := P.mapSurjective (f := f) (a.surjective.comp hsur)
  have hfix (b : Q) : cocodeRepresentation b.val (E (Additive.ofMul z)) = E (Additive.ofMul z) := by
    obtain ⟨l,hl,hb⟩ := b.property
    rw [←hb]
    change cocodeRepresentation (a (D.mathieuComponentAutomizer l)) (E (Additive.ofMul z)) = _
    rw [←hE]
    apply congrArg E
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G)*(z : G)*(l : G)⁻¹=(z : G)
    rw [hz l (hPT (mem_map_of_mem L.subtype hl)),mul_inv_cancel_right]
  have hv : E (Additive.ofMul z) ≠ 0 := by
    intro he
    exact hne (congrArg Additive.toMul (E.injective (he.trans E.map_zero.symm)))
  obtain ⟨S,hS,_⟩ := MathieuSextet.sylow_fixed_sextet Q _ hv hfix
  exact ⟨S,hS⟩

/-- Source 8.2.11(1) and the group quotient in (2), on the original
central involution. The centralizer map records its literal M24 action. -/
theorem sourceOrbit_m24_centralizer_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ (S : Sextet)
      (c : (L ⊓ centralizer ({(z : G)} : Set G) : Subgroup G) →* sextetStabilizer S),
      E (Additive.ofMul z) = sextetVector S ∧ Function.Surjective c ∧ IsPGroup 2 c.ker ∧
      (∀ l, (c l).val = a (D.mathieuComponentAutomizer ⟨l,l.property.1⟩)) ∧
      Nonempty ((localResidual L z ⧸ pCore 2 (localResidual L z)) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      ((localResidual L z).subgroupOf
        (normalizer (L : Set G) ⊓ centralizer ({(z : G)} : Set G))).IsCComponent ∧
      (T : Subgroup G) ≤ normalizer (localResidual L z : Set G) := by
  obtain ⟨S,hS⟩ := D.sourceOrbit_m24_central_sextet h hmany hV hq hnon a E hE z hz hne
  let q := a.toMonoidHom.comp D.mathieuComponentAutomizer
  have hsur : Function.Surjective q := a.surjective.comp
    (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (.inr hq))
  have hk : IsPGroup 2 q.ker := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective,
      D.sourceOrbit_largeMathieu_component_kernel h.toHypothesis1221 (.inr hq)]
    exact pCore_isPGroup
  obtain ⟨c,hc,hk,hcval⟩ := MathieuSextet.marked_centralizer_action D.sourceOrbit L
    D.sourceOrbit_component_normalizes q hsur hk E (fun l w => hE (D.mathieuComponentAutomizer l) _)
    z S hS
  obtain ⟨e⟩ := MathieuSextet.marked_residual_quotient L z S c hc hk
  refine ⟨S,c,hS,hc,hk,hcval,⟨e⟩,MathieuSextet.marked_residual_component L z e,?_⟩
  apply le_trans (le_inf D.sylow_normalizes_component ?_) (MathieuSextet.residual_normalized L z)
  intro t ht
  exact mem_centralizer_singleton_iff.mpr (hz t ht)

private theorem generator_of_card_two (W Z : Subgroup G) [IsElementaryAbelian 2 W]
    (hZW : Z ≤ W) (hc : Nat.card Z = 2) :
    ∃ z : W, z ≠ 1 ∧ orderOf (z : G) = 2 ∧ zpowers (z : G) = Z := by
  have hZne : Z ≠ ⊥ := (one_lt_card_iff_ne_bot _).mp (by rw [hc]; decide)
  obtain ⟨z,hzne⟩ := ne_bot_iff_exists_ne_one.mp hZne
  have hzn : (z : G) ≠ 1 := fun he => hzne (Subtype.ext he)
  let zv : W := ⟨z,hZW z.property⟩
  have hvne : zv ≠ 1 := fun he => hzn (congrArg Subtype.val he)
  have ho : orderOf (z : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) (z : G) (hZW z.property)) hzn
  refine ⟨zv,hvne,ho,?_⟩
  apply eq_of_le_of_card_ge (zpowers_le.mpr z.property)
  rw [Nat.card_zpowers,ho,hc]

/-- The original order-two fixed subgroup supplies its generator and the
full literal centralizer quotient, without a point-marking callback. -/
theorem sourceOrbit_m24_exists_centralizer_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v)) :
    ∃ z : D.sourceOrbit, z ≠ 1 ∧ orderOf (z : G) = 2 ∧
      zpowers (z : G) = omegaOneCenterAmbient (T : Subgroup G) ∧
      Nonempty ((localResidual L z ⧸ pCore 2 (localResidual L z)) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      ((localResidual L z).subgroupOf
        (normalizer (L : Set G) ⊓ centralizer ({(z : G)} : Set G))).IsCComponent ∧
      (T : Subgroup G) ≤ normalizer (localResidual L z : Set G) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hz,hzc⟩ :=
    D.sourceOrbit_m24_cocode_block_structure h hmany hV hq hnon a E hE
  obtain ⟨z,hne,ho,hZ⟩ := generator_of_card_two D.sourceOrbit
    (omegaOneCenterAmbient (T : Subgroup G)) (hz.le.trans inf_le_left) hzc
  have hzf : (z : G) ∈ centralizer (T : Set G) :=
    (hz.le.trans inf_le_right) (hZ.le (mem_zpowers _))
  obtain ⟨_,_,_,_,_,_,he,hcomp,hn⟩ :=
    D.sourceOrbit_m24_centralizer_residual h hmany hV hq hnon a E hE z hzf hne
  exact ⟨z,hne,ho,hZ,he,hcomp,hn⟩

/-- The actual centralizer contains a normal C-component above the same
point residual. This is the original component placement used in 8.2.13. -/
theorem sourceOrbit_m24_centralizer_containing_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ K : Subgroup G, K ≤ centralizer ({(z : G)} : Set G) ∧
      (K.subgroupOf (centralizer ({(z : G)} : Set G))).IsCComponent ∧
      localResidual L z ≤ K ∧
      centralizer ({(z : G)} : Set G) ≤ normalizer (K : Set G) := by
  obtain ⟨_,_,_,_,_,_,_,hR,hTR⟩ :=
    D.sourceOrbit_m24_centralizer_residual h hmany hV hq hnon a E hE z hz hne
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
  have hU2 : IsPGroup 2 U :=
    (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW
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

/-- The original point residual has exactly V∩L_z as marking kernel,
and its intrinsic two-core covers every native sextet translation. This
retains the action required to compute [V,O₂(L_z)] in source 8.2.11. -/
theorem sourceOrbit_m24_centralizer_core_action
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (z : D.sourceOrbit) (hz : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ (S : Sextet) (r : localResidual L z →* sextetStabilizer S),
      E (Additive.ofMul z) = sextetVector S ∧
      r.range = solvableResidual (sextetStabilizer S) ∧
      r.ker = D.sourceOrbit.subgroupOf (localResidual L z) ∧
      (pCore 2 (localResidual L z)).map r =
        (MathieuCode.SextetLayers.CoordinateTransport.nativeQuotient S).ker ∧
      ∀ x, (r x).val = a (D.mathieuComponentAutomizer
        ⟨x,((localResidual_le L z) x.property).1⟩) := by
  obtain ⟨S,c,hS,hc,hk,hcval,_,_,_⟩ :=
    D.sourceOrbit_m24_centralizer_residual h hmany hV hq hnon a E hE z hz hne
  obtain ⟨r,hr,_,hcore,hrval⟩ := MathieuSextet.marked_residual_core_action L z S c hc hk
  have hval (x : localResidual L z) : (r x).val =
      a (D.mathieuComponentAutomizer ⟨x,((localResidual_le L z) x.property).1⟩) := by
    rw [hrval]
    exact hcval _
  obtain ⟨_,_,hW⟩ := D.sourceOrbit_m24_cocode_block_core h hmany hV hq hnon a E hE
  let R := localResidual L z
  let j : R →* L := inclusion ((localResidual_le L z).trans inf_le_left)
  let q := a.toMonoidHom.comp D.mathieuComponentAutomizer
  have he : (sextetStabilizer S).subtype.comp r = q.comp j := by
    apply MonoidHom.ext
    exact hval
  have hqker : q.ker = pCore 2 L := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    exact D.sourceOrbit_largeMathieu_component_kernel h.toHypothesis1221 (.inr hq)
  have hrker : r.ker = (pCore 2 L).comap j := by
    rw [←MonoidHom.ker_comp_of_injective r (sextetStabilizer S).subtype
      (sextetStabilizer S).subtype_injective,he]
    change q.ker.comap j = _
    rw [hqker]
  refine ⟨S,r,hS,hr,?_,hcore,hval⟩
  rw [hrker]
  ext x
  change j x ∈ pCore 2 L ↔ (x : G) ∈ D.sourceOrbit
  constructor
  · intro hx
    exact hW.ge (mem_map_of_mem L.subtype hx)
  · intro hx
    obtain ⟨y,hy,hyx⟩ := hW.le hx
    exact (show y = j x from Subtype.ext hyx) ▸ hy

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
