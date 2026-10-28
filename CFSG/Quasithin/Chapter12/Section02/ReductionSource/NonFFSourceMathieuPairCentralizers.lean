module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuAutomizer
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPairCentralizers
public import Theory.Mathieu.SchurMultipliers.SourceCovers
public import Theory.Mathieu.SchurMultipliers.M23Kernel
public import Theory.GroupTheory.AutomorphismOvergroupCore
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# The distinguished-vector centralizers on the original Mathieu orbit

For the M23 and M24 rows, L induces the whole ambient automizer of the
chosen orbit W. The original central-quotient comparison and the genuine
Schur-multiplier results show that its kernel is precisely O2(L).

The concrete cocode markings then identify C_L(x)/O2(C_L(x)) with M22
or Aut(M22) for every source two-set vector x, respectively. Surjectivity
on the actual perfect residual lifts native displacement generation to
[W,C_L(x)^∞] = W. The M23 application constructs its cocode marking from
the original hypotheses; the M24 application retains the code alternative
and constructs these centralizer data on the cocode alternative.

These are the literal stabilizer and residual-action inputs of 8.1.1.
The pushing-up hypotheses, ambient containment C_G(x) ≤ N_G(L), stronger
cocode escaping bounds and final J4 recognition remain with the same
normalized Mathieu assembly. No ambient centralizer containment is asserted
here. The private implementation import checks the original action formula.
Source: Aschbacher--Smith, H.15.1(1)--(2), 8.1.1 and I.1.3,
printed pp.398,712,407--408 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual component conjugation map into the source-orbit automizer. -/
def mathieuComponentAutomizer : L →* Automizer D.sourceOrbit :=
  D.sourceOrbit.normalizerMonoidHom.rangeRestrict.comp
    (inclusion D.sourceOrbit_component_normalizes)

omit [Finite G] in
private theorem component_coordinates (l : L) (w : D.orbitSpace) :
    D.sourceOrbitCoordinates (D.orbitRepresentation (D.orbitComponentHom l) w) =
      automizerRepresentation D.sourceOrbit (D.mathieuComponentAutomizer l)
        (D.sourceOrbitCoordinates w) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (D.sourceOrbitCoordinates_apply
    (D.orbitRepresentation (D.orbitComponentHom l) w)).trans
      (congrArg (fun x : G => (l : G) * x * (l : G)⁻¹)
        (D.sourceOrbitCoordinates_apply w).symm)

private theorem component_surjective_of_simple
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    [IsSimpleGroup (Automizer D.sourceOrbit)] :
    Function.Surjective D.mathieuComponentAutomizer := by
  let N := normalizer (D.sourceOrbit : Set G)
  let q := D.sourceOrbit.normalizerMonoidHom.rangeRestrict
  have hk : D.mathieuComponentAutomizer.range = (L.subgroupOf N).map q := by
    ext a
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨inclusion D.sourceOrbit_component_normalizes l,l.property,rfl⟩
    · rintro ⟨l,hl,rfl⟩
      exact ⟨⟨l,hl⟩,rfl⟩
  let : (L.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer
    (D.sourceOrbit_normalizer_le h)
  have hnormal : D.mathieuComponentAutomizer.range.Normal :=
    hk ▸ Normal.map inferInstance q D.sourceOrbit.normalizerMonoidHom.rangeRestrict_surjective
  obtain ⟨f,hf,he,hfq⟩ := faithful_action_factor
    (D.orbitRepresentation.comp D.orbitComponent.subtype)
    (automizerRepresentation D.sourceOrbit)
    ((subspaceImageRepresentation_injective _ _).comp Subtype.val_injective)
    (automizerRepresentation_injective _) D.orbitComponentHom
    D.orbitComponentHom_surjective D.mathieuComponentAutomizer
    D.sourceOrbitCoordinates D.component_coordinates
  have hne : D.mathieuComponentAutomizer.range ≠ ⊥ := by
    intro hb
    obtain ⟨a,ha⟩ := exists_ne (1 : D.orbitComponent)
    obtain ⟨l,hl⟩ := D.orbitComponentHom_surjective a
    have hk1 : D.mathieuComponentAutomizer l = 1 :=
      mem_bot.mp (hb ▸ (show D.mathieuComponentAutomizer l ∈ D.mathieuComponentAutomizer.range from ⟨l,rfl⟩))
    have hf1 : f a = f 1 :=
      (congrArg f hl).symm.trans ((hfq l).trans (hk1.trans (map_one f).symm))
    exact ha (hf hf1)
  exact MonoidHom.range_eq_top.mp (hnormal.eq_bot_or_eq_top.resolve_left hne)

/-- For either large Mathieu quotient, L already induces the full ambient
source-orbit automizer, not only the original LT action. -/
theorem sourceOrbit_largeMathieu_component_surjective
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24)) :
    Function.Surjective D.mathieuComponentAutomizer := by
  rcases hq with h23 | h24
  · rcases D.sourceOrbit_m23_automizer_marking h hs h23 with ⟨a,_,_⟩ | ⟨a,_,_⟩ <;>
      let := m23_isSimpleGroup <;>
      let := a.isSimpleGroup <;>
      exact D.component_surjective_of_simple h
  · obtain ⟨a,_⟩ := D.sourceOrbit_m24_automizer_marking h hs h24
    let := m24_isSimpleGroup
    let := a.isSimpleGroup
    exact D.component_surjective_of_simple h

/-- The surviving M23 marking gives the actual M22 quotient of every
source two-set centralizer in L. Its full action kernel is retained and the
literal perfect residual generates the original source orbit by commutators. -/
theorem sourceOrbit_m23_pair_residuals_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ a : Automizer D.sourceOrbit ≃* M23,
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode,
        (∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
          m23CocodeRepresentation (a b) (E v)) ∧
        ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ m23WeightTwoOrbit →
          ∃ f : (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) →* M22,
            Function.Surjective f ∧
            f.ker = (centralizer (D.sourceOrbit : Set G)).subgroupOf
              (L ⊓ centralizer ({(x : G)} : Set G)) ∧
            ⁅D.sourceOrbit, (solvableResidual
              (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
                (L ⊓ centralizer ({(x : G)} : Set G)).subtype⁆ = D.sourceOrbit := by
  obtain ⟨a,E,hE⟩ := D.sourceOrbit_m23_cocode_of_many h hmany hV hq hnon
  refine ⟨a,E,hE,?_⟩
  intro x hx
  let q := a.toMonoidHom.comp D.mathieuComponentAutomizer
  have hq' : Function.Surjective q := a.surjective.comp
    (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (Or.inl hq))
  obtain ⟨f,hf,hcompat,hker,hm⟩ := MathieuPairs.pair_residual_lift
    D.sourceOrbit L D.sourceOrbit_component_normalizes m23CocodeRepresentation q hq' E
    (fun l v => hE (D.mathieuComponentAutomizer l) v) m23Cocode_faithful x
    (ChapterH.Section13To16.CocodeLocal.m23_pair_residual_commutator hx)
  obtain ⟨b⟩ := ChapterH.Section13To16.CocodeLocal.m23_pair_stabilizer hx
  refine ⟨b.toMonoidHom.comp f,b.surjective.comp hf,?_,hm⟩
  rw [MonoidHom.ker_comp_of_injective _ _ b.injective,hker]

/-- On the actual M24 cocode branch the same construction retains the full
Aut(M22) quotient, including the genuine outer involution. -/
theorem sourceOrbit_m24_pair_residuals
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (x : D.sourceOrbit) (hx : E (Additive.ofMul x) ∈ weightTwoOrbit) :
    ∃ f : (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) →* MulAut M22,
      Function.Surjective f ∧
      f.ker = (centralizer (D.sourceOrbit : Set G)).subgroupOf
        (L ⊓ centralizer ({(x : G)} : Set G)) ∧
      ⁅D.sourceOrbit, (solvableResidual
        (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
          (L ⊓ centralizer ({(x : G)} : Set G)).subtype⁆ = D.sourceOrbit := by
  let := m24_isSimpleGroup
  let := a.isSimpleGroup
  let q := a.toMonoidHom.comp D.mathieuComponentAutomizer
  have hq : Function.Surjective q := a.surjective.comp (D.component_surjective_of_simple h)
  obtain ⟨f,hf,hcompat,hker,hm⟩ := MathieuPairs.pair_residual_lift
    D.sourceOrbit L D.sourceOrbit_component_normalizes cocodeRepresentation q hq E
    (fun l v => hE (D.mathieuComponentAutomizer l) v) cocode_faithful x
    (ChapterH.Section13To16.CocodeLocal.m24_pair_residual_commutator hx)
  obtain ⟨b⟩ := ChapterH.Section13To16.CocodeLocal.m24_pair_stabilizer hx
  refine ⟨b.toMonoidHom.comp f,b.surjective.comp hf,?_,hm⟩
  rw [MonoidHom.ker_comp_of_injective _ _ b.injective,hker]

private theorem kernel_of_injective_quotient
    {A B : Type*} [Group A] [Group B] (f : A →* B)
    (N : Subgroup A) [N.Normal] (hN : N ≤ f.ker)
    (hi : Function.Injective (QuotientGroup.lift N f hN)) : f.ker = N := by
  apply le_antisymm _ hN
  have hb := (MonoidHom.ker_eq_bot_iff (QuotientGroup.lift N f hN)).mpr hi
  rw [QuotientGroup.ker_lift,Subgroup.map_eq_bot_iff,QuotientGroup.ker_mk'] at hb
  exact hb

private theorem faithful_of_quasisimple_centerless
    {A B : Type*} [Group A] [Group B] [Nontrivial B] [IsQuasisimple A]
    (f : A →* B) (hf : Function.Surjective f) (hc : center A = ⊥) :
    Function.Injective f := by
  apply (MonoidHom.ker_eq_bot_iff f).mp
  rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with hker | htop
  · exact bot_unique (hker.trans_eq hc)
  · obtain ⟨b,hb⟩ := exists_ne (1 : B)
    obtain ⟨a,ha⟩ := hf b
    exact (hb (ha.symm.trans (show a ∈ f.ker from htop.symm ▸ mem_top a))).elim

/-- In the two large Mathieu rows the original action kernel on L is
exactly O2(L). The central covering kernel is discharged by the genuine
M23 and M24 Schur-multiplier theorems. -/
theorem sourceOrbit_largeMathieu_component_kernel
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24)) :
    D.mathieuComponentAutomizer.ker = pCore 2 L := by
  let := h.quasisimple
  have hc : center (L ⧸ pCore 2 L) = ⊥ := by
    rcases hq with he | he
    · obtain ⟨e⟩ := he
      exact SchurMultipliers.m23_center_eq_bot_of_centralQuotientEquiv
        ((D.orbitCentralQuotientEquiv h).trans e)
    · obtain ⟨e⟩ := he
      exact SchurMultipliers.m24_center_eq_bot_of_centralQuotientEquiv
        ((D.orbitCentralQuotientEquiv h).trans e)
  have hi := faithful_of_quasisimple_centerless (D.orbitComponentQuotientHom h)
    (D.orbitComponentQuotientHom_surjective h) hc
  have hcore : D.orbitComponentHom.ker = pCore 2 L :=
    kernel_of_injective_quotient D.orbitComponentHom (pCore 2 L)
      (D.orbitComponentHom_kills_core h) hi
  obtain ⟨f,hf,he,hfq⟩ := faithful_action_factor
    (D.orbitRepresentation.comp D.orbitComponent.subtype)
    (automizerRepresentation D.sourceOrbit)
    ((subspaceImageRepresentation_injective _ _).comp Subtype.val_injective)
    (automizerRepresentation_injective _) D.orbitComponentHom
    D.orbitComponentHom_surjective D.mathieuComponentAutomizer
    D.sourceOrbitCoordinates D.component_coordinates
  have heq : D.mathieuComponentAutomizer = f.comp D.orbitComponentHom :=
    (MonoidHom.ext hfq).symm
  rw [heq,MonoidHom.ker_comp_of_injective _ _ hf,hcore]

/-- The literal common kernel in a centralizer C_L(x) is a two-group;
this uses the original L action and retains the actual vector x. -/
theorem sourceOrbit_largeMathieu_pair_kernel_isTwoGroup
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (x : D.sourceOrbit) :
    IsPGroup 2 ((centralizer (D.sourceOrbit : Set G)).subgroupOf
      (L ⊓ centralizer ({(x : G)} : Set G))) := by
  let C := L ⊓ centralizer ({(x : G)} : Set G)
  let i : C →* L := inclusion inf_le_left
  have heq : (centralizer (D.sourceOrbit : Set G)).subgroupOf C =
      (pCore 2 L).comap i := by
    rw [←D.sourceOrbit_largeMathieu_component_kernel h hq]
    ext c
    change (c : G) ∈ centralizer (D.sourceOrbit : Set G) ↔
      D.mathieuComponentAutomizer (i c) = 1
    constructor
    · intro hc
      apply Subtype.ext
      apply MulEquiv.ext
      intro w
      apply Subtype.ext
      change (c : G) * (w : G) * (c : G)⁻¹ = (w : G)
      rw [mul_inv_eq_iff_eq_mul]
      exact (mem_centralizer_iff.mp hc w w.property).symm
    · intro hc
      apply mem_centralizer_iff.mpr
      intro w hw
      have hv := congrArg (fun a : Automizer D.sourceOrbit => (a.val (⟨w,hw⟩ : D.sourceOrbit) : G)) hc
      change (c : G) * w * (c : G)⁻¹ = w at hv
      exact ((mul_inv_eq_iff_eq_mul).mp hv).symm
  rw [heq]
  exact pCore_isPGroup.comap_of_injective i (inclusion_injective _)

private theorem m22_twoCore : pCore 2 M22 = ⊥ := by
  let := m22_isSimpleGroup
  rcases (inferInstance : (pCore 2 M22).Normal).eq_bot_or_eq_top with hb | ht
  · exact hb
  · obtain ⟨n,hn⟩ := (pCore_isPGroup : IsPGroup 2 (pCore 2 M22)).exists_card_eq
    have hc : Nat.card (pCore 2 M22) = Nat.card M22 := by
      rw [ht]
      exact Nat.card_congr topEquiv.toEquiv
    rw [hc,m22_order] at hn
    have h3 : 3 ∣ 2^n := hn ▸ (by decide : 3 ∣ 443520)
    have h2 := Nat.prime_three.dvd_of_dvd_pow h3
    norm_num at h2

private theorem autM22_twoCore : pCore 2 (MulAut M22) = ⊥ := by
  have hc := automorphism_core_eq_bot 2 (conj_injective_of_center_eq_bot m22_center_eq_bot)
    m22_twoCore (⊤ : Subgroup (MulAut M22)) (fun _ => mem_top _)
  have he := pCore_map_iso 2 (topEquiv : (⊤ : Subgroup (MulAut M22)) ≃* MulAut M22)
  rw [hc,Subgroup.map_bot] at he
  exact he.symm

private theorem pair_quotient_of_kernel
    {Q : Type*} [Group Q] [Finite Q] (hQ : pCore 2 Q = ⊥)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (x : D.sourceOrbit)
    (f : (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) →* Q)
    (hf : Function.Surjective f)
    (hker : f.ker = (centralizer (D.sourceOrbit : Set G)).subgroupOf
      (L ⊓ centralizer ({(x : G)} : Set G))) :
    Nonempty (((L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ⧸
      pCore 2 (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)) ≃* Q) := by
  have hp : IsPGroup 2 f.ker := hker.symm ▸
    D.sourceOrbit_largeMathieu_pair_kernel_isTwoGroup h hq x
  have hc := f.comap_pCore_of_ker_isPGroup hf hp
  rw [hQ,MonoidHom.comap_bot] at hc
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- The precise two-core quotient and residual-action inputs of source
8.1.1 on every distinguished vector in the surviving M23 row. -/
theorem sourceOrbit_m23_pair_quotients_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ a : Automizer D.sourceOrbit ≃* M23,
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode,
        (∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
          m23CocodeRepresentation (a b) (E v)) ∧
        ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ m23WeightTwoOrbit →
          Nonempty (((L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ⧸
            pCore 2 (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)) ≃* M22) ∧
          ⁅D.sourceOrbit, (solvableResidual
            (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
              (L ⊓ centralizer ({(x : G)} : Set G)).subtype⁆ = D.sourceOrbit := by
  obtain ⟨a,E,hE,hpair⟩ := D.sourceOrbit_m23_pair_residuals_of_many h hmany hV hq hnon
  refine ⟨a,E,hE,?_⟩
  intro x hx
  obtain ⟨f,hf,hker,hm⟩ := hpair x hx
  exact ⟨D.pair_quotient_of_kernel m22_twoCore h.toHypothesis1221 (Or.inl hq)
    x f hf hker,hm⟩

/-- The M24 cocode gives the genuine outer extension Aut(M22) modulo the
full two-core of the original vector centralizer, and the same residual
moves the entire original orbit. -/
theorem sourceOrbit_m24_pair_quotient
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    (x : D.sourceOrbit) (hx : E (Additive.ofMul x) ∈ weightTwoOrbit) :
    Nonempty (((L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ⧸
      pCore 2 (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)) ≃* MulAut M22) ∧
    ⁅D.sourceOrbit, (solvableResidual
      (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({(x : G)} : Set G)).subtype⁆ = D.sourceOrbit := by
  obtain ⟨f,hf,hker,hm⟩ := D.sourceOrbit_m24_pair_residuals h a E hE x hx
  exact ⟨D.pair_quotient_of_kernel autM22_twoCore h (Or.inr hq) x f hf hker,hm⟩

/-- Source construction on the M24 row, retaining both the code alternative
and the complete pair-centralizer data in its cocode alternative. -/
theorem sourceOrbit_m24_code_or_pair_quotients_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ a : Automizer D.sourceOrbit ≃* M24,
      Nonempty ((automizerRepresentation D.sourceOrbit).Equiv
        (codeRepresentation.comp a.toMonoidHom)) ∨
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode,
        (∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
          cocodeRepresentation (a b) (E v)) ∧
        ∀ x : D.sourceOrbit, E (Additive.ofMul x) ∈ weightTwoOrbit →
          Nonempty (((L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) ⧸
            pCore 2 (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)) ≃* MulAut M22) ∧
          ⁅D.sourceOrbit, (solvableResidual
            (L ⊓ centralizer ({(x : G)} : Set G) : Subgroup G)).map
              (L ⊓ centralizer ({(x : G)} : Set G)).subtype⁆ = D.sourceOrbit := by
  obtain ⟨a,hc | hd⟩ := D.sourceOrbit_m24_automizer_marking h.toHypothesis1221
    (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hq
  · obtain ⟨E⟩ := hc
    have hE (b) (v) : E (automizerRepresentation D.sourceOrbit b v) =
        cocodeRepresentation (a b) (E v) := LinearMap.congr_fun (E.isIntertwining' b) v
    exact ⟨a,Or.inr ⟨E.toLinearEquiv,hE,fun x hx =>
      D.sourceOrbit_m24_pair_quotient h.toHypothesis1221 hq a E.toLinearEquiv hE x hx⟩⟩
  · exact ⟨a,Or.inl hd⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
