module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesCartan
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesChiefPlane
public import Theory.GroupAction.SL2FourCubicLength
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.AbelianQuotientFixedSubgroup

/-!
# Locating the derived cubic obstruction in the original left core

Write V₂ for the cubic four-plane and S for the opposite G.2.3 core.
Local characteristic two puts V₂ in O₂(L). Since I = L₂U, L₂ lies in L,
and [U,U] lies in the original point, [S,S] also lies in L. The cubic
centralizes V₂[S,S] modulo O₂(L); its nonidentity image in PSL₂(2ⁿ)
centralizes no nonidentity Sylow two-element. Thus V₂[S,S] ≤ O₂(L).

Coprime splitting on [S,S], together with C_{V₂}(C) = 1, identifies the
previously constructed fixed factor as [S,S] intersect C_G(C). It is
disjoint from V₂. These are reductions for the remaining ambient
obstruction, not a claim that this factor vanishes.

Source: Aschbacher--Smith G.2.3 and 5.1.21--23, printed pp.333--334
and 644--646, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
open ChapterG.Section02 ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The moving plane lies in the two-core of the original rank-one component. -/
theorem LocalData.plane_le_original_core
    (d : LocalData T H C z) (hC : Nat.card C = 3) (hCL : C ≤ L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hchar : centralizer (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) :
      Set (L ⊔ (T : Subgroup G) : Subgroup G)) ≤ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) :
    plane C z ≤ L.pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let E := plane C z
  have hQT : Q ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow J (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hz := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp d.point_mem
  have hzQ : z ∈ Q := by
    apply mem_map_of_mem J.subtype (x := ⟨z,mem_sup_right hz.1⟩)
    apply hchar
    intro q hq
    apply Subtype.ext
    exact hz.2.2 q (hQT (mem_map_of_mem J.subtype hq))
  have hJQ : J ≤ normalizer (Q : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hEQ : E ≤ Q := conjugateSpanBy_le (zpowers_le.mpr hzQ)
    (hCL.trans (le_sup_left.trans hJQ))
  let : IsElementaryAbelian 2 E := d.g2.elementary
  have hCE : C ≤ normalizer (E : Set G) := le_normalizer_conjugateSpanBy _ _
  have hthree : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hC)
  have hEcomm : ⁅E,C⁆ = E :=
    Matrix.SpecialLinearGroup.CubicChiefCount.moved_eq_plane C E E hthree
      d.g2.elementary.isPGroup le_rfl hCE hCE d.plane_card
      (d.plane_cubic_length hC) (by rw [d.plane_cubic_length hC])
  have hEL : E ≤ L := by
    rw [← hEcomm]
    exact (commutator_mono le_rfl hCL).trans
      (le_normalizer_iff_commutator_le_right.mp (d.g2.V_le_T.trans hTL))
  exact (le_inf hEL hEQ).trans (inf_pCoreIn_le_of_le 2 (show L ≤ J from le_sup_left))

/-- The original component contains the derived subgroup of the opposite core. -/
theorem core_derived_le_original_component
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (b : (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData)
    (hCL : C ≤ L) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hVL : plane C z ≤ L)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let D := setup T (centralizer ({z} : Set G)) C z
    ⁅D.S g,D.S g⁆ ≤ L := by
  intro D
  have hga : g ∈ D.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨hI,_,_,_,_⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  have hactor : D.L ≤ L := conjugateSpanBy_le hCL hTL
  have hUU : ⁅D.U,D.U⁆ ≤ L :=
    (commutator_mono le_rfl s.U_le_core).trans
      (s.commutator_U_core_le_point.trans (s.point_le.trans hVL))
  have hII : ⁅D.I g,D.I g⁆ ≤ L := by
    rw [hI]
    exact (commutator_mono (sup_le_sup_right hactor D.U)
      (sup_le_sup_right hactor D.U)).trans
        (commutator_sup_le_of_normalized_derived L D.U (s.U_normal_in_T.1.trans hTL) hUU)
  exact (commutator_mono (pCoreIn_le 2 _) (pCoreIn_le 2 _)).trans hII

/-- A two-subgroup in L centralized by the cubic modulo O₂(L) lies in O₂(L). -/
theorem psl_cubic_fixed_mod_core_le_core
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hC : Nat.card C = 3) (hCL : C ≤ L)
    (X : Subgroup G) (hXT : X ≤ (T : Subgroup G)) (hXL : X ≤ L)
    (hcomm : ⁅X,C⁆ ≤ L.pCoreIn 2) : X ≤ L.pCoreIn 2 := by
  obtain ⟨F,_,_,hF,⟨e₀⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let e := e₀.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).symm
  let q : L →* SL(2,F) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let Q := P.mapSurjective hq
  have hCne : C ≠ ⊥ := by
    intro he
    have hc := card_eq_one.mpr he
    omega
  obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp hCne
  let aL : L := ⟨a,hCL a.property⟩
  have hdis : Disjoint C (L.pCoreIn 2) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 L).exists_card_eq
    rw [hC,hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have han : q aL ≠ 1 := by
    intro he
    have haK : aL ∈ pCore 2 L := hk ▸ he
    exact ha (Subtype.ext (Subgroup.disjoint_def.mp hdis a.property
      (mem_map_of_mem L.subtype haK)))
  have ha3 : q aL ^ 3 = 1 := by
    rw [← map_pow]
    have hh : aL ^ 3 = 1 := Subtype.ext
      (congrArg (fun x : C => (x : G)) (hC ▸ pow_card_eq_one' (x := a)))
    rw [hh,map_one]
  intro x hx
  let xL : L := ⟨x,hXL hx⟩
  have hxP : xL ∈ P := by
    change xL ∈ (P : Subgroup L)
    rw [hP]
    exact hXT hx
  have hxc : Commute (q xL) (q aL) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    have hmem := hcomm (commutator_mem_commutator hx a.property)
    have hmem' : ⁅xL,aL⁆ ∈ pCore 2 L := by
      obtain ⟨y,hy,he⟩ := hmem
      exact (show y = ⁅xL,aL⁆ from Subtype.ext he) ▸ hy
    exact (show ⁅xL,aL⁆ ∈ q.ker from hk.symm ▸ hmem')
  have he := Matrix.SpecialLinearGroup.eq_one_of_sylow_commutes_nontrivial_odd Q
    (q xL) (q aL) (mem_map_of_mem q hxP) han (by decide : Odd 3) ha3 hxc
  exact mem_map_of_mem L.subtype (show xL ∈ pCore 2 L from hk ▸ he)

/-- The full elementary derived layer is in the original left two-core. -/
theorem core_commutator_plane_le_original_core
    (c : LinearFieldCartan T L H A B C n) (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (b : (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hchar : centralizer (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) :
      Set (L ⊔ (T : Subgroup G) : Subgroup G)) ≤ pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let D := setup T (centralizer ({z} : Set G)) C z
    D.V ⊔ ⁅D.S g,D.S g⁆ ≤ L.pCoreIn 2 := by
  intro D
  let F := D.V ⊔ ⁅D.S g,D.S g⁆
  have hCL : C ≤ L := c.cubic_le.trans (c.left_le.trans inf_le_left)
  have hVK := d.plane_le_original_core c.cubic_card hCL hTL hchar
  have hga : g ∈ D.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨hI,_,hnorm,hi,_⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  obtain ⟨hN,hA,_σ,a,_,_,hVE,hES,_,_,_,hEC,_⟩ :=
    D.binary_source_clauses_three_to_seven s b s.U_normal_in_T.1 s.frattini_U_le_point
      g hga hgn hI (binarySourceCoreEquiv s b s.U_normal_in_T.1 g hga hgn) hnorm hi
  let := hN
  let := hA
  have hderived : ⁅D.S g,D.S g⁆ ≤ D.S₂ g := by
    apply commutator_le.mpr
    intro x hx y hy
    apply (a.coordinates_eq_one_iff (⁅(⟨x,hx⟩ : D.S g),⟨y,hy⟩⁆)).mp
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hFE : F ≤ D.S₂ g := sup_le hVE hderived
  have hST : D.S g ≤ (T : Subgroup G) :=
    (binary_S_le_LT_core s.U_normal_in_T.1 g hga
      (binaryStarEquiv s.toBaseHypothesis b s.U_normal_in_T.1)
      (binary_source_star_generation s b s.U_normal_in_T.1 g hga hgn)).trans
        s.toBaseHypothesis.binary_core_le_T
  have hCI : C ≤ D.I g := (le_conjugateSpanBy C (T : Subgroup G)).trans
    (le_sup_left.trans hI.ge)
  apply psl_cubic_fixed_mod_core_le_core hpsl hTL c.cubic_card hCL F
    (hFE.trans (hES.trans hST))
    (sup_le (hVK.trans (pCoreIn_le 2 L))
      (core_derived_le_original_component s b hCL hTL
        (hVK.trans (pCoreIn_le 2 L)) g hg hgn))
  exact ((commutator_mono hFE hCI).trans hEC).trans hVK

/-- The original cubic has no nonidentity fixed element in its four-plane. -/
theorem LocalData.plane_cubic_fixed_eq_bot
    (d : LocalData T H C z) (hC : Nat.card C = 3) :
    plane C z ⊓ centralizer (C : Set G) = ⊥ := by
  let E := plane C z
  let : IsElementaryAbelian 2 E := d.g2.elementary
  have hCE : C ≤ normalizer (E : Set G) := le_normalizer_conjugateSpanBy _ _
  have hthree : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hC)
  have hEcomm : ⁅E,C⁆ = E :=
    Matrix.SpecialLinearGroup.CubicChiefCount.moved_eq_plane C E E hthree
      d.g2.elementary.isPGroup le_rfl hCE hCE d.plane_card
      (d.plane_cubic_length hC) (by rw [d.plane_cubic_length hC])
  have hc : Nat.Coprime (Nat.card C) (Nat.card E) := by
    rw [hC,d.plane_card]
    decide
  have hd := commutator_disjoint_centralizer_of_coprime E C hCE hc
  rw [hEcomm,disjoint_iff,inf_eq_right.mpr inf_le_left] at hd
  exact hd

/-- The fixed factor constructed in the previous reduction is already
inside the derived subgroup and has trivial intersection with the plane. -/
theorem core_commutator_fixed_factor
    (c : LinearFieldCartan T L H A B C n) (d : LocalData T H C z)
    (s : (setup T (centralizer ({z} : Set G)) C z).Hypothesis)
    (b : (setup T (centralizer ({z} : Set G)) C z).BinaryNaturalData)
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let D := setup T (centralizer ({z} : Set G)) C z
    let R := ⁅D.S g,D.S g⁆
    let X := (D.V ⊔ R) ⊓ centralizer (C : Set G)
    X = R ⊓ centralizer (C : Set G) ∧ Disjoint D.V X := by
  intro D R X
  let F := D.V ⊔ R
  let Y := R ⊓ centralizer (C : Set G)
  obtain ⟨_,hEF,_,_⟩ := core_commutator_fixed_split c d s b g hg hgn
  let : IsElementaryAbelian 2 F := hEF
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.of_le
    (show R ≤ F from le_sup_right)
  have hga : g ∈ D.L := le_conjugateSpanBy C (T : Subgroup G) hg
  obtain ⟨hI,_,hnorm,hi,_⟩ := binary_source_inputs s b s.U_normal_in_T.1 g hga hgn
  obtain ⟨hN,hA,_σ,a,_,_,_,_,_,_,_,hEC,_⟩ :=
    D.binary_source_clauses_three_to_seven s b s.U_normal_in_T.1 s.frattini_U_le_point
      g hga hgn hI (binarySourceCoreEquiv s b s.U_normal_in_T.1 g hga hgn) hnorm hi
  let := hN
  let := hA
  have hRE : R ≤ D.S₂ g := by
    apply commutator_le.mpr
    intro x hx y hy
    apply (a.coordinates_eq_one_iff (⁅(⟨x,hx⟩ : D.S g),⟨y,hy⟩⁆)).mp
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  have hCI : C ≤ D.I g := (le_conjugateSpanBy C (T : Subgroup G)).trans
    (le_sup_left.trans hI.ge)
  have hCS := hCI.trans (D.binary_core_normalized g)
  have hCR : C ≤ normalizer (R : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.S g,D.S g⁆).map (MulAut.conj x).toMonoidHom = ⁅D.S g,D.S g⁆
    have hm : (D.S g).map (MulAut.conj x).toMonoidHom = D.S g :=
      mem_normalizer_iff_map_conj_eq.mp (hCS hx)
    rw [map_commutator,hm]
  have hmove : ⁅R,C⁆ ≤ D.V := (commutator_mono hRE hCI).trans hEC
  have hc : Nat.Coprime (Nat.card C) (Nat.card R) := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup 2 R).exists_card_eq
    rw [c.cubic_card,hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hRsplit := eq_commutator_sup_centralizer_of_solvable_coprime R C hCR
    inferInstance hc
  have hFY : F ≤ D.V ⊔ Y := sup_le le_sup_left
    (hRsplit.le.trans (sup_le (hmove.trans le_sup_left) le_sup_right))
  have hYV : Y ≤ normalizer (D.V : Set G) := by
    apply (le_centralizer_iff.mp ?_).trans (Subgroup.centralizer_le_normalizer _)
    exact ((show D.V ≤ F from le_sup_left).trans F.le_centralizer).trans
      (centralizer_le (inf_le_left.trans (show R ≤ F from le_sup_right)))
  have hfix : D.V ⊓ centralizer (C : Set G) = ⊥ := d.plane_cubic_fixed_eq_bot c.cubic_card
  constructor
  · apply le_antisymm ?_ (show Y ≤ X from le_inf
      (inf_le_left.trans (show R ≤ F from le_sup_right)) inf_le_right)
    intro x hx
    have hmul : x ∈ (D.V : Set G) * (Y : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left D.V Y hYV]
      exact hFY hx.1
    obtain ⟨v,hv,y,hy,he⟩ := hmul
    change v * y = x at he
    have hvC : v ∈ centralizer (C : Set G) := by
      have hh := (centralizer (C : Set G)).mul_mem hx.2
        ((centralizer (C : Set G)).inv_mem hy.2)
      rwa [← he,mul_inv_cancel_right] at hh
    have hv1 : v = 1 := hfix.le ⟨hv,hvC⟩
    rw [hv1,one_mul] at he
    exact he ▸ hy
  · rw [disjoint_iff]
    exact bot_unique ((le_inf inf_le_left (inf_le_right.trans inf_le_right)).trans hfix.le)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape
