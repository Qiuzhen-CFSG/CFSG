module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointNaturalCoreIntersection
public import Theory.GroupTheory.Commutator.CentralizerQuotient

/-!
# The original core quotient is the same natural eight as the central seed

The faithful action on W identifies C_Q(W) with the literal Q intersection
O2(C). Both W's Q-displacement and its L-displacement lie in the original
natural eight V. A central commutator row therefore gives an equivariant
isomorphism from Q/C_Q(W) onto V. The denominator is retained explicitly;
this does not assert that Q is characteristic in the point kernel.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem irreducible_section_dichotomy
    {A V : Type*} [Group A] [AddCommGroup V] [Module (ZMod 2) V]
    {L D Z T : Subgroup G} {a : L →* A} {σ : Representation (ZMod 2) A V}
    [IsIrreducible σ] (ha : Function.Surjective a)
    (hs : HasSectionModel L D Z a σ)
    (hZT : Z ≤ T) (hTD : T ≤ D) (hLT : L ≤ normalizer T) : T = Z ∨ T = D := by
  obtain ⟨hZD,hLD,_,hn,e,he⟩ := hs
  let := hn
  let p := e.toMonoidHom.comp (QuotientGroup.mk' (Z.subgroupOf D))
  have hp : Function.Surjective p := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : p.ker = Z.subgroupOf D := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let U : Subrepresentation σ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 ((T.subgroupOf D).map p).toAddSubgroup'
    apply_mem_toSubmodule g := by
      intro v hv
      obtain ⟨l,rfl⟩ := ha g
      change Multiplicative.ofAdd v ∈ (T.subgroupOf D).map p at hv
      obtain ⟨x,hx,hv⟩ := hv
      let y := D.normalizerMonoidHom (inclusion hLD l) x
      have hyT : (y : G) ∈ T := (mem_normalizer_iff.mp (hLT l.property) x).mp hx
      change Multiplicative.ofAdd (σ (a l) v) ∈ (T.subgroupOf D).map p
      refine ⟨y,hyT,?_⟩
      apply Multiplicative.toAdd.injective
      have hh := he l x y rfl
      change (p y).toAdd = σ (a l) (p x).toAdd at hh
      rw [hh,hv]
      rfl }
  rcases eq_bot_or_eq_top U with hbot | htop
  · left
    apply le_antisymm ?_ hZT
    intro t ht
    have hv : (p ⟨t,hTD ht⟩).toAdd ∈ U := mem_map_of_mem p ht
    rw [hbot] at hv
    have hz : (⟨t,hTD ht⟩ : D) ∈ p.ker := hv
    rw [hk] at hz
    exact hz
  · right
    apply le_antisymm hTD
    intro d hd
    have hv : (p ⟨d,hd⟩).toAdd ∈ U := htop ▸ Submodule.mem_top
    change p ⟨d,hd⟩ ∈ (T.subgroupOf D).map p at hv
    obtain ⟨t,ht,heq⟩ := hv
    have hz : (⟨d,hd⟩ : D) / t ∈ p.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_div,heq,div_self']
    rw [hk] at hz
    have hh := T.mul_mem (hZT hz) ht
    change d / (t : G) * (t : G) ∈ T at hh
    simpa only [div_mul_cancel] using hh

/-- The same original natural eight models Q modulo its point-kernel intersection. -/
theorem binary_three_source_natural_core_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))
    [K.Normal]
    (hBK : (c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) ≤ K)
    (hm : ClassicalGroup.IsPSL K 4 2)
    (hz : z ∈ intrinsicFour c.L) (hz1 : z ≠ 1) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let Q := LinearThree.commutatorCore c.L
    let V := ⁅coreCenter c.L,c.L⁆
    let W := conjugateSpanBy V C
    Q ⊓ centralizer (W : Set G) = Q ⊓ N ∧
      ⁅W,Q⁆ ≤ V ∧ ⁅W,c.L⁆ ≤ V ∧
      ∃ hn : ((centralizer (W : Set G)).subgroupOf Q).Normal,
        let := hn
        ∃ E : (Q ⧸ (centralizer (W : Set G)).subgroupOf Q) ≃* V,
          ∀ l : c.L, ∀ x : Q,
            ∀ y : Q, (y : G)=l*x*(l : G)⁻¹ →
              (E (QuotientGroup.mk' ((centralizer (W : Set G)).subgroupOf Q) y) : G)=
                l*E (QuotientGroup.mk' ((centralizer (W : Set G)).subgroupOf Q) x)*(l : G)⁻¹ := by
  let C := centralizer ({z} : Set G)
  let N := C.pCoreIn 2
  let q := QuotientGroup.mk' (pCore 2 C)
  let Q := LinearThree.commutatorCore c.L
  let V := ⁅coreCenter c.L,c.L⁆
  let W := conjugateSpanBy V C
  let R := Q ⊓ N
  obtain ⟨_,hWQ,_⟩ := binary_three_source_natural_core_intersection
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm hz hz1
  obtain ⟨ρ,hρ,hi,_⟩ := binary_three_source_four_central_span_action
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK hm
  obtain ⟨_,hVcard,_,hWcenter,hCW,_⟩ := binary_three_source_binary_central_eight_span
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm
  have hWN : W ≤ N := hWcenter.trans (map_subtype_le _)
  have hNW : N ≤ centralizer (W : Set G) := by
    apply le_centralizer_iff.mp
    intro w hw
    obtain ⟨w,hwz,rfl⟩ := hWcenter hw
    intro n hn
    exact congrArg Subtype.val (mem_center_iff.mp hwz ⟨n,hn⟩)
  have hQL : Q ≤ c.L := (LinearThree.commutatorCore_le c.L).trans (c.L.pCoreIn_le 2)
  have hLC : c.L ≤ C := le_sup_left.trans hLS
  have hQC : Q ≤ C := hQL.trans hLC
  have hfix : Q ⊓ centralizer (W : Set G) = R := by
    apply le_antisymm ?_ (le_inf inf_le_left (inf_le_right.trans hNW))
    intro x hx
    refine ⟨hx.1,?_⟩
    let xc : C := ⟨x,hQC hx.1⟩
    let k : K := ⟨q xc,hBK (mem_map_of_mem q (hQL hx.1))⟩
    have hact : (ρ.comp K.subtype) k = 1 := by
      ext w
      change (ρ (q xc) w : G) = (w : G)
      rw [hρ]
      change x*w*x⁻¹=w
      rw [←hx.2 w w.property,mul_inv_cancel_right]
    have hk : k = 1 := hi (hact.trans (map_one (ρ.comp K.subtype)).symm)
    have hq : q xc = 1 := congrArg Subtype.val hk
    have hxcore : xc ∈ pCore 2 C := (QuotientGroup.eq_one_iff xc).mp hq
    exact mem_map_of_mem C.subtype hxcore
  have hJQ : c.L ⊔ d.S ≤ normalizer Q := by
    have hJL : c.L ⊔ d.S ≤ normalizer c.L :=
      (normal_subgroupOf_iff_le_normalizer (show c.L ≤ c.L ⊔ d.S from le_sup_left)).mp
        b.component_normal
    exact hJL.trans (normalizer_le_normalizer_commutatorCore c.L)
  have hNS : N ≤ d.S := hP ▸ pCoreIn_le_sylow C P
  have hWQcomm : ⁅W,Q⁆ ≤ V := (le_inf
    (le_normalizer_iff_commutator_le_left.mp (hQC.trans hCW))
    (le_normalizer_iff_commutator_le_right.mp ((hWN.trans (hNS.trans le_sup_right)).trans hJQ))).trans hWQ.le
  have hNL : ⁅N,c.L⁆ = R := (binary_three_source_binary_kernel_residual
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm).1
  have hWLcomm : ⁅W,c.L⁆ ≤ V := (le_inf
    (le_normalizer_iff_commutator_le_left.mp (hLC.trans hCW))
    ((commutator_mono hWN le_rfl).trans (hNL.le.trans inf_le_left))).trans hWQ.le
  have hLZ : c.L ≤ normalizer (coreCenter c.L) :=
    (normalizer_commutator_ge_right _ _).trans
      (normalizer_le_normalizer_characteristic_image Q (center Q))
  have hVZ : V ≤ coreCenter c.L := le_normalizer_iff_commutator_le_left.mp hLZ
  have hZQ : coreCenter c.L ≤ Q := map_subtype_le _
  have hVc : V ≤ centralizer (Q : Set G) := by
    intro v hv
    obtain ⟨v,hvz,rfl⟩ := hVZ hv
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hvz ⟨x,hx⟩)
  have hRcard : Nat.card R = 131072 := by
    have hh := (binary_three_source_binary_core_sizes
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hLS P hP K hBK (Or.inl rfl) hm).2
    simpa only [Nat.reduceSub,Nat.reduceMul,Nat.reducePow] using hh
  have hQcard : Nat.card Q = 1048576 := (binary_three_large_distance_original_core_structure
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb).2.2.2.1
  have hne : ⁅W,Q⁆ ≠ ⊥ := by
    intro hh
    have hQWc : Q ≤ centralizer (W : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh)
    have he : Q = R := (inf_eq_left.mpr hQWc).symm.trans hfix
    rw [he,hRcard] at hQcard
    omega
  have hbound : (centralizer (W : Set G)).relIndex Q ≤ Nat.card V := by
    have hsub : (centralizer (W : Set G)).subgroupOf Q = R.subgroupOf Q := by
      ext x
      change (x : G) ∈ centralizer (W : Set G) ↔ (x : G) ∈ R
      exact (and_iff_right x.property).symm.trans (SetLike.ext_iff.mp hfix (x:G))
    change ((centralizer (W : Set G)).subgroupOf Q).index ≤ Nat.card V
    rw [hsub,hVcard]
    have hh := (R.subgroupOf Q).card_mul_index
    have hcard : Nat.card (R.subgroupOf Q) = Nat.card R :=
      Nat.card_congr (subgroupOfEquivOfLe (show R ≤ Q from inf_le_left)).toEquiv
    rw [hcard,hRcard,hQcard] at hh
    omega
  obtain ⟨common⟩ := t.commonFacts hc
  obtain ⟨a,ha,_,hs⟩ := binary_three_original_natural_seed d c.L b t common hb
  let : IsIrreducible BinaryLinearThree.W := BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  have hmin (A : Subgroup G) (hLA : c.L ≤ normalizer A) (hAV : A ≤ V) : A=⊥ ∨ A=V :=
    irreducible_section_dichotomy ha hs bot_le hAV hLA
  obtain ⟨hn,E,hE⟩ := exists_equivariant_centralizer_quotient c.L Q W V
    (le_sup_left.trans hJQ) hWQcomm hWLcomm (hVZ.trans hZQ) hVc hmin hne hbound
  refine ⟨hfix,hWQcomm,hWLcomm,hn,E,?_⟩
  intro l x y hy
  have he : y = ⟨(l:G)*x*(l:G)⁻¹,
    (mem_normalizer_iff.mp ((le_sup_left.trans hJQ) l.property) x).mp x.property⟩ := Subtype.ext hy
  subst y
  exact hE l x

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
