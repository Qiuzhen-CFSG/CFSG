module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.FiveSupportFamily
public import CFSG.Quasithin.ChapterD.Section02.StarredConjugacy
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.NormalOddSeed
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.Assembly
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.ElementaryCore.SupportExclusion.Linear
public import Theory.Representation.FiveSupportResidual
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.GroupTheory.Fitting.NormalSylowFactorization

/-!
# Normal closure of an original quintic minimum actor

For a rank-one starred actor moving the five-core, D.2.13 gives an order-five
commutator with a four-dimensional support and a fixed complement. Every
ambient conjugate of this commutator is normalized by the original Jhat and
fixes the complementary vectors of its starred conjugate. The sum of these
supports and the fixed space of the normal closure span the original module.
Their faithful four-dimensional action images have normal quintic subgroups,
so the two-residual of the actor's normal closure is a five-group. Its ambient
image lies in the Fitting subgroup. A Sylow-fixed generating seed then yields
the literal fully Fitting-moved factor action and its finite decomposition.

Source: Aschbacher--Smith D.2.13 and D.2.23--24, printed pp.184--189, and
the original normal-closure reduction in 15.1.2, printed pp.1084--1085.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem five_fixed_actor (hf : Function.Injective ρ) {A : Subgroup G}
    (hA : A ∈ QhatStar ρ) (hr : rank A = 1) (hm : ⁅pCore 5 G,A⁆ ≠ ⊥) :
    fixedSpace ρ ⁅pCore 5 G,A⁆ ≤ fixedSpace ρ A := by
  obtain ⟨_,hc,_,_,hs⟩ := source_lemma_D_2_13_cyclic_five ρ hf hA hr hm
  have ho : Odd (Nat.card (⁅pCore 5 G,A⁆ : Subgroup G)) := by rw [hc]; decide
  have hs' := (ElementaryCore.SupportExclusion.moved_split ρ ⁅pCore 5 G,A⁆ ho).symm
  have he : fixedSpace ρ (⁅pCore 5 G,A⁆ ⊔ A) = fixedSpace ρ ⁅pCore 5 G,A⁆ := by
    apply Submodule.eq_of_le_of_finrank_eq (fixedSpace_antitone ρ le_sup_left)
    have h₁ := Submodule.finrank_add_eq_of_isCompl hs
    have h₂ := Submodule.finrank_add_eq_of_isCompl hs'
    omega
  rw [←he]
  exact fixedSpace_antitone ρ le_sup_right

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem closure_involutions_normalClosure {A : Subgroup G}
    (hA : IsElementaryTwo A) :
    closure {s : normalClosure (A : Set G) | IsInvolution s} = ⊤ := by
  let N := normalClosure (A : Set G)
  let C := closure {s : N | IsInvolution s}
  have hNC : N ≤ C.map N.subtype := by
    apply (closure_le _).mpr
    intro x hx
    obtain ⟨a,ha,hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hax
    have hxN : g * a * g⁻¹ ∈ N :=
      (inferInstance : N.Normal).conj_mem a (le_normalClosure ha) g
    let x : N := ⟨g * a * g⁻¹,hxN⟩
    have hxpow : x ^ 2 = 1 := by
      apply Subtype.ext
      change (g * a * g⁻¹) ^ 2 = 1
      rw [conj_pow]
      let : IsElementaryAbelian 2 A := hA.2
      simpa using elemPow_eq_one_of_isElementaryAbelian a ha
    by_cases hx : x = 1
    · have hx' : g * a * g⁻¹ = 1 := congrArg Subtype.val hx
      rw [hx']
      exact (C.map N.subtype).one_mem
    · exact mem_map.mpr ⟨x,subset_closure ⟨hx,hxpow⟩,rfl⟩
  apply top_unique
  intro x _
  obtain ⟨y,hy,he⟩ := hNC x.property
  exact (Subtype.ext he : y = x) ▸ hy

/-- The literal original normal closure has quintic two-residual. -/
theorem source_five_normalClosure_residual (hf : Function.Injective ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hr : rank A = 1)
    (hm : ⁅pCore 5 G,A⁆ ≠ ⊥) :
    IsPGroup 5 (pResidual 2 (normalClosure (A : Set G))) := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : (Jhat ρ).Normal := Jhat_normal ρ
  let N := normalClosure (A : Set G)
  let σ := ρ.comp N.subtype
  let E (g : G) := A.map (MulAut.conj g).toMonoidHom
  let D (g : G) := ⁅pCore 5 G,E g⁆
  let U (g : G) := subspaceCommutator ρ ⊤ (D g)
  let R := ⨆ g : G, D g
  have hAN : A ≤ N := le_normalClosure
  have hNJ : N ≤ Jhat ρ := normalClosure_le_normal (le_sSup hA)
  have hE (g : G) : E g ∈ QhatStar ρ := QhatStar.map_conj ρ hA g
  have hrE (g : G) : rank (E g) = 1 :=
    (rank_map_injective _ (MulAut.conj g).injective _).trans hr
  have hEN (g : G) : E g ≤ N :=
    (map_mono hAN).trans_eq (Normal.map_conj_eq N g)
  have hDconj (g : G) : D g = (⁅pCore 5 G,A⁆ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [map_commutator]
    change ⁅pCore 5 G,E g⁆ = ⁅(pCore 5 G).map (MulAut.conj g).toMonoidHom,E g⁆
    rw [show (pCore 5 G).map (MulAut.conj g).toMonoidHom = pCore 5 G from Normal.map_conj_eq _ _]
  obtain ⟨hq,hc,_,_,_⟩ := source_lemma_D_2_13_cyclic_five ρ hf hA hr hm
  have hmD (g : G) : D g ≠ ⊥ := by
    have hc' : Nat.card (D g) = 5 := by
      rw [hDconj,card_map_of_injective (MulAut.conj g).injective,hc]
    intro he
    simp [he] at hc'
  have hcard (g : G) : Nat.card (D g) = 5 :=
    (source_lemma_D_2_13_cyclic_five ρ hf (hE g) (hrE g) (hmD g)).2.1
  have hdim (g : G) : Module.finrank (ZMod 2) (U g) = 4 :=
    (source_lemma_D_2_13_cyclic_five ρ hf (hE g) (hrE g) (hmD g)).2.2.2.1
  have hDN (g : G) : D g ≤ N :=
    (commutator_mono le_rfl (hEN g)).trans (commutator_le_right _ _)
  have hnorm (g : G) : N ≤ normalizer (D g : Set G) := by
    let := BinaryGroupAction.action ρ
    apply hNJ.trans
    apply fiveSupport_Jhat_le_normalizer ρ hf hq
    refine ⟨(commutator_le_left _ _).trans (pCore_le_fitting G 5),hcard g,?_⟩
    rw [BinaryGroupAction.commutator_card,hdim]
  have hU (g : G) : (⊤ : Subgroup N) ≤ subspaceStabilizer σ (U g) := by
    have hh := subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) (hnorm g)
    apply le_subspaceStabilizer
    intro n _ v hv
    exact (hh n.property v).2 hv
  have hRP : R ≤ pCore 5 G := iSup_le fun g => commutator_le_left _ _
  have hodd : Odd (Nat.card R) := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup.to_le hRP).exists_card_eq
    exact hk ▸ (by decide : Odd 5).pow
  have hfixed : fixedSpace ρ R ≤ fixedSpace σ ⊤ := by
    rw [fixedSpace_comp_map,←MonoidHom.range_eq_map,range_subtype]
    intro v hv
    apply (mem_fixedSpace_closure_iff ρ _ v).mpr
    intro x hx
    obtain ⟨a,ha,hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hax
    have hvD : v ∈ fixedSpace ρ (D g) := fixedSpace_antitone ρ (le_iSup D g) hv
    exact five_fixed_actor ρ hf (hE g) (hrE g) (hmD g) hvD
      ⟨g * a * g⁻¹,mem_map.mpr ⟨a,ha,rfl⟩⟩
  have hspan : (⨆ g, U g) ⊔ fixedSpace σ ⊤ = ⊤ := by
    apply top_unique
    have hs := (ElementaryCore.SupportExclusion.moved_split ρ R hodd).symm
    rw [←hs.sup_eq_top]
    apply sup_le_sup _ hfixed
    exact (subspaceCommutator_iSup_family ρ D).le
  let B (g : G) := (D g).subgroupOf N |>.map (invariantActionHom σ (U g) (hU g))
  have hBn (g : G) : (B g).Normal := by
    let : ((D g).subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer (hnorm g)
    exact Normal.map inferInstance _ (invariantActionHom_surjective σ (U g) (hU g))
  let : ∀ g, (B g).Normal := hBn
  have hBc (g : G) : Nat.card (B g) = 5 := by
    have hk : subspaceKernel σ (U g) ((D g).subgroupOf N) = ⊥ := by
      apply (subspaceKernel_eq_bot_iff _ _ _).mpr
      intro x hx hfix
      apply Subtype.ext
      apply (ElementaryCore.SupportExclusion.moved_faithful ρ hf (D g)
        (by rw [hcard]; decide)).le
      exact ⟨hx,hfix⟩
    have hc' := card_subspaceKernel_mul_image σ (U g) ((D g).subgroupOf N)
      (le_top.trans (hU g))
    rw [hk,card_bot,one_mul,←invariantActionHom_map] at hc'
    exact hc'.trans ((Nat.card_congr (subgroupOfEquivOfLe (hDN g)).toEquiv).trans (hcard g))
  exact SmallBinaryPrimeNormalizer.five_residual_of_subspace_images σ
    (hf.comp N.subtype_injective) U hU hspan
    (closure_involutions_normalClosure hA.1.2.1) hdim B hBc

/-- Its image modulo the ambient Fitting subgroup is a two-group. -/
theorem source_five_normalClosure_image_two (hf : Function.Injective ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hr : rank A = 1)
    (hm : ⁅pCore 5 G,A⁆ ≠ ⊥) :
    IsPGroup 2 ((normalClosure (A : Set G)).map (QuotientGroup.mk' (fittingSubgroup G))) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := normalClosure (A : Set G)
  let P := (pResidual 2 N).map N.subtype
  have hp : IsPGroup 5 P := (source_five_normalClosure_residual ρ hf hA hr hm).map N.subtype
  let : Group.IsNilpotent P := hp.isNilpotent
  have hPF : P ≤ fittingSubgroup G := le_sSup ⟨inferInstance,inferInstance⟩
  intro x
  obtain ⟨n,hn,he⟩ := x.property
  obtain ⟨k,hk⟩ := isPGroup_quotient_pResidual (G := N) 2
    (QuotientGroup.mk' (pResidual 2 N) ⟨n,hn⟩)
  have hn' : (⟨n,hn⟩ : N) ^ 2 ^ k ∈ pResidual 2 N :=
    (QuotientGroup.eq_one_iff _).mp hk
  refine ⟨k,Subtype.ext ?_⟩
  change (x : G ⧸ fittingSubgroup G) ^ 2 ^ k = 1
  rw [←he,←map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact hPF (mem_map_of_mem N.subtype hn')

/-- The image lands in the two-core of the ambient Fitting quotient. -/
theorem source_five_normalClosure_le_twoCore_preimage (hf : Function.Injective ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hr : rank A = 1)
    (hm : ⁅pCore 5 G,A⁆ ≠ ⊥) :
    normalClosure (A : Set G) ≤ (pCore 2 (G ⧸ fittingSubgroup G)).comap
      (QuotientGroup.mk' (fittingSubgroup G)) := by
  apply map_le_iff_le_comap.mp
  exact le_sSup ⟨Normal.map inferInstance _ (QuotientGroup.mk'_surjective _),
    source_five_normalClosure_image_two ρ hf hA hr hm⟩

/-- The embedded odd residual and the ambient Sylow intersection generate the normal closure. -/
theorem source_five_normalClosure_odd_factorization (hf : Function.Injective ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hr : rank A = 1)
    (hm : ⁅pCore 5 G,A⁆ ≠ ⊥) (S : Sylow 2 G) :
    let N := normalClosure (A : Set G)
    let P := (pResidual 2 N).map N.subtype
    P.Normal ∧ Odd (Nat.card P) ∧ P ≤ fittingSubgroup G ∧
      N = P ⊔ (N ⊓ (S : Subgroup G)) ∧ P.subgroupOf N ≤ fittingSubgroup N := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := normalClosure (A : Set G)
  let P := (pResidual 2 N).map N.subtype
  have hp := source_five_normalClosure_residual ρ hf hA hr hm
  let : Group.IsNilpotent (pResidual 2 N) := hp.isNilpotent
  let : Group.IsNilpotent P := (hp.map N.subtype).isNilpotent
  have hP : P.Normal := inferInstance
  have hPN : P ≤ N := map_subtype_le _
  have he : P.subgroupOf N = pResidual 2 N := by
    apply Subgroup.map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le hPN]
  have hi : IsPGroup 2 (N.map (QuotientGroup.mk' P)) := by
    intro x
    obtain ⟨n,hn,hx⟩ := x.property
    obtain ⟨k,hk⟩ := isPGroup_quotient_pResidual (G := N) 2
      (QuotientGroup.mk' (pResidual 2 N) ⟨n,hn⟩)
    have hn' : (⟨n,hn⟩ : N) ^ 2 ^ k ∈ pResidual 2 N :=
      (QuotientGroup.eq_one_iff _).mp hk
    refine ⟨k,Subtype.ext ?_⟩
    change (x : G ⧸ P) ^ 2 ^ k = 1
    rw [←hx,←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (mem_map_of_mem N.subtype hn')
  refine ⟨hP,?_,le_sSup ⟨inferInstance,inferInstance⟩,?_,?_⟩
  · obtain ⟨k,hk⟩ := (hp.map N.subtype).exists_card_eq
    exact hk ▸ (by decide : Odd 5).pow
  · simpa only [inf_eq_right.mpr hPN] using
      eq_inf_sup_inf_sylow_of_quotient_image_isPGroup N P S hi
  · rw [he]
    exact le_sSup ⟨inferInstance,inferInstance⟩

open RatioDecomposition in
/-- The source seed gives a literal fully moved factor action and finite decomposition. -/
theorem source_five_normalClosure_seed_factors (hf : Function.Injective ρ)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hr : rank A = 1)
    (hm : ⁅pCore 5 G,A⁆ ≠ ⊥) (S : Sylow 2 G)
    (Z : Submodule (ZMod 2) V) (hZ : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤) :
    let N := normalClosure (A : Set G)
    let P := (pResidual 2 N).map N.subtype
    ∃ d : FactorData ρ N (subspaceCommutator ρ ⊤ P),
      subspaceCommutator d.representation ⊤ (fittingSubgroup N) = ⊤ ∧
      ∃ c : Decomposition d.representation, c.FittingFull := by
  let N := normalClosure (A : Set G)
  let P := (pResidual 2 N).map N.subtype
  have hPN : P ≤ N := map_subtype_le _
  have hAN : A ≤ N := le_normalClosure
  obtain ⟨_,ho,_,hgen,hPF⟩ := source_five_normalClosure_odd_factorization ρ hf hA hr hm S
  let σ := oddMovedAction ρ N P
  have ht := oddMovedAction_transport ρ N P S ho hgen Z hZ hspan ⟨A,hA,hAN⟩
  have hJ : Jhat σ = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [←MonoidHom.range_eq_map,range_subtype]
    apply le_antisymm (map_subtype_le _)
    apply (closure_le _).mpr
    intro x hx
    obtain ⟨a,ha,hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨g,rfl⟩ := isConj_iff.mp hax
    let E := A.map (MulAut.conj g).toMonoidHom
    have hEN : E ≤ N := (map_mono hAN).trans_eq (Normal.map_conj_eq N g)
    have hE : E.subgroupOf N ∈ QhatStar σ := by
      apply (ht.2 _).mpr
      rw [map_subgroupOf_eq_of_le hEN]
      exact QhatStar.map_conj ρ hA g
    have hh : E ≤ (Jhat σ).map N.subtype := by
      have hh := Subgroup.map_mono (le_sSup hE) (f := N.subtype)
      simpa only [Jhat,map_subgroupOf_eq_of_le hEN] using hh
    exact hh (mem_map.mpr ⟨a,ha,rfl⟩)
  let d : FactorData ρ N (subspaceCommutator ρ ⊤ P) :=
    ⟨σ,fun _ _ => rfl,oddMovedAction_faithful ρ hf N P S ho hgen Z hZ hspan,hJ,
      oddMovedAction_full ρ N P S ho hgen Z hZ hspan,
      NormalOddSeed.moved_eq ρ N P S hgen Z hZ hspan,
      (NormalOddSeed.isCompl_moved_fixed ρ N P S ho hgen Z hZ hspan).sup_eq_top,
      ht.1,ht.2⟩
  have hfull : subspaceCommutator d.representation ⊤ (fittingSubgroup N) = ⊤ :=
    oddMovedAction_full_of_le ρ N P hPN ho _ hPF
  refine ⟨d,hfull,source_fitting_decomposition d.representation d.faithful d.generated hfull ?_⟩
  rw [d.ratio,(source_lemma_D_2_13_cyclic_five ρ hf hA hr hm).1]
end CFSG.Quasithin.ChapterD.CyclicSource
