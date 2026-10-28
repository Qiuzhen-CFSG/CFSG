module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.LocalReduction.Source
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.FullAxis
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.QuotientHyperplane
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates
public import Theory.GroupTheory.ConjugateOrbitIndexTwo

/-!
# The actual natural TI pair at corank one

Vanishing of the full fixed part makes each moved factor an elementary eight.
The corank bound puts at least four elements in the offender. The elementary
TI-pair theorem then forces both mutual normalizers to have order four and
identifies their full fixed-axis action. Their order-sixteen product is normal
inside the pair. If the first factor lay in its two-core, adjoining the second
would make the whole pair a two-group and force commutation, a contradiction.

These results use the literal natural geometry and earlier local conclusions;
no survivor or later w=2 equality is used. The terminal consumer is in Source.
Source: Aschbacher--Smith, 10.2.12, printed p.755, and I.6.2, pp.424--425.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02 ChapterE ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {g : G}

/-- The natural section has trivial kernel when the full component-fixed part vanishes. -/
theorem moved_fixed_eq_bot_of_full_fixed_eq_bot
    (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp hn
  have hcross : ⁅D.fullModule,L⁆ ≤
      centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
    have htn' : t⁻¹ ∉ normalizer (L : Set G) := by
      simpa only [inv_mem_iff] using htn
    intro w hw l hl
    obtain ⟨l,hl,rfl⟩ := hl
    have hh := (m.crossed t⁻¹ ((T : Subgroup G).inv_mem ht) htn'
      (mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hw)) l hl
    simpa only [MulEquiv.coe_toMonoidHom, map_mul, MulAut.conj_apply,
      inv_inv, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
      mul_inv_cancel_right, inv_mul_cancel_right, mul_inv_cancel, inv_mul_cancel,
      mul_one, one_mul] using congrArg (MulAut.conj t) hh
  have hpair : localOrbit T L = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hn)
      inf_le_right ht htn
  have hC : ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) ≤
      centralizer (localOrbit T L : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hpair]
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans hcross))
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  exact bot_unique ((le_inf (inf_le_left.trans hWV) hC).trans_eq hz)

/-- The literal moved factor then has order eight. -/
theorem natural_moved_card_of_full_fixed_eq_bot
    (m : SourceLinearThreeGeometry T D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    Nat.card (⁅D.fullModule,L⁆ : Subgroup G) = 8 := by
  have he := m.natural.card_section
  rw [moved_fixed_eq_bot_of_full_fixed_eq_bot m hn hz, card_bot] at he
  norm_num [Nat.card_fun,Nat.card_fin,Nat.card_zmod] at he ⊢
  exact he

/-- A noncommuting natural pair has exactly the source four-element mutual normalizers; the offender is its full mutual normalizer. -/
theorem natural_active_pair_normalizers
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    let W := ⁅D.fullModule,L⁆
    let P := W.map (MulAut.conj g).toMonoidHom
    let A := P ⊓ D.maximalLocal
    Disjoint W P ∧
      A = P ⊓ normalizer (W : Set G) ∧ Nat.card A = 4 ∧
      Nat.card (W ⊓ normalizer (P : Set G) : Subgroup G) = 4 := by
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj g).toMonoidHom
  let A := P ⊓ D.maximalLocal
  let B := P ⊓ normalizer (W : Set G)
  let U := W ⊓ normalizer (P : Set G)
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  have hW : Nat.card W = 8 := natural_moved_card_of_full_fixed_eq_bot m c.nonnormal hz
  have hP : Nat.card P = Nat.card W := card_map_of_injective (MulAut.conj g).injective
  have hpt : IsTISubgroup P := hti.map_equiv (MulAut.conj g)
  have hd : Disjoint W P := by
    rcases hti.eq_or_disjoint_conjugate g with he | hd
    · apply False.elim
      apply hactive
      rw [he]
      exact W.le_centralizer
    · exact hd.symm
  have hAN := (natural_offender_geometry c m hsmall hd.eq_bot).1
  have hAB : A ≤ B := le_inf inf_le_left hAN
  have hi : A.relIndex P ≤ 2 := Recognition.moved_intersection_index_le D hsmall
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G) A P bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hP,hW] at hm
  have hAlo : 4 ≤ Nat.card A := by
    have hh := Nat.mul_le_mul_left (Nat.card A) hi
    rw [hm] at hh
    omega
  have hBproper : B ≠ P := by
    intro he
    exact hactive (ti_pair_commute_of_full_normalizer P W hd.symm hpt hti hP he)
  have hBind : 2 ≤ B.relIndex P := by
    have hn : B.relIndex P ≠ 0 := index_ne_zero_of_finite
    have hone : B.relIndex P ≠ 1 := by
      intro he
      exact hBproper (le_antisymm inf_le_left (relIndex_eq_one.mp he))
    omega
  have hmB := relIndex_mul_relIndex (⊥ : Subgroup G) B P bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hP,hW] at hmB
  have hBhi : Nat.card B ≤ 4 := by
    have hh := Nat.mul_le_mul_left (Nat.card B) hBind
    rw [hmB] at hh
    omega
  have hAle : Nat.card A ≤ Nat.card B := card_le_of_le hAB
  have he : A = B := eq_of_le_of_card_ge hAB (by omega)
  have hAc : Nat.card A = 4 := by omega
  refine ⟨hd,he,hAc,?_⟩
  exact (ti_pair_mutual_normalizers_card_eq W P hd hti hpt hP.symm).trans
    (show Nat.card B = 4 from he ▸ hAc)

private theorem pair_core_escape
    (W P : Subgroup G) [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 P]
    (hd : Disjoint W P) (hW : IsTISubgroup W) (hP : IsTISubgroup P)
    (hcard : Nat.card P = Nat.card W)
    (hB : P ⊓ normalizer (W : Set G) ≠ ⊥)
    (hactive : ¬ P ≤ centralizer (W : Set G)) :
    ¬ W ≤ (W ⊔ P).pCoreIn 2 := by
  intro hcore
  let I := W ⊔ P
  let Q := I.pCoreIn 2
  have hIQ : I ≤ normalizer (Q : Set G) := by
    simpa only [Q,pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 I).le_normalizer_map I.subtype
  have htwo : IsPGroup 2 I :=
    ((isPGroup_pCoreIn 2 I).to_sup_of_normal_left'
      (IsElementaryAbelian.isPGroup 2 P) (le_sup_right.trans hIQ)).to_le
      (sup_le (hcore.trans le_sup_left) le_sup_right)
  exact hactive (ti_pair_directProduct_of_isPGroup P W hd.symm hP hW hcard hB
    (by rw [show P ⊔ W = I from sup_comm P W]; exact htwo)).1

/-- The original moved factor escapes the two-core of the subgroup generated by the noncommuting TI pair. -/
theorem natural_active_pair_core_escape
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    ¬ ⁅D.fullModule,L⁆ ≤ (⁅D.fullModule,L⁆ ⊔
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom).pCoreIn 2 := by
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj g).toMonoidHom
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  obtain ⟨hd,he,hA,_⟩ := natural_active_pair_normalizers c m hsmall hz hti hactive
  apply pair_core_escape W P hd hti (hti.map_equiv (MulAut.conj g))
    (card_map_of_injective (MulAut.conj g).injective) ?_ hactive
  intro hbot
  rw [he,hbot,card_bot] at hA
  omega

/-- The opposite mutual normalizer is the common fixed plane. Their order-sixteen product is normal in the generated pair and lies in its two-core. -/
theorem natural_active_pair_axis
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    let W := ⁅D.fullModule,L⁆
    let P := W.map (MulAut.conj g).toMonoidHom
    let A := P ⊓ D.maximalLocal
    let U := W ⊓ normalizer (P : Set G)
    U = W ⊓ centralizer (A : Set G) ∧
      ((U ⊔ A).subgroupOf (W ⊔ P)).Normal ∧
      Nat.card (U ⊔ A : Subgroup G) = 16 ∧
      U ⊔ A ≤ (W ⊔ P).pCoreIn 2 := by
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj g).toMonoidHom
  let A := P ⊓ D.maximalLocal
  let B := P ⊓ normalizer (W : Set G)
  let U := W ⊓ normalizer (P : Set G)
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  have hpt := hti.map_equiv (MulAut.conj g)
  obtain ⟨hd,he,hA,hU⟩ := natural_active_pair_normalizers c m hsmall hz hti hactive
  change A = B at he
  change Nat.card A = 4 at hA
  change Nat.card U = 4 at hU
  have hB : B ≠ ⊥ := by
    intro hb
    rw [he,hb,card_bot] at hA
    omega
  have hfix : U = W ⊓ centralizer (B : Set G) := by
    apply le_antisymm
    · exact le_inf inf_le_left (ti_pair_mutual_normalizers_commute W P hd)
    · obtain ⟨b,hbne⟩ := ne_bot_iff_exists_ne_one.mp hB
      have hb1 : (b : G) ≠ 1 := fun hh => hbne (Subtype.ext hh)
      change W ⊓ centralizer (B : Set G) ≤ W ⊓ normalizer (P : Set G)
      rw [ti_pair_opposite_normalizer_eq_centralizer P W hd.symm hpt
        b.property.1 b.property.2 hb1]
      intro w hw
      exact ⟨hw.1,mem_centralizer_singleton_iff.mpr (hw.2 b b.property).symm⟩
  have hc : Nat.card (U ⊔ B : Subgroup G) = 16 := by
    obtain ⟨e,_⟩ := ti_pair_mutual_normalizers_mulEquiv W P hd
    rw [←Nat.card_congr e.toEquiv,Nat.card_prod]
    change Nat.card U * Nat.card B = 16
    rw [hU,←he,hA]
  change U = W ⊓ centralizer (A : Set G) ∧
    ((U ⊔ A).subgroupOf (W ⊔ P)).Normal ∧
    Nat.card (U ⊔ A : Subgroup G) = 16 ∧ U ⊔ A ≤ (W ⊔ P).pCoreIn 2
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [he] using hfix
  · rw [he]
    exact ti_pair_normal_subgroupOf W P hd hti hpt
  · simpa only [he] using hc
  · rw [he]
    exact ti_pair_mutual_normalizers_le_twoCore W P hd hti hpt

/-- The literal action of the offender is the full binary transvection group with the prescribed common fixed axis. -/
theorem natural_active_pair_full_axis
    (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1)
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    (hti : IsTISubgroup ⁅D.fullModule,L⁆)
    (hactive : ¬ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ≤
      centralizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)) :
    let W := ⁅D.fullModule,L⁆
    let P := W.map (MulAut.conj g).toMonoidHom
    let _ := source_full_moved_elementary D
    ∃ f : Module.Dual (ZMod 2) (Additive W), f ≠ 0 ∧
      (∀ v : Additive W, f v = 0 ↔ (v.toMul : G) ∈ normalizer (P : Set G)) ∧
      (pairNormalizerLinearAction W P).range = BinaryLinear.radical f.ker := by
  dsimp only
  let W := ⁅D.fullModule,L⁆
  let P := W.map (MulAut.conj g).toMonoidHom
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 P := IsElementaryAbelian.map _
  obtain ⟨hd,_,_,hU⟩ := natural_active_pair_normalizers c m hsmall hz hti hactive
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup G)
    (W ⊓ normalizer (P : Set G)) W bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hU,
    natural_moved_card_of_full_fixed_eq_bot m c.nonnormal hz,inf_relIndex_left] at hmul
  have hi : (normalizer (P : Set G)).relIndex W = 2 := by omega
  obtain ⟨f,hf,hker⟩ := pairAxisSpace_exists_form W P
    (pairAxisSpace_isCoatom_of_index_two W P hi)
  exact ⟨f,hf,hker,pairNormalizerLinearAction_range_eq_radical W P hd hti
    (hti.map_equiv (MulAut.conj g))
    (card_map_of_injective (MulAut.conj g).injective).symm f hf hker⟩

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
