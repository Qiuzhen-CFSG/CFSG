module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CoveredNatural
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CoveredOneAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.LargerRow
public import CFSG.Quasithin.Chapter13.Section03.PointResidualImage.CoveredConclusion
public import Theory.GroupTheory.PrimeOrderClosurePerfect
public import Theory.GroupTheory.PResidual.CubicGeneration
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointResidualRestriction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.AugmentationOutsideAt

/-!
# Covered 13.3.9 from structural facts at the original G,T

The cubic closure of a relatively normal subgroup of any original outside overgroup lies in
L₁. Its Sylow-invariant quotient has four possibilities; the L₀ and L₁
normalizer bounds exclude both unwanted nontrivial alternatives. Disjoint
cubic directions make the full module-action kernel a two-group. The
natural point action bounds the remaining order, so cubic generation
identifies the subgroup with the literal L₁,+.

This specializes CoveredPointResidual without a universal structural
premise. The natural action is constructed from the original five-space,
and the final consumer proves the universal Source1339 statement, including
the literal barred actions. No containment of the outside overgroup in the
point centralizer is required. The source guard, both normality placements and
the original Sylow subgroup remain unchanged.
Source: Aschbacher--Smith 13.3.7--9, pp.886--887.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable Nonsolvable
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Solvable.OneFactor
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V V₁ V₃ Y H : Subgroup G}

private theorem covered_residual_four_cases
    (d : NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hY : Y ≤ one L (T : Subgroup G) V₁) (hp : IsPPerfect 2 Y)
    (hn : (T : Subgroup G) ≤ normalizer (Y : Set G)) :
    Y = ⊥ ∨ Y = zero L ∨ Y = plus L (T : Subgroup G) V₁ ∨
      Y = one L (T : Subgroup G) V₁ := by
  let B := one L (T : Subgroup G) V₁
  have hf := Section08.SourceCompletion.CoverFactorization.source_factorization d
  have hBc : Nat.card (B ⧸ pCore 2 B) = 9 := d.one_quotient_card hf
  have hB : IsPGroup 3 (B ⧸ pCore 2 B) := IsPGroup.of_card (n := 2) hBc
  let C := Section08.Source.starImage B Y
  have hC : pCore 2 C = ⊥ := by
    have hh := IsPGroup.disjoint_of_ne 2 3 (by decide) (pCore 2 C) ⊤
      pCore_isPGroup ((hB.to_subgroup C).to_subgroup ⊤)
    simpa only [disjoint_top] using hh
  have he : Nat.card (Y ⧸ pCore 2 Y) = Nat.card C := by
    have hh := Nat.card_congr (starCoreQuotientEquiv B Y hY).toEquiv
    rwa [hC,Nat.card_congr (QuotientGroup.quotientBot).toEquiv] at hh
  have hdiv : Nat.card C ∣ 9 := hBc ▸ C.card_subgroup_dvd_card
  have hcore : B.pCoreIn 2 ≤ T := (isPGroup_pCoreIn 2 B).le_sylow_of_normalized T
    ((T_normalizes_one L _ V₁ d.line_stable).trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))
  have hposs : Nat.card C = 1 ∨ Nat.card C = 3 ∨ Nat.card C = 9 := by
    have hpos := Nat.card_pos (α := C)
    have hle := Nat.le_of_dvd (by decide : 0 < 9) hdiv
    interval_cases h : Nat.card C <;> omega
  rcases hposs with hc | hc | hc
  · left
    have hb : C = ⊥ := C.eq_bot_iff_card.mpr hc
    exact eq_of_starImage_eq B Y ⊥ hY bot_le hp (by intro N _ _; exact Subsingleton.elim _ _)
      (hcore.trans hn) (by intro x _; rw [mem_normalizer_iff]; intro y; simp)
      (by change C = _; rw [hb]; simp only [Section08.Source.starImage,bot_subgroupOf,Subgroup.map_bot])
  · rcases Section03.PointResidualImage.covered_residual_eq_zero_or_plus T d hY hp hn
      (he.trans hc) with hz | hx
    · exact Or.inr (Or.inl hz)
    · exact Or.inr (Or.inr (Or.inl hx))
  · apply Or.inr ∘ Or.inr ∘ Or.inr
    have htop : C = ⊤ := C.eq_top_of_card_eq (hc.trans hBc.symm)
    exact eq_of_starImage_eq B Y B hY le_rfl hp (isPPerfect_embedded_pResidual 2 _)
      (hcore.trans hn) ((pCoreIn_le 2 B).trans B.le_normalizer) (by
        change C = Section08.Source.starImage B B
        rw [Section08.Source.starImage,subgroupOf_self,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
        exact htop)

/-- The cubic closure of the original relatively normal subgroup is either
trivial or the literal L₁,+, with L₀ and L₁ excluded by their proved normalizers. -/
private theorem covered_point_cubic_closure
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (d : NaturalSetup L (T : Subgroup G) V
      (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) V₃)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G))
    (hnY : H ≤ normalizer (Y : Set G))
    (hYz : Y ≤ centralizer ({z.val} : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) :
    closure {x : G | x ∈ Y ∧ orderOf x = 3} = ⊥ ∨
      closure {x : G | x ∈ Y ∧ orderOf x = 3} =
        plus L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) := by
  let A := closure {x : G | x ∈ Y ∧ orderOf x = 3}
  have hAY : A ≤ Y := primeOrderClosure_le 3 Y
  have hAL : A ≤ L := by
    rw [←normalizer_theta h D m]
    exact closure_mono (fun x hx => ⟨hYM hx.1,hx.2⟩)
  have hp : IsPPerfect 2 A := primeOrderClosure_isPPerfect (by decide : Nat.Coprime 2 3) Y
  have hn : H ≤ normalizer (A : Set G) :=
    hnY.trans (normalizer_le_primeOrderClosure_normalizer 3 Y)
  have hAB : A ≤ one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) := by
    rw [covered_firstFlagNormalizer_residual_at h structural D m hc z hz hzL,
      firstCentralizerResidual_eq,
      ←twoResidual_eq_primeToResidual_three (covered_augmentation_point_twoThree D m hc z hzL)]
    have he : residual A = A := by
      change (pResidual 2 A).map A.subtype = A
      rw [(pResidual_eq_top_iff 2 A).mpr hp,←MonoidHom.range_eq_map,range_subtype]
    exact he ▸ embedded_pResidual_mono 2 (le_inf hAL (hAY.trans hYz))
  rcases covered_residual_four_cases d hAB hp (hH.1.2.trans hn) with
    he | he | he | he
  · exact Or.inl he
  · exact (covered_zero_not_normal_outside h.toHypothesis1221 D.sylow_normalizes_component hc hH.2
      (he ▸ hn)).elim
  · exact Or.inr he
  · exact (hH.2 (hn.trans (he.symm ▸ covered_one_normalizer_at h structural D m hc z hz hzL))).elim

private theorem covered_plus_no_cubic_kernel
    (D : ChosenModule T L V) (m : CoreMarking D)
    (d : NaturalSetup L (T : Subgroup G) V V₁ V₃)
    {x : G} (hx : x ∈ plus L (T : Subgroup G) V₁)
    (hxc : x ∈ centralizer (V : Set G)) : orderOf x ≠ 3 := by
  intro ho
  let B := one L (T : Subgroup G) V₁
  let A := plus L (T : Subgroup G) V₁
  have hf := Section08.SourceCompletion.CoverFactorization.source_factorization d
  have hxL := plus_le_L L (T : Subgroup G) V₁ D.sylow_normalizes_component hx
  let l : L := ⟨x,hxL⟩
  have hl : l ∈ centralCore L := by
    have he : BinaryPermutation.coreRepresentation (Fin 6)
        (m.quotient (QuotientGroup.mk' (centralCore L) l)).val = 1 := by
      apply LinearMap.ext
      intro w
      obtain ⟨v,hv⟩ := m.coordinate.surjective (Multiplicative.ofAdd w)
      have he := m.equivariant l v
      have hfix : V.normalizerMonoidHom ⟨l.val,D.normalizes l.property⟩ v = v := by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (hxc v.val v.property).symm
      rw [hfix,hv] at he
      exact he.symm
    have hperm : (m.quotient (QuotientGroup.mk' (centralCore L) l)).val = 1 :=
      BinaryPermutation.SixCoreNormalizer.action_injective (he.trans (map_one _).symm)
    exact (QuotientGroup.eq_one_iff l).mp
      (m.quotient.injective (by rw [map_one]; exact Subtype.ext hperm))
  have hxpre : x ∈ centralPreimage L := mem_map_of_mem L.subtype hl
  have hxzero : x ∈ zero L := by
    refine ⟨⟨x,hxpre⟩,mem_pResidual_of_orderOf_coprime ?_,rfl⟩
    rw [←(centralPreimage L).orderOf_coe,ho]
    decide
  let b : B := ⟨x,plus_le_one L _ V₁ d.line_stable hx⟩
  have hz : QuotientGroup.mk' (pCore 2 B) b ∈
      (zeroCoreMap L _ V₁ d.normalizes_L hf).range := by
    rw [zeroCoreMap,localCoreMap_range]
    exact ⟨b,hxzero,rfl⟩
  have ha : QuotientGroup.mk' (pCore 2 B) b ∈
      (plusCoreMap L _ V₁ d.line_stable).range := by
    rw [plusCoreMap,localCoreMap_range]
    exact ⟨b,hx,rfl⟩
  have hb : b ∈ pCore 2 B := (QuotientGroup.eq_one_iff b).mp
    ((disjoint_iff_inf_le.mp (d.marks_disjoint hf)) ⟨hz,ha⟩)
  have hc := (pCore_isPGroup (p := 2) (G := B)).orderOf_coprime
    (by decide : Nat.Coprime 2 3) (⟨b,hb⟩ : pCore 2 B)
  have hb3 : orderOf (⟨b,hb⟩ : pCore 2 B) = 3 := by
    rw [←(pCore 2 B).orderOf_coe,←B.orderOf_coe]
    exact ho
  rw [hb3] at hc
  exact (by decide : ¬ Nat.Coprime 3 3) hc

/-- The actual covered outside subgroup has a two-group module-action kernel.
The cubic closure and both forbidden residual alternatives are discharged. -/
private theorem covered_point_kernel_isTwo
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (d : NaturalSetup L (T : Subgroup G) V
      (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) V₃)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G))
    (hYH : Y ≤ H) (hnY : H ≤ normalizer (Y : Set G))
    (hYz : Y ≤ centralizer ({z.val} : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    IsPGroup 2 (Y ⊓ centralizer (V : Set G) : Subgroup G) := by
  have h23 := augmentation_outside_twoThree_at h structural D m
    H hH
    Y hYH hnY hp hYM
  have hk23 : IsPiGroup twoThreePrimes (Y ⊓ centralizer (V : Set G) : Subgroup G) :=
    h23.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left)
  apply isPGroup_two_of_isPiGroup_twoThree hk23
  intro hd
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 hd
  have hx3 : orderOf x.val = 3 := ((Y ⊓ centralizer (V : Set G)).orderOf_coe x).trans hx
  have hxA : x.val ∈ closure {a : G | a ∈ Y ∧ orderOf a = 3} :=
    subset_closure ⟨x.property.1,hx3⟩
  rcases covered_point_cubic_closure h structural D m hc d z hz hzL hH hnY hYz hYM with hb | he
  · rw [hb] at hxA
    have hx1 : x = 1 := Subtype.ext (mem_bot.mp hxA)
    rw [hx1,orderOf_one] at hx
    omega
  · exact covered_plus_no_cubic_kernel D m d (he ▸ hxA) x.property.2 hx3

/-- The two-group kernel puts the original point subgroup in L and recovers
it from its cubic closure. This retains the five-dimensional action. -/
private theorem augmentation_point_eq_cubic_closure
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hzL : z.val ∉ centralizer (L : Set G))
    (hYH : Y ≤ centralizer ({z.val} : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y)
    (hk : IsPGroup 2 (Y ⊓ centralizer (V : Set G) : Subgroup G)) :
    Y = closure {x : G | x ∈ Y ∧ orderOf x = 3} := by
  obtain ⟨q,hq,hqL,hker⟩ := exists_core_normalizer_permutation D m
    (normalizer_component_le_module_at h structural D m)
  let a := q.comp (inclusion hYM)
  let w := BinaryPermutation.coreToNatural (Fin 6) (m.coordinate z).toAdd
  have hw : w ≠ 0 := by
    intro he
    apply hzL
    apply (m.mem_fixed_iff z).mpr
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val he)
  let line := Submodule.span (ZMod 2) {w}
  have hline : Module.finrank (ZMod 2) line = 1 := finrank_span_singleton hw
  have hstab : a.range ≤ Representation.BinaryOffender.subspaceStabilizer
      (BinaryPermutation.naturalRepresentation (Fin 6)) line := by
    apply Representation.BinaryOffender.le_subspaceStabilizer
    rintro _ ⟨y,rfl⟩ v hv
    obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hv
    have hfix : V.normalizerMonoidHom
        ⟨y.val,(normalizer_component_le_module_at h structural D m) (hYM y.property)⟩ z = z := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hYH y.property))
    have he := hq (inclusion hYM y) z
    change (m.coordinate (V.normalizerMonoidHom
      ⟨y.val,(normalizer_component_le_module_at h structural D m) (hYM y.property)⟩ z)).toAdd =
      BinaryPermutation.coreRepresentation (Fin 6) (a y) (m.coordinate z).toAdd at he
    rw [hfix] at he
    have hf : BinaryPermutation.naturalRepresentation (Fin 6) (a y) w = w := by
      change BinaryPermutation.naturalRepresentation (Fin 6) (a y)
        (BinaryPermutation.coreToNatural (Fin 6) (m.coordinate z).toAdd) = _
      rw [←BinaryPermutation.coreToNatural_equivariant,←he]
    simpa only [map_smul,hf] using Submodule.smul_mem line c
      (Submodule.mem_span_singleton_self w)
  have hka : IsPGroup 2 a.ker := by
    let j : a.ker →* (Y ⊓ centralizer (V : Set G) : Subgroup G) :=
      (Y.subtype.comp a.ker.subtype).codRestrict _ (fun x => by
        refine ⟨x.val.property,?_⟩
        have hx : inclusion hYM x.val ∈ q.ker := x.property
        rw [hker] at hx
        exact hx)
    apply hk.of_injective j
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (Y ⊓ centralizer (V : Set G) : Subgroup G) => z.val) hh
  let P₁ := Representation.BinaryOffender.subspaceStabilizer
    (BinaryPermutation.naturalRepresentation (Fin 6)) line
  let S₁ : Sylow 2 P₁ := Classical.choice inferInstance
  have hi : (S₁ : Subgroup P₁).index = 3 := by
    have hh := Theory.SpecificGroups.SymmetricSix.BinaryFlags.point_sylow_index_three
      (⊤ : Subgroup (Equiv.Perm (Fin 6))) (by simp) line hline
    rw [top_inf_eq] at hh
    exact hh S₁
  obtain ⟨m,hm⟩ := S₁.isPGroup'.exists_card_eq
  obtain ⟨n,hn⟩ := hka.exists_card_eq
  have hP : Nat.card P₁ = 2^m*3 := by rw [←(S₁ : Subgroup P₁).card_mul_index,hm,hi]
  have hd : Nat.card Y ∣ 2^(n+m)*3 := by
    have him : Nat.card a.range ∣ 2^m*3 := hP ▸ card_dvd_of_le hstab
    have hh := a.ker.card_mul_index
    rw [index_ker,hn] at hh
    rw [←hh,pow_add,mul_assoc]
    exact Nat.mul_dvd_mul_left _ him
  have h23 : IsPiGroup twoThreePrimes Y := by
    rw [IsPiGroup_iff]
    intro p hp
    change p.val = 2 ∨ p.val = 3
    have hp' : p.val ∣ 2^(n+m)*3 := hp.trans hd
    rcases p.property.dvd_mul.mp hp' with hp' | hp'
    · exact Or.inl (((Nat.dvd_prime Nat.prime_two).mp (p.property.dvd_of_dvd_pow hp')).resolve_left p.property.ne_one)
    · exact Or.inr (((Nat.dvd_prime Nat.prime_three).mp hp').resolve_left p.property.ne_one)
  have h9 : ¬9 ∣ Nat.card Y := by
    intro h9
    have hh : 9 ∣ 2^(n+m)*3 := h9.trans hd
    have hcop : Nat.Coprime 9 (2^(n+m)) := (by decide : Nat.Coprime 9 2).pow_right _
    exact (by decide : ¬9∣3) (hcop.dvd_mul_left.mp hh)
  have hgen := Subgroup.cubic_closure_eq_top_of_twoPerfect h23 hp h9
  have he := congrArg (Subgroup.map Y.subtype) hgen
  rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,range_subtype] at he
  have hset : Y.subtype '' {y : Y | orderOf y = 3} = {x : G | x ∈ Y ∧ orderOf x = 3} := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,(Y.orderOf_coe y).trans hy⟩
    · rintro ⟨hx,ho⟩
      exact ⟨⟨x,hx⟩,(Y.orderOf_coe ⟨x,hx⟩).symm.trans ho,rfl⟩
  exact he.symm.trans (congrArg Subgroup.closure hset)

/-- The covered 13.3.9 conclusion on the literal original plane and point,
with the action kernel, cubic closure and full L₁ exclusion proved. -/
private theorem covered_point_residual_of_natural_setup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (d : NaturalSetup L (T : Subgroup G) V
      (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) V₃)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G))
    (hYH : Y ≤ H) (hnY : H ≤ normalizer (Y : Set G))
    (hYz : Y ≤ centralizer ({z.val} : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    Y = ⊥ ∨ (Y = plus L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3) := by
  have hk := covered_point_kernel_isTwo h structural D m hc d z hz hzL hH hYH hnY hYz hYM hp
  have hgen := augmentation_point_eq_cubic_closure h structural D m z hzL hYz hYM hp hk
  rcases covered_point_cubic_closure h structural D m hc d z hz hzL hH hnY hYz hYM with hb | he
  · exact Or.inl (hgen.trans hb)
  · have he' := hgen.trans he
    exact Or.inr ⟨he',he'.symm ▸ d.plus_core_card
      (Section08.SourceCompletion.CoverFactorization.source_factorization d)⟩

/-- Covered 13.3.9 in any original outside overgroup. The natural marking,
kernel and residual choice are constructed from the augmentation data. -/
theorem covered_outside_residual_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G))
    (hYH : Y ≤ H) (hnY : H ≤ normalizer (Y : Set G))
    (hYz : Y ≤ centralizer ({z.val} : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3) := by
  obtain ⟨V₃,⟨d⟩⟩ := covered_augmentation_natural_setup h structural D m hc z hz hzL
  have hn : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
    rintro ⟨e⟩
    have hh := Nat.card_congr (centerCongr e).toEquiv
    rw [hc,alternatingGroup.center_eq_bot (by simp),card_bot] at hh
    omega
  simpa only [selectedFirstResidual,if_neg hn] using
    covered_point_residual_of_natural_setup h structural D m hc d z hz hzL hH hYH hnY hYz hYM hp

/-- The same construction supplies the literal two-group kernel without an
additional natural-marking or local selection premise. -/
theorem covered_outside_action_kernel_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G))
    (hYH : Y ≤ H) (hnY : H ≤ normalizer (Y : Set G))
    (hYz : Y ≤ centralizer ({z.val} : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    IsPGroup 2 (Y ⊓ centralizer (V : Set G) : Subgroup G) := by
  obtain ⟨V₃,⟨d⟩⟩ := covered_augmentation_natural_setup h structural D m hc z hz hzL
  exact covered_point_kernel_isTwo h structural D m hc d z hz hzL hH hYH hnY hYz hYM hp

/-- Every original covered 13.3.9 clause, including equality of the literal
barred actions, for a relatively normal subgroup of any outside overgroup. -/
theorem covered_outside_source_conclusion_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G))
    (hYH : Y ≤ H) (hnY : H ≤ normalizer (Y : Set G))
    (hYz : Y ≤ centralizer ({z.val} : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    Section08.SolvableExclusion.Residual.Conclusion1339 L
      (one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
      (plus L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
      (normalizer (L : Set G)) V Y := by
  obtain ⟨V₃,⟨d⟩⟩ := covered_augmentation_natural_setup h structural D m hc z hz hzL
  rcases covered_point_residual_of_natural_setup h structural D m hc d z hz hzL hH hYH hnY hYz hYM hp with
    hb | ⟨he,hcard⟩
  · exact Or.inl hb
  · exact Section03.PointResidualImage.covered_conclusion_of_placement T d L.le_normalizer
      hH hYH hp
      ((normal_subgroupOf_iff_le_normalizer hYH).mpr hnY)
      (he.symm ▸ plus_le_one L _ _ d.line_stable) hcard
      (covered_zero_normalizer h.toHypothesis1221 D.sylow_normalizes_component hc).le

/-- Apply the outside-overgroup source result to the actual escaping point centralizer. -/
theorem covered_point_residual_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hYH : Y ≤ centralizer ({z.val} : Set G))
    (hnY : centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧
      Nat.card (Y ⧸ pCore 2 Y) = 3) := by
  exact covered_outside_residual_at h structural D m hc z hz hzL
    ⟨centralizer_mem_HOver hz (fun he => hzL (he ▸ one_mem _)),hout⟩
    hYH hnY hYH hYM hp

/-- Apply the outside-overgroup source result to the actual escaping point centralizer. -/
theorem covered_point_action_kernel_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hYH : Y ≤ centralizer ({z.val} : Set G))
    (hnY : centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    IsPGroup 2 (Y ⊓ centralizer (V : Set G) : Subgroup G) := by
  exact covered_outside_action_kernel_at h structural D m hc z hz hzL
    ⟨centralizer_mem_HOver hz (fun he => hzL (he ▸ one_mem _)),hout⟩
    hYH hnY hYH hYM hp

/-- Apply the outside-overgroup source result to the actual escaping point centralizer. -/
theorem covered_point_source_conclusion_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hYH : Y ≤ centralizer ({z.val} : Set G))
    (hnY : centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G))
    (hYM : Y ≤ normalizer (L : Set G)) (hp : IsPPerfect 2 Y) :
    Section08.SolvableExclusion.Residual.Conclusion1339 L
      (one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
      (plus L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
      (normalizer (L : Set G)) V Y := by
  exact covered_outside_source_conclusion_at h structural D m hc z hz hzL
    ⟨centralizer_mem_HOver hz (fun he => hzL (he ▸ one_mem _)),hout⟩
    hYH hnY hYH hYM hp

/-- The full covered 13.3.9 source at the original fixed plane. All outside
subgroups and their relatively normal two-perfect subgroups are quantified;
no action-kernel, placement, normalizer or selected-residual premise remains. -/
theorem covered_source1339_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    Section08.SolvableExclusion.Residual.Source1339 L
      (one L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
      (plus L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G)))
      (T : Subgroup G) (normalizer (L : Set G)) V
      (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) := by
  intro _ H Y hH hYH hp hn hv
  obtain ⟨v,hv,hvL,hYv⟩ := hv
  exact covered_outside_source_conclusion_at h structural D m hc ⟨v,hv.1⟩ hv.2
    (fun hc => hvL ⟨hv.1,hc⟩) hH hYH
    ((normal_subgroupOf_iff_le_normalizer hYH).mp hn)
    (hYv.trans inf_le_right) (hYv.trans inf_le_left) hp

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
