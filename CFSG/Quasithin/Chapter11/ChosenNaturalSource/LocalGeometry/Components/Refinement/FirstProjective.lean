module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Refinement.FirstJanko
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.EvenLinear

/-!
# The literal PGL₃(4) quotient at the first flag normalizer

For a normal PSL₃(4) subgroup generated with an elementary cubic supplement,
the action on the component is faithful. The supplement makes the action
kernel a three-group, while the component's full three-rank and the ambient
rank bound make that kernel prime to three. Every supplement element acts
inner-diagonally; an outside element and the index-three comparison identify
the entire action image with PGL₃(4).

Apply this after passage through the ambient two-core. The C-component
quotient equivalence retains K/O₂(K), and outside cubic membership reflects
through the two-group kernel. At the actual first flag normalizer, the
field-four Cartan is elementary of order nine. Its factor faithful on V₁
supplies an element outside K. Thus the theorem identifies the full original
(K ⊔ X)/O₂(K ⊔ X), not an odd-core quotient or only a subgroup of K ⊔ X.

The final sieve consumer leaves only the SL₃(4) covering row before
RefinementReduction. It does not establish the triangle or the exhaustive
embedding disjunction. Those, the cover exclusion, second-component equality
and source-family assembly remain with qt-d-1222-natural-relative-components.
The earlier flag/Cartan and Sylow-normalizer inputs retain their producers
qt-d-1222-natural-flag-cartan and qt-d-1222-natural-line-action, with ultimate
discharge by qt-d-1222-natural-local-geometry.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, the assertion (*) on printed p.762, using A.3.18 on pp.51--53.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.GroupAction.ComponentRankAction
open CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Projective

private theorem ordinary {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    (hF : Nat.card F = 4) (K X : Subgroup H) [K.Normal]
    (eK : K ≃* PSL(3,F)) (hr : primeRank 3 H ≤ 2)
    (hX : IsPGroup 3 X) (hpow : ∀ x : X, x^3=1)
    (hgen : K ⊔ X = ⊤) (hout : ¬ X ≤ K) :
    Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 3) F) := by
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv eK.symm
  have hz : center K = ⊥ := by
    apply bot_unique
    intro x hx
    apply eK.map_eq_one_iff.mp
    have hh := ((centerCongr eK) ⟨x,hx⟩).property
    change eK x ∈ center PSL(3,F) at hh
    exact (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)).le hh
  let e : K ⧸ center K ≃* PSL(3,F) :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans eK
  have hzc : Nat.Coprime 3 (Nat.card (center K)) := by rw [hz,card_bot]; decide
  have hrK : 2 ≤ primeRank 3 K := by
    rw [primeRank_congr 3 eK]
    exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective
      (show Nat.card F = 2^2 by simpa using hF) (by decide)
  let a := normalAction K e
  have hker : Nat.Coprime 3 (Nat.card a.ker) := by
    rw [normalAction_ker]
    exact centralizer_coprime K hzc hrK hr
  have hrestrict : (a.comp K.subtype).ker = ⊥ := by
    apply bot_unique
    intro k hk
    have hk' : (k : H) ∈ centralizer (K : Set H) := by
      rw [←normalAction_ker K e]
      exact hk
    exact hz.le (mem_center_iff.mpr (fun y => Subtype.ext (mem_centralizer_iff.mp hk' y y.property)))
  have hker3 : IsPGroup 3 a.ker := a.kernel_isPGroup_of_normal_supplement K X hX hgen (by
    rw [hrestrict]
    exact IsPGroup.of_subsingleton 3 _)
  have hinj : Function.Injective a := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    obtain ⟨m,hm⟩ := hker3 (⟨x,hx⟩ : a.ker)
    have hord : orderOf (⟨x,hx⟩ : a.ker) = 1 := Nat.eq_one_of_dvd_coprimes
      (hker.pow_left m) (orderOf_dvd_of_pow_eq_one hm) (orderOf_dvd_natCard _)
    exact congrArg Subtype.val (orderOf_eq_one_iff.mp hord)
  have hi : MulAut.innerSubgroup PSL(3,F) ≤ a.range := by
    rw [←normalAction_component_image K e]
    exact Subgroup.map_le_range a K
  have hXimage : X.map a ≤ innerDiagonal F := by
    rintro _ ⟨x,hx,rfl⟩
    apply Matrix.PSL3.CubicComponentAction.cubic_innerDiagonal
      (show IsComponent H K from ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩)
      (by rw [hz]; exact IsPGroup.of_subsingleton 2 _) hr
      (show 0 < 2 by decide) (show Nat.card F = 2^2 by simpa using hF) (by decide) e
      (⟨x,by rw [K.normalizer_eq_top]; trivial⟩ : normalizer (K : Set H))
    have hx3 : x ^ 3 = 1 := congrArg (fun z : X => (z : H)) (hpow ⟨x,hx⟩)
    exact Subtype.ext hx3
  have hdiag : a.range ≤ innerDiagonal F := by
    rw [MonoidHom.range_eq_map,←hgen,Subgroup.map_sup,normalAction_component_image]
    exact sup_le (inner_le_innerDiagonal F) hXimage
  have hneq : a.range ≠ MulAut.innerSubgroup PSL(3,F) := by
    intro he
    apply hout
    intro x hx
    have hm : a x ∈ K.map a := by
      rw [normalAction_component_image,←he]
      exact ⟨x,rfl⟩
    obtain ⟨k,hk,hke⟩ := hm
    exact hinj hke ▸ hk
  have he : a.range = innerDiagonal F := by
    apply actionImage_eq_of_index_three _ _ _ hi hdiag hneq
    rw [←Nat.card_congr (pglEquivInnerDiagonal F).toEquiv,
      CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.card_pgl_three_eq_three_mul_psl
        (by simp [hF])]
    congr 1
    exact Nat.card_congr (MonoidHom.ofInjective (inner_injective F)).toEquiv
  exact ⟨(MonoidHom.ofInjective hinj).trans
    ((MulEquiv.subgroupCongr he).trans (pglEquivInnerDiagonal F).symm)⟩

/-- A normal PSL₃(4) two-core section and an outside elementary cubic
supplement yield the literal ambient PGL₃(4) two-core quotient. -/
theorem twoCore {H F : Type*} [Group H] [Finite H] [Field F] [Finite F]
    (hF : Nat.card F = 4) (K X : Subgroup H) [K.Normal]
    (hK : K.IsCComponent) (eK : (K ⧸ pCore 2 K) ≃* PSL(3,F))
    (hr : primeRank 3 H ≤ 2) (hX : IsPGroup 3 X) (hpow : ∀ x : X, x^3=1)
    (hgen : K ⊔ X = ⊤) (hout : ¬ X ≤ K) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.ProjGenLinGroup (Fin 3) F) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.map q
  let Y := X.map q
  let : B.Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective _)
  have hgen' : B ⊔ Y = ⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hout' : ¬ Y ≤ B := by
    intro hy
    apply hout
    intro x hx
    by_cases he : x = 1
    · exact he ▸ K.one_mem
    have hx3 : orderOf x = 3 := orderOf_eq_prime
      (congrArg Subtype.val (hpow ⟨x,hx⟩)) he
    exact CComponentPrimeRank.prime_actor_mem_of_twoGroup_image (pCore 2 H) K
      pCore_isPGroup (by decide : Odd 3) x hx3 (hy (mem_map_of_mem q hx))
  apply ordinary hF B Y ((cComponentTwoCoreQuotientEquiv hK).symm.trans eK)
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hr)
    (hX.map q) ?_ hgen' hout'
  rintro ⟨y,hy⟩
  obtain ⟨x,hx,rfl⟩ := hy
  apply Subtype.ext
  change q x ^ 3 = 1
  have hx3 : x ^ 3 = 1 := congrArg (fun z : X => (z : H)) (hpow ⟨x,hx⟩)
  rw [←map_pow,hx3,map_one]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Projective

open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- The PSL₃(4) branch gives the literal KX/O₂(KX), including the whole
original Cartan, as required before the field-four triangle construction. -/
theorem first_projective_four_quotient
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfour : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4) :
    IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)) := by
  obtain ⟨F,_,_,hF,⟨eK⟩⟩ := hk
  let J := K ⊔ X
  let B := K.subgroupOf J
  let Y := X.subgroupOf J
  have hKJ : K ≤ J := le_sup_left
  have hXJ : X ≤ J := le_sup_right
  have hJH : J ≤ normalizer (f.Vi 0 : Set G) :=
    sup_le hK.1.1 (f.cartan_normalizes hu hX 0)
  let k : B ≃* K := subgroupOfEquivOfLe hKJ
  let y : Y ≃* X := subgroupOfEquivOfLe hXJ
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (hJH.trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2))
  have hB : B.IsCComponent := hK.1.2.subgroupOf_of_le hKJ hJH
  have hr : primeRank 3 J ≤ 2 :=
    (_root_.primeRank_le_of_injective 3 (inclusion hJH) (inclusion_injective hJH)).trans
      ((S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)).stronglyQuasithin
        3 Nat.prime_three (by decide))
  have hX3 : IsPGroup 3 X := IsPGroup.of_card (n := 2) (by
    simpa [hfour] using c.cartan_card hX)
  have hpX (x : X) : x^3=1 := by
    let e := c.cartanTorusEquiv hX
    have hc : Nat.card S.field.Carrierˣ = 3 := by
      rw [Nat.card_units,S.field.card_eq,hfour]
      norm_num
    apply e.injective
    rw [map_pow,map_one]
    apply Prod.ext
    · change (e x).1 ^ 3 = 1
      simpa only [hc] using pow_card_eq_one' (x := (e x).1)
    · change (e x).2 ^ 3 = 1
      simpa only [hc] using pow_card_eq_one' (x := (e x).2)
  have hout : ¬ X ≤ K := by
    intro hXK
    let X₁ := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    have hc : Nat.card X₁ = 3 := by simpa [X₁,hfour] using hXcard
    obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := X₁) 3 (by rw [hc])
    have hd := first_component_disjoint_of_faithful_cartan D S f hm hfix hK.1 hLK hfaith
    have he : (x : G) = 1 := hd.le_bot ⟨hXK x.property.1,x.property⟩
    have ho : orderOf (x : G) = 3 := (orderOf_coe x).trans hx
    rw [he,orderOf_one] at ho
    contradiction
  refine ⟨F,inferInstance,inferInstance,hF,?_⟩
  apply Projective.twoCore hF B Y hB
    ((QuotientGroup.congr _ _ k (pCore_map_iso 2 k)).trans eK) hr
    (hX3.of_equiv y.symm) ?_ ?_ ?_
  · intro x
    apply y.injective
    simpa only [map_pow,map_one] using hpX (y x)
  · rw [←subgroupOf_sup hKJ hXJ]
    exact subgroupOf_self J
  · intro hYB
    apply hout
    intro x hx
    exact hYB (show (⟨x,hXJ hx⟩ : J) ∈ Y from hx)

/-- After the J₁ exclusion, the first-index sieve has only the actual
SL₃(4) covering row left before the source refinement reduction. The
PSL₃(4) row already supplies the required full KX quotient. -/
theorem first_reduction_or_specialLinearFour_of_cartan
    (hu : f.IsInnerUnique)
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K) (hLK : f.Li 0 ≤ K)
    (hXcard : Nat.card ↥(X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) = 2 ^ S.field.degree - 1)
    (hfaith : (X ⊓ Closure.coreQuotientCentralizer (f.Li 0)) ⊓ centralizer (f.Vi 0 : Set G) = ⊥)
    (hk : ComponentAlternative (f.Li 0) K S.field.degree) :
    RefinementReduction L (f.Li 0) (f.Li 1) K X 0 S.field.degree ∨
      (S.field.degree = 2 ∧ Source.IsSL (K ⧸ pCore 2 K) 3 4) := by
  rcases first_refinement_or_linearFour_of_cartan D S f hu hm hfix hNT hX hK hLK
    hXcard hfaith hk with h | ⟨hn,hs | hp⟩
  · left
    cases h with
    | equal he => exact .equal he
    | sl2 hi hn p hp hm => exact .sl2 hi hn p hp hm
    | psl2 hi hn p hp hl hm hx => exact .psl2 hi hn p hp hl hm hx
    | triangle hi hn ht => exact .pgl3 hi hn ht.1
  · exact .inr ⟨hn,hs⟩
  · exact .inl (.pgl3 rfl hn (first_projective_four_quotient D S f hu hm hn hfix
      hX hK hLK hXcard hfaith hp))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
