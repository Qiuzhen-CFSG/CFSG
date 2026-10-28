module

public import Theory.GroupTheory.CoreCentralNormalizerAction.PSL2Inverter
public import Theory.SpecificGroups.PSL2.PerfectBlockQuinticPlacement
import all Theory.SpecificGroups.PSL2.PerfectBlockQuinticPlacement
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Quintic placement through the full original two-core

The original subgroup need only have a perfect linear-two quotient modulo
its full two-core. Its quintic actor either lies in the original subgroup or
acts trivially on that exact quotient. No centrality of the two-core kernel
is required. Perfect-cover rigidity is used only after dividing by the full
two-core, to pass from trivial central-quotient action to trivial quotient
action.

The `import all` is an intentional internal proof extension: it reuses the
preceding module's image-order and full-kernel lemmas without changing that
frozen public interface. Source: Aschbacher--Smith 6.1.4, printed p.666.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2

private theorem core_action_trivial {G : Type*} [_root_.Group G]
    (K : Subgroup G) [Group.IsPerfect (K ⧸ pCore 2 K)]
    (x : normalizer (K : Set G)) (hx : normalizerCoreCentralAction K x = 1) :
    quotientAut (pCore 2 K) (K.normalizerMonoidHom x) = 1 := by
  let C := K ⧸ pCore 2 K
  let q := QuotientGroup.mk' (center C)
  let b := quotientAut (pCore 2 K) (K.normalizerMonoidHom x)
  apply MulEquiv.toMonoidHom_injective
  apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq q
    (by rw [QuotientGroup.ker_mk'])
  apply MonoidHom.ext
  intro z
  change q (b z) = q z
  have hh := congrArg (fun a : MulAut (coreCentralQuotient K) => a (q z)) hx
  change (quotientAut (center C) b) (q z) = q z at hh
  exact (quotientAut_apply_mk (center C) b z).symm.trans hh

private theorem placement_or_trivial_core_action
    {G F : Type*} [_root_.Group G] [Finite G] [Field F] [Finite F]
    (K X : Subgroup G) [Group.IsPerfect (K ⧸ pCore 2 K)]
    (U : Sylow 2 K)
    (hUX : (U : Subgroup K).map K.subtype ≤ normalizer (X : Set G))
    (hXN : X ≤ normalizer (K : Set G))
    (hX : IsPPerfect 2 X) (hfive : Nat.card (X ⧸ pCore 2 X) = 5)
    {p n : ℕ} (hp : p.Prime) (ho : Odd p) (hn : 0 < n) (hn2 : n ≤ 2)
    (hF : Nat.card F = p^n) (e : coreCentralQuotient K ≃* PSL(2,F)) :
    X ≤ K ∨ ∀ x : normalizer (K : Set G), (x : G) ∈ X →
      quotientAut (pCore 2 K) (K.normalizerMonoidHom x) = 1 := by
  let C := coreCentralQuotient K
  let a := normalizerCoreCentralAction K
  let D := coreCentralActorImage K X
  by_cases hDne : Nat.card D ≠ 1
  · left
    let ex := (subgroupOfEquivOfLe hXN).symm
    let f : X →* D := (a.subgroupMap (X.subgroupOf (normalizer (K : Set G)))).comp ex.toMonoidHom
    have hf : Function.Surjective f := (a.subgroupMap_surjective _).comp ex.surjective
    have hDp : IsPPerfect 2 D := hX.of_surjective f hf
    have hDfive := image_five_quotient f hf hX hfive hDne
    have houter : IsPGroup 2 (MulAut.Outer C) :=
      (OuterSolvable.SmallDegreeSquares.outer_isPGroup_two hp ho hn2 hF).of_injective
        (MulAut.outerCongr e).toMonoidHom (MulAut.outerCongr e).injective
    have hinner : D ≤ MulAut.innerSubgroup C := by
      let r : D →* MulAut.Outer C := (QuotientGroup.mk' (MulAut.innerSubgroup C)).comp D.subtype
      have hr := hDp.hom_eq_one_of_isPGroup houter r
      intro d hd
      exact (QuotientGroup.eq_one_iff _).mp (DFunLike.congr_fun hr ⟨d,hd⟩)
    have hz : center C = ⊥ := by
      apply bot_unique
      intro c hc
      have hh := (centerCongr e ⟨c,hc⟩).property
      change e c ∈ center PSL(2,F) at hh
      rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hh
      exact e.injective (hh.trans e.map_one.symm)
    let ec : C ≃* MulAut.innerSubgroup C :=
      MonoidHom.ofInjective (Theory.GroupTheory.conj_injective_of_center_eq_bot hz)
    let em := ec.symm.trans e
    let R := (D.subgroupOf (MulAut.innerSubgroup C)).map em.toMonoidHom
    let er : D ≃* R := (subgroupOfEquivOfLe hinner).symm.trans
      ((D.subgroupOf (MulAut.innerSubgroup C)).equivMapOfInjective em.toMonoidHom em.injective)
    have hRp : IsPPerfect 2 R := hDp.of_surjective er.toMonoidHom er.surjective
    have hRfive : Nat.card (R ⧸ pCore 2 R) = 5 := by
      rw [←Nat.card_congr (QuotientGroup.congr _ _ er (pCore_map_iso 2 er)).toEquiv]
      exact hDfive
    have hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) := ⟨p,n,hp,ho,hn,hF⟩
    have hDcard : Nat.card D = 5 := (Nat.card_congr er.toEquiv).trans
      (odd_twoPerfect_quintic_subgroup hodd R hRp hRfive).2
    have hker := kernel_eq_twoCore f hf hDcard hfive
    obtain ⟨u,hu,_,hinv⟩ := Theory.GroupTheory.coreCentral_odd_quintic_sylow_inverter
      K X U hUX hinner hDcard hodd e
    apply le_of_normalized_inverter X K hX hXN u u.property
    intro x hx
    let v : normalizer (K : Set G) := ⟨x,hXN hx⟩
    let t : normalizer (K : Set G) := ⟨u,K.le_normalizer u.property⟩
    have hzX : ((t*v*t⁻¹*v : normalizer (K : Set G)) : G) ∈ X :=
      X.mul_mem ((mem_normalizer_iff.mp (hUX (mem_map_of_mem K.subtype hu)) x).mp hx) hx
    let z : X := ⟨t*v*t⁻¹*v,hzX⟩
    have hfz : f z = 1 := by
      apply Subtype.ext
      change a (t*v*t⁻¹*v)=1
      simp only [map_mul,map_inv]
      rw [hinv v hx,inv_mul_cancel]
    have hzcore : z ∈ pCore 2 X := by
      rw [←hker]
      exact hfz
    exact mem_map_of_mem X.subtype hzcore
  · right
    have hb : D = ⊥ := eq_bot_of_card_eq D (not_ne_iff.mp hDne)
    intro x hx
    apply core_action_trivial K x
    have hh : a x ∈ D := mem_map_of_mem a hx
    rwa [hb,mem_bot] at hh

/-- Placement of the whole original actor, or triviality on the literal
full two-core quotient. The two-core itself need not be central. -/
theorem quintic_le_or_trivial_twoCore_action
    {G F : Type*} [_root_.Group G] [Finite G] [Field F] [Finite F]
    (K X : Subgroup G) (U : Sylow 2 K)
    (hUX : (U : Subgroup K).map K.subtype ≤ normalizer (X : Set G))
    (hXN : X ≤ normalizer (K : Set G))
    (hX : IsPPerfect 2 X) (hfive : Nat.card (X ⧸ pCore 2 X) = 5)
    {p n : ℕ} (hp : p.Prime) (ho : Odd p) (hn : 0 < n) (hn2 : n ≤ 2)
    (hF : Nat.card F = p^n) (hlarge : 3 < Nat.card F)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* SL(2,F)) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* PSL(2,F))) :
    X ≤ K ∨ ∀ x : normalizer (K : Set G), (x : G) ∈ X →
      quotientAut (pCore 2 K) (K.normalizerMonoidHom x) = 1 := by
  let : Group.IsPerfect SL(2,F) := GorensteinWalter.sl2_isPerfect_of_card_gt_three F hlarge
  let : Group.IsPerfect PSL(2,F) := Group.IsPerfect.ofSurjective
    (f := GorensteinWalter.sl2ProjectiveProjection F)
    (GorensteinWalter.sl2ProjectiveProjection_surjective F)
  rcases hm with he | he
  · obtain ⟨e⟩ := he
    let : Group.IsPerfect (K ⧸ pCore 2 K) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    let ec : coreCentralQuotient K ≃* PSL(2,F) :=
      QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e)
    exact placement_or_trivial_core_action K X U hUX hXN hX hfive hp ho hn hn2 hF ec
  · obtain ⟨e⟩ := he
    let : Group.IsPerfect (K ⧸ pCore 2 K) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    let ec : coreCentralQuotient K ≃* PSL(2,F) :=
      (QuotientGroup.congr _ _ e (Theory.GroupTheory.FixedElementary.map_center e)).trans
        ((QuotientGroup.quotientMulEquivOfEq (GorensteinWalter.psl2_center_eq_bot F)).trans
          QuotientGroup.quotientBot)
    exact placement_or_trivial_core_action K X U hUX hXN hX hfive hp ho hn hn2 hF ec

end Theory.PSL2
