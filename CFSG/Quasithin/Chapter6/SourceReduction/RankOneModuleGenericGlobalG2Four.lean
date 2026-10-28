module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryMaximal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Maximal
public import Theory.Representation.G2.NaturalScalarCubic
public import Mathlib.GroupTheory.FixedPointFree

/-!
# The actual cubic actor in the G₂(4) maximality argument

The equal-coordinate split torus centralizes the short rank-one quotient.
A nonidentity field-four scalar acts by a on the four horizontal root
coordinates and by a² on the central coordinate. Both weights are nontrivial,
so the action is fixed-point-free on the entire special core. The finite
fixed-point-free commutator map proves that the cubic generates the core
by commutators, hence also moves its whole Frattini quotient.

Transport uses the compatible middle and right maps of the actual amalgam.
It constructs the cubic inside the original whole overlap, retains its
pointwise quotient action and acts on the original right core. For a proper
maximal overcomponent normalizing that core, source 1.2.7 and uniqueness of
containing C-components make the same cubic normalize the overcomponent.
The quotient is then in the actual A.3.14 shortlist. Together with the
already proved larger-field maximality, this leaves precisely the displayed
field-four cases, with the cubic-actor premise discharged.

Core normality and the remaining field-four representation exclusions are
not proved here. Exhaustive F.1.12 comparison, original left uniqueness and
ambient completion recognition remain required for GlobalExit. The Chapter12
companion applies these statements to the literal prepared pair.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`).
The root formulas are from the existing licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. No new ATLAS text is copied.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.LieParabolicSetup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2Four
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem scalar_fixed_free (a : Fˣ) (ha : a ≠ 1)
    (r : Model F) (hr : r ∈ radical₁) (hc : Commute (torus a a) r) : r = 1 := by
  obtain ⟨t,ht,rfl⟩ := hr
  have he : torusUnipotentParameters a a t = t := by
    apply unipotentProduct_injective
    rw [←torus_unipotentProduct,hc.eq,mul_inv_cancel_right]
  have ha1 : (a : F) ≠ 1 := fun hh => ha (Units.ext hh)
  have ha2 : (a : F)^2 ≠ 1 := by
    intro hh
    exact ha1 (by
      have hh' : (a : F)^2 = (1 : F)^2 := by simpa using hh
      exact frobenius_inj F 2 hh')
  have hz (w z : F) (hw : w ≠ 1) (hh : w*z=z) : z=0 := by
    have he : (w-1)*z=0 := by rw [sub_mul,one_mul,hh,sub_self]
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hw)
  have h0 : t 0=0 := hz _ _ ha2 (by simpa [torusUnipotentParameters,pow_two] using congrFun he 0)
  have h1 : t 1=0 := hz _ _ ha1 (by simpa [torusUnipotentParameters,pow_two] using congrFun he 1)
  have h2 : t 2=0 := hz _ _ ha1 (by simpa [torusUnipotentParameters] using congrFun he 2)
  have h3 : t 3=0 := hz _ _ ha1 (by simpa [torusUnipotentParameters] using congrFun he 3)
  have h4 : t 4=0 := hz _ _ ha1 (by simpa [torusUnipotentParameters,pow_two] using congrFun he 4)
  simp [unipotentProduct,h0,h1,h2,h3,h4,ht]

private theorem model_actor (hF : Nat.card F = 4) :
    ∃ x : Model F, x ∈ ChapterF.GreenBook.LieModels.G2.overlap ∧ orderOf x = 3 ∧
      (∀ k ∈ local₁ (F := F), ⁅x,k⁆ ∈ radical₁) ∧
      (∀ q ∈ radical₁ (F := F), Commute x q → q = 1) := by
  obtain ⟨a,ha⟩ : ∃ a : Fˣ, orderOf a = 3 := by
    apply exists_prime_orderOf_dvd_card' 3
    rw [Nat.card_units,hF]
  let f : Fˣ →* Model F := torusHom.comp ((MonoidHom.id _).prod (MonoidHom.id _))
  have hf : Function.Injective f := fun _ _ hh => congrArg Prod.fst (torusHom_injective hh)
  refine ⟨torus a a,ChapterF.GreenBook.LieModels.G2.borel_le_overlap
    (mem_sup_right ⟨(a,a),rfl⟩),(orderOf_injective f hf a).trans ha,
    NaturalScalarCubic.short_commutators a,?_⟩
  exact scalar_fixed_free a (fun hh => by simp [hh] at ha)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2Four

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

private theorem fixed_free_core_commutator {Q : Subgroup G} {x : G}
    (hn : x ∈ normalizer (Q : Set G))
    (hf : ∀ q ∈ Q, Commute x q → q=1) : ⁅Q,zpowers x⁆ = Q := by
  let a := Q.normalizerMonoidHom ⟨x,hn⟩
  have hfree : MonoidHom.FixedPointFree a := by
    intro q hq
    apply Subtype.ext
    apply hf q q.property
    apply (mul_inv_eq_iff_eq_mul).mp
    exact congrArg Subtype.val hq
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hn))
  intro q hq
  obtain ⟨r,hr⟩ := hfree.commutatorMap_surjective ⟨q,hq⟩
  have he : ⁅(r:G),x⁆ = q := by
    have hh := congrArg Subtype.val hr
    simpa only [MonoidHom.commutatorMap_apply,coe_div,coe_mul,coe_inv,a,
      normalizerMonoidHom_apply_apply_coe,div_eq_mul_inv,
      mul_inv_rev,inv_inv,commutatorElement_def,mul_assoc] using hh
  exact he ▸ commutator_mem_commutator r.property (mem_zpowers x)

/-- The small-field scalar is constructed inside the whole original overlap.
It fixes the right core quotient and is fixed-point-free on the entire
special two-core, so that core is generated by its commutators with the
cubic subgroup. This is the cubic actor in the last paragraph of 5.2.8. -/
theorem Preparation.g2_four_cubic_actor
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G}
    (d : Preparation T L H A B (residual H))
    (h : Input κ T L W 2) (hTH : (T : Subgroup G) ≤ H)
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    ∃ x : G, x ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ∧
      orderOf x = 3 ∧ x ∈ normalizer (residual H : Set G) ∧
      (∀ k ∈ residual H, ⁅x,k⁆ ∈ (residual H).pCoreIn 2) ∧
      (∀ q ∈ (residual H).pCoreIn 2, Commute x q → q = 1) ∧
      ⁅(residual H).pCoreIn 2,zpowers x⁆ = (residual H).pCoreIn 2 := by
  have hF : Nat.card F = 4 := (d.g2_local_structure h hTH hp F he).1
  rcases he with he | he
  · exact (d.not_g2_short_left_parabolic h hTH hp (he.map fun e => e.left)).elim
  obtain ⟨e⟩ := he
  let K := residual H
  let P := ChapterF.Source.parabolic ![L,K] (sourceS L H) 1
  let I := ChapterF.Source.parabolic ![L,K] (sourceS L H) 0 ⊓ P
  let f : P →* Model F := (parabolic₁ (F := F)).subtype.comp e.right.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.right.injective
  have hKP : K ≤ P := le_sup_left.trans le_sup_left
  have hK0 : K.subgroupOf P = solvableResidual P := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le hKP,d.parabolic_residuals h hTH hp 1]
    rfl
  have hmapK : (K.subgroupOf P).map f = local₁ (F := F) := by
    rw [hK0,show f = (parabolic₁ (F := F)).subtype.comp e.right.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq e.right.toMonoidHom e.right.surjective,
      HigherFieldResiduals.parabolic₁_residual (by omega : 2 < Nat.card F)]
  have hmapQ : ((K.pCoreIn 2).subgroupOf P).map f = radical₁ (F := F) := by
    rw [←pCoreIn_subgroupOf 2 K P hKP,map_pCoreIn_of_injective 2 _ f hf,hmapK,local₁_pCore]
  have hQP : K.pCoreIn 2 ≤ P := (map_subtype_le _).trans hKP
  have hPN : P ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hKP).mp ((d.hypothesisF11 h hTH).local_normal_in_parabolic 1)
  obtain ⟨y,hy,ho,hquot,hfree⟩ := G2Four.model_actor hF
  let b : I := e.middle.symm ⟨y,hy⟩
  let x : G := b.val
  have hxP : x ∈ P := b.property.2
  have hfx : f ⟨x,hxP⟩ = y := by
    have hh := e.right_commutes b
    rw [show e.middle b = ⟨y,hy⟩ from e.middle.apply_symm_apply _] at hh
    exact congrArg Subtype.val hh
  have hxorder : orderOf x = 3 := by
    have h1 := orderOf_injective f hf ⟨x,hxP⟩
    rw [hfx,ho] at h1
    have h2 := orderOf_injective P.subtype P.subtype_injective ⟨x,hxP⟩
    exact h2.trans h1.symm
  have hqn : x ∈ normalizer (K.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image K (pCore 2 K) (hPN hxP)
  have hfree' : ∀ q ∈ K.pCoreIn 2, Commute x q → q=1 := by
    intro q hq hcomm
    have hqf : f ⟨q,hQP hq⟩ ∈ radical₁ (F := F) :=
      hmapQ ▸ mem_map_of_mem f (show (⟨q,hQP hq⟩:P) ∈ (K.pCoreIn 2).subgroupOf P from hq)
    have hcomm' : Commute y (f ⟨q,hQP hq⟩) := by
      rw [←hfx]
      apply Commute.map
      exact (show Commute (⟨x,hxP⟩:P) ⟨q,hQP hq⟩ from Subtype.ext hcomm.eq)
    have heq : (⟨q,hQP hq⟩:P) = 1 :=
      hf ((hfree _ hqf hcomm').trans (map_one f).symm)
    exact congrArg Subtype.val heq
  refine ⟨x,b.property,hxorder,hPN hxP,?_,hfree',fixed_free_core_commutator hqn hfree'⟩
  intro k hk
  have hfk : f ⟨k,hKP hk⟩ ∈ local₁ (F := F) :=
    hmapK ▸ mem_map_of_mem f (show (⟨k,hKP hk⟩:P) ∈ K.subgroupOf P from hk)
  have hh := hquot _ hfk
  rw [←hfx,←map_commutatorElement,←hmapQ] at hh
  exact (mem_map_iff_mem hf).mp hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]

/-- The G₂ row is maximal or lies at field four. In the latter case a
proper maximal overcomponent either does not normalize the original core,
or has exactly that core and one of the actual A.3.14 quotients. In the
normal-core case the original overlap supplies a cubic normalizing the
overcomponent, centralizing K/Q and generating Q by commutators. -/
theorem Preparation.g2_maximal_or_four_obstruction
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (he : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F))) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∨
      n = 2 ∧ Nat.card F = 4 ∧ ∃ J ∈ Chapter1.LStar G (T : Subgroup G),
        residual H < J ∧
        (¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G) ∨
          J.pCoreIn 2 = (residual H).pCoreIn 2 ∧
          ChapterA.Section03.SourceEmbeddings.AlternatingFive.Shortlist (J ⧸ pCore 2 J) ∧
          ∃ x : G, x ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
              ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ∧
            orderOf x = 3 ∧ x ∈ normalizer (J : Set G) ∧
            (∀ k ∈ residual H, ⁅x,k⁆ ∈ (residual H).pCoreIn 2) ∧
            (∀ q ∈ J.pCoreIn 2, Commute x q → q = 1) ∧
            ⁅J.pCoreIn 2,zpowers x⁆ = J.pCoreIn 2) := by
  by_cases hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)
  · exact .inl hmax
  have hn : n = 2 := by
    have hh := h.exponent
    by_contra hn
    exact hmax (d.g2_right_maximal h hH hp (by omega) F he)
  subst n
  have hf := d.g2_local_structure h hH.1.1.2 hp F he
  have hK := residual_binary_mem_local hH.1.1 hp h.exponent hf.2.2.2.1
  obtain ⟨J,hJ,hKJ⟩ := Chapter1.exists_mem_LStar_ge hK
  have hlt : residual H < J := lt_of_le_of_ne hKJ (fun hh => hmax (hh.symm ▸ hJ))
  refine .inr ⟨rfl,hf.1,J,hJ,hlt,?_⟩
  by_cases hn : J ≤ normalizer ((residual H).pCoreIn 2 : Set G)
  · right
    have hc := d.maximal_overcomponent_core_of_normal h hH.1.1.2 hp (.g2 F he) hK hJ hKJ hn
    have hm := local_binary_overcomponent_of_core_eq h.qtke hJ.1
      (hH.1.1.2.trans (le_normalizer_residual H)) hlt hc.1 h.exponent hp hf.2.2.2.1
    obtain ⟨x,hx,ho,hxN,hquot,hfree,hmove⟩ := d.g2_four_cubic_actor h hH.1.1.2 hp F he
    exact ⟨hc.1,hm.2,x,hx,ho,hc.2 hxN,hquot,by rwa [hc.1],by rwa [hc.1]⟩
  · exact .inl hn

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
