module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SeedCubic
public import Theory.Representation.SL2.OddSquareExchange

/-!
# Odd-linear exchanges on the original central Hall seed

The literal quotient marking identifies the nonseparated original seed with
an irreducible faithful PSL₂(p) square. For p at least eleven, the model exchange
bound forces every small elementary actor to preserve the original L-image.
The previously proved seed cubic bound therefore supplies a small cubic actor
inside that component-preserving normalizer, from the original Context alone.

If the actual Sylow exchanger belongs to a small seed actor, the exchange bound
forces separation in either original orientation. This gives crossed movement
and the literal Hall exponent through the existing moved-minimality consumer.
No ambient involution lift or Schur-linearity hypothesis is imposed.

The component-preserving odd-linear exclusion, even-linear tensor branch and
constituent minimality remain with qt-d-10-nona5-central-hall-orders. This does
not assert SeedAnalysisAt or SourceNonnormalCentralHallAt.
Source: Aschbacher--Smith D.3.7, 3.2.6 and10.1.1, printed pp.197--199,581,741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary

/-- The unchanged seed restricted to the original component. -/
@[expose] def originalSeedComponentAction : Representation (ZMod 2) L (Additive D.seed) :=
  (originalSeedAction D).comp (inclusion (le_componentOrbit L T))

/-- Every small elementary actor on a nonseparated odd PSL₂ seed preserves
its literal L-image. Both original seed orientations are retained. -/
theorem original_seed_odd_small_actor_preserves
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p)
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,ZMod p))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (A : Subgroup (Module.End (ZMod 2) (Additive D.seed))ˣ)
    [IsElementaryAbelian 2 A] (hA : A ≤ linearNormalizer (originalSeedAction D))
    (hsmall : fixedCodim (Units.coeHom (Module.End (ZMod 2) (Additive D.seed))) A ≤
      2 * rank A) :
    A ≤ normalizer (actionImage (originalSeedComponentAction D) : Set _) := by
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : IsSimpleGroup PSL(2,ZMod p) := e.symm.isSimpleGroup
  let : IsQuasisimple PSL(2,ZMod p) := IsQuasisimple.of_mulEquiv e
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,hq,_,hl,hr,σ,hi,hσ⟩ := original_seed_product_action D c e ht htn
  have hf := original_seed_product_faithful_of_not_separated D e ht hsep q hl hr σ hσ
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨q l,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext rfl⟩
  have hAσ : A ≤ linearNormalizer σ := by
    change A ≤ normalizer (actionImage σ : Set _)
    rw [←himage]
    exact hA
  let C := A.subgroupOf (linearNormalizer σ)
  let E : C ≃* A := subgroupOfEquivOfLe hAσ
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective E.toMonoidHom E.injective
  have hcod : fixedCodim (normalizerRepresentation σ) C =
      fixedCodim (Units.coeHom (Module.End (ZMod 2) (Additive D.seed))) A := by
    change fixedCodim ((Units.coeHom _).comp (linearNormalizer σ).subtype) C = _
    unfold fixedCodim
    rw [fixedSpace_comp_map,show C.map (linearNormalizer σ).subtype = A from
      map_subgroupOf_eq_of_le hAσ]
  have hrank : rank C = rank A := congrArg (Nat.log 2) (Nat.card_congr E.toEquiv)
  have hb := SL2.odd_prime_square_small_actor_preserves hp σ hi hf C (by
    rw [hcod,hrank]
    exact hsmall)
  have hcomp : actionImage (originalSeedComponentAction D) =
      ((⊤ : Subgroup PSL(2,ZMod p)).prod ⊥).map σ.asGroupHom := by
    have hact (l : L) : (originalSeedComponentAction D).asGroupHom l =
        σ.asGroupHom (e (QuotientGroup.mk' _ l),1) := by
      apply Units.ext
      have hh := DFunLike.congr_fun hσ ⟨l,le_componentOrbit L T l.property⟩
      change σ (q ⟨l,le_componentOrbit L T l.property⟩) = _ at hh
      rw [hl] at hh
      exact hh.symm
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨(e (QuotientGroup.mk' _ l),1),⟨mem_top _,rfl⟩,(hact l).symm⟩
    · rintro ⟨⟨g,h⟩,hg,rfl⟩
      have hh : h=1 := mem_bot.mp hg.2
      subst h
      obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
      exact ⟨l,hact l⟩
  rw [hcomp]
  intro a ha
  exact hb ⟨a,hAσ ha⟩ ha

/-- In the original nonseparated odd-linear branch, a cubic actor of ratio
at most two exists in the literal component-preserving normalizer. The exchange
alternative has been excluded from the original context, not assumed away. -/
theorem original_seed_odd_preserving_cubic_actor
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p)
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,ZMod p))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    ∃ A : Subgroup (linearNormalizer (originalSeedAction D)),
      IsElementaryTwo A ∧ IsCubic (normalizerRepresentation (originalSeedAction D)) A ∧
      fixedCodim (normalizerRepresentation (originalSeedAction D)) A ≤ 2 * rank A ∧
      ∀ a ∈ A, a.val ∈ normalizer (actionImage (originalSeedComponentAction D) : Set _) := by
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  let : Finite (Module.End (ZMod 2) (Additive D.seed)) := Finite.of_injective
    (fun f : Module.End (ZMod 2) (Additive D.seed) => (f : Additive D.seed → Additive D.seed))
    DFunLike.coe_injective
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff _ 2).mp
    (original_seed_normalizer_cubic_of_not_separated D c ht htn hsep)
  let : IsElementaryAbelian 2 A := hA.2
  let f := (linearNormalizer (originalSeedAction D)).subtype
  let E := A.map f
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map f
  have hE : E ≤ linearNormalizer (originalSeedAction D) := by
    rintro a ⟨b,_,rfl⟩
    exact b.property
  have hcod : fixedCodim (Units.coeHom (Module.End (ZMod 2) (Additive D.seed))) E =
      fixedCodim (normalizerRepresentation (originalSeedAction D)) A := by
    change _ = fixedCodim ((Units.coeHom _).comp f) A
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  have hrank : rank E = rank A := rank_map_injective f (subtype_injective _) A
  have hpres := original_seed_odd_small_actor_preserves D c hp e ht htn hsep E hE (by
    rw [hcod,hrank]
    exact hd)
  exact ⟨A,hA,hc,hd,fun a ha => hpres (mem_map_of_mem f ha)⟩

/-- An actual small seed actor containing the Sylow exchanger forces
separation. The action on the seed, rather than the ambient lift, is involutory. -/
theorem original_seed_separated_of_odd_elementary_exchange
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p)
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,ZMod p))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hs : t ∈ normalizer (D.seed : Set G))
    (A : Subgroup (Module.End (ZMod 2) (Additive D.seed))ˣ)
    [IsElementaryAbelian 2 A]
    (hA : A ≤ linearNormalizer (originalSeedAction D))
    (htA : (originalSeedNormalizerAction D).asGroupHom ⟨t,hs⟩ ∈ A)
    (hsmall : fixedCodim (Units.coeHom (Module.End (ZMod 2) (Additive D.seed))) A ≤
      2 * rank A) :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G) := by
  by_contra hsep
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : IsSimpleGroup PSL(2,ZMod p) := e.symm.isSimpleGroup
  let : IsQuasisimple PSL(2,ZMod p) := IsQuasisimple.of_mulEquiv e
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,hq,_,hl,hright,σ,hi,hσ⟩ := original_seed_product_action D c e ht htn
  have hf := original_seed_product_faithful_of_not_separated D e ht hsep q hl hright σ hσ
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨q l,Units.ext (by simp only [Representation.asGroupHom_apply]; rfl)⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext (by simp only [Representation.asGroupHom_apply]; rfl)⟩
  have hAσ : A ≤ linearNormalizer σ := by
    change A ≤ normalizer (actionImage σ : Set _)
    rw [←himage]
    exact hA
  let C := A.subgroupOf (linearNormalizer σ)
  let E : C ≃* A := subgroupOfEquivOfLe hAσ
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective E.toMonoidHom E.injective
  let a : linearNormalizer σ := ⟨(originalSeedNormalizerAction D).asGroupHom ⟨t,hs⟩,hAσ htA⟩
  have ha : a ∈ C := htA
  have h2 : originalSeedNormalizerAction D ⟨t,hs⟩ *
      originalSeedNormalizerAction D ⟨t,hs⟩ = 1 := by
    have he := congrArg Units.val (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      ((originalSeedNormalizerAction D).asGroupHom ⟨t,hs⟩) htA)
    simpa only [pow_two,Units.val_mul,Units.val_one,Representation.asGroupHom_apply] using he
  have hswap : ∀ g v, normalizerRepresentation σ a (σ g v) =
      σ (g.2,g.1) (normalizerRepresentation σ a v) :=
    original_seed_product_exchange D e ht hs q hl hright σ hσ h2
  have hb := SL2.odd_prime_square_exchanged_actor_strict_bound hp σ hi hf C a ha hswap
  have hcod : fixedCodim (normalizerRepresentation σ) C =
      fixedCodim (Units.coeHom (Module.End (ZMod 2) (Additive D.seed))) A := by
    change fixedCodim ((Units.coeHom _).comp (linearNormalizer σ).subtype) C = _
    unfold fixedCodim
    rw [fixedSpace_comp_map,show C.map (linearNormalizer σ).subtype = A from
      map_subgroupOf_eq_of_le hAσ]
  have hrank : rank C = rank A := congrArg (Nat.log 2) (Nat.card_congr E.toEquiv)
  rw [hcod,hrank] at hb
  omega
/-- The exchanged odd-linear branch reaches the literal Hall exponent. The
component-preserving case and moved minimality remain with the final owner. -/
theorem hall_exponent_of_odd_elementary_exchange
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p)
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,ZMod p))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hs : t ∈ normalizer (D.seed : Set G))
    (A : Subgroup (Module.End (ZMod 2) (Additive D.seed))ˣ)
    [IsElementaryAbelian 2 A]
    (hA : A ≤ linearNormalizer (originalSeedAction D))
    (htA : (originalSeedNormalizerAction D).asGroupHom ⟨t,hs⟩ ∈ A)
    (hsmall : fixedCodim (Units.coeHom (Module.End (ZMod 2) (Additive D.seed))) A ≤
      2 * rank A) (hmin : MovedMinimal D) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 :=
  hall_exponent_of_moved_minimal_and_crossed T D c hnot ht htn hmin
    (full_moved_centralizes_opposite_of_seed_separated D ht htn
      (original_seed_separated_of_odd_elementary_exchange D c hp e ht htn hs A hA htA hsmall))
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
