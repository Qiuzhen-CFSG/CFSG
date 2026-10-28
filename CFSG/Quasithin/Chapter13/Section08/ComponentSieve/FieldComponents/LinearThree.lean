module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Definitions
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.MarkedH65
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.OrdinaryAssembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.CoveredAssembly

/-!
# The L₃(2) arguments in the field-component sieve

The conditional 13.8.19 deduction retains all five H.6.5 alternatives. An
explicit natural-module exclusion removes W; an equivariant projection and
fixed-codimension monotonicity remove S, W ⊕ S, and U₂ ⊕ S. The remaining
seven-point core has no quadratic four-group in the marked line radical,
contradicting the critical-group rank bound.

The adapter uses H/O₂(H), the source star images, and the actual conjugation
action on U_H/V₁. The marked H.6.5 classification and earlier representation
bounds remain explicit inputs. The source geometry now supplies the parabolic
marking. Both external-L₁ branches construct their component identifications
and feed the proved paired-chief-factor and marked tensor exclusions.

`Hstar_not_PSL3` and `L₁_le_of_source_list` assemble the two requested
implications from the genuine earlier source clauses. The exact list in
13.8.21(2) remains an independent input to containment. Neither theorem
excludes K* ≅ L₃(2).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.19 and
13.8.21(1), printed pp.953 and 956–957.
-/

public section
open Subgroup Representation
open Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree
open BinaryLinearThree
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) Group U)

/-- Eliminate the natural alternative and every alternative with a Steinberg
quotient. The action-ratio bound on the concrete Steinberg module is the
explicit earlier representation-theoretic input. -/
theorem core_of_H65
    (hclass : H65Alternatives ρ) (hnatural : ¬ Nonempty (ρ.Equiv W))
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic S A → 2 * rank A < fixedCodim S A)
    (A : Subgroup Group) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A) : Nonempty (ρ.Equiv U₂) := by
  have exclude (f : U →ₗ[ZMod 2] Steinberg) (hf : Function.Surjective f)
      (he : ∀ g u, f (ρ g u) = S g (f u)) : False :=
    not_small_quadratic_of_equivariant_quotient ρ S f hf he hS A hA hq hsmall
  unfold H65Alternatives at hclass
  rcases hclass with hn | hc | hs | hws | hcs
  · exact (hnatural hn).elim
  · exact hc
  · obtain ⟨e⟩ := hs
    exact (exclude e.toLinearMap e.surjective (fun g u => LinearMap.congr_fun (e.isIntertwining' g) u)).elim
  · obtain ⟨e⟩ := hws
    apply False.elim
    apply exclude ((LinearMap.snd (ZMod 2) Vector Steinberg).comp e.toLinearMap)
    · intro v
      obtain ⟨u, hu⟩ := e.surjective (0,v)
      refine ⟨u, ?_⟩
      exact congrArg Prod.snd hu
    · intro g u
      exact congrArg Prod.snd (LinearMap.congr_fun (e.isIntertwining' g) u)
  · obtain ⟨e⟩ := hcs
    apply False.elim
    apply exclude ((LinearMap.snd (ZMod 2) Core Steinberg).comp e.toLinearMap)
    · intro v
      obtain ⟨u, hu⟩ := e.surjective (0,v)
      refine ⟨u, ?_⟩
      exact congrArg Prod.snd hu
    · intro g u
      exact congrArg Prod.snd (LinearMap.congr_fun (e.isIntertwining' g) u)

/-- The core has no quadratic subgroup of rank greater than one in the marked
line radical. The 13.8.18(4) lower bound therefore contradicts H.6.5. -/
theorem no_critical_configuration
    (hclass : H65Alternatives ρ) (hnatural : ¬ Nonempty (ρ.Equiv W))
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic S A → 2 * rank A < fixedCodim S A)
    (hcore : ∀ g : Group, fixedCodim U₂ (Subgroup.zpowers g) ≠ 1)
    (A B : Subgroup Group) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hsmall : fixedCodim ρ A ≤ 2 * rank A)
    (hB : B ≤ R) (hBq : IsQuadratic ρ B)
    (hlarge : (∀ g : Group, fixedCodim ρ (Subgroup.zpowers g) ≠ 1) → 1 < rank B) : False := by
  obtain ⟨e⟩ := core_of_H65 ρ hclass hnatural hS A hA hq hsmall
  have he (g : Group) (u : U) : e (ρ g u) = U₂ g (e u) :=
    LinearMap.congr_fun (e.isIntertwining' g) u
  have hcod (D : Subgroup Group) : fixedCodim ρ D = fixedCodim U₂ D := by
    simpa only [Subgroup.map_id] using
      fixedCodim_map_equivariant ρ U₂ (MonoidHom.id Group) e.toLinearEquiv he D
  have hlt := hlarge (fun g => by rw [hcod]; exact hcore g)
  have hquad := quadratic_of_equivariant_surjection ρ U₂
    e.toLinearMap e.surjective he B hBq
  have hle := quadratic_rank_le_one B hB hquad
  omega
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree
variable {G : Type*} [Group G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsMulCommutative (Source.Utilde H V₃ V₁)]
  [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
  [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- The 13.8.19 implication on the literal source quotient and module.

`hmodels` is the marked H.6.5 input, `hnatural` is the 13.7.6(1) exclusion,
and `hS` and `hcore` are the concrete earlier representation bounds. The
quadratic actor and its codimension bound come from 13.8.8; the quadratic
critical group, conjugate rank, and strict lower bound come from 13.8.4(6),
13.8.8 and 13.8.18(4). The source owner must supply each of these premises.
The conclusion concerns H*, and does not exclude K* ≅ L₃(2). -/
theorem Hstar_not_PSL3_of_H65
    (act : SourceAction H V₃ V₁) (Uγ Vα Vγ : Subgroup G)
    (hmodels : Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL) →
      ∃ e : Source.Hstar H ≃* BinaryLinearThree.Group,
        H65Alternatives (act.representation.comp e.symm.toMonoidHom) ∧
          (Source.starImage H Vα).map e.toMonoidHom ≤ BinaryLinearThree.R)
    (hnatural : ∀ e : Source.Hstar H ≃* BinaryLinearThree.Group,
      ¬ Nonempty (Representation.Equiv (act.representation.comp e.symm.toMonoidHom) BinaryLinearThree.W))
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic BinaryLinearThree.S A →
      2 * rank A < fixedCodim BinaryLinearThree.S A)
    (hcore : ∀ g : BinaryLinearThree.Group,
      fixedCodim BinaryLinearThree.U₂ (Subgroup.zpowers g) ≠ 1)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hq : IsQuadratic act.representation (Source.starImage H Uγ))
    (hsmall : fixedCodim act.representation (Source.starImage H Uγ) ≤
      2 * rank (Source.starImage H Uγ))
    (hBq : IsQuadratic act.representation (Source.starImage H Vα))
    (hrank : rank (Source.starImage H Vα) = rank (Source.starImage H Vγ))
    (hlarge : (∀ g : Source.Hstar H,
      fixedCodim act.representation (Subgroup.zpowers g) ≠ 1) →
        1 < rank (Source.starImage H Vγ)) :
    ¬ Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL) := by
  intro hiso
  obtain ⟨e, hc, hB⟩ := hmodels hiso
  let ρ := act.representation
  let σ := ρ.comp e.symm.toMonoidHom
  have he (g : Source.Hstar H) (u : Additive (Source.Utilde H V₃ V₁)) :
      (LinearEquiv.refl (ZMod 2) _ : _ ≃ₗ[ZMod 2] _) (ρ g u) =
        σ (e g) ((LinearEquiv.refl (ZMod 2) _ : _ ≃ₗ[ZMod 2] _) u) := by
    change ρ g u = ρ (e.symm (e g)) u
    rw [e.symm_apply_apply]
  have hcod (D : Subgroup (Source.Hstar H)) :
      fixedCodim ρ D = fixedCodim σ (D.map e.toMonoidHom) :=
    fixedCodim_map_equivariant ρ σ e.toMonoidHom (LinearEquiv.refl _ _) he D
  have hquad (D : Subgroup (Source.Hstar H)) (hD : IsQuadratic ρ D) :
      IsQuadratic σ (D.map e.toMonoidHom) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ u
    simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply] using hD a ha b hb u
  have helem : IsElementaryTwo ((Source.starImage H Uγ).map e.toMonoidHom) := by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let : IsElementaryAbelian 2 (Source.starImage H Uγ) := hA.2
    refine ⟨?_, IsElementaryAbelian.map e.toMonoidHom⟩
    intro hb
    apply hA.1
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_bot] using hb
  apply no_critical_configuration σ hc (hnatural e) hS hcore
    ((Source.starImage H Uγ).map e.toMonoidHom)
    ((Source.starImage H Vα).map e.toMonoidHom) helem (hquad _ hq)
    (by rw [← hcod, rank_map_injective e.toMonoidHom e.injective]; exact hsmall)
    hB (hquad _ hBq)
  intro hn
  rw [rank_map_injective e.toMonoidHom e.injective, hrank]
  apply hlarge
  intro g
  rw [hcod, MonoidHom.map_zpowers]
  exact hn (e g)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree


open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree
open Geometry Geometry.ParabolicMarking
variable {G : Type*} [Group G] [Finite G]
variable (H L L₁ M V V₃ V₁ : Subgroup G) (T : Sylow 2 G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- The actual earlier quadratic actor and its critical conjugate, extracted
from 13.8.8(2), with quadraticity from 13.8.4(6) and the exact 13.8.18(4)
rank implication. No module classification or rank-one bound is included. -/
structure HstarCriticalEarlier (act : SourceAction H V₃ V₁) where
  Uγ : Subgroup G
  Vα : Subgroup G
  Vγ : Subgroup G
  placement : Vα ≤ (L₁ ⊔ (T : Subgroup G)).pCoreIn 2
  elementary : IsElementaryTwo (Source.starImage H Uγ)
  quadratic : IsQuadratic act.representation (Source.starImage H Uγ)
  small : fixedCodim act.representation (Source.starImage H Uγ) ≤
    2 * rank (Source.starImage H Uγ)
  critical_quadratic : IsQuadratic act.representation (Source.starImage H Vα)
  conjugate_rank : rank (Source.starImage H Vα) = rank (Source.starImage H Vγ)
  large : (∀ a : Source.Hstar H,
    fixedCodim act.representation (zpowers a) ≠ 1) → 1 < rank (Source.starImage H Vγ)

/-- 13.8.19 from the actual earlier source actions and critical clauses.
The model alternatives in 13.8.5(2) first exclude its transvection branch by
orders, making 13.8.8(2) available. The source geometry constructs the H.6.5
marking, after which the five-alternative sieve leaves U₂ and gives the
rank-one contradiction with 13.8.18(4), using the earlier G.6.4 bound.
H.6.5, 13.7.6(1), B.4/B.5 and the earlier critical results remain explicit. -/
theorem Hstar_not_PSL3
    [(V₁.subgroupOf V₃).Normal] [IsKleinFour (V₃ ⧸ V₁.subgroupOf V₃)]
    (act : SourceAction H V₃ V₁)
    (hTH : (T : Subgroup G) ≤ H) (hL₁H : L₁ ≤ H)
    (hPM : L₁ ⊔ (T : Subgroup G) ≤ M) (hHM : ¬ H ≤ M)
    (hT : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hV : L ⊔ (T : Subgroup G) ≤ normalizer (V : Set G))
    (hL₁ : (pResidual 2 (sourcePointStabilizer L V₁ T)).map
      (sourcePointStabilizer L V₁ T).subtype = L₁)
    (hPn : L₁ ⊔ (T : Subgroup G) ≤ normalizer (V₃ : Set G))
    (a : SeedAction V₃ V₁ (L₁ ⊔ (T : Subgroup G)) hPn)
    (h3V : V₃ ≤ V)
    (hcentralizer : ∀ h : H,
      (∀ u : Source.UH H V₃,
        QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) (conjugateUH H V₃ h u) =
          QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) → h ∈ pCore 2 H)
    (h65 : H65Theorem (U := Additive (Source.Utilde H V₃ V₁)))
    (hnatural : ∀ e : Source.Hstar H ≃* BinaryLinearThree.Group,
      ¬ Nonempty (Representation.Equiv (act.representation.comp e.symm.toMonoidHom) BinaryLinearThree.W))
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic BinaryLinearThree.S A →
      2 * rank A < fixedCodim BinaryLinearThree.S A)
    (hcore : ∀ g : BinaryLinearThree.Group,
      fixedCodim BinaryLinearThree.U₂ (zpowers g) ≠ 1)
    (htrans : (∃ a : Source.Hstar H, fixedCodim act.representation (zpowers a) = 1) →
      Nonempty (Source.Hstar H ≃* Equiv.Perm (Fin 6)) ∨
      Nonempty (Source.Hstar H ≃* Equiv.Perm (Fin 7)) ∨
      Nonempty (Source.Hstar H ≃* PSL(4, ZMod 2)))
    (critical : (∀ a : Source.Hstar H, fixedCodim act.representation (zpowers a) ≠ 1) →
      Nonempty (HstarCriticalEarlier H L₁ V₃ V₁ T act)) :
    ¬ Nonempty (Source.Hstar H ≃* Matrix.PSL3Two.PSL) := by
  rintro ⟨e⟩
  have hcard : Nat.card (Source.Hstar H) = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hnotrans : ∀ a : Source.Hstar H, fixedCodim act.representation (zpowers a) ≠ 1 := by
    intro a ha
    rcases htrans ⟨a,ha⟩ with hf | hf | hf
    · obtain ⟨f⟩ := hf
      have hc := Nat.card_congr f.toEquiv
      norm_num [hcard, Nat.card_eq_fintype_card, Fintype.card_perm] at hc
    · obtain ⟨f⟩ := hf
      have hc := Nat.card_congr f.toEquiv
      norm_num [hcard, Nat.card_eq_fintype_card, Fintype.card_perm] at hc
    · obtain ⟨f⟩ := hf
      have hc := Nat.card_congr (f.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).toEquiv
      rw [hcard, nat_card_alternatingGroup] at hc
      norm_num at hc
  obtain ⟨c⟩ := critical hnotrans
  exact Hstar_not_PSL3_of_H65 H V₃ V₁ act c.Uγ c.Vα c.Vγ
    (source_H65_input H L L₁ M V V₃ V₁ c.Vα T act hTH hL₁H hPM hHM
      hT hV hL₁ hPn a h3V c.placement hcentralizer h65)
    hnatural hS hcore c.elementary c.quadratic c.small c.critical_quadratic
    c.conjugate_rank c.large ⟨e⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree


open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree
open Geometry Geometry.ExternalComponentAction Geometry.CoveredProduct.ResidualPlacement
open ExternalModules
variable {G : Type*} [Group G] [Finite G]

/-- Only the ordinary earlier local clauses: the actual A₆ quotient, its
marked cubic residual, commutator identities and the ordinary 13.8.14
alternative. No external-component geometry or containment is included. -/
structure OrdinaryEarlier (H L L₁ T V₃ : Subgroup G) where
  model : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)
  order : Nat.card (L₁ ⧸ pCore 2 L₁) = 3
  full : ⁅L₁,T⁆ = L₁
  seed : ⁅V₃,L₁⁆ = V₃
  fitting : fittingPreimageResidual H = ⊥ ∨ fittingPreimageResidual H = L₁

variable (H L L₁ T V V₃ V₁ M : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

/-- Only the covered earlier local clauses, including the actual natural
section and the earlier critical-pair implication. The latter must be
instantiated after excluding transvections, not assumed unconditionally.
The component quotient and its product/point markings are not inputs. -/
structure CoveredEarlier (act : SourceAction H V₃ V₁) where
  natural : LocalAction.NaturalSetup L T V V₁ V₃
  factor : one L T V₁ = plus L T V₁ ⊔ zero L
  normalizer : Subgroup.normalizer (zero L : Set G) = M
  fitting : fittingPreimageResidual H = ⊥ ∨
    (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      fittingPreimageResidual H = one L T V₁) ∨
    fittingPreimageResidual H = plus L T V₁
  seed_dimension : Module.finrank (ZMod 2) (seedSpace H V₃ V₁) = 2
  critical : (∀ a : Source.Hstar H,
    fixedCodim act.representation (zpowers a) ≠ 1) →
    Nonempty (CriticalEarlier H (one L T V₁) T V V₃ V₁ act)

variable (κ : GroupClass) (K G₁ : Subgroup G) (S : Sylow 2 G)

/-- 13.8.21(1), conditional on the independently supplied exact list (2)
and genuine earlier source results. The local alternatives retain actual
A₆ or covered-A₆ actions. In the external case the component list reduces
K* to L₃(2); the ordinary full-automorphism and covered marked-tensor
exclusions then prove containment. K* ≅ L₃(2) itself remains allowed.

The section assembly supplies `d` from 13.7.3 and 13.8.12–16, solvable
overgroups from 13.8.13, quasisimplicity from 13.8.15, the source centralizer
identity, the earlier local alternatives, and the B.4 bounds. The list's
production and these earlier-source discharges remain with their owners. -/
theorem L₁_le_of_source_list
    (hQTKE : IsSimpleQTKE κ G)
    (d : RankReduction.SourceSetup κ H K L₁ M G₁ S)
    (models : (∃ n : ℕ, 3 ≤ n ∧ n ≤ 5 ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) n 2) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* commutator (Atlas.G2.Model (ZMod 2))))
    (hmarked : L₁ = one L S V₁)
    (hflag : (S : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hsolvable : ∀ J : Subgroup G, L₁ ⊔ (S : Subgroup G) ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (hqs : IsQuasisimple (Source.starImage H K))
    (act : SourceAction H V₃ V₁)
    (hfaithful : ∀ h : H,
      (∀ u : Source.UH H V₃,
        QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) (conjugateUH H V₃ h u) =
          QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) → h ∈ pCore 2 H)
    (earlier : Nonempty (OrdinaryEarlier H L L₁ S V₃) ∨
      Nonempty (CoveredEarlier H L S V V₃ V₁ M act))
    (hS : ∀ A, IsElementaryTwo A → IsQuadratic BinaryLinearThree.S A →
      rank A < fixedCodim BinaryLinearThree.S A)
    (hND : ∀ A, IsElementaryTwo A → IsQuadratic naturalDual A →
      rank A < fixedCodim naturalDual A)
    (hsmall : quadraticRatio act.representation ≤ 2) : L₁ ≤ K := by
  have hm := RankReduction.smallQuotient_of_source_list models
  rcases earlier with ho | hc
  · obtain ⟨o⟩ := ho
    exact L₁_le_of_ordinary_source κ H K L L₁ M G₁ V₁ V₃ S hQTKE d hm
      o.model hmarked hflag o.order o.full o.seed hsolvable o.fitting hqs
      act hfaithful hS hND hsmall
  · obtain ⟨c⟩ := hc
    subst L₁
    exact L₁_le_of_covered_source H V V₃ V₁ κ K L M G₁ S d hm c.natural
      c.factor c.normalizer c.fitting hqs act hfaithful c.seed_dimension c.critical

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree
