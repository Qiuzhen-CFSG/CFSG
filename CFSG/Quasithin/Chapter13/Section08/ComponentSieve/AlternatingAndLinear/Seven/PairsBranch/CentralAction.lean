module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.ModuleSieve
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Tactic

/-!
# Nontrivial component action in the three-pairs branch

Let W be a subrepresentation of the actual binary conjugation representation
on Ũ_H = U_H/V₁. The two witnesses supplied by the other branches are an
isomorphism L/O₂(L) ≃ A₆ and an equivariant equivalence Ũ_H/W ≃ Core(7).
Suppose K centralizes W. Transitivity of A₇ and odd degree show that the
quotient has no K-fixed vectors, and consequently C_{Ũ_H}(K)=W.
The earlier generation equality U_H=[U_H,K] makes the literal image Ũ_K
all of Ũ_H. The first isomorphism theorem therefore constructs the natural
identification of Ũ_K/C_{Ũ_K}(K) required by 13.7.6(3). No splitting of Ũ_H
is assumed or asserted.

The earlier theorem is an explicit universal implication, retaining both
n=6 and n=7 and their different group conclusions. Its unused coordinate and
chief-factor conclusions are not asserted here. In degree seven its conclusion
is a genuine perfect central three-fold cover of A₆, incompatible by order with
the supplied A₆ quotient. This proves an actual moving component element and
vector for W.toRepresentation, in the form consumed by the module sieve.

This is the independent conditional helper, not the completed 13.8.24 or a
proof of 13.7.6. The source assembly must supply the earlier implication, the
local hypotheses and the two witnesses. Normality of V₁ is relative to U_H;
C-component membership is relative to H. The component's intrinsic quotient
is identified with K* by the proved componentStarEquiv, not by a family tag.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
combined manuscript of 1 March 2004, 13.7.6(3), printed pp.938–939,
and the three-pairs paragraph of 13.8.24, printed p.959 (PDF p.976).
-/

@[expose] public section

open Subgroup
open BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.CentralAction
private theorem fixed_core_alt :
    fixedSpace (coreRepresentation (Fin 7)) (alternatingGroup (Fin 7)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro v hv
  apply Subtype.ext
  have hconst : ∀ i j : Fin 7, v.val i = v.val j := by
    intro i j
    let := alternatingGroup.isPretransitive_of_three_le_card (Fin 7) (by norm_num)
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) i j
    have hfix := (mem_core_fixedSpace_iff (alternatingGroup (Fin 7)) v).mp hv g g.property
    change g.val i = j at hg
    have hgs : g.val.symm j = i := by
      have := congrArg g.val.symm hg
      simpa using this.symm
    simpa [hgs] using hfix j
  have hvconst : v.val ∈ constants (Fin 7) := by
    rw [mem_constants_iff]
    exact ⟨v.val 0, fun i => hconst i 0⟩
  have hdis : Disjoint (core (Fin 7)) (constants (Fin 7)) :=
    (core_isCompl_constants (Fin 7) (by norm_num)).1
  exact Submodule.disjoint_def.mp hdis v.val v.property hvconst

variable {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
  (ρ : Representation (ZMod 2) H E)

private theorem fixedSpace_quotient_eq_bot (φ : H →* Equiv.Perm (Fin 7))
    (K : Subgroup H) (hK : K.map φ = alternatingGroup (Fin 7))
    (W : Subrepresentation ρ)
    (e : (E ⧸ W.toSubmodule) ≃ₗ[ZMod 2] core (Fin 7))
    (he : ∀ g q, e (W.quotientRepresentation g q) = coreRepresentation _ (φ g) (e q)) :
    fixedSpace W.quotientRepresentation K = ⊥ := by
  apply eq_bot_iff.mpr
  intro q hq
  have hfix : e q ∈ fixedSpace (coreRepresentation (Fin 7)) (alternatingGroup (Fin 7)) := by
    rw [← hK]
    rintro ⟨g, k, hk, rfl⟩
    exact (he k q).symm.trans (congrArg e (hq ⟨k, hk⟩))
  rw [fixed_core_alt] at hfix
  exact e.injective (hfix.trans (map_zero e).symm)

private theorem fixedSpace_eq_submodule (W : Subrepresentation ρ) (K : Subgroup H)
    (hQ : fixedSpace W.quotientRepresentation K = ⊥)
    (hW : ∀ k ∈ K, ∀ w : W.toSubmodule, W.toRepresentation k w = w) :
    fixedSpace ρ K = W.toSubmodule := by
  apply le_antisymm
  · intro v hv
    apply (Submodule.Quotient.mk_eq_zero _).mp
    have hq : W.toSubmodule.mkQ v ∈ fixedSpace W.quotientRepresentation K := by
      intro k
      change W.toSubmodule.mkQ (ρ k v) = W.toSubmodule.mkQ v
      exact congrArg W.toSubmodule.mkQ (hv k)
    rw [hQ] at hq
    exact hq
  · intro w hw k
    exact congrArg Subtype.val (hW k k.property ⟨w, hw⟩)

/-- Coordinate formulation of a natural action on the literal section S/C_S(K).
Equivariance is imposed on every representative, and invariance is part of the premise. -/
def NaturalSection (S : Submodule (ZMod 2) E) (K : Subgroup H)
    {J : Type*} [Group J] (a : J →* H) (n : ℕ) (π : J →* Equiv.Perm (Fin n)) : Prop :=
  ∃ (hs : ∀ j (s : S), ρ (a j) s ∈ S)
    (e : (S ⧸ (fixedSpace ρ K).comap S.subtype) ≃ₗ[ZMod 2] natural (Fin n)),
    ∀ j (s : S), e (Submodule.Quotient.mk ⟨ρ (a j) s, hs j s⟩) =
      naturalRepresentation _ (π j) (e (Submodule.Quotient.mk s))

private theorem naturalSection_of_generated (φ : H →* Equiv.Perm (Fin 7))
    (K : Subgroup H) (hK : K.map φ = alternatingGroup (Fin 7))
    (W : Subrepresentation ρ)
    (e : (E ⧸ W.toSubmodule) ≃ₗ[ZMod 2] core (Fin 7))
    (he : ∀ g q, e (W.quotientRepresentation g q) = coreRepresentation _ (φ g) (e q))
    (hW : ∀ k ∈ K, ∀ w : W.toSubmodule, W.toRepresentation k w = w)
    (S : Submodule (ZMod 2) E) (hS : S = ⊤)
    {J : Type*} [Group J] (a : J →* H) (π : J →* Equiv.Perm (Fin 7))
    (hπ : ∀ j, π j = φ (a j)) : NaturalSection ρ S K a 7 π := by
  have hf := fixedSpace_eq_submodule ρ W K
    (fixedSpace_quotient_eq_bot ρ φ K hK W e he) hW
  let p : S →ₗ[ZMod 2] core (Fin 7) :=
    e.toLinearMap.comp (W.toSubmodule.mkQ.comp S.subtype)
  have hp : Function.Surjective p := by
    intro v
    obtain ⟨q, rfl⟩ := e.surjective v
    obtain ⟨u, rfl⟩ := W.toSubmodule.mkQ_surjective q
    exact ⟨⟨u, hS.ge Submodule.mem_top⟩, rfl⟩
  have hk : (fixedSpace ρ K).comap S.subtype = p.ker := by
    ext s
    change s.val ∈ fixedSpace ρ K ↔ e (W.toSubmodule.mkQ s) = 0
    rw [hf, e.map_eq_zero_iff]
    exact (Submodule.Quotient.mk_eq_zero _).symm
  let f := ((Submodule.quotEquivOfEq _ _ hk).trans
    (p.quotKerEquivOfSurjective hp)).trans (coreEquivNatural (Fin 7) (by decide))
  refine ⟨fun _ _ => hS.ge Submodule.mem_top, f, ?_⟩
  intro j s
  change coreEquivNatural (Fin 7) (by decide)
    (e (W.quotientRepresentation (a j) (W.toSubmodule.mkQ s))) =
    naturalRepresentation _ (π j)
      (coreEquivNatural (Fin 7) (by decide) (e (W.toSubmodule.mkQ s)))
  rw [he, coreEquivNatural_equivariant, hπ]



open scoped IsMulCommutative Pointwise

/-- A genuine perfect central three-fold cover of A₆. -/
def IsTripleCoverSix (X : Type*) [Group X] : Prop :=
  Group.IsPerfect X ∧ ∃ f : X →* alternatingGroup (Fin 6),
    Function.Surjective f ∧ f.ker ≤ center X ∧ Nat.card f.ker = 3

private theorem not_tripleCoverSix {X : Type*} [Group X] [Finite X]
    (e : X ≃* alternatingGroup (Fin 6)) : ¬ IsTripleCoverSix X := by
  rintro ⟨_, f, hf, _, hk⟩
  have hc := f.ker.card_eq_card_quotient_mul_card_subgroup
  have he := Nat.card_congr e.toEquiv
  have hq := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
  have ha : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup]
    norm_num
  rw [he, hq, hk, ha] at hc
  omega

section Source
variable {G : Type*} [Group G] [Finite G]
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The additive image Ũ_K of the literal group commutator U_K=[U_H,K]. -/
def commutatorImage (K : Subgroup G) :
    Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) :=
  AddSubgroup.toZModSubmodule 2
    (((⁅Source.UH H V₃, K⁆).subgroupOf (Source.UH H V₃)).map
      (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)))).toAddSubgroup

omit [Finite G] in
private theorem commutatorImage_eq_top (K : Subgroup G)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆) :
    commutatorImage H V₃ V₁ K = ⊤ := by
  apply top_unique
  intro v _
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) v.toMul
  exact ⟨u, hgen ▸ u.property, hu⟩

/-- The conjugation compatibility on actual representatives of U_H/V₁. -/
def IsSourceAction
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))) : Prop :=
  ∀ (h : H) (u : Source.UH H V₃),
    ρ (QuotientGroup.mk' (pCore 2 H) h)
      (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) =
    Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
      ⟨h.val * u.val * h.val⁻¹,
        le_normalizer_iff.mp (le_normalizer_conjugateSpanBy V₃ H) h.val h.property
          u.val u.property⟩)

variable {H V₃ V₁}
/-- The source actor K→H/O₂(H), with its actual kernel. -/
def starHom (K : Subgroup G) (hKH : K ≤ H) : K →* Source.Hstar H :=
  (QuotientGroup.mk' (pCore 2 H)).comp (Subgroup.inclusion hKH)

omit [Finite G] in
/-- The actor's range is exactly the source star image, so fixed vectors for
this range are the K-fixed vectors in the literal source premise. -/
theorem starHom_range (K : Subgroup G) (hKH : K ≤ H) :
    (starHom K hKH).range = Source.starImage H K := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨k.val, hKH k.property⟩, k.property, rfl⟩
  · rintro ⟨h, hh, rfl⟩
    exact ⟨⟨h.val, hh⟩, rfl⟩

/-- The permutation action pulled back through an actual two-core quotient equivalence. -/
def alternatingHom (K : Subgroup G) {n : ℕ}
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n)) : K →* Equiv.Perm (Fin n) :=
  (alternatingGroup (Fin n)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))

/-- The group conclusions of universal 13.7.6(3), before selecting a degree.
This deliberately retains both alternatives and the perfect central triple cover.
The coordinate and chief-factor conclusions of that theorem are not needed here. -/
def AlternatingConclusions (L L₁ T H V₃ J : Subgroup G) (n : ℕ) : Prop :=
  Source.UH H V₃ = ⁅Source.UH H V₃, J⁆ ∧ L₁ ≤ J ∧
    (H : Set G) = (J : Set G) * (T : Set G) ∧
    ((n = 6 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))) ∨
      (n = 7 ∧ IsTripleCoverSix (L ⧸ pCore 2 L)))

/-- The precise group-conclusion implication needed from 13.7.6(3).
It is universal over components and degrees. The natural-module premise uses
U_K=[U_H,K] and the quotient by its K-fixed vectors, independently of W.
This is an explicit earlier-theorem input, not a proved source theorem. -/
def AlternatingNaturalImplication (L L₁ T G₁ M : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))) : Prop :=
  H ∈ Source.Hz L₁ T G₁ M → V₁ ≤ Source.UH H V₃ →
    IsSourceAction H V₃ V₁ ρ →
    ∀ (J : Subgroup G) (hJH : J ≤ H), (J.subgroupOf H).IsCComponent →
      ∀ (n : ℕ) (e : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin n)),
        NaturalSection ρ (commutatorImage H V₃ V₁ J) (Source.starImage H J)
          (starHom J hJH) n (alternatingHom J e) →
        AlternatingConclusions L L₁ T H V₃ J n

/-- Nontrivial component action on W in the three-pairs branch, using the
universal earlier implication and the two independently constructed witnesses. -/
theorem nontrivial_on_submodule
    (L L₁ T G₁ M K : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hV₁ : V₁ ≤ Source.UH H V₃)
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (hφK : (Source.starImage H K).map φ = alternatingGroup (Fin 7))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (W : Subrepresentation ρ)
    (e : ((Additive (Source.Utilde H V₃ V₁)) ⧸ W.toSubmodule) ≃ₗ[ZMod 2] core (Fin 7))
    (he : ∀ g q, e (W.quotientRepresentation g q) = coreRepresentation _ (φ g) (e q))
    (h1376 : AlternatingNaturalImplication L L₁ T G₁ M ρ) :
    ∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w := by
  by_contra! hW
  let eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7) :=
    ((Components.componentStarEquiv H K hKH hK).trans
      ((Source.starImage H K).equivMapOfInjective φ hφ)).trans
        (MulEquiv.subgroupCongr hφK)
  have heK (k : K) : alternatingHom K eK k = φ (starHom K hKH k) := by
    change φ ((Components.componentStarEquiv H K hKH hK
      (QuotientGroup.mk' (pCore 2 K) k)) : Source.Hstar H) = _
    rw [Components.componentStarEquiv_mk]
    rfl
  have hnat := naturalSection_of_generated ρ φ (Source.starImage H K) hφK W e he hW
    (commutatorImage H V₃ V₁ K) (commutatorImage_eq_top H V₃ V₁ K hgen)
    (starHom K hKH) (alternatingHom K eK) heK
  obtain ⟨_, _, _, h6 | h7⟩ := h1376 hH hV₁ hρ K hKH hK 7 eK hnat
  · omega
  · exact not_tripleCoverSix eL h7.2
end Source
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch.CentralAction
