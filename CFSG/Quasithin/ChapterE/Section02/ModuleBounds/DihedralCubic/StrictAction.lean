module

public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.Strict

/-!
# Strict dihedral bounds in the original quotient action

The strict source actor estimate applies both to Aut_X(V) and to the
original relative-normalizer quotient of an ambient group. The Sylow
inclusion supplies the actor map; the two-conjugate group itself need
not normalize V. No TI or module-classification input is required in
this dihedral family.

Source: Aschbacher–Smith E.2.13 and the dihedral branch of E.2.15,
combined manuscript (1 March 2004), printed pp.224–228.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.DihedralCubic
open TwoConjugate
variable {X : Type*} [Group X] [Finite X]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

/-- E.2.13(2–3), the elementary upper bound in the dihedral case.
The exported actor is nontrivial, is cubic, and has kernel exactly C_A(V)=Z. -/
theorem local_cubic_actor_strict (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2) :
    letI := h.elementary
    let ρ := canonicalAction (normalizer (V : Set X)) V le_rfl
    let f := localActor h
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range < 2 * rank f.range ∧
      actionRatio ρ f.range < 2 ∧ cubicRatio ρ < 2 := by
  let := h.elementary
  let := centralizer_normal (normalizer (V : Set X)) V le_rfl
  apply h.dihedral_cubic_actor_strict hproper hfit hcard (MulEquiv.refl V) _
    (representation_injective _ V le_rfl _ (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)) (localActor h)
  intro a v
  exact representation_apply _ V le_rfl _ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) _ _
end CFSG.Quasithin.ChapterE.DihedralCubic

namespace CFSG.Quasithin.ChapterE.DihedralCubic
open TwoConjugate
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
variable {I U V : Subgroup G} {S : Sylow 2 I} {N : Subgroup I} {g : I}

/-- The E.2.13 dihedral bound in the original ambient quotient action.
Only the Sylow subgroup of I is placed in U; I need not normalize V. -/
theorem ambient_cubic_actor_strict [IsElementaryAbelian 2 V]
    (hVI : V ≤ I) (hn : U ≤ normalizer (V : Set G))
    (h : Hypotheses S (V.subgroupOf I) N g)
    (hSU : (S : Subgroup I).map I.subtype ≤ U)
    (hproper : V.subgroupOf I ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting I = pCore 2 I)
    (hcard : Nat.card ((V.subgroupOf I).map (QuotientGroup.mk' (J N))) = 2)
    (q : U →* D) (hq : Function.Surjective q)
    (hk : q.ker = (centralizer (V : Set G)).subgroupOf U) :
    let ρ := representation U V hn q hq hk
    let f := actorMap h hSU q
    f.ker = (Z (V.subgroupOf I) g).subgroupOf (A (V.subgroupOf I) N g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range < 2 * rank f.range ∧
      actionRatio ρ f.range < 2 ∧ cubicRatio ρ < 2 := by
  let e := subgroupOfEquivOfLe hVI
  let ρ := representation U V hn q hq hk
  let f := actorMap h hSU q
  apply h.dihedral_cubic_actor_strict hproper hfit hcard e ρ
    (representation_injective U V hn q hq hk) f
  intro a v
  apply Subtype.ext
  change ((ρ (q (actorIn h hSU a)) (Additive.ofMul (e v))).toMul : G) =
    ((a : I) : G) * ((v : I) : G) * ((a : I) : G)⁻¹
  rw [representation_apply]
  rfl

end CFSG.Quasithin.ChapterE.DihedralCubic
