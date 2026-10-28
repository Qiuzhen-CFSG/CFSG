module

public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.Bound
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.Action

/-!
# The dihedral cubic actor and its original ambient action

The nontrivial elementary actor is the actual image of A=B^g, with kernel
C_A(V)=Z, and its fixed-space quotient has dimension at most twice its rank.
`local_cubic_actor` gives the canonical Aut_X(V) action. For an actual
subgroup I of a larger group, `ambient_cubic_actor` embeds A through
A≤O₂(I)≤S and the supplied S≤U, then uses the original quotient map of U.
Neither I nor its overgroup H is assumed to normalize V.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), E.2.10–13, printed pp.222–225; the application to
15.4.2(4), printed p.1156, is in `Centralizer.Preliminaries.TwoConjugateRatio`.
The E.2.9/E.2.11 witness and order-two image supplied by B.6.8(5) remain
explicit inputs; no nonsolvable covering or general degree theorem is used.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.DihedralCubic
open Subgroup TwoConjugate Representation.BinaryOffender
open scoped IsMulCommutative
variable {X : Type*} [Group X] [Finite X]
variable {T : Sylow 2 X} {V M : Subgroup X} {g : X}

/-- The actual centralizer quotient of a relative normalizer. -/
abbrev ActionQuotient (U V : Subgroup X) (hn : U ≤ normalizer (V : Set X)) :=
  letI := centralizer_normal U V hn
  U ⧸ (centralizer (V : Set X)).subgroupOf U

instance actionQuotientGroup (U V : Subgroup X) (hn : U ≤ normalizer (V : Set X)) :
    Group (ActionQuotient U V hn) :=
  letI := centralizer_normal U V hn
  inferInstanceAs (Group (U ⧸ (centralizer (V : Set X)).subgroupOf U))

/-- The literal quotient map, with its original relative centralizer denominator. -/
def projection (U V : Subgroup X) (hn : U ≤ normalizer (V : Set X)) :
    U →* ActionQuotient U V hn :=
  letI := centralizer_normal U V hn
  QuotientGroup.mk' _

/-- Canonical faithful conjugation on the original V. -/
noncomputable def canonicalAction (U V : Subgroup X) [IsElementaryAbelian 2 V]
    (hn : U ≤ normalizer (V : Set X)) :
    Representation (ZMod 2) (ActionQuotient U V hn) (Additive V) :=
  letI := centralizer_normal U V hn
  representation U V hn (projection U V hn) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)

/-- The actor in Aut_X(V) is the image of A under its actual inclusion
in N_X(V), followed by the quotient by C_(N_X(V))(V). -/
def localActor (h : Hypotheses T V M g) :
    A V M g →* ActionQuotient (normalizer (V : Set X)) V le_rfl :=
  (projection _ V le_rfl).comp (inclusion
    ((show A V M g ≤ pCore 2 X by rw [h.A_eq_twoCore_inf]; exact inf_le_left).trans
      h.twoCore_normalizes_V))

/-- E.2.13(2–3), the elementary upper bound in the dihedral case.
The exported actor is nontrivial, is cubic, and has kernel exactly C_A(V)=Z. -/
theorem local_cubic_actor (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : Theory.GroupTheory.generalizedFitting X = pCore 2 X)
    (hcard : Nat.card (V.map (QuotientGroup.mk' (J M))) = 2) :
    letI := h.elementary
    let ρ := canonicalAction (normalizer (V : Set X)) V le_rfl
    let f := localActor h
    f.ker = (Z V g).subgroupOf (A V M g) ∧
      IsElementaryTwo f.range ∧ IsCubic ρ f.range ∧
      fixedCodim ρ f.range ≤ 2 * rank f.range ∧ cubicRatio ρ ≤ 2 := by
  let := h.elementary
  let := centralizer_normal (normalizer (V : Set X)) V le_rfl
  apply h.dihedral_cubic_actor hproper hfit hcard (MulEquiv.refl V) _
    (representation_injective _ V le_rfl _ (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _)) (localActor h)
  intro a v
  exact representation_apply _ V le_rfl _ (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) _ _
end CFSG.Quasithin.ChapterE.DihedralCubic

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.DihedralCubic
open TwoConjugate
variable {G D : Type*} [Group G] [Finite G] [Group D] [Finite D]
variable {I U V : Subgroup G} {S : Sylow 2 I} {N : Subgroup I} {g : I}

/-- The source actor is in the actual Sylow subgroup of the two-conjugate group. -/
lemma A_le_sylow (h : Hypotheses S (V.subgroupOf I) N g) :
    A (V.subgroupOf I) N g ≤ (S : Subgroup I) := by
  rw [h.A_eq_twoCore_inf]
  exact inf_le_left.trans (pCore_isPGroup.le_sylow_of_normal S)

/-- Inclusion of the actual A in U, via A ≤ O₂(I) ≤ S and S ≤ U. -/
def actorIn (h : Hypotheses S (V.subgroupOf I) N g)
    (hSU : (S : Subgroup I).map I.subtype ≤ U) : A (V.subgroupOf I) N g →* U :=
  (I.subtype.comp (A (V.subgroupOf I) N g).subtype).codRestrict U
    (fun a => hSU (mem_map_of_mem I.subtype (A_le_sylow h a.property)))

/-- The actor map is the restriction of the original quotient map. -/
def actorMap (h : Hypotheses S (V.subgroupOf I) N g)
    (hSU : (S : Subgroup I).map I.subtype ≤ U) (q : U →* D) :
    A (V.subgroupOf I) N g →* D := q.comp (actorIn h hSU)

/-- The E.2.13 dihedral bound in the original ambient quotient action.
Only the Sylow subgroup of I is placed in U; I need not normalize V. -/
theorem ambient_cubic_actor [IsElementaryAbelian 2 V]
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
      fixedCodim ρ f.range ≤ 2 * rank f.range ∧ cubicRatio ρ ≤ 2 := by
  let e := subgroupOfEquivOfLe hVI
  let ρ := representation U V hn q hq hk
  let f := actorMap h hSU q
  apply h.dihedral_cubic_actor hproper hfit hcard e ρ
    (representation_injective U V hn q hq hk) f
  intro a v
  apply Subtype.ext
  change ((ρ (q (actorIn h hSU a)) (Additive.ofMul (e v))).toMul : G) =
    ((a : I) : G) * ((v : I) : G) * ((a : I) : G)⁻¹
  rw [representation_apply]
  rfl

end CFSG.Quasithin.ChapterE.DihedralCubic
