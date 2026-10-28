module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.Basic
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.QuaternionFixed
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.CoreEquality

/-!
# The special two-core in J.2.3

This boundary proves all nine clauses from the genuine LocalSetup. The
preceding parabolic core equalities supply the Sylow-fixed commutator seed;
the natural parabolic action propagates it to every noncentral element of S.
The Singer restriction then gives the centralizer splitting and nonabelian
Suzuki factor. The cubic fixed-vector interchange gives the actual quaternion
subgroup. The same marked Steinberg action supplies the quotient fixed space
and the intersections of distinct conjugates of U.

`SingerChoice.source_conclusions` applies to every source Singer choice.
`lemma_J_2_3` constructs that choice for any specified B in Syl₃(L₁), and
`SpecialCore.exists_source_choices` also chooses B. Every preceding-source,
full-commutator, nonabelianness and quaternion-recognition premise is discharged.
The result record only organizes the nine proved conclusions; none of them
is assumed in LocalSetup.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma J.2.3, printed pp.433–434 (PDF pp.444–445).
-/

public section
noncomputable section
open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.ChapterJ
variable {G : Type*} [Group G] [Finite G]

namespace SpecialCore

/-- The nine conclusions of J.2.3, for the literal source subgroups.
The direct product retains multiplication and both factor embeddings, and
the quotient kernels are normal only in their specified containing groups. -/
structure Conclusions (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (c : SingerChoice d.toTypeRuSetup B) : Prop where
  one : fixedCore d.toTypeRuSetup c.B7 =
      ⁅fixedCore d.toTypeRuSetup c.B7, cubicSubgroup d.toTypeRuSetup B⁆ ∧
    Nonempty (fixedCore d.toTypeRuSetup c.B7 ≃* Multiplicative (ZMod 2 × ZMod 2))
  two : ∀ z ∈ d.toTypeRuSetup.Z, z ≠ 1 →
    {s : G | IsConj z s} ∩ (fixedCore d.toTypeRuSetup c.B7 : Set G) = ∅
  three : ∀ s : G, s ∈ fixedCore d.toTypeRuSetup c.B7 → s ≠ 1 →
    (↑(d.L ⊓ centralizer ({s} : Set G)) : Set G) =
        (fixedCore d.toTypeRuSetup c.B7 : Set G) *
          (movingCore d.toTypeRuSetup c.B7 s : Set G) * (c.B7 : Set G) ∧
    (∃ e : fixedCore d.toTypeRuSetup c.B7 × movingCore d.toTypeRuSetup c.B7 s ≃*
        (d.toTypeRuSetup.S ⊓ centralizer ({s} : Set G) : Subgroup G),
      ∀ a m, (e (a,m) : G) = (a : G) * (m : G)) ∧
    (∃ P : Sylow 2 (d.L ⊓ centralizer ({s} : Set G) : Subgroup G),
      (P : Subgroup (d.L ⊓ centralizer ({s} : Set G) : Subgroup G)).map
        (d.L ⊓ centralizer ({s} : Set G) : Subgroup G).subtype =
          d.toTypeRuSetup.S ⊓ centralizer ({s} : Set G)) ∧
    Nat.card (d.toTypeRuSetup.S ⊓ centralizer ({s} : Set G) : Subgroup G) = 256 ∧
    Monoid.exponent (d.toTypeRuSetup.S ⊓ centralizer ({s} : Set G) : Subgroup G) = 4
  four : ∀ s : G, s ∈ fixedCore d.toTypeRuSetup c.B7 → s ≠ 1 →
    cubicSubgroup d.toTypeRuSetup B ≤
        normalizer (d.toTypeRuSetup.S ⊓ centralizer ({s} : Set G) : Subgroup G) ∧
    cubicSubgroup d.toTypeRuSetup B ≤ normalizer (fixedCore d.toTypeRuSetup c.B7) ∧
    cubicSubgroup d.toTypeRuSetup B ≤ normalizer (movingCore d.toTypeRuSetup c.B7 s)
  five : ∀ s : G, s ∈ fixedCore d.toTypeRuSetup c.B7 → s ≠ 1 →
    IsPGroup 2 (movingCore d.toTypeRuSetup c.B7 s) ∧
    ¬ IsMulCommutative (movingCore d.toTypeRuSetup c.B7 s) ∧
    _root_.commutator (movingCore d.toTypeRuSetup c.B7 s) =
      center (movingCore d.toTypeRuSetup c.B7 s) ∧
    ∃ A : Subgroup (MulAut (movingCore d.toTypeRuSetup c.B7 s)), IsCyclic A ∧
      ∀ x y : movingCore d.toTypeRuSetup c.B7 s, orderOf x = 2 → orderOf y = 2 →
        ∃ a ∈ A, a x = y
  six : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
    let := d.ru1.coreCentralizer_kernel_normal t
    ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V ∧
    Nonempty (((d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ⧸
      d.V.subgroupOf (d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G))) ≃*
        Multiplicative (Fin 5 → ZMod 2)) ∧
    primeRank 2 ((d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) ⧸
      d.V.subgroupOf (d.toTypeRuSetup.S ⊓ centralizer ({(t : G)} : Set G))) = 5
  seven : Nonempty ((d.toTypeRuSetup.Q ⊓
    centralizer (cubicSubgroup d.toTypeRuSetup B : Set G) : Subgroup G) ≃*
      QuaternionGroup 2)
  eight : let := d.ru1.steinberg.kernel_normal
    CommutatorGeometry.quotientFixed d =
      (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.S).map
        (QuotientGroup.mk' (d.V.subgroupOf d.toTypeRuSetup.S))
  nine : ∀ l ∈ d.L, l ∉ d.toTypeRuSetup.H →
    d.toTypeRuSetup.U ⊓ d.toTypeRuSetup.U.map (MulAut.conj l).toMonoidHom = d.V

/-- All nine clauses for any source Singer choice, with the preceding
J.2.1–2 facts and every intermediate premise supplied by their proofs. -/
theorem SingerChoice.source_conclusions (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁) (c : SingerChoice d.toTypeRuSetup B) :
    Conclusions d B c := by
  let r := d.toTypeRuSetup
  have hprod : r.R₁ = r.Q ⊔ r.S :=
    d.parabolic_core_eq_R₁.symm.trans d.Q_sup_S_eq_parabolic_core.symm
  have hfull := CommutatorGeometry.full_commutator d hprod d.parabolic_core_eq_R₁
  have hB := cubicSubgroup_card r B d.card_Z (d.center_eq.le.trans inf_le_left)
  obtain ⟨h6, h8, _, h9⟩ :=
    CommutatorGeometry.source_six_eight_nine d hprod d.parabolic_core_eq_R₁
  refine {
    one := ⟨(c.fixedCore_commutator_cubic r B hB).symm, ⟨c.fixedCoreEquivFour r B⟩⟩
    two := ?_
    three := ?_
    four := c.centralizer_normalization r B hB hfull
    five := c.movingCore_suzuki r B hB hfull
    six := h6
    seven := c.cubicFixedQ_equiv_quaternion d B d.Q_le_K hfull
    eight := h8
    nine := h9 }
  · intro z hz hz1
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro s ⟨hconj, hs⟩
    exact not_isConj_of_mem_fixedCore r d.card_Z c.B7 c.card_seven z hz hz1 s hs hconj
  · intro s hs hs1
    exact ⟨c.fullCentralizer_product r B hB hfull s hs hs1,
      c.coreCentralizer_internalProduct r B hB hfull s hs hs1,
      c.coreCentralizer_sylow r B s hs hs1,
      c.coreCentralizer_order_exponent_from_restriction r B hfull s hs hs1⟩

end SpecialCore

/-- J.2.3 from the source LocalSetup, constructing the B-invariant subgroup
of order seven and proving all nine clauses. B is the specified Sylow
three-subgroup of the actual two-residual O²(C_L(Z)). -/
theorem lemma_J_2_3 (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁) :
    ∃ c : SpecialCore.SingerChoice d.toTypeRuSetup B, SpecialCore.Conclusions d B c := by
  obtain ⟨c⟩ := SpecialCore.nonempty_singerChoice d.toTypeRuSetup B
  exact ⟨c, c.source_conclusions d B⟩

/-- Choose both source subgroups B and B₇ and obtain the entire lemma.
No existence or earlier-source hypothesis is left for the consumer. -/
theorem SpecialCore.exists_source_choices (d : LocalSetup G) :
    ∃ (B : Sylow 3 d.toTypeRuSetup.L₁) (c : SingerChoice d.toTypeRuSetup B),
      Conclusions d B c := by
  let B : Sylow 3 d.toTypeRuSetup.L₁ := Classical.choice inferInstance
  exact ⟨B, lemma_J_2_3 d B⟩

end CFSG.Quasithin.ChapterJ
