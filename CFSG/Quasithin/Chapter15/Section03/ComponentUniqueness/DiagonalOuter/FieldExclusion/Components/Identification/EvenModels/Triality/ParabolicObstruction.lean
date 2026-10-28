module

public import Theory.SpecificGroups.PSL3Two.EmbeddingObstructions
public import Theory.SpecificGroups.Triality.ParabolicLocalStructure
public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient
public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.Residual
public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.GroupAction.InnerInvolutionGeometry
public import BenderSuzuki.External.Huppert.II.theorem_8_27
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# The inner triality branch of the PSL₃(2) component sieve

The genuine local-factor quotients are PSL₂(q³) and PSL₂(q). A faithful
PSL₃(2) subgroup survives their solvable two-cores, contradicting the
noncommuting involutions in its dihedral Sylow two-group. Perfectness removes
the cyclic quotient of the full parabolic above its local factor.

The proved normalizer cover places every involution centralizer in a
conjugate of one of these full parabolics. This closes the inner-automorphism
branch, including q = 2, without using a classification of root involutions.
All radicals, quotients and conjugations are those of the pinned D₄
graph-field carrier; normality of the radical is relative to its local factor.

Sources: Aschbacher--Smith, proof of 15.3.38, printed p.1137, and
F.1.12(I)(4), pp.263--264, `refs/quasithin.pdf`; GLS3 2.6.5 and 3.1.3,
`refs/KGroup/GLS3/chapter2.tex` and `chapter3.tex`.
-/

public section

open Subgroup
open Triality.Standard Triality.Standard.Parabolics
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification.EvenModels.TrialityCase

private theorem not_injective_psl2 {F : Type*} [Field F] [Finite F]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (f : Matrix.PSL3Two.PSL →* PSL(2, F)) :
    ¬ Function.Injective f := by
  let P : Sylow 2 PSL(2, F) := default
  obtain ⟨e⟩ := BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive hF P
  apply Matrix.PSL3Two.not_injective_of_sylow_involutions_commute P
    (fun a b _ _ => ?_) f
  exact e.symm.injective (by simp only [map_mul]; exact mul_comm _ _)

private theorem injective_mod_twoCore {G : Type*} [Group G] [Finite G]
    (f : Matrix.PSL3Two.PSL →* G) (hf : Function.Injective f) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 G)).comp f) := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect 3 (by decide)
  let q := (QuotientGroup.mk' (pCore 2 G)).comp f
  apply (MonoidHom.ker_eq_bot_iff q).mp
  rcases (inferInstance : q.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have hmem (x : Matrix.PSL3Two.PSL) : f x ∈ pCore 2 G := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact show x ∈ q.ker from h ▸ mem_top x
    let k := f.codRestrict (pCore 2 G) hmem
    have hk : Function.Injective k := fun x y h => hf (congrArg Subtype.val h)
    let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
    exact Group.IsPerfect.not_isSolvable Matrix.PSL3Two.PSL
      (Group.isSolvable_of_isSolvable_injective hk)

/-- The two-core projection stays faithful on the simple PSL₃(2), but the
actual rank-one Levi has abelian Sylow two-subgroups. -/
theorem not_injective_localFactor (P : Parameters) (hp : P.prime = 2) (a : Node)
    (f : Matrix.PSL3Two.PSL →* localFactor P a) : ¬ Function.Injective f := by
  intro hf
  let q := (QuotientGroup.mk' (pCore 2 (localFactor P a))).comp f
  have hq : Function.Injective q := injective_mod_twoCore f hf
  cases a with
  | arms =>
    let e := localFactorArmsQuotientEquivPSL2 P hp
    exact not_injective_psl2 (by rw [card_extensionField, Parameters.q, hp, ← pow_mul])
      (e.toMonoidHom.comp q) (e.injective.comp hq)
  | central =>
    let e := localFactorCentralQuotientEquivPSL2 P hp
    have hF : Nat.card (GaloisField P.prime P.exponent) = 2 ^ P.exponent := by
      rw [GaloisField.card P.prime P.exponent P.exponent_pos.ne', hp]
    exact not_injective_psl2 hF (e.toMonoidHom.comp q) (e.injective.comp hq)

/-- Perfectness removes the full parabolic's cyclic torus quotient, reducing
to its genuine local factor and rank-one Levi. -/
theorem not_injective_parabolic (P : Parameters) (hp : P.prime = 2) (a : Node)
    (f : Matrix.PSL3Two.PSL →* parabolic P a) : ¬ Function.Injective f := by
  intro hf
  let : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect 3 (by decide)
  let N := (localFactor P a).subgroupOf (parabolic P a)
  let : IsCyclic (parabolic P a ⧸ N) := parabolic_quotient_isCyclic P hp a
  have hcomm : commutator (parabolic P a) ≤ N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp inferInstance
  have hle : f.range ≤ N := by
    calc
      f.range = (commutator Matrix.PSL3Two.PSL).map f := by
        rw [Group.IsPerfect.commutator_eq_top, MonoidHom.range_eq_map]
      _ ≤ commutator (parabolic P a) := by
        rw [map_commutator_eq]
        exact commutator_mono le_top le_top
      _ ≤ N := hcomm
  let e : N ≃* localFactor P a := subgroupOfEquivOfLe (localFactor_le_parabolic P a)
  let k := e.toMonoidHom.comp (f.codRestrict N (fun x => hle ⟨x, rfl⟩))
  exact not_injective_localFactor P hp a k
    (e.injective.comp (fun x y h => hf (congrArg Subtype.val h)))

/-- The obstruction is preserved by conjugating a genuine root parabolic. -/
theorem not_injective_root_parabolic (n : ℕ) (hn : 0 < n)
    (Q : Subgroup (BinaryCarrier n hn))
    (hQ : EvenInvolutionGeometry.IsRootParabolic n hn Q)
    (f : Matrix.PSL3Two.PSL →* Q) : ¬ Function.Injective f := by
  obtain ⟨a, g, hQg⟩ := hQ
  let e : parabolic (binaryParameters n hn) a ≃* Q :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr hQg.symm)
  exact fun hf => not_injective_parabolic _ rfl a (e.symm.toMonoidHom.comp f)
    (e.symm.injective.comp hf)

/-- Every subgroup of a fixed group contained in a root parabolic is
excluded; no promotion of relative component membership is needed. -/
theorem not_fixed_component_of_parabolic (n : ℕ) (hn : 0 < n)
    (a : MulAut (BinaryCarrier n hn)) (Q : Subgroup (BinaryCarrier n hn))
    (hQ : EvenInvolutionGeometry.IsRootParabolic n hn Q)
    (hC : a.fixedSubgroup ≤ Q) (C : Subgroup a.fixedSubgroup) :
    ¬ Nonempty (C ≃* Matrix.PSL3Two.PSL) := by
  rintro ⟨e⟩
  let f := (inclusion hC).comp (C.subtype.comp e.symm.toMonoidHom)
  exact not_injective_root_parabolic n hn Q hQ f
    ((inclusion_injective hC).comp (C.subtype_injective.comp e.symm.injective))

/-- The involution centralizer normalizes its nontrivial cyclic two-group.
The proved normalizer cover therefore places it in a full root parabolic. -/
theorem not_injective_involution_centralizer (n : ℕ) (hn : 0 < n)
    (t : BinaryCarrier n hn) (ht : orderOf t = 2)
    (f : Matrix.PSL3Two.PSL →* centralizer ({t} : Set (BinaryCarrier n hn))) :
    ¬ Function.Injective f := by
  intro hf
  have htn : t ≠ 1 := by intro h; simp [h] at ht
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using ht)
  obtain ⟨g, a, hN⟩ := TwoLocalCover.normalizer_cover n hn
    (zpowers t) (zpowers_ne_bot.mpr htn) hp
  have hCN : centralizer ({t} : Set (BinaryCarrier n hn)) ≤
      normalizer (zpowers t : Set (BinaryCarrier n hn)) := by
    have he : centralizer (zpowers t : Set (BinaryCarrier n hn)) =
        centralizer ({t} : Set (BinaryCarrier n hn)) := by
      rw [zpowers_eq_closure, centralizer_closure]
    rw [← he]
    exact Subgroup.centralizer_le_normalizer _
  let j := (MulAut.conj g).toMonoidHom.comp
    ((centralizer ({t} : Set (BinaryCarrier n hn))).subtype.comp f)
  have hj (x : Matrix.PSL3Two.PSL) : j x ∈ parabolic (binaryParameters n hn) a :=
    hN (mem_map_of_mem _ (hCN (f x).property))
  exact not_injective_parabolic _ rfl a (j.codRestrict _ hj)
    (fun x y h => hf (Subtype.ext ((MulAut.conj g).injective (congrArg Subtype.val h))))

/-- An inner involutory automorphism in the supplied simple perfect carrier
has a literal involution representative, whose centralizer excludes PSL₃(2). -/
theorem not_fixed_component_of_inner (n : ℕ) (hn : 0 < n)
    [IsSimpleGroup (BinaryCarrier n hn)] [Group.IsPerfect (BinaryCarrier n hn)]
    (a : MulAut (BinaryCarrier n hn)) (ha : orderOf a = 2)
    (hi : a ∈ MulAut.innerSubgroup (BinaryCarrier n hn))
    (C : Subgroup a.fixedSubgroup) : ¬ Nonempty (C ≃* Matrix.PSL3Two.PSL) := by
  rintro ⟨e⟩
  obtain ⟨t, ht, _, hC⟩ := MulAut.inner_involution_representative
    center_eq_bot_of_simple_perfect a ha (by
      obtain ⟨t, ht⟩ := hi
      exact ⟨t, ht.symm⟩)
  let d : a.fixedSubgroup ≃* centralizer ({t} : Set (BinaryCarrier n hn)) :=
    MulEquiv.subgroupCongr hC
  let f := d.toMonoidHom.comp (C.subtype.comp e.symm.toMonoidHom)
  exact not_injective_involution_centralizer n hn t ht f
    (d.injective.comp (C.subtype_injective.comp e.symm.injective))

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification.EvenModels.TrialityCase
