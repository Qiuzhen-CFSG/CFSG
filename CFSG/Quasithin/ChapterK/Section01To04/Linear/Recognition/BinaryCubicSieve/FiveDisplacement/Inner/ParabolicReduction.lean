module

public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.NormalInvariants
public import Theory.Representation.GeneratedSubgroupInvariants

/-!
# The fixed-space reduction for the end-node parabolics

For a normal subgroup N and an elementary actor A, the dimension formula for
C_V(N) and C_V(A) bounds the quotient actor's fixed codimension by
codim C_V(A) minus codim C_V(A ∩ N). Rank-nullity on A → G/N then gives the
radical-or-quotient offender alternative. Cubicity is retained on both branches.
The quotient representation is literally `quotientToInvariants`, so normality
is required only inside the overgroup to which the argument is applied.

These preliminary lemmas are used by the actual SL₅ parabolic consumer in
`Inner.lean`. They do not assert irreducibility of the parabolic fixed space,
identify its highest support, or exclude radical offenders.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, author manuscript,
Proposition 2.4, p.6, used in Proposition 4.7, pp.25–26; Aschbacher–Smith K.3.2,
printed pp.454–455.
-/

public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (N : Subgroup G) [N.Normal]

omit [Finite G] in
/-- The quotient actor costs at most the original codimension minus the cost
of its intersection with the normal subgroup. This is a common-fixed-space
inequality, without any splitting of the representation. -/
theorem quotient_fixedCodim_add_intersection_le (A : Subgroup G) :
    fixedCodim (ρ.quotientToInvariants N) (A.map (QuotientGroup.mk' N)) +
      fixedCodim ρ (A ⊓ N) ≤ fixedCodim ρ A := by
  let W := ρ.fixedSubrepresentationOfNormal N
  have he : fixedCodim (ρ.quotientToInvariants N) (A.map (QuotientGroup.mk' N)) =
      fixedCodim W.toRepresentation A := by
    unfold fixedCodim
    rw [← fixedSpace_comp_map]
    rfl
  rw [he]
  have hf := (subrepresentationFixedEquiv ρ W A).finrank_eq
  have hw := fixedCodim_add_finrank W.toRepresentation A
  have ha := fixedCodim_add_finrank ρ A
  have hn := fixedCodim_add_finrank ρ (A ⊓ N)
  have hs := (fixedSpace ρ N).finrank_sup_add_finrank_inf_eq (fixedSpace ρ A)
  have hle : fixedSpace ρ N ⊔ fixedSpace ρ A ≤ fixedSpace ρ (A ⊓ N) :=
    sup_le (ρ.invariants_comp_subtype_antitone inf_le_right)
      (ρ.invariants_comp_subtype_antitone inf_le_left)
  have hd := Submodule.finrank_mono hle
  change Module.finrank (ZMod 2) (fixedSpace W.toRepresentation A) =
    Module.finrank (ZMod 2) (fixedSpace ρ N ⊓ fixedSpace ρ A : Submodule (ZMod 2) V) at hf
  change fixedCodim W.toRepresentation A + _ = Module.finrank (ZMod 2) (fixedSpace ρ N) at hw
  omega

/-- Rank-nullity for the literal elementary actor and normal quotient map. -/
theorem rank_intersection_add_quotient_image {A : Subgroup G} (hA : IsElementaryTwo A) :
    rank (A ⊓ N) + rank (A.map (QuotientGroup.mk' N)) = rank A := by
  let : IsElementaryAbelian 2 A := hA.2
  have hp := IsElementaryAbelian.isPGroup 2 A
  have hi : IsPGroup 2 (A ⊓ N : Subgroup G) :=
    hp.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  let : IsElementaryAbelian 2 (A.map (QuotientGroup.mk' N)) :=
    IsElementaryAbelian.map (QuotientGroup.mk' N)
  have hm : IsPGroup 2 (A.map (QuotientGroup.mk' N)) := by
    exact IsElementaryAbelian.isPGroup 2 _
  obtain ⟨i, hi⟩ := hi.exists_card_eq
  obtain ⟨m, hm⟩ := hm.exists_card_eq
  have hc := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ N) A bot_le inf_le_left
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left,
    Subgroup.inf_relIndex_left, ← QuotientGroup.ker_mk' N,
    Subgroup.relIndex_ker, QuotientGroup.ker_mk', hi, hm, ← pow_add] at hc
  simp only [rank, hi, hm, ← hc, Nat.log_pow (by decide : 1 < 2)]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Cubicity descends to the actual quotient action on normal fixed vectors. -/
theorem cubic_quotient_invariants {A : Subgroup G} (hc : IsCubic ρ A) :
    IsCubic (ρ.quotientToInvariants N) (A.map (QuotientGroup.mk' N)) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hcc, rfl⟩ v
  apply Subtype.ext
  exact hc a ha b hb c hcc v

/-- An elementary cubic actor of ratio at most two either has such a
subactor in the normal subgroup, or its actual quotient image is such an actor
on the normal fixed space. No irreducibility or field extension is required. -/
theorem normal_offender_alternative {A : Subgroup G} (hA : IsElementaryTwo A)
    (hc : IsCubic ρ A) (hsmall : fixedCodim ρ A ≤ 2 * rank A) :
    (∃ C : Subgroup G, C ≤ A ∧ C ≤ N ∧ IsElementaryTwo C ∧ IsCubic ρ C ∧
      fixedCodim ρ C ≤ 2 * rank C) ∨
    (IsElementaryTwo (A.map (QuotientGroup.mk' N)) ∧
      IsCubic (ρ.quotientToInvariants N) (A.map (QuotientGroup.mk' N)) ∧
      fixedCodim (ρ.quotientToInvariants N) (A.map (QuotientGroup.mk' N)) ≤
        2 * rank (A.map (QuotientGroup.mk' N))) := by
  by_cases hi : A ⊓ N ≠ ⊥ ∧ fixedCodim ρ (A ⊓ N) ≤ 2 * rank (A ⊓ N)
  · exact Or.inl ⟨A ⊓ N, inf_le_left, inf_le_right,
      hA.of_le inf_le_left hi.1,
      fun a ha b hb c hcc v => hc a ha.1 b hb.1 c hcc.1 v, hi.2⟩
  · have hd : 2 * rank (A ⊓ N) ≤ fixedCodim ρ (A ⊓ N) := by
      by_cases hb : A ⊓ N = ⊥
      · simp only [hb, BinaryOffender.rank_bot, mul_zero, Nat.zero_le]
      · exact (lt_of_not_ge (fun hs => hi ⟨hb, hs⟩)).le
    let : IsElementaryAbelian 2 A := hA.2
    have hm : IsElementaryTwo (A.map (QuotientGroup.mk' N)) := by
      refine ⟨?_, IsElementaryAbelian.map (QuotientGroup.mk' N)⟩
      intro hb
      have hAN : A ≤ N := by
        intro a ha
        have hmem := Subgroup.mem_map_of_mem (QuotientGroup.mk' N) ha
        rw [hb] at hmem
        exact (QuotientGroup.eq_one_iff a).mp (Subgroup.mem_bot.mp hmem)
      have he : A ⊓ N = A := inf_eq_left.mpr hAN
      exact hi ⟨he.symm ▸ hA.1, he.symm ▸ hsmall⟩
    refine Or.inr ⟨hm, cubic_quotient_invariants ρ N hc, ?_⟩
    have hbound := quotient_fixedCodim_add_intersection_le ρ N A
    have hrank := rank_intersection_add_quotient_image N hA
    omega
end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner

