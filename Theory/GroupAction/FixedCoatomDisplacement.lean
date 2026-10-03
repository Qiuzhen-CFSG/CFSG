module
public import Theory.GroupAction.FourElementInvolutionLines
public import Theory.GroupAction.FixedHyperplaneQuadratic
public import Theory.GroupAction.SubgroupQuotientCommutatorImage

/-!
# Cyclic displacement over a fixed coatom

For an automorphism of a finite elementary abelian two-group, fixed index
dividing two implies that its full cyclic commutator subgroup has order at
most two. The automorphism is not assumed to be an involution.

Index one makes the action trivial. At index two, every displacement lies
in the fixed subgroup, so expanding this fixed-displacement identity in
characteristic two shows that the automorphism squares to one. The
involution rank-nullity identity then gives commutator order two.

This elementary action count supplies the small-cost competitor in
Stellmacher (8.6)(13), printed p.43 of
`refs/files/stellmacher-n-group.pdf`. It uses no graph or classification
hypotheses and preserves the literal supplied automorphism.

The quotient-conjugation companion lifts a fixed coatom from an ambient
subgroup and translates the displacement cardinality into the exact relative
index used by the minimizing-actor cost. It reuses the supplied quotient
normality and action rather than replacing the module by an isomorphic copy.
-/

namespace MulAut
open scoped IsMulCommutative

/-- Fixing a subgroup of index at most two pointwise makes an automorphism
of an elementary binary group square to the identity. -/
public theorem square_eq_one_of_fixed_index_dvd_two
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (actor : MulAut V)
    (hindex : (FixedPoints.subgroup (Subgroup.zpowers actor) V).index ∣ 2) :
    actor ^ 2 = 1 := by
  rcases (Nat.dvd_prime Nat.prime_two).mp hindex with hone | htwo
  · have htop := Subgroup.index_eq_one.mp hone
    have heq : actor = 1 := by
      ext point
      exact (htop ▸ Subgroup.mem_top point :
        point ∈ FixedPoints.subgroup (Subgroup.zpowers actor) V)
        ⟨actor, Subgroup.mem_zpowers actor⟩
    simp only [heq, one_pow]
  · ext point
    have hmem : point⁻¹ * actor point ∈ commutatorAction (Subgroup.zpowers actor) V :=
      Subgroup.subset_closure ⟨⟨actor, Subgroup.mem_zpowers actor⟩, point,
        Subgroup.mem_top point, rfl⟩
    have hfixed := commutatorAction_le_fixedPoints_of_index_two htwo hmem
      ⟨actor, Subgroup.mem_zpowers actor⟩
    have hinv (x : V) : x⁻¹ = x := by
      apply inv_eq_of_mul_eq_one_left
      simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) x
    change actor (point⁻¹ * actor point) = point⁻¹ * actor point at hfixed
    simp only [map_mul, hinv] at hfixed
    apply mul_left_cancel (a := actor point)
    exact hfixed.trans (mul_comm _ _)

public theorem commutatorAction_card_le_two_of_fixed_index_dvd_two
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (actor : MulAut V)
    (hindex : (FixedPoints.subgroup (Subgroup.zpowers actor) V).index ∣ 2) :
    Nat.card (commutatorAction (Subgroup.zpowers actor) V) ≤ 2 := by
  let actors := Subgroup.zpowers actor
  let F := FixedPoints.subgroup actors V
  rcases (Nat.dvd_prime Nat.prime_two).mp hindex with hone | htwo
  · have htop : F = ⊤ := Subgroup.index_eq_one.mp hone
    have hbot : commutatorAction actors V = ⊥ := by
      apply bot_unique
      apply (Subgroup.closure_le _).mpr
      rintro point ⟨mover, source, _, rfl⟩
      have hfixed := (htop ▸ Subgroup.mem_top source : source ∈ F) mover
      simp only [hfixed, inv_mul_cancel]
      exact Subgroup.one_mem _
    rw [hbot, Subgroup.card_bot]
    decide
  change F.index = 2 at htwo
  have hsquare : actor ^ 2 = 1 :=
    square_eq_one_of_fixed_index_dvd_two actor hindex
  have hne : actor ≠ 1 := by
    intro heq
    have htop : F = ⊤ := by
      apply top_unique
      intro point _ mover
      have hmover : (mover : MulAut V) = 1 := by
        obtain ⟨power, hpower⟩ := mover.property
        simpa only [heq, one_zpow] using hpower.symm
      change (mover : MulAut V) point = point
      rw [hmover]
      rfl
    have hidx : F.index = 1 := Subgroup.index_eq_one.mpr htop
    omega
  have horder : orderOf actor = 2 := orderOf_eq_prime hsquare hne
  have hcard : Nat.card actors = 2 := by rw [Nat.card_zpowers, horder]
  have hprod := F.card_mul_index
  rw [htwo] at hprod
  let _ : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by
    have hpos : 0 < Nat.card F := Nat.card_pos
    omega)
  have hrank := (card_two_action_fixed_commutator_card_data
    (U := V) (⟨actor, Subgroup.mem_zpowers actor⟩ : actors)
    ⟨fun heq => hne (congrArg Subtype.val heq), Subtype.ext hsquare⟩ hcard).1
  have hpos : 0 < Nat.card F := Nat.card_pos
  change Nat.card V = Nat.card F * Nat.card (commutatorAction actors V) at hrank
  nlinarith

end MulAut

namespace Subgroup
open scoped commutatorElement

public theorem quotient_commutator_card_le_two_of_fixed_coatom
    {G : Type*} [Group G] [Finite G]
    (P V Z K : Subgroup G) (hZV : Z ≤ V)
    (hPV : P ≤ normalizer (V : Set G))
    (hN : (Z.subgroupOf V).Normal) :
    let _ := hN
    ∀ (_ : IsElementaryAbelian 2 (V ⧸ Z.subgroupOf V))
      (action : P →* MulAut (V ⧸ Z.subgroupOf V)),
      (∀ actor : P, ∀ point : V,
        action actor (QuotientGroup.mk' (Z.subgroupOf V) point) =
          QuotientGroup.mk' (Z.subgroupOf V)
            ⟨(actor : G) * (point : G) * (actor : G)⁻¹,
              (mem_normalizer_iff.mp (hPV actor.property) point).mp point.property⟩) →
      ∀ actor : P, K ≤ V → K.relIndex V ∣ 2 →
        ⁅K, zpowers (actor : G)⁆ ≤ Z →
        Z.relIndex (⁅V, zpowers (actor : G)⁆ ⊔ Z) ≤ 2 := by
  let _ := hN
  dsimp only
  intro hW action haction actor hKV hindex hcomm
  let _ := hW
  let W := V ⧸ Z.subgroupOf V
  let q : V →* W := QuotientGroup.mk' (Z.subgroupOf V)
  let Kbar := (K.subgroupOf V).map q
  let F := FixedPoints.subgroup (zpowers (action actor)) W
  have hKfix : Kbar ≤ F := by
    rintro point ⟨source, hsource, rfl⟩ mover
    have hfixed : action actor (q source) = q source := by
      rw [haction]
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hc : ⁅(actor : G), (source : G)⁆ ∈ Z := by
        rw [← commutatorElement_inv]
        exact Z.inv_mem (hcomm (commutator_mem_commutator hsource (mem_zpowers _)))
      change ((actor : G) * (source : G) * (actor : G)⁻¹) / (source : G) ∈ Z
      simpa only [commutatorElement_def, div_eq_mul_inv] using hc
    exact smul_eq_self_of_mem_zpowers mover.property hfixed
  have hfixIndex : F.index ∣ 2 :=
    (index_dvd_of_le hKfix).trans
      (((K.subgroupOf V).index_map_dvd (QuotientGroup.mk'_surjective _)).trans hindex)
  have hbound := MulAut.commutatorAction_card_le_two_of_fixed_index_dvd_two
    (action actor) hfixIndex
  let D := zpowers (actor : G)
  have hDP : D ≤ P := zpowers_le.mpr actor.property
  have hDV : ⁅V,D⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp (hDP.trans hPV)
  have hinternal : D.subgroupOf P = zpowers actor := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le hDP, MonoidHom.map_zpowers]
    rfl
  have hrank := quotient_conjugation_commutatorAction_card
    P V Z D hPV hDP hN action haction
  rw [hinternal, MonoidHom.map_zpowers] at hrank
  have heq := relIndex_sup_right (⁅V,D⁆.subgroupOf V) (Z.subgroupOf V)
  rw [← subgroupOf_sup hDV hZV, relIndex_subgroupOf (sup_le hDV hZV),
    relIndex_subgroupOf hDV] at heq
  rw [heq, ← hrank]
  exact hbound

end Subgroup
