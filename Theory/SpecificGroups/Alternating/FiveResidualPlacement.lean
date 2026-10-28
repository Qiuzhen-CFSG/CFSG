module
public import Theory.SpecificGroups.Alternating.FiveTwoCoreExtension
public import Theory.SpecificGroups.SymmetricFive.LocalTwoCore
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PResidual.SylowSupplement
/-!
# Placement of local two-cores above an A₅ residual

Let S be a Sylow two-subgroup and let B contain every proper overgroup of S.
If O²(G)/O₂(O²(G)) is A₅, then O₂(B) lies in O²(G)O₂(G). The core quotient
of G is A₅ or S₅. In the second case the Sylow fixes a point on five letters;
the inverse image of its point stabilizer is proper and lies in B. Thus the
image of B has order divisible by three, and the S₅ local-core calculation
puts its two-core in A₅, which is the image of the original residual.

All residuals and cores are intrinsic to their stated carriers. No splitting
or unmarked replacement of the quotient is used.

Source application: Aschbacher--Smith, 12.2.19, printed p.801 of
`refs/quasithin.pdf`, the containment of the original V in K O₂(H).
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.Alternating.FiveResidualPlacement
variable {G : Type*} [Group G] [Finite G]
private theorem stabilizer_card (i : Fin 5) :
    Nat.card (MulAction.stabilizer (Equiv.Perm (Fin 5)) i) = 24 := by
  rw [Nat.card_eq_fintype_card]
  revert i
  decide +kernel

private theorem stabilizer_ne_top (i : Fin 5) :
    MulAction.stabilizer (Equiv.Perm (Fin 5)) i ≠ ⊤ := by
  intro he
  have hh := stabilizer_card i
  rw [he, Nat.card_congr (topEquiv : (⊤ : Subgroup (Equiv.Perm (Fin 5))) ≃*
    Equiv.Perm (Fin 5)).toEquiv] at hh
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm] at hh

/-- In a symmetric-five quotient, the unique proper Sylow overgroup has
an element of order three. The proof uses the fixed point of the Sylow
on five letters, then pulls back its proper point stabilizer. -/
theorem three_dvd_image_of_proper_overgroups_le
    (S : Sylow 2 G) (B : Subgroup G)
    (hb : ∀ Y : Subgroup G, (S : Subgroup G) ≤ Y → Y ≠ ⊤ → Y ≤ B)
    (f : G →* Equiv.Perm (Fin 5)) (hf : Function.Surjective f) :
    3 ∣ Nat.card (B.map f) := by
  let P := S.mapSurjective hf
  obtain ⟨i,hi⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card
    (Fin 5) (by simp)
  let A := MulAction.stabilizer (Equiv.Perm (Fin 5)) i
  have hSA : (S : Subgroup G) ≤ A.comap f := by
    intro s hs
    exact MulAction.mem_fixedPoints.mp hi ⟨f s, mem_map_of_mem f hs⟩
  have hne : A.comap f ≠ ⊤ := by
    intro he
    apply stabilizer_ne_top i
    have hh := congrArg (map f) he
    rwa [map_comap_eq_self_of_surjective hf, map_top_of_surjective f hf] at hh
  have hab : A ≤ B.map f := by
    have hh := map_mono (f := f) (hb _ hSA hne)
    rwa [map_comap_eq_self_of_surjective hf] at hh
  have hd := card_dvd_of_le hab
  rw [stabilizer_card] at hd
  exact dvd_trans (by decide : 3 ∣ 24) hd

/-- The embedded two-core of the proper Sylow overgroup lies in the
residual times the two-core whenever the latter quotient is S₅. -/
theorem core_le_residual_join_core_of_symmetric_quotient
    (S : Sylow 2 G) (B : Subgroup G) (hSB : (S : Subgroup G) ≤ B)
    (hb : ∀ Y : Subgroup G, (S : Subgroup G) ≤ Y → Y ≠ ⊤ → Y ≤ B)
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 5)) :
    B.pCoreIn 2 ≤ pResidual 2 G ⊔ pCore 2 G := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hc := SymmetricFive.LocalTwoCore.core_le_alternating (B.map f)
    (S.mapSurjective hf) (map_mono hSB)
    (three_dvd_image_of_proper_overgroups_le S B hb f hf)
  have hi := (FiveBorelCentralFactor.core_image_le f B).trans hc
  rw [← Equiv.Perm.twoResidual_eq_alternating (Fin 5),
    ← map_pResidual_of_surjective 2 f hf] at hi
  have hh := (map_le_iff_le_comap.mp hi)
  rwa [comap_map_eq, hk] at hh

/-- An A₅ residual quotient forces the same placement in either possible
A₅/S₅ extension. This is an intrinsic finite-group statement. -/
theorem core_le_residual_join_core
    (S : Sylow 2 G) (B : Subgroup G) (hSB : (S : Subgroup G) ≤ B)
    (hb : ∀ Y : Subgroup G, (S : Subgroup G) ≤ Y → Y ≠ ⊤ → Y ≤ B)
    (e : (pResidual 2 G ⧸ pCore 2 (pResidual 2 G)) ≃* alternatingGroup (Fin 5)) :
    B.pCoreIn 2 ≤ pResidual 2 G ⊔ pCore 2 G := by
  have hn : (S : Subgroup G) ≤ normalizer (pResidual 2 G : Set G) := le_normalizer_of_normal
  have he := FiveExtensionAction.core_quotient_of_two_supplement
    (pResidual 2 G) (S : Subgroup G) hn S.isPGroup' e
  rw [pResidual_sup_sylow_eq_top S] at he
  let c : ((⊤ : Subgroup G) ⧸ pCore 2 (⊤ : Subgroup G)) ≃* (G ⧸ pCore 2 G) :=
    QuotientGroup.congr _ _ topEquiv (pCore_map_iso 2 topEquiv)
  rcases he with ha | ha
  · obtain ⟨a⟩ := ha
    let d := c.symm.trans a
    let f := d.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
    have hf : Function.Surjective f := d.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : f.ker = pCore 2 G := by
      rw [MonoidHom.ker_comp_of_injective _ _ d.injective, QuotientGroup.ker_mk']
    have hr : (pResidual 2 G).map f = ⊤ := by
      rw [map_pResidual_of_surjective 2 f hf]
      let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
        ⟨commutator_alternatingGroup_eq_top (by simp)⟩
      let : Group.IsNilpotent (alternatingGroup (Fin 5) ⧸ pResidual 2 (alternatingGroup (Fin 5))) :=
        (isPGroup_quotient_pResidual 2).isNilpotent
      exact top_unique (le_of_isPerfect_of_solvable_quotient ⊤ _)
    have htop : pResidual 2 G ⊔ pCore 2 G = ⊤ := by
      have hh := congrArg (comap f) hr
      rwa [comap_map_eq, hk, comap_top] at hh
    rw [htop]
    exact le_top
  · obtain ⟨a⟩ := ha
    exact core_le_residual_join_core_of_symmetric_quotient S B hSB hb (c.symm.trans a)
end Theory.SpecificGroups.Alternating.FiveResidualPlacement
