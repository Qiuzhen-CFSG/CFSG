module
public import Theory.GroupAction.NormalizingFixedPoints
public import Theory.ElementaryAbelian.Basic
public import Theory.PGroupCore

/-!
# Two-cores in irreducible binary actions

A two-group acting on a nontrivial finite elementary abelian two-group has
a nonidentity fixed point. If a larger group acts irreducibly and normalizes
the acting two-group, that fixed subgroup is the whole module. Consequently
an irreducible automorphism subgroup has trivial two-core, and the two-core
of a group represented on an irreducible binary module lies in the kernel.

Orbit counting supplies the nonidentity fixed point. Normalizer invariance
and irreducibility promote the fixed subgroup to the whole module. Evaluation
is faithful for an automorphism subgroup; mapping a native two-core to the
representation range then gives the kernel containment.

These source-neutral lemmas are extracted, with unchanged statements and
proofs, from Stellmacher's local irreducible-actor argument in (8.4), printed
p.40. They also let the intrinsic chief action in (10.1)(15) descend through
the actual terminal two-core quotient.
-/

public theorem irreducible_fixed_nontrivial
    {G W : Type*} [Group G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W] [Nontrivial W]
    (T : Subgroup G) (hT : IsPGroup 2 T) :
    FixedPoints.subgroup T W ≠ ⊥ := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdiv : 2 ∣ Nat.card W :=
    (IsElementaryAbelian.isPGroup 2 W).card_eq_or_dvd.resolve_left
      (Nat.ne_of_gt Finite.one_lt_card)
  obtain ⟨w, hw, hne⟩ :=
    hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point (α := W) hdiv
      (show (1 : W) ∈ MulAction.fixedPoints T W by simp [MulAction.mem_fixedPoints])
  intro heq
  have hw' : w ∈ FixedPoints.subgroup T W := hw
  rw [heq, Subgroup.mem_bot] at hw'
  exact hne hw'.symm

public theorem irreducible_normal_two_subgroup_fixes
    {G W : Type*} [Group G] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [MulDistribMulAction G W] [Nontrivial W]
    (hirr : ∀ D : Subgroup W, (∀ g : G, ∀ w : W, w ∈ D → g • w ∈ D) →
      D = ⊥ ∨ D = ⊤)
    (N : Subgroup G) [N.Normal] (hN : IsPGroup 2 N) :
    FixedPoints.subgroup N W = ⊤ := by
  have hnorm : (⊤ : Subgroup G) ≤ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.normalizer_eq_top]
  have hinv := fixedPoints_isInvariant_of_normalizing_actor (V := W)
    (⊤ : Subgroup G) N hnorm
  exact (hirr _ (fun g w hw =>
    (hinv.invariant ⟨g, Subgroup.mem_top g⟩ w).mp hw)).resolve_left
      (irreducible_fixed_nontrivial N hN)

public theorem irreducible_range_two_core_eq_bot
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W] [Nontrivial W]
    (G : Subgroup (MulAut W))
    (hirr : ∀ D : Subgroup W, (∀ g : G, ∀ w : W, w ∈ D → g • w ∈ D) →
      D = ⊥ ∨ D = ⊤) : pCore 2 G = ⊥ := by
  have hfix := irreducible_normal_two_subgroup_fixes hirr (pCore 2 G)
    (pCore_isPGroup (p := 2) (G := G))
  apply le_bot_iff.mp
  intro g hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  apply MulEquiv.ext
  intro w
  have hw : w ∈ FixedPoints.subgroup (pCore 2 G) W := by rw [hfix]; trivial
  exact hw ⟨g, hg⟩

public theorem irreducible_range_core_le_ker
    {P W : Type*} [Group P] [Finite P] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] [Nontrivial W]
    (f : P →* MulAut W)
    (hirr : ∀ D : Subgroup W, (∀ g : f.range, ∀ w : W, w ∈ D → g • w ∈ D) →
      D = ⊥ ∨ D = ⊤) : pCore 2 P ≤ f.ker := by
  let N := (pCore 2 P).map f.rangeRestrict
  let _ : N.Normal := (pCore_normal (p := 2) (G := P)).map
    f.rangeRestrict f.rangeRestrict_surjective
  have hNp : IsPGroup 2 N := (pCore_isPGroup (p := 2) (G := P)).map f.rangeRestrict
  have hle : N ≤ pCore 2 f.range := le_sSup ⟨inferInstance, hNp⟩
  rw [irreducible_range_two_core_eq_bot f.range hirr] at hle
  intro g hg
  have hzero := hle (Subgroup.mem_map_of_mem f.rangeRestrict hg)
  have heq := congrArg Subtype.val (Subgroup.mem_bot.mp hzero)
  exact heq

