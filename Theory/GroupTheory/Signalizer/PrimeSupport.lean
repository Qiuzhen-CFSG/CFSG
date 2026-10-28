module
public import Theory.GroupTheory.Signalizer.Generation
public import Theory.GroupTheory.Signalizer.Restriction
public import Theory.GroupAction.OddInvariantSylow

/-!
# Prime support of a binary signalizer subgroup

Let a finite elementary abelian two-group of order at least four act on a
finite group with an odd solvable signalizer family. If every family value
has order coprime to a prime q, every signalizer subgroup has order coprime
to q. The result assumes no completeness and retains the supplied action.

Choose an invariant Sylow q-subgroup inside the odd signalizer subgroup and
map it into the original ambient group. It remains a signalizer subgroup.
Restrict the family to it: each restricted value is both a q-group and of
q-coprime order, hence is trivial. The top subgroup is a signalizer subgroup
for that restricted family, and noncyclic binary fixed-point generation
places it in the generated subgroup, which is trivial. The Sylow subgroup
is therefore trivial, and its index is coprime to q.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, §11.1.5, printed
pp.307–308, `refs/latex/kurzweil.tex`. Applied to a completed q-prime subfamily,
this proves that its generated subgroup has order coprime to q.
-/

namespace Theory.GroupTheory.TwoSignalizerFamily

public theorem IsSignalizerSubgroup.coprime_of_values_coprime
    {A G : Type*} [Group A] [Finite A] [Group G] [Finite G]
    [IsElementaryAbelian 2 A] [MulDistribMulAction A G]
    {θ : TwoSignalizerFamily A G} {U : Subgroup G}
    (hU : θ.IsSignalizerSubgroup U) (hA : 4 ≤ Nat.card A)
    (q : ℕ) [Fact q.Prime]
    (hvalues : ∀ a, Nat.Coprime (Nat.card (θ.subgroup a)) q) :
    Nat.Coprime (Nat.card U) q := by
  let _ := hU.2.2.1
  obtain ⟨P, _, hPI⟩ := exists_invariant_sylow_le_of_isPGroup
    (G := U) (A := A) (IsElementaryAbelian.isPGroup 2 A) hU.1
    (p := q) (⊥ : Subgroup U) (IsPGroup.of_subsingleton q (⊥ : Subgroup U))
    (isInvariant_of_characteristic (A := A) (⊥ : Subgroup U))
  let Q : Subgroup G := (P : Subgroup U).map U.subtype
  let _ := hPI
  let _ : IsInvariant A G Q := isInvariant_map_subtype U (P : Subgroup U)
  have hQp : IsPGroup q Q := P.isPGroup'.map U.subtype
  have hQ : θ.IsSignalizerSubgroup Q :=
    hU.mono (Subgroup.map_subtype_le _) inferInstance
  have hvalues_bot : ∀ a, (θ.restrict Q).subgroup a = ⊥ := by
    intro a
    apply Subgroup.card_eq_one.mp
    have hqgroup := hQp.to_subgroup ((θ.restrict Q).subgroup a)
    apply hqgroup.card_eq_or_dvd.resolve_right
    apply (Fact.out : q.Prime).coprime_iff_not_dvd.mp
    apply Nat.Coprime.symm
    rw [θ.restrict_subgroup Q a]
    exact (hvalues a).of_dvd_left (Subgroup.card_comap_dvd_of_injective
      (θ.subgroup a) Q.subtype Q.subtype_injective)
  have hclosure : (θ.restrict Q).closure = ⊥ := by
    simp only [closure, hvalues_bot, iSup_bot]
  have htop : (θ.restrict Q).IsSignalizerSubgroup (⊤ : Subgroup Q) := by
    have h := (θ.isSignalizerSubgroup_subgroupOf_iff Q Q le_rfl).mpr hQ
    simpa only [Subgroup.subgroupOf_self] using h
  have htopbot : (⊤ : Subgroup Q) = ⊥ := by
    exact bot_unique (hclosure ▸ htop.le_closure hA)
  have hQcard : Nat.card Q = 1 := by
    have h := congrArg (fun V : Subgroup Q => Nat.card V) htopbot
    simpa using h
  have hPcard : Nat.card (P : Subgroup U) = 1 := by
    rwa [Subgroup.card_map_of_injective U.subtype_injective] at hQcard
  apply Nat.Coprime.symm
  apply (Fact.out : q.Prime).coprime_iff_not_dvd.mpr
  rw [← (P : Subgroup U).card_mul_index, hPcard, one_mul]
  exact P.not_dvd_index

end Theory.GroupTheory.TwoSignalizerFamily
