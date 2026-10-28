module
public import Theory.SpecificGroups.Triality.OddSupplement
public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient
public import Theory.SpecificGroups.SL2.SolvableSylowOvergroups
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.PCoreSurjective
public import GorensteinWalter.PSL2Cardinality
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The marked nonsolvable local section in binary triality

A proper nonsolvable subgroup normalized by the full positive Sylow lies
in one of the two genuine root parabolics. At q = 2 the central parabolic
is solvable, so only the arm parabolic remains. A perfect subgroup maps
trivially to the cyclic full-parabolic quotient. Together with the Sylow
it fills the arm local factor, by solvability of proper Sylow overgroups
of SL₂(8). Normality then makes its image the whole simple arm quotient.

The resulting two-core quotient equivalence is induced by the actual
inclusion, and Sylow alignment retains that map on every representative.
No nonbinary solvable-Sylow control or comparison with an unrelated field
parameter is used. This supplies the binary endpoint of the rank-two
embedding argument in Aschbacher–Smith 5.1.13 and 5.2.2, printed pp.636
and 648; the root parabolic structure is GLS3 §§2.3–2.6.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Triality.Standard.BinaryLocalSections
open Parabolics

private theorem central_local_solvable :
    Group.IsSolvable (localFactor (binaryParameters 1 Nat.zero_lt_one) .central) := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let e := (localFactorCentralQuotientEquivPSL2 P rfl).trans
    (Theory.PSL2.sl2QuotientEquiv (GaloisField 2 1)).symm
  have hs : Group.IsSolvable (SL(2, GaloisField 2 1)) := by
    apply isSolvable_of_prime_dvd_card_eq_two_or_three
    intro p hp hd
    rw [GorensteinWalter.sl2_card_formula, GaloisField.card 2 1 (by decide)] at hd
    norm_num at hd
    have hh := hp.dvd_mul.mp (show p ∣ 2 * 3 from hd)
    exact hh.elim (fun h => Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one))
      (fun h => Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left hp.ne_one))
  let := hs
  let : Group.IsSolvable (localFactor P .central ⧸ pCore 2 (localFactor P .central)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 (localFactor P .central)) := pCore_isNilpotent
  exact Group.isSolvable_of_ker_le_range (pCore 2 (localFactor P .central)).subtype
    (QuotientGroup.mk' (pCore 2 (localFactor P .central))) (by simp)

/-- The central full parabolic is solvable at the binary endpoint. -/
theorem central_parabolic_solvable :
    Group.IsSolvable (parabolic (binaryParameters 1 Nat.zero_lt_one) .central) := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let N := (localFactor P .central).subgroupOf (parabolic P .central)
  let : Group.IsSolvable (localFactor P .central) := central_local_solvable
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (localFactor_le_parabolic P .central)).toMonoidHom)
    (subgroupOfEquivOfLe (localFactor_le_parabolic P .central)).injective
  let : IsCyclic (parabolic P .central ⧸ N) := parabolic_quotient_isCyclic P rfl .central
  let : CommGroup (parabolic P .central ⧸ N) := IsCyclic.commGroup
  exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by simp)

private theorem perfect_le_local (P : Parameters) (hp : P.prime = 2) (a : Node)
    (R : Subgroup (Carrier P)) [Group.IsPerfect R] (hR : R ≤ parabolic P a) :
    R ≤ localFactor P a := by
  let X := R.subgroupOf (parabolic P a)
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hR).symm.toMonoidHom) (subgroupOfEquivOfLe hR).symm.surjective
  let : IsCyclic (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    parabolic_quotient_isCyclic P hp a
  let : CommGroup (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    IsCyclic.commGroup
  have hh := le_of_isPerfect_of_solvable_quotient X
    ((localFactor P a).subgroupOf (parabolic P a))
  intro x hx
  exact hh (show (⟨x,hR hx⟩ : parabolic P a) ∈ X from hx)

/-- A proper nonsolvable subgroup normalized by the positive Sylow lies in
its nonsolvable arm parabolic. -/
theorem le_arms_of_normalized
    (R : Subgroup (BinaryCarrier 1 Nat.zero_lt_one))
    (hne : R ≠ ⊤) (hns : ¬ Group.IsSolvable R)
    (hn : unipotent (binaryParameters 1 Nat.zero_lt_one) ≤ normalizer (R : Set _)) :
    R ⊔ unipotent (binaryParameters 1 Nat.zero_lt_one) ≤
      parabolic (binaryParameters 1 Nat.zero_lt_one) .arms := by
  let P := binaryParameters 1 Nat.zero_lt_one
  have hproper : R ⊔ unipotent P ≠ ⊤ := by
    intro he
    have hnR : R.Normal := normalizer_eq_top_iff.mp (by
      apply top_unique
      rw [← he]
      exact sup_le R.le_normalizer hn)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal R hnR with hb | ht
    · apply hns
      rw [hb]
      infer_instance
    · exact hne ht
  obtain ⟨a,ha⟩ := OddSupplement.le_parabolic 1 Nat.zero_lt_one
    (R ⊔ unipotent P) le_sup_right hproper
  cases a with
  | arms => exact ha
  | central =>
    let := central_parabolic_solvable
    exact (hns (Group.isSolvable_of_isSolvable_injective
      (inclusion_injective (le_sup_left.trans ha)))).elim

private theorem nonsolvable_cover_eq_top {A F : Type*} [Group A] [Finite A]
    [Field F] [Finite F] [CharP F 2]
    (f : A →* SL(2,F)) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (S : Sylow 2 A) (H : Subgroup A)
    (hSH : (S : Subgroup A) ≤ H) (hH : ¬ Group.IsSolvable H) : H = ⊤ := by
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let : Group.IsSolvable f.ker := inferInstance
  have him : H.map f = ⊤ := by
    by_contra hne
    let := Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
      (S.mapSurjective hf) (H.map f) (map_mono hSH) hne
    let := isSolvable_comap_of_solvable_ker f (H.map f)
    exact hH (Group.isSolvable_of_isSolvable_injective (inclusion_injective (le_comap_map f H)))
  simpa only [comap_map_eq, comap_top,
    sup_eq_left.mpr ((hk.le_sylow_of_normal S).trans hSH)] using congrArg (comap f) him

/-- The literal arm quotient map is onto on the invariant perfect subgroup.
This marks the rank-one section inside the same parabolic. -/
theorem arm_quotient_surjective
    (R : Subgroup (BinaryCarrier 1 Nat.zero_lt_one)) [Group.IsPerfect R]
    (hne : R ≠ ⊤) (hns : ¬ Group.IsSolvable R)
    (hn : unipotent (binaryParameters 1 Nat.zero_lt_one) ≤ normalizer (R : Set _)) :
    ∃ hRL : R ≤ localFactor (binaryParameters 1 Nat.zero_lt_one) .arms,
      Function.Surjective ((QuotientGroup.mk'
        (pCore 2 (localFactor (binaryParameters 1 Nat.zero_lt_one) .arms))).comp (inclusion hRL)) := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let L := localFactor P .arms
  let U := unipotent P
  let S := unipotentSylow P rfl
  have hRP := le_arms_of_normalized R hne hns hn
  have hRL : R ≤ L := perfect_le_local P rfl .arms R (le_sup_left.trans hRP)
  have hUL : U ≤ L := sylow_le_localFactor P .arms S (le_sup_right.trans hRP)
  let q := QuotientGroup.mk' (pCore 2 L)
  let e := (localFactorArmsQuotientEquivPSL2 P rfl).trans
    (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).symm
  let f := e.toMonoidHom.comp q
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = pCore 2 L := by
      ext x
      change e (q x) = 1 ↔ x ∈ pCore 2 L
      rw [← e.map_one, e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    rw [he]
    exact pCore_isPGroup
  have hHL : R ⊔ U ≤ L := sup_le hRL hUL
  have hHns : ¬ Group.IsSolvable ((R ⊔ U).subgroupOf L) := by
    intro hs
    let := hs
    let : Group.IsSolvable (R ⊔ U : Subgroup _) := Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe hHL).toMonoidHom) (subgroupOfEquivOfLe hHL).surjective
    exact hns (Group.isSolvable_of_isSolvable_injective (inclusion_injective (show R ≤ R ⊔ U from le_sup_left)))
  have hjoin : R ⊔ U = L := le_antisymm hHL (subgroupOf_eq_top.mp
    (nonsolvable_cover_eq_top f hf hk (S.subtype hUL) ((R ⊔ U).subgroupOf L)
      (fun _ hx => (show U ≤ R ⊔ U from le_sup_right) hx) hHns))
  let R' := R.subgroupOf L
  let : R'.Normal := (normal_subgroupOf_iff_le_normalizer hRL).mpr (by
    rw [← hjoin]
    exact sup_le R.le_normalizer hn)
  let : IsSimpleGroup (PSL(2, ExtensionField P)) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by rw [card_extensionField]; decide)
  let : IsSimpleGroup (L ⧸ pCore 2 L) :=
    (localFactorArmsQuotientEquivPSL2 P rfl).isSimpleGroup
  have him : R'.map q = ⊤ := by
    let : (R'.map q).Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R'.map q) inferInstance with hb | ht
    · have hle : R' ≤ pCore 2 L := by
        intro x hx
        apply (QuotientGroup.eq_one_iff x).mp
        exact mem_bot.mp (hb ▸ mem_map_of_mem q hx)
      let : Group.IsNilpotent (pCore 2 L) := pCore_isNilpotent
      let : Group.IsSolvable R' := Group.isSolvable_of_isSolvable_injective (inclusion_injective hle)
      exact (hns (Group.isSolvable_of_surjective
        (f := (subgroupOfEquivOfLe hRL).toMonoidHom) (subgroupOfEquivOfLe hRL).surjective)).elim
    · exact ht
  refine ⟨hRL,?_⟩
  intro y
  obtain ⟨r,hr,he⟩ := mem_map.mp (him.symm ▸ mem_top y)
  exact ⟨⟨r.val,hr⟩,he⟩


/-- The isomorphism of two-core quotients is induced by the literal inclusion. -/
theorem arm_quotient_equiv
    (R : Subgroup (BinaryCarrier 1 Nat.zero_lt_one)) [Group.IsPerfect R]
    (hne : R ≠ ⊤) (hns : ¬ Group.IsSolvable R)
    (hn : unipotent (binaryParameters 1 Nat.zero_lt_one) ≤ normalizer (R : Set _)) :
    ∃ hRL : R ≤ localFactor (binaryParameters 1 Nat.zero_lt_one) .arms,
      ∃ e : (R ⧸ pCore 2 R) ≃*
        (localFactor (binaryParameters 1 Nat.zero_lt_one) .arms ⧸
          pCore 2 (localFactor (binaryParameters 1 Nat.zero_lt_one) .arms)),
        ∀ r : R, e (QuotientGroup.mk' (pCore 2 R) r) =
          QuotientGroup.mk' _ (inclusion hRL r) := by
  obtain ⟨hRL,hf⟩ := arm_quotient_surjective R hne hns hn
  let L := localFactor (binaryParameters 1 Nat.zero_lt_one) .arms
  let f := (QuotientGroup.mk' (pCore 2 L)).comp (inclusion hRL)
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((QuotientGroup.mk' (pCore 2 L)).comp (inclusion hRL)).ker
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hRL)
  let q := QuotientGroup.mk' (pCore 2 L)
  have hqk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hcoreL := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hqk
  have hker : f.ker = pCore 2 R := by
    change (q.comp (inclusion hRL)).ker = pCore 2 R
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', ← hcoreL, comap_comap]
    exact f.comap_pCore_of_ker_isPGroup hf hk
  exact ⟨hRL,(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf),fun _ => rfl⟩

/-- Sylow alignment retains the actual subgroup and the induced arm quotient
map. No identification of any unrelated field parameter is made. -/
theorem marked_arm_quotient {G : Type*} [Group G] [Finite G]
    (eG : G ≃* BinaryCarrier 1 Nat.zero_lt_one) (S : Sylow 2 G)
    (R : Subgroup G) [Group.IsPerfect R]
    (hne : R ≠ ⊤) (hns : ¬ Group.IsSolvable R)
    (hn : (S : Subgroup G) ≤ normalizer (R : Set G)) :
    ∃ a : G ≃* BinaryCarrier 1 Nat.zero_lt_one,
      (S : Subgroup G).map a.toMonoidHom = unipotent (binaryParameters 1 Nat.zero_lt_one) ∧
      ∃ hRL : R.map a.toMonoidHom ≤ localFactor (binaryParameters 1 Nat.zero_lt_one) .arms,
      ∃ e : (R ⧸ pCore 2 R) ≃*
        (localFactor (binaryParameters 1 Nat.zero_lt_one) .arms ⧸
          pCore 2 (localFactor (binaryParameters 1 Nat.zero_lt_one) .arms)),
        ∀ r : R, e (QuotientGroup.mk' (pCore 2 R) r) =
          QuotientGroup.mk' _ (inclusion hRL (a.subgroupMap R r)) := by
  obtain ⟨_,a,_,ha⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    eG S (unipotentSylow (binaryParameters 1 Nat.zero_lt_one) rfl)
  change (S : Subgroup G).map a.toMonoidHom = unipotent (binaryParameters 1 Nat.zero_lt_one) at ha
  let R' := R.map a.toMonoidHom
  let b := a.subgroupMap R
  let : Group.IsPerfect R' := Group.IsPerfect.ofSurjective (f := b.toMonoidHom) b.surjective
  have hne' : R' ≠ ⊤ := by
    intro ht
    apply hne
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [map_top_of_surjective _ a.surjective]
    exact ht
  have hns' : ¬ Group.IsSolvable R' := by
    intro hs
    exact hns (@Group.isSolvable_of_isSolvable_injective R (R.map a.toMonoidHom)
      _ _ b.toMonoidHom b.injective hs)
  have hn' : unipotent (binaryParameters 1 Nat.zero_lt_one) ≤ normalizer (R' : Set _) := by
    rw [←ha]
    exact (map_mono hn).trans (le_normalizer_map a.toMonoidHom)
  obtain ⟨hRL,e,he⟩ := arm_quotient_equiv R' hne' hns' hn'
  let q := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  exact ⟨a,ha,hRL,q.trans e,fun r => he (b r)⟩

end Triality.Standard.BinaryLocalSections
