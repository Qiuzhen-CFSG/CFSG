module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.FourObstruction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.CosetIdentification.ModelRank
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.CosetIdentification.CentralFactor
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.CosetIdentification.DerivedQuotient
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Involutions in a central coset of the local derived group

Strong embedding makes the derived involutions one conjugacy class.
Starting with a distinguished involution in the central coset, conjugacy
therefore identifies all its noncentral involutions. A commuting conjugate
in the derived group then expresses each derived involution as a product
of two distinguished involutions. The required four-group is supplied by
the actual simple Bender quotient through the odd core.

Source: GLS, Volume 4, Chapter 2, Lemma 4.7(b,c), lines 599–638 of the
transcription, and Chapter 4, Section 3. The final theorems discharge the
structural premises of the initial helpers from `StructureConclusion` in
the centralizer. The central-factor identification uses the trivial center
of the actual simple Bender factor; the derived quotient comparison and
strong embedding are re-exported from `DerivedQuotient`. Centralizer
selection remains with the caller. Normality in the ambient group is
never assumed for the local derived subgroup.
-/

namespace BenderSuzuki.ZD.LocalCosetIdentification
open Theory.GroupTheory PFAppendixIII PFchapter1section1
open scoped Pointwise

private theorem mul_involution {G : Type*} [Group G] {a b : G}
    (ha : IsInvolution a) (hb : IsInvolution b) (hab : Commute a b) (hne : a ≠ b) :
    IsInvolution (a * b) := by
  refine ⟨?_, ?_⟩
  · intro heq
    apply hne
    have heq' := congrArg (fun x => x * b) heq
    simpa only [mul_assoc, ← pow_two, hb.2, mul_one, one_mul] using heq'
  · rw [hab.mul_pow, ha.2, hb.2, one_mul]

private theorem cancel_central_pair {G : Type*} [Group G] {u a b : G}
    (hu : IsInvolution u) (hc : Commute u a) :
    (u * a) * (u * b) = a * b := by
  calc
    (u * a) * (u * b) = (u * u) * (a * b) := by
      rw [mul_assoc, ← mul_assoc a, hc.eq.symm]
      group
    _ = a * b := by rw [← pow_two, hu.2, one_mul]

/-- The conjugacy argument of GLS 4, Chapter 2, Lemma 4.7(b).
Only placement of the distinguished involutions in the nontrivial coset
is assumed; strong embedding proves the reverse inclusion. -/
public theorem mul_mem_distinguished
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M D : Subgroup G} {u : G}
    (h : IsProductDisconnected Z M) (hu : IsInvolution u) (huZ : u ∉ Z)
    (hD : D ≤ Subgroup.centralizer ({u} : Set G))
    (hne : ∃ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G))
    (hZD : ∀ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) → u * z ∈ D)
    (hSE : IsStronglyEmbedded (M.comap D.subtype)) :
    ∀ a ∈ D, IsInvolution a → u * a ∈ Z := by
  obtain ⟨z, hz, hzC⟩ := hne
  have huz : Commute u z := (Subgroup.mem_centralizer_singleton_iff.mp hzC).symm
  have ht : IsInvolution (u * z) :=
    mul_involution hu (h.involutions z hz) huz (fun heq => huZ (heq ▸ hz))
  let t : D := ⟨u * z, hZD z hz hzC⟩
  intro a ha hai
  obtain ⟨g, hg⟩ := hSE.involutions_conjugate
    (IsInvolution.subtype ht t.property) (IsInvolution.subtype hai ha)
  have hg' : rightConjugateElem (u * z) (g : G) = a := congrArg D.subtype hg
  have hgu : Commute u (g : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hD g.property)).symm
  have hconj : MulAut.conj (g : G)⁻¹ z = u * a := by
    rw [← hg']
    simp only [MulAut.conj_apply, inv_inv, rightConjugateElem]
    simp only [← mul_assoc]
    rw [hgu.inv_right.eq, mul_assoc (g : G)⁻¹ u u, ← pow_two, hu.2, mul_one]
  rw [← hconj]
  exact h.invariant _ _ hz

/-- Every derived involution is a product of two distinguished involutions.
A commuting conjugate in the derived group supplies the two factors. -/
public theorem derived_involution_product
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M D : Subgroup G} {u : G}
    (hu : IsInvolution u)
    (hD : D ≤ Subgroup.centralizer ({u} : Set G))
    (hSE : IsStronglyEmbedded (M.comap D.subtype)) (hrank : TwoRankAtLeastTwo D)
    (hcoset : ∀ a ∈ D, IsInvolution a → u * a ∈ Z) :
    ∀ a ∈ D, IsInvolution a → ∃ b ∈ Z, ∃ c ∈ Z, a = b * c := by
  intro a ha hai
  let aD : D := ⟨a, ha⟩
  obtain ⟨g, hne, hc⟩ :=
    hSE.exists_distinct_commuting_conjugate_of_twoRank hrank aD
      (IsInvolution.subtype hai ha)
  let bD : D := MulAut.conj g aD
  have hb : IsInvolution (bD : G) :=
    IsInvolution.map_of_injective
      (IsInvolution.map_of_injective (IsInvolution.subtype hai ha)
        (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
      D.subtype D.subtype_injective
  have hab : Commute a (bD : G) := hc.map D.subtype
  have habne : a ≠ (bD : G) := fun heq => hne (Subtype.ext heq.symm)
  have habi := mul_involution hai hb hab habne
  refine ⟨u * (bD : G), hcoset _ bD.property hb,
    u * (a * (bD : G)), hcoset _ (D.mul_mem ha bD.property) habi, ?_⟩
  rw [cancel_central_pair hu
    (Subgroup.mem_centralizer_singleton_iff.mp (hD bD.property)).symm]
  rw [← mul_assoc, ← hab.eq, mul_assoc, ← pow_two, hb.2, mul_one]

private theorem centralizer_self {G : Type*} [Group G] (u : G) :
    u ∈ Subgroup.centralizer ({u} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

/-- The involutions in the nontrivial coset, excluding its central representative,
are exactly the distinguished involutions of the centralizer. Multiplication by
`u` tests membership in `uD`, since `u² = 1`. -/
public theorem coset_involutions_eq
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M D : Subgroup G} {u : G}
    (h : IsProductDisconnected Z M) (hu : IsInvolution u) (huZ : u ∉ Z)
    (hD : D ≤ Subgroup.centralizer ({u} : Set G))
    (hne : ∃ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G))
    (hZD : ∀ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) → u * z ∈ D)
    (hSE : IsStronglyEmbedded (M.comap D.subtype)) :
    {x : G | IsInvolution x ∧ u * x ∈ D ∧ x ≠ u} =
      Z ∩ (Subgroup.centralizer ({u} : Set G) : Set G) := by
  have hcoset := mul_mem_distinguished h hu huZ hD hne hZD hSE
  ext x
  constructor
  · rintro ⟨hx, hxD, hxu⟩
    have hxC : x ∈ Subgroup.centralizer ({u} : Set G) := by
      have hh := (Subgroup.centralizer ({u} : Set G)).mul_mem
        (centralizer_self u) (hD hxD)
      simpa only [← mul_assoc, ← pow_two, hu.2, one_mul] using hh
    have hux := mul_involution hu hx
      (Subgroup.mem_centralizer_singleton_iff.mp hxC).symm (Ne.symm hxu)
    have hxZ := hcoset _ hxD hux
    exact ⟨by simpa only [← mul_assoc, ← pow_two, hu.2, one_mul] using hxZ, hxC⟩
  · rintro ⟨hxZ, hxC⟩
    exact ⟨h.involutions x hxZ, hZD x hxZ hxC, fun heq => huZ (heq ▸ hxZ)⟩

/-- The derived involutions are exactly `u` times the distinguished local set. -/
public theorem derived_involutions_eq
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M D : Subgroup G} {u : G}
    (h : IsProductDisconnected Z M) (hu : IsInvolution u) (huZ : u ∉ Z)
    (hD : D ≤ Subgroup.centralizer ({u} : Set G))
    (hne : ∃ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G))
    (hZD : ∀ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) → u * z ∈ D)
    (hSE : IsStronglyEmbedded (M.comap D.subtype)) :
    {a : G | a ∈ D ∧ IsInvolution a} =
      (fun z => u * z) '' (Z ∩ (Subgroup.centralizer ({u} : Set G) : Set G)) := by
  have hcoset := mul_mem_distinguished h hu huZ hD hne hZD hSE
  ext a
  constructor
  · rintro ⟨haD, ha⟩
    refine ⟨u * a, ⟨hcoset a haD ha, ?_⟩, ?_⟩
    · exact (Subgroup.centralizer ({u} : Set G)).mul_mem (centralizer_self u) (hD haD)
    · change u * (u * a) = a
      rw [← mul_assoc, ← pow_two, hu.2, one_mul]
  · rintro ⟨z, ⟨hzZ, hzC⟩, rfl⟩
    exact ⟨hZD z hzZ hzC, mul_involution hu (h.involutions z hzZ)
      (Subgroup.mem_centralizer_singleton_iff.mp hzC).symm (fun heq => huZ (heq ▸ hzZ))⟩

private theorem mem_zpowers_involution {G : Type*} [Group G] [Finite G]
    {u x : G} (hu : IsInvolution u) (hx : x ∈ Subgroup.zpowers u) : x = 1 ∨ x = u := by
  classical
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hx)
  have hn : n < 2 := by
    simpa only [Finset.mem_range, orderOf_eq_prime hu.2 hu.1] using hn
  interval_cases n <;> simp

/-- A central factor of order two gives two actual cosets, with no ambient
normality assumption on `D`. -/
public theorem mem_sup_involution_cosets
    {G : Type*} [Group G] [Finite G] {D : Subgroup G} {u x : G}
    (hu : IsInvolution u) (hD : D ≤ Subgroup.centralizer ({u} : Set G))
    (hx : x ∈ D ⊔ Subgroup.zpowers u) : x ∈ D ∨ u * x ∈ D := by
  have hn : Subgroup.zpowers u ≤ Subgroup.normalizer (D : Set G) := by
    apply Subgroup.zpowers_le.mpr
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact Subgroup.mem_centralizer_singleton_iff.mp (hD hd)
  have hx' : x ∈ (Subgroup.zpowers u : Set G) * (D : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn, sup_comm]
    exact hx
  obtain ⟨v, hv, d, hd, rfl⟩ := hx'
  rcases mem_zpowers_involution hu hv with hv1 | hvu
  · left
    change v * d ∈ D
    rw [hv1, one_mul]
    exact hd
  · right
    change u * (v * d) ∈ D
    rw [hvu, ← mul_assoc, ← pow_two, hu.2, one_mul]
    exact hd

/-- Coset placement already implies generation of the local closure by `D`
and `u`. The intersection is trivial when `u` lies outside `D`, and the factors
commute because the local closure centralizes `u`. -/
public theorem closure_direct_product
    {G : Type*} [Group G] [Finite G] {Z : Set G} {D : Subgroup G} {u : G}
    (hu : IsInvolution u) (huL : u ∈ centralizerClosure Z u)
    (hDL : D ≤ centralizerClosure Z u) (huD : u ∉ D)
    (hZD : ∀ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) → u * z ∈ D) :
    D ⊔ Subgroup.zpowers u = centralizerClosure Z u ∧
      Disjoint D (Subgroup.zpowers u) ∧
      (∀ d ∈ D, ∀ v ∈ Subgroup.zpowers u, Commute d v) := by
  refine ⟨le_antisymm (sup_le hDL (Subgroup.zpowers_le.mpr huL)) ?_, ?_, ?_⟩
  · apply (Subgroup.closure_le _).mpr
    rintro z ⟨hzZ, hzC⟩
    have hh := (D ⊔ Subgroup.zpowers u).mul_mem
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers u))
      (Subgroup.mem_sup_left (hZD z hzZ hzC))
    rw [← mul_assoc, ← pow_two, hu.2, one_mul] at hh
    exact hh
  · apply Subgroup.disjoint_def.mpr
    intro x hxD hxU
    rcases mem_zpowers_involution hu hxU with h | rfl
    · exact h
    · exact False.elim (huD hxD)
  · intro d hd v hv
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (show Commute d u from
      Subgroup.mem_centralizer_singleton_iff.mp (centralizerClosure_le Z u (hDL hd))).zpow_right n

/-- The three-way involution partition needed by the four-group obstruction.
Conjugacy and a four-group prove the product clause rather than assuming it. -/
public theorem involution_partition
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M D L : Subgroup G} {u : G}
    (h : IsProductDisconnected Z M) (hu : IsInvolution u) (huZ : u ∉ Z)
    (hD : D ≤ Subgroup.centralizer ({u} : Set G))
    (hne : ∃ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G))
    (hZD : ∀ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) → u * z ∈ D)
    (hSE : IsStronglyEmbedded (M.comap D.subtype)) (hrank : TwoRankAtLeastTwo D)
    (hgen : D ⊔ Subgroup.zpowers u = L) :
    ∀ x ∈ L, IsInvolution x →
      x = u ∨ x ∈ Z ∨ ∃ a ∈ Z, ∃ b ∈ Z, x = a * b := by
  have hcoset := mul_mem_distinguished h hu huZ hD hne hZD hSE
  intro x hx hxi
  by_cases hxu : x = u
  · exact Or.inl hxu
  · right
    rw [← hgen] at hx
    rcases mem_sup_involution_cosets hu hD hx with hxD | hxD
    · exact Or.inr (derived_involution_product hu hD hSE hrank hcoset x hxD hxi)
    · left
      have heq := coset_involutions_eq h hu huZ hD hne hZD hSE
      have hx' : x ∈ {y : G | IsInvolution y ∧ u * y ∈ D ∧ y ≠ u} := ⟨hxi, hxD, hxu⟩
      rw [heq] at hx'
      exact hx'.1

/-- The direct-product decomposition as a multiplicative equivalence with
the specified multiplication map, not merely an abstract isomorphism. -/
public theorem closure_product_equiv
    {G : Type*} [Group G] [Finite G] {Z : Set G} {D : Subgroup G} {u : G}
    (hu : IsInvolution u) (huL : u ∈ centralizerClosure Z u)
    (hDL : D ≤ centralizerClosure Z u) (huD : u ∉ D)
    (hZD : ∀ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) → u * z ∈ D) :
    ∃ e : D × Subgroup.zpowers u ≃* centralizerClosure Z u,
      ∀ d v, (e (d, v) : G) = (d : G) * (v : G) := by
  obtain ⟨hgen, hdisj, hcomm⟩ := closure_direct_product hu huL hDL huD hZD
  obtain ⟨e, he⟩ := Subgroup.exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    D (Subgroup.zpowers u) hdisj (by
      intro d hd
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hcomm d hd v hv).symm)
  exact ⟨e.trans (MulEquiv.subgroupCongr hgen), he⟩

/-- Assemble the two inputs used by `local_centralizer_not_twoRank` from
structural data on the actual ambient image of the local derived subgroup.
The Bender quotient supplies the four-group; no rank or conjugacy premise
is added. Coset placement and derived recognition remain explicit obligations. -/
public theorem local_obstruction_inputs_of_derived_structure
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G} {u : G}
    (h : IsProductDisconnected Z M) (hu : IsInvolution u) (huM : u ∈ M)
    (hC : ¬ Subgroup.centralizer ({u} : Set G) ≤ M)
    (hne : ∃ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) ∧ z ∈ M)
    (huL : u ∈ centralizerClosure Z u)
    (huD : u ∉ (commutator (centralizerClosure Z u)).map
      (centralizerClosure Z u).subtype)
    (hZD : ∀ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) →
      u * z ∈ (commutator (centralizerClosure Z u)).map
        (centralizerClosure Z u).subtype)
    (hSE : IsStronglyEmbedded (M.comap
      ((commutator (centralizerClosure Z u)).map (centralizerClosure Z u).subtype).subtype))
    (hmodel : IsSimpleBenderGroup
      (((commutator (centralizerClosure Z u)).map (centralizerClosure Z u).subtype) ⧸
        pPrimeCore 2 ((commutator (centralizerClosure Z u)).map
          (centralizerClosure Z u).subtype))) :
    (∀ a ∈ (commutator (centralizerClosure Z u)).map (centralizerClosure Z u).subtype,
      IsInvolution a → u * a ∈ Z) ∧
    (∀ x ∈ centralizerClosure Z u, IsInvolution x →
      x = u ∨ x ∈ Z ∨ ∃ a ∈ Z, ∃ b ∈ Z, x = a * b) := by
  let L := centralizerClosure Z u
  let D := (commutator L).map L.subtype
  have hDL : D ≤ L := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hDC : D ≤ Subgroup.centralizer ({u} : Set G) :=
    hDL.trans (centralizerClosure_le Z u)
  have huZ := (not_mem_or_product_of_centralizer_not_le h hu huM hC).1
  have hne' : ∃ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) := by
    obtain ⟨z, hz, hzC, _⟩ := hne
    exact ⟨z, hz, hzC⟩
  have hgen := (closure_direct_product hu huL hDL huD hZD).1
  exact ⟨mul_mem_distinguished h hu huZ hDC hne' hZD hSE,
    involution_partition h hu huZ hDC hne' hZD hSE
      (twoRank_of_model_oddCore_quotient hmodel) hgen⟩

private theorem local_derived_le_closure
    {G : Type*} [Group G] (Z : Set G) (u : G) :
    (commutator (centralizerClosure Z u)).map (centralizerClosure Z u).subtype ≤
      centralizerClosure Z u := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

/-- The actual internal direct product `L = D⟨u⟩`, with trivial intersection
and commuting factors, deduced from the local structural conclusion. -/
public theorem local_direct_product_of_structure
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G} {u : G}
    (hu : IsInvolution u) (huL : u ∈ centralizerClosure Z u)
    (hs : StructureConclusion ((Subgroup.centralizer ({u} : Set G)).subtype ⁻¹' Z)
      (M.comap (Subgroup.centralizer ({u} : Set G)).subtype)) :
    let D := (commutator (centralizerClosure Z u)).map (centralizerClosure Z u).subtype
    D ⊔ Subgroup.zpowers u = centralizerClosure Z u ∧
      Disjoint D (Subgroup.zpowers u) ∧
      (∀ d ∈ D, ∀ v ∈ Subgroup.zpowers u, Commute d v) := by
  obtain ⟨huD, hZD⟩ := central_factor_of_structure hu huL hs
  exact closure_direct_product hu huL (local_derived_le_closure Z u) huD hZD

/-- The direct-product equivalence is the multiplication map on the specified
derived subgroup and the cyclic subgroup generated by the specified `u`. -/
public theorem local_product_equiv_of_structure
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G} {u : G}
    (hu : IsInvolution u) (huL : u ∈ centralizerClosure Z u)
    (hs : StructureConclusion ((Subgroup.centralizer ({u} : Set G)).subtype ⁻¹' Z)
      (M.comap (Subgroup.centralizer ({u} : Set G)).subtype)) :
    let D := (commutator (centralizerClosure Z u)).map (centralizerClosure Z u).subtype
    ∃ e : D × Subgroup.zpowers u ≃* centralizerClosure Z u,
      ∀ d v, (e (d, v) : G) = (d : G) * (v : G) := by
  obtain ⟨huD, hZD⟩ := central_factor_of_structure hu huL hs
  exact closure_product_equiv hu huL (local_derived_le_closure Z u) huD hZD

/-- GLS Chapter 2, Lemma 4.7(b,c), with explicit centralizer inputs.
Since `u² = 1`, the test `u * x ∈ D` is exactly membership in the coset `uD`.
The last clause gives commuting distinguished factors, as required for the
source set `𝒫`, not merely an arbitrary factorization. -/
public theorem local_involution_identifications_of_structure
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G} {u : G}
    (h : IsProductDisconnected Z M) (hu : IsInvolution u) (huM : u ∈ M)
    (hC : ¬ Subgroup.centralizer ({u} : Set G) ≤ M)
    (hne : ∃ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) ∧ z ∈ M)
    (huL : u ∈ centralizerClosure Z u)
    (hs : StructureConclusion ((Subgroup.centralizer ({u} : Set G)).subtype ⁻¹' Z)
      (M.comap (Subgroup.centralizer ({u} : Set G)).subtype)) :
    let D := (commutator (centralizerClosure Z u)).map (centralizerClosure Z u).subtype
    ({x : G | IsInvolution x ∧ u * x ∈ D ∧ x ≠ u} =
      Z ∩ (Subgroup.centralizer ({u} : Set G) : Set G)) ∧
    ({a : G | a ∈ D ∧ IsInvolution a} =
      (fun z => u * z) '' (Z ∩ (Subgroup.centralizer ({u} : Set G) : Set G))) ∧
    (∀ a ∈ D, IsInvolution a →
      ∃ b ∈ Z, ∃ c ∈ Z, Commute b c ∧ a = b * c) := by
  obtain ⟨_, hZD⟩ := central_factor_of_structure hu huL hs
  obtain ⟨hmodel, _, _, hSE⟩ := LocalDerivedQuotient.local_derived_data Z M u hs
  have hDC := (local_derived_le_closure Z u).trans (centralizerClosure_le Z u)
  have huZ := (not_mem_or_product_of_centralizer_not_le h hu huM hC).1
  have hne' : ∃ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) := by
    obtain ⟨z, hz, hzC, _⟩ := hne
    exact ⟨z, hz, hzC⟩
  refine ⟨coset_involutions_eq h hu huZ hDC hne' hZD hSE,
    derived_involutions_eq h hu huZ hDC hne' hZD hSE, ?_⟩
  intro a ha hai
  obtain ⟨b, hb, c, hc, habc⟩ := derived_involution_product hu hDC hSE
    (twoRank_of_model_oddCore_quotient hmodel)
    (mul_mem_distinguished h hu huZ hDC hne' hZD hSE) a ha hai
  refine ⟨b, hb, c, hc, ?_, habc⟩
  change b * c = c * b
  calc
    b * c = (b * c)⁻¹ := by rw [← habc, hai.inv_eq_self]
    _ = c * b := by
      rw [mul_inv_rev, (h.involutions c hc).inv_eq_self, (h.involutions b hb).inv_eq_self]

/-- Both inputs of `local_centralizer_not_twoRank`, with the derived coset,
conjugacy, and rank premises proved from the centralizer's ZD structure. -/
public theorem local_obstruction_inputs_of_structure
    {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G} {u : G}
    (h : IsProductDisconnected Z M) (hu : IsInvolution u) (huM : u ∈ M)
    (hC : ¬ Subgroup.centralizer ({u} : Set G) ≤ M)
    (hne : ∃ z ∈ Z, z ∈ Subgroup.centralizer ({u} : Set G) ∧ z ∈ M)
    (huL : u ∈ centralizerClosure Z u)
    (hs : StructureConclusion ((Subgroup.centralizer ({u} : Set G)).subtype ⁻¹' Z)
      (M.comap (Subgroup.centralizer ({u} : Set G)).subtype)) :
    (∀ a ∈ (commutator (centralizerClosure Z u)).map (centralizerClosure Z u).subtype,
      IsInvolution a → u * a ∈ Z) ∧
    (∀ x ∈ centralizerClosure Z u, IsInvolution x →
      x = u ∨ x ∈ Z ∨ ∃ a ∈ Z, ∃ b ∈ Z, x = a * b) := by
  obtain ⟨huD, hZD⟩ := central_factor_of_structure hu huL hs
  obtain ⟨hmodel, _, _, hSE⟩ := LocalDerivedQuotient.local_derived_data Z M u hs
  exact local_obstruction_inputs_of_derived_structure h hu huM hC hne huL
    huD hZD hSE hmodel

end BenderSuzuki.ZD.LocalCosetIdentification
