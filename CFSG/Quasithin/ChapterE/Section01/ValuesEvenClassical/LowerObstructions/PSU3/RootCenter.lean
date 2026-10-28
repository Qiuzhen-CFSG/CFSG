module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSU3.Obstruction
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Root centers in normally embedded binary PSU₃ groups

For a normal subgroup L isomorphic to PSU₃(2^f), the intersection S = L ∩ T
with an ambient Sylow two-subgroup is intrinsically Sylow in L. Transport
through the actual model equivalence and a Hermitian basis change identifies
its omega subgroup with its center, an elementary abelian group of order 2^f.
The arbitrary input form, its 2^f-power conjugation and matrix-field order
(2^f)^2 are retained throughout this transport.

Normality of L puts every conjugate of Z(S) contained in T inside S. Its
elements have square one and hence lie in Z(S); equal finite orders give
equality. The genuine model root subgroup has order (2^f)^3, proving that
Z(S) is proper in L. Simplicity is needed only in the E-generation consumer.

These results discharge all five center premises of the root-geometry
obstruction. The final application still takes root-pair generation explicitly;
its independent construction belongs to the source assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, E.1.1–6
and E.1.14(1), printed pp.209–211, 214 (citing Aschbacher 1982, Lemma 4.7);
Hermitian root calculations from Huppert II.10.12.
-/

public section
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSU3
open Subgroup BenderSuzuki.MatrixGroups.HermitianForm
open OddPrimeSylow.NormalizedOuter.FormTransport
variable {G : Type*} [Group G] [Finite G]

private theorem rootCenter_data (L : Subgroup G) (T : Sylow 2 G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f)) :
    IsElementaryAbelian 2 (rootCenter L T) ∧
      Nat.card (rootCenter L T) = 2 ^ f ∧
      ∀ x ∈ rootSection L T, x ^ 2 = 1 → x ∈ rootCenter L T := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 f
    (by omega) hcard hconj
  obtain ⟨eJ⟩ := exists_projectiveEquiv J (2 ^ f) hcard hfixed
  obtain ⟨P, hP⟩ := T.exists_subgroupOf_eq_of_normal L
  obtain ⟨homega, helem, hsize⟩ := SylowOmega.omega_of_projective_equiv
    (standardForm J) hf hcard hfixed rfl (e.trans eJ) P
  let := helem
  have hPS : (P : Subgroup L).map L.subtype = rootSection L T := by
    rw [hP, subgroupOf_map_subtype]
    exact inf_comm _ _
  have hZ : (omegaOneAmbient (P : Subgroup L)).map L.subtype = rootCenter L T := by
    rw [homega, map_embeddedCenter _ _ L.subtype_injective, hPS]
    rfl
  refine ⟨hZ ▸ IsElementaryAbelian.map L.subtype, ?_, ?_⟩
  · rw [← hZ, card_map_of_injective L.subtype_injective]
    exact hsize
  · intro x hx hsq
    rw [← hZ]
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    apply (omegaOneAmbient_le_iff _ _).mp le_rfl
    · rw [hP]
      exact hx.2
    · exact Subtype.ext hsq

/-- The actual embedded root center is elementary abelian at two. -/
theorem rootCenter_elementary (L : Subgroup G) (T : Sylow 2 G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f)) :
    IsElementaryAbelian 2 (rootCenter L T) :=
  (rootCenter_data L T hf hmodel).1

/-- The actual embedded root center has the fixed-field order. -/
theorem rootCenter_card (L : Subgroup G) (T : Sylow 2 G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f)) :
    Nat.card (rootCenter L T) = 2 ^ f :=
  (rootCenter_data L T hf hmodel).2.1

/-- Every square-one element of the intrinsic Sylow subgroup lies in its center. -/
theorem square_one_mem_rootCenter (L : Subgroup G) (T : Sylow 2 G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f))
    (x : G) (hx : x ∈ rootSection L T) (hsq : x ^ 2 = 1) :
    x ∈ rootCenter L T :=
  (rootCenter_data L T hf hmodel).2.2 x hx hsq

/-- The root center is nontrivial for the source parameter range. -/
theorem rootCenter_ne_bot (L : Subgroup G) (T : Sylow 2 G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f)) :
    rootCenter L T ≠ ⊥ := by
  intro h
  have hc := rootCenter_card L T hf hmodel
  rw [h, card_bot] at hc
  have := one_lt_pow₀ (by decide : 1 < (2 : ℕ)) (by omega : f ≠ 0)
  omega

/-- The larger root subgroup in the genuine model makes the center proper in L. -/
theorem rootCenter_ne_L (L : Subgroup G) (T : Sylow 2 G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f)) :
    rootCenter L T ≠ L := by
  intro h
  have hsize := rootCenter_card L T hf hmodel
  rw [h] at hsize
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  have hcube := BinarySylowOrder.cube_dvd_card_projective J (by omega : f ≠ 0)
    hcard hconj
  rw [← Nat.card_congr e.toEquiv, hsize] at hcube
  have hle := Nat.le_of_dvd (by positivity : 0 < 2 ^ f) hcube
  have hq : 1 < 2 ^ f := one_lt_pow₀ (by decide) (by omega)
  have hlt := pow_lt_pow_right₀ hq (by decide : 1 < 3)
  exact (not_lt_of_ge hle) (by simpa only [pow_one] using hlt)

/-- The generator rank of the root center is the fixed-field exponent. -/
theorem rootCenter_rank (L : Subgroup G) (T : Sylow 2 G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f)) :
    Group.rank (rootCenter L T) = f := by
  let := rootCenter_elementary L T hf hmodel
  have hc := rootCenter_card L T hf hmodel
  exact le_antisymm (IsElementaryAbelian.rank_le_of_card_le _ hc.le)
    (IsElementaryAbelian.rank_ge_of_card hc)

/-- The root center is the unique member of its ambient conjugacy class contained in T. -/
theorem rootCenter_conjugate_eq (L : Subgroup G) (T : Sylow 2 G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f))
    (g : G) (hg : (rootCenter L T).map (MulAut.conj g).toMonoidHom ≤
      (T : Subgroup G)) :
    (rootCenter L T).map (MulAut.conj g).toMonoidHom = rootCenter L T := by
  let := rootCenter_elementary L T hf hmodel
  apply eq_of_le_of_card_ge
  · rintro x ⟨z, hz, rfl⟩
    apply square_one_mem_rootCenter L T hf hmodel
    · constructor
      · exact (inferInstance : L.Normal).conj_mem z ((map_subtype_le _ hz).1) g
      · exact hg ⟨z, hz, rfl⟩
    · rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian z hz, map_one]
  · rw [card_map_of_injective (MulAut.conj g).injective]

/-- All five center inputs for the PSU₃ lower obstruction, with no geometric premise. -/
theorem rootCenter_geometry (L : Subgroup G) (T : Sylow 2 G) [L.Normal]
    {f : ℕ} (hf : 2 ≤ f) (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f)) :
    IsElementaryAbelian 2 (rootCenter L T) ∧
      rootCenter L T ≠ ⊥ ∧ rootCenter L T ≠ L ∧
      Group.rank (rootCenter L T) = f ∧
      ∀ g : G, (rootCenter L T).map (MulAut.conj g).toMonoidHom ≤
        (T : Subgroup G) →
        (rootCenter L T).map (MulAut.conj g).toMonoidHom = rootCenter L T :=
  ⟨rootCenter_elementary L T hf hmodel, rootCenter_ne_bot L T hf hmodel,
    rootCenter_ne_L L T hf hmodel, rootCenter_rank L T hf hmodel,
    rootCenter_conjugate_eq L T hf hmodel⟩

/-- The literal E-generation obstruction with all center premises discharged.
Only the independently constructed root-pair generation remains explicit. -/
theorem not_isEGenerated_of_root_pair (L : Subgroup G) (T : Sylow 2 G)
    [L.Normal] [IsSimpleGroup L] {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSU L 3 (2 ^ f))
    (hpair : ∀ g : G, (rootSection L T).map (MulAut.conj g).toMonoidHom ≠
      rootSection L T →
      L ≤ rootSection L T ⊔ (rootSection L T).map (MulAut.conj g).toMonoidHom) :
    ¬ IsEGenerated (f - 1) G := by
  obtain ⟨helem, hne, hproper, hrank, huniq⟩ := rootCenter_geometry L T hf hmodel
  exact not_isEGenerated_of_root_geometry L T (by omega) helem hne hproper hrank huniq
    (root_overgroup_of_conjugate_join L T hpair)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSU3
