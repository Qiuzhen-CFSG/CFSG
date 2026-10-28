module
public import Theory.GroupTheory.RadicalNormalizerControl
public import Theory.GroupTheory.PRadical
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin
/-!
# The solvable Fitting preimage above the two-core

The inverse image of F(G/O₂(G)) is solvable. Its quotient above O₂(G)
has odd order, so any radical two-subgroup is Sylow in its join with this
preimage. A self-centralizing two-core in the preimage remains self-centralizing
after adjoining the normalizing two-subgroup. The original quotient map and
subgroup inclusions are retained throughout.

This is the group-theoretic content of Aschbacher–Smith C.2.6(1), printed
p.145; the ordered block decomposition is a separate pushing-up argument.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

@[expose] def twoFittingCore (G : Type*) [Group G] : Subgroup G :=
  (fittingSubgroup (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G))
instance twoFittingCore_normal : (twoFittingCore G).Normal := by
  unfold twoFittingCore
  infer_instance

omit [Finite G] in
theorem twoCore_le_twoFittingCore : pCore 2 G ≤ twoFittingCore G := by
  intro x hx
  change QuotientGroup.mk' (pCore 2 G) x ∈ fittingSubgroup _
  rw [show QuotientGroup.mk' (pCore 2 G) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
  exact one_mem _

theorem twoFittingCore_solvable : Group.IsSolvable (twoFittingCore G) := by
  let F := twoFittingCore G
  let f : F →* fittingSubgroup (G ⧸ pCore 2 G) :=
    ((QuotientGroup.mk' (pCore 2 G)).comp F.subtype).codRestrict _ (fun x => x.property)
  have hk : f.ker = (pCore 2 G).subgroupOf F := by
    ext x
    change (⟨QuotientGroup.mk' (pCore 2 G) x.val, _⟩ : fittingSubgroup _) = 1 ↔ _
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff x.val
  let : Group.IsNilpotent f.ker := by
    rw [hk]
    exact pCore_isPGroup.comap_subtype.isNilpotent
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by simp)

theorem twoFittingCore_sup_solvable (R : Subgroup G) (hR : IsPGroup 2 R) :
    Group.IsSolvable (twoFittingCore G ⊔ R : Subgroup G) := by
  let D := twoFittingCore G ⊔ R
  let N := (twoFittingCore G).subgroupOf D
  let : N.Normal := inferInstance
  let : Group.IsSolvable (twoFittingCore G) := twoFittingCore_solvable
  let : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show twoFittingCore G ≤ D from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show twoFittingCore G ≤ D from le_sup_left)).injective
  have hgen : N ⊔ R.subgroupOf D = ⊤ := by
    rw [← subgroupOf_sup (show twoFittingCore G ≤ D from le_sup_left)
      (show R ≤ D from le_sup_right), subgroupOf_self]
  have hp : IsPGroup 2 (D ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (R.subgroupOf D) hR.comap_subtype hgen
  let : Group.IsNilpotent (D ⧸ N) := hp.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance,inferInstance⟩

omit [Finite G] in
theorem twoFittingCore_sup_characteristicTwo (R : Subgroup G) (hR : IsPGroup 2 R)
    (hc : centralizer (pCore 2 (twoFittingCore G) : Set (twoFittingCore G)) ≤
      pCore 2 (twoFittingCore G)) :
    centralizer (pCore 2 (twoFittingCore G ⊔ R : Subgroup G) : Set _) ≤
      pCore 2 (twoFittingCore G ⊔ R : Subgroup G) :=
  centralizer_pCore_sup_le 2 (twoFittingCore G) R hc hR le_normalizer_of_normal
theorem twoFittingCore_sup_sylow (R : Subgroup G) (hr : IsPRadical 2 R) :
    let F := (fittingSubgroup (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G))
    ∃ S : Sylow 2 (F ⊔ R : Subgroup G),
      (S : Subgroup (F ⊔ R : Subgroup G)).map (F ⊔ R : Subgroup G).subtype = R := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := pCore 2 G
  let q := QuotientGroup.mk' Q
  let F := (fittingSubgroup (G ⧸ Q)).comap q
  have hQR : Q ≤ R := pCore_le_of_pCore_normalizer_le R hr.isPGroup hr.2.le
  have hQF : Q ≤ F := by
    intro x hx
    change q x ∈ fittingSubgroup (G ⧸ Q)
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  let f : F →* G ⧸ Q := q.comp F.subtype
  have hk : f.ker = Q.subgroupOf F := by
    ext x
    exact QuotientGroup.eq_one_iff (x : G)
  have hrange : f.range = fittingSubgroup (G ⧸ Q) := by
    rw [MonoidHom.range_comp, range_subtype]
    exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q) _
  have hfodd : Nat.Coprime 2 (Nat.card (fittingSubgroup (G ⧸ Q))) :=
    (pPrimeCore_coprime_card (p := 2) (G := G ⧸ Q)).of_dvd_right
      (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2
        (pCore_quotient_pCore_eq_bot 2)))
  have hi : ¬ 2 ∣ (Q.subgroupOf F).index := by
    rw [← hk, index_ker, hrange]
    exact Nat.prime_two.coprime_iff_not_dvd.mp hfodd
  apply IsPGroup.exists_sylow_sup_of_coprime_index F R hr.isPGroup
    le_normalizer_of_normal (Q.subgroupOf F) hi
  rw [map_subgroupOf_eq_of_le hQF]
  exact hQR


end Theory.GroupTheory
