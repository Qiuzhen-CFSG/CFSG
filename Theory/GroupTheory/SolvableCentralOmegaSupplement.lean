module

public import Theory.GroupTheory.SylowCentralizerCore
public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.CoprimeQuotientNormalizer
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Odd-core supplements for central elementary Sylow subgroups

In a finite solvable group, an elementary subgroup central in a chosen Sylow
two-subgroup has elementary normal closure in a supplement to the odd core.
The supplement contains the chosen Sylow, and the closure remains inside it.

Lift the two-core of the odd-core quotient into the Sylow subgroup and take
its normalizer. Fitting self-centralization puts the given elementary subgroup
in this lift. Its central omega is characteristic in the lift, so it contains
the normal closure and proves both required properties.

Source: Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, p.387,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup
open scoped IsMulCommutative

/-- An elementary subgroup central in a Sylow admits an odd-core supplement in which
its normal closure is elementary and remains in the chosen Sylow subgroup. -/
public theorem exists_supplement_of_central_elementary_subgroup
    {G : Type*} [Group G] [Finite G] (hsol : Group.IsSolvable G)
    (T : Sylow 2 G) (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hET : E ≤ T) (hEc : E ≤ centralizer (T : Set G)) :
    ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧ E ≤ H ∧
      H ⊔ pPrimeCore 2 G = ⊤ ∧
      IsElementaryAbelian 2 (normalClosure (E.subgroupOf H : Set H)) ∧
      (normalClosure (E.subgroupOf H : Set H)).map H.subtype ≤ T := by
  let : Group.IsSolvable G := hsol
  let M := pPrimeCore 2 G
  let q := QuotientGroup.mk' M
  let f := q.comp (T : Subgroup G).subtype
  let Tb : Sylow 2 (G ⧸ M) := T.mapSurjective (QuotientGroup.mk'_surjective M)
  let R := pCore 2 (G ⧸ M)
  have hfr : f.range = (Tb : Subgroup (G ⧸ M)) := by
    rw [MonoidHom.range_comp, range_subtype]
    rfl
  have hRr : R ≤ f.range := by
    rw [hfr]
    exact fitting_pCore_le_sylow Tb
  let Q₀ := R.comap f
  let Q := Q₀.map (T : Subgroup G).subtype
  have hQT : Q ≤ T := map_subtype_le Q₀
  have hQq : Q.map q = R := by
    rw [map_map]
    exact map_comap_eq_self hRr
  have hTn : (T : Subgroup G) ≤ normalizer (Q : Set G) := by
    simpa only [Q₀.normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      Q₀.le_normalizer_map (T : Subgroup G).subtype
  have hER : E.map q ≤ R := by
    apply le_trans ?_ (centralizer_sylow_le_pCore_of_pPrimeCore_eq_bot
      (inferInstance : Group.IsSolvable (G ⧸ M))
      (pPrimeCore_quotient_pPrimeCore_eq_bot 2) Tb)
    rintro _ ⟨e, he, rfl⟩ t ht
    change t ∈ (T : Subgroup G).map q at ht
    obtain ⟨s, hs, rfl⟩ := ht
    simpa only [map_mul] using congrArg q (hEc he s hs)
  have hEQ : E ≤ Q := by
    intro e he
    exact ⟨⟨e, hET he⟩, hER (mem_map_of_mem q he), rfl⟩
  let O := omega₁ (center Q) (p := 2)
  let Z := O.map (center Q).subtype
  let B := Z.map Q.subtype
  let : O.Characteristic := omega₁_characteristic _
  let : Z.Characteristic := characteristic_of_characteristic_of_characteristic
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map_subtype
  have hEB : E ≤ B := by
    intro e he
    have hec : (⟨e, hEQ he⟩ : Q) ∈ center Q := by
      apply mem_center_iff.mpr
      intro x
      exact Subtype.ext (hEc he x (hQT x.property))
    refine ⟨⟨e, hEQ he⟩, ⟨⟨⟨e, hEQ he⟩, hec⟩, subset_closure ?_, rfl⟩, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) e he
  let H := normalizer (Q : Set G)
  have hBH : B ≤ H := (map_subtype_le Z).trans le_normalizer
  have hEH : E ≤ H := hET.trans hTn
  let : (B.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hBH).mpr
      (normalizer_le_normalizer_characteristic_image Q Z)
  let : IsElementaryAbelian 2 (B.subgroupOf H) := IsElementaryAbelian.subgroupOf hBH
  have hcl : normalClosure (E.subgroupOf H : Set H) ≤ B.subgroupOf H :=
    normalClosure_le_normal (fun _ hx => hEB hx)
  have hcle : IsElementaryAbelian 2 (normalClosure (E.subgroupOf H : Set H)) := {
    toIsMulCommutative := isMulCommutative_iff.mpr (by
      intro x y
      exact Subtype.ext (congrArg (fun u : B.subgroupOf H => (u : H)) (mul_comm
        (⟨x, hcl x.property⟩ : B.subgroupOf H) (⟨y, hcl y.property⟩ : B.subgroupOf H))))
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (by
      intro x
      exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
        (A := B.subgroupOf H) x (hcl x.property))) }
  refine ⟨H, hTn, hEH, ?_, hcle, ?_⟩
  · let : Fact (IsPGroup 2 Q) := ⟨T.isPGroup'.to_le hQT⟩
    have hn : H.map q = ⊤ := by
      rw [← normalizer_map_quotient_eq_map_normalizer 2 Q M inferInstance
        (pPrimeCore_coprime_card (p := 2) (G := G)), hQq]
      exact normalizer_eq_top R
    have hh := congrArg (Subgroup.comap q) hn
    simpa only [q, QuotientGroup.comap_map_mk', comap_top, sup_comm] using hh
  · exact ((map_mono hcl).trans_eq (map_subgroupOf_eq_of_le hBH)).trans
      ((map_subtype_le Z).trans hQT)
