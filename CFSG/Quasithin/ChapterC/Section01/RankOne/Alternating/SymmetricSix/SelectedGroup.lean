module
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Pulling the selected cubic back through the original two-core

In G/O₂(G), an invariant cubic and the actual image of R form a group of
order six. Pull back their join. Since O₂(G) ≤ R, the original R has
index three in that preimage and is its Sylow two-subgroup. Containment
of the original core gives characteristic two. The literal image of the
two-residual is exactly the selected cubic, and O₂(G) normalizes it.

Source: Aschbacher–Smith C.1.24(c), printed pp.130–131, the subgroup Y₀
and its two-residual. No full action-kernel two-group hypothesis is used.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
variable {G : Type*} [Group G] [Finite G]

def selectedGroup (R : Subgroup G) (M : Subgroup (G ⧸ pCore 2 G)) : Subgroup G :=
    (M ⊔ R.map (QuotientGroup.mk' (pCore 2 G))).comap (QuotientGroup.mk' (pCore 2 G))

omit [Finite G] in
theorem le_selectedGroup (R : Subgroup G) (M : Subgroup (G ⧸ pCore 2 G)) :
    R ≤ selectedGroup R M := by
  intro x hx
  exact mem_sup_right (mem_map_of_mem _ hx)

omit [Finite G] in
theorem core_le_selectedGroup (R : Subgroup G) (M : Subgroup (G ⧸ pCore 2 G)) :
    pCore 2 G ≤ selectedGroup R M := by
  intro x hx
  change QuotientGroup.mk' (pCore 2 G) x ∈ M ⊔ R.map (QuotientGroup.mk' (pCore 2 G))
  have he : QuotientGroup.mk' (pCore 2 G) x=1 := (QuotientGroup.eq_one_iff _).mpr hx
  rw [he]
  exact one_mem _

omit [Finite G] in
theorem selected_index_three (R : Subgroup G) (hQR : pCore 2 G ≤ R)
    (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M=3)
    (hR : Nat.card (R.map (QuotientGroup.mk' (pCore 2 G)))=2)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G))) :
    (R.subgroupOf (selectedGroup R M)).index = 3 := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let A := R.map q
  have hAcard : Nat.card A=2 := hR
  have hd : Disjoint M A := disjoint_of_coprime_natCard (by rw [hM,hR];decide)
  have hcard : Nat.card (M ⊔ A : Subgroup (G ⧸ pCore 2 G))=6 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint M A hn hd,hM,hR]
  have hi : A.relIndex (M ⊔ A) = 3 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup (G ⧸ pCore 2 G)) A (M ⊔ A) bot_le le_sup_right
    simp only [relIndex_bot_left,hAcard,hcard] at hh
    omega
  change R.relIndex (selectedGroup R M)=3
  have hh := relIndex_map_map q R (selectedGroup R M)
  rw [show q.ker = pCore 2 G from QuotientGroup.ker_mk' _,sup_of_le_left hQR,
    sup_of_le_left (core_le_selectedGroup R M)] at hh
  rw [←hh]
  change A.relIndex (((M ⊔ A).comap q).map q)=3
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _]
  exact hi

omit [Finite G] in
theorem selected_sylow (R : Subgroup G) (hpR : IsPGroup 2 R) (hQR : pCore 2 G ≤ R)
    (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M=3)
    (hR : Nat.card (R.map (QuotientGroup.mk' (pCore 2 G)))=2)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G))) :
    ∃ T : Sylow 2 (selectedGroup R M), (T : Subgroup (selectedGroup R M))=R.subgroupOf (selectedGroup R M) ∧
      (T : Subgroup (selectedGroup R M)).index=3 := by
  have hi := selected_index_three R hQR M hM hR hn
  let T := hpR.comap_subtype.toSylow (show ¬2 ∣ (R.subgroupOf (selectedGroup R M)).index by rw [hi];decide)
  exact ⟨T,rfl,hi⟩

theorem selected_characteristic_two (R : Subgroup G) (M : Subgroup (G ⧸ pCore 2 G))
    (hf : generalizedFitting G = pCore 2 G) :
    generalizedFitting (selectedGroup R M)=pCore 2 (selectedGroup R M) := by
  have hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
    rw [←hf]
    exact centralizer_generalizedFitting_le G
  exact generalizedFitting_eq_pCore_of_selfCentralizing 2
    (centralizer_pCore_le_of_pCore_le (selectedGroup R M) hc (core_le_selectedGroup R M))

theorem selected_residual_image (R : Subgroup G) (hpR : IsPGroup 2 R)
    (M : Subgroup (G ⧸ pCore 2 G)) (hM : Nat.card M=3)
    (hn : R.map (QuotientGroup.mk' (pCore 2 G)) ≤ normalizer (M : Set (G ⧸ pCore 2 G))) :
    ((pResidual 2 (selectedGroup R M)).map (selectedGroup R M).subtype).map
      (QuotientGroup.mk' (pCore 2 G))=M := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let A := R.map q
  let J := M ⊔ A
  let f : selectedGroup R M →* J := q.subgroupComap J
  have hf : Function.Surjective f := q.subgroupComap_surjective_of_surjective J (QuotientGroup.mk'_surjective _)
  let C := M.subgroupOf J
  let D := A.subgroupOf J
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le M.le_normalizer hn)
  have hC : IsPPerfect 2 C := by
    apply (pResidual_eq_top_iff 2 C).mp
    apply top_unique
    intro x _
    apply mem_pResidual_of_orderOf_coprime
    have hcard : Nat.card C=3 := (Nat.card_congr (subgroupOfEquivOfLe
      (show M ≤ J from le_sup_left)).toEquiv).trans hM
    exact (show Nat.Coprime 2 (Nat.card C) by rw [hcard];decide).of_dvd_right (orderOf_dvd_natCard x)
  have hD : IsPGroup 2 D := (hpR.map q).comap_subtype
  have hgen : C ⊔ D=⊤ := by
    rw [←subgroupOf_sup (show M ≤ J from le_sup_left) (show A ≤ J from le_sup_right)]
    exact subgroupOf_self _
  have hres : pResidual 2 J=C := pResidual_eq_of_isPPerfect_sup C D hC hD hgen
  have he : q.comp (selectedGroup R M).subtype=J.subtype.comp f := rfl
  rw [map_map,he,←map_map,map_pResidual_of_surjective 2 f hf,hres]
  exact map_subgroupOf_eq_of_le (show M ≤ J from le_sup_left)

omit [Finite G] in
theorem core_normalizes_selected_residual (R : Subgroup G) (M : Subgroup (G ⧸ pCore 2 G)) :
    pCore 2 G ≤ normalizer ((pResidual 2 (selectedGroup R M)).map
      (selectedGroup R M).subtype : Set G) := by
  exact (core_le_selectedGroup R M).trans ((selectedGroup R M).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (selectedGroup R M) (pResidual 2 (selectedGroup R M))))
end CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
