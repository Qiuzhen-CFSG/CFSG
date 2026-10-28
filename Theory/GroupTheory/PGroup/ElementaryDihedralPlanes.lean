module
public import Stellmacher.ElementaryAbelianMaxDihedral
public import Theory.GroupTheory.DihedralGeneratedFactor
public import Theory.ElementaryAbelian.Injective

/-!
# Counting the reflection planes of an elementary-by-dihedral group

Every maximum elementary subgroup of a dihedral two-group is generated
by its central half-turn and one reflection. Reflections whose parameters
differ by a half-turn define the same plane. This bounds the family by
half the rotation order. In a direct product with an elementary group,
every maximum elementary subgroup contains that whole factor.

Source application: Aschbacher–Smith C.6.4, printed pp.168–169, the
index-two normalizer step for a maximal dihedral overgroup.
-/

public noncomputable section
open Subgroup Stellmacher DihedralGroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.ElementaryDihedral

private theorem rotation_square_center {m : ℕ} {i : ZMod m}
    (hi : (r i : DihedralGroup m) ^ 2 = 1) : r i ∈ center (DihedralGroup m) := by
  have he : i + i = 0 := r.inj (by simpa only [pow_two, r_mul_r, one_def] using hi)
  have hneg : -i = i := neg_eq_iff_add_eq_zero.mpr he
  apply mem_center_iff.mpr
  rintro (j | j)
  · simp only [r_mul_r, add_comm]
  · simp only [sr_mul_r, r_mul_sr, sub_eq_add_neg, hneg]

private theorem center_elementary {n : ℕ} (hn : 2 ≤ n) :
    IsElementaryAbelian 2 (center (DihedralGroup (2 ^ n))) := by
  rw [DihedralFrattini.center_eq_half hn]
  exact IsElementaryAbelian.zpowers_of_pow_eq_one (DihedralFrattini.half_square (by omega))

private theorem reflection_not_center {n : ℕ} (hn : 2 ≤ n) (i : ZMod (2 ^ n)) :
    sr i ∉ center (DihedralGroup (2 ^ n)) := by
  rw [DihedralFrattini.center_eq_half hn]
  rintro ⟨k,hk⟩
  simp only [r_zpow] at hk
  cases hk

/-- The elementary four-group on a reflection and the central half-turn. -/
def plane {n : ℕ} (i : ZMod (2 ^ n)) : Subgroup (DihedralGroup (2 ^ n)) :=
  center _ ⊔ zpowers (sr i)

private theorem plane_properties {n : ℕ} (hn : 2 ≤ n) (i : ZMod (2 ^ n)) :
    IsElementaryAbelian 2 (plane i) ∧ Nat.card (plane i) = 4 := by
  let := center_elementary hn
  let : IsElementaryAbelian 2 (zpowers (sr i)) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by simp [pow_two])
  have hc : zpowers (sr i) ≤ centralizer (center (DihedralGroup (2 ^ n)) : Set _) :=
    le_centralizer_iff.mp (center_le_centralizer _)
  refine ⟨IsElementaryAbelian.sup_of_le_centralizer hc,?_⟩
  rw [plane,card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hc.trans (Subgroup.centralizer_le_normalizer _))
    (disjoint_zpowers_of_prime_order_not_mem _ _ (orderOf_sr i) (reflection_not_center hn i)),
    DihedralGroup.center_card_of_equiv hn (MulEquiv.refl _),Nat.card_zpowers,orderOf_sr]

private theorem plane_max {n : ℕ} (hn : 2 ≤ n) (i : ZMod (2 ^ n)) :
    plane i ∈ elementaryAbelianMaxSubgroups ⊤ :=
  (dihedral_maxFamily_iff_card_four hn _).mpr (plane_properties hn i)

/-- Every maximum elementary subgroup is the plane on one of its reflections. -/
theorem max_eq_plane {n : ℕ} (hn : 2 ≤ n)
    (A : Subgroup (DihedralGroup (2 ^ n))) (hA : A ∈ elementaryAbelianMaxSubgroups ⊤) :
    ∃ i : ZMod (2 ^ n), A = plane i := by
  have hcard := (dihedral_maxFamily_iff_card_four hn A).mp hA |>.2
  let := hA.2.1
  have hnot : ¬ A ≤ center (DihedralGroup (2 ^ n)) := by
    intro h
    have hb := card_le_of_le h
    rw [hcard,DihedralGroup.center_card_of_equiv hn (MulEquiv.refl _)] at hb
    omega
  obtain ⟨a,ha,haZ⟩ := SetLike.not_le_iff_exists.mp hnot
  cases a with
  | r i => exact (haZ (rotation_square_center (elemPow_eq_one_of_isElementaryAbelian _ ha))).elim
  | sr i =>
    have hZA : center (DihedralGroup (2 ^ n)) ≤ A := by
      let := center_elementary hn
      have hc : center (DihedralGroup (2 ^ n)) ≤ centralizer (A : Set _) := center_le_centralizer _
      have he : IsElementaryAbelian 2 (A ⊔ center (DihedralGroup (2 ^ n)) : Subgroup _) :=
        IsElementaryAbelian.sup_of_le_centralizer hc
      have heq : A ⊔ center (DihedralGroup (2 ^ n)) = A :=
        (eq_of_le_of_card_ge le_sup_left (hA.2.2 _ le_top he)).symm
      exact heq ▸ le_sup_right
    refine ⟨i,(eq_of_le_of_card_ge (sup_le hZA (zpowers_le.mpr ha)) ?_).symm⟩
    change Nat.card A ≤ Nat.card (plane i)
    rw [hcard,(plane_properties hn i).2]

private theorem plane_eq_reduced {n : ℕ} (hn : 2 ≤ n) (i : ZMod (2 ^ n)) :
    ∃ j : Fin (2 ^ (n - 1)), plane i = plane (j.val : ZMod (2 ^ n)) := by
  have hp : 2 ^ n = 2 ^ (n - 1) * 2 := by
    rw [← pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ n)]
  by_cases hi : i.val < 2 ^ (n - 1)
  · refine ⟨⟨i.val,hi⟩,?_⟩
    rw [ZMod.natCast_zmod_val]
  · have hv := ZMod.val_lt i
    have hj : i.val - 2 ^ (n - 1) < 2 ^ (n - 1) := by omega
    let j : Fin (2 ^ (n - 1)) := ⟨i.val - 2 ^ (n - 1),hj⟩
    have he : (j.val : ZMod (2 ^ n)) + (2 ^ (n - 1) : ℕ) = i := by
      rw [← Nat.cast_add,show j.val + 2 ^ (n - 1) = i.val by dsimp [j]; omega,
        ZMod.natCast_zmod_val]
    have hz : r (2 ^ (n - 1) : ℕ) ∈ plane (j.val : ZMod (2 ^ n)) := by
      apply mem_sup_left
      rw [DihedralFrattini.center_eq_half hn]
      exact mem_zpowers _
    have hs : sr i ∈ plane (j.val : ZMod (2 ^ n)) := by
      have hh := (plane (j.val : ZMod (2 ^ n))).mul_mem
        (mem_sup_right (mem_zpowers (sr (j.val : ZMod (2 ^ n))))) hz
      simpa only [sr_mul_r,he] using hh
    refine ⟨j,eq_of_le_of_card_ge (sup_le le_sup_left (zpowers_le.mpr hs)) ?_⟩
    rw [(plane_properties hn _).2,(plane_properties hn _).2]

/-- There are at most 2^(n-1) maximum elementary four-groups. -/
theorem max_family_card_le {n : ℕ} (hn : 2 ≤ n) :
    Nat.card {A : Subgroup (DihedralGroup (2 ^ n)) // A ∈ elementaryAbelianMaxSubgroups ⊤}
      ≤ 2 ^ (n - 1) := by
  let f : Fin (2 ^ (n - 1)) →
      {A : Subgroup (DihedralGroup (2 ^ n)) // A ∈ elementaryAbelianMaxSubgroups ⊤} :=
    fun j => ⟨plane (j.val : ZMod (2 ^ n)),plane_max hn _⟩
  have hf : Function.Surjective f := by
    rintro ⟨A,hA⟩
    obtain ⟨i,rfl⟩ := max_eq_plane hn A hA
    obtain ⟨j,hj⟩ := plane_eq_reduced hn i
    exact ⟨j,Subtype.ext hj.symm⟩
  simpa only [Nat.card_fin] using Nat.card_le_card_of_surjective f hf

/-- The plane on a reflection is its full centralizer. -/
theorem reflection_centralizer {n : ℕ} (i : ZMod (2 ^ n)) :
    centralizer ({sr i} : Set (DihedralGroup (2 ^ n))) = plane i := by
  apply le_antisymm
  · intro a ha
    have hc := mem_centralizer_singleton_iff.mp ha
    cases a with
    | r j =>
      have he : i - j = i + j := sr.inj hc
      have hj : j + j = 0 := by linear_combination -he
      have hz : r j ∈ center (DihedralGroup (2 ^ n)) :=
        rotation_square_center (by simp only [pow_two,r_mul_r,hj,r_zero])
      exact mem_sup_left hz
    | sr j =>
      have he : i - j = j - i := r.inj hc
      have hj : (j-i)+(j-i)=0 := by linear_combination -he
      have hz : r (j-i) ∈ center (DihedralGroup (2 ^ n)) :=
        rotation_square_center (by simp only [pow_two,r_mul_r,hj,r_zero])
      have hh := (plane i).mul_mem (mem_sup_right (mem_zpowers (sr i))) (mem_sup_left hz)
      simpa only [sr_mul_r,add_sub_cancel] using hh
  · refine sup_le (center_le_centralizer _) ?_
    exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)

/-- A noncentral involution has a maximum elementary centralizer in the
actual elementary-by-dihedral product. -/
theorem involution_centralizer_max {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] {n : ℕ} (hn : 2 ≤ n)
    (x : E × DihedralGroup (2 ^ n)) (hx : x ^ 2 = 1)
    (hxZ : x ∉ center (E × DihedralGroup (2 ^ n))) :
    centralizer ({x} : Set (E × DihedralGroup (2 ^ n))) ∈ elementaryAbelianMaxSubgroups ⊤ := by
  obtain ⟨a,b⟩ := x
  have hb : b ^ 2 = 1 := congrArg Prod.snd hx
  cases b with
  | r i =>
    apply (hxZ ?_).elim
    rw [Subgroup.center_prod,mem_prod,center_eq_top]
    exact ⟨mem_top _,rotation_square_center hb⟩
  | sr i =>
    have heq : centralizer ({(a,sr i)} : Set (E × DihedralGroup (2 ^ n))) =
        (⊤ : Subgroup E).prod (plane i) := by
      ext y
      simp only [mem_centralizer_singleton_iff,mem_prod,mem_top,true_and]
      rw [← reflection_centralizer,mem_centralizer_singleton_iff]
      exact ⟨fun h => congrArg Prod.snd h, fun h => Prod.ext (mul_comm _ _) h⟩
    rw [heq,← top_prod_top]
    have hE : (⊤ : Subgroup E) ∈ elementaryAbelianMaxSubgroups ⊤ :=
      ⟨le_rfl, IsElementaryAbelian.of_injective (⊤ : Subgroup E).subtype
        (⊤ : Subgroup E).subtype_injective, fun _ _ _ => card_le_of_le le_top⟩
    exact maxFamily_prod hE (plane_max hn i)

/-- Ambient centralizers of noncentral involutions belong to the literal
maximum elementary family of the overgroup. -/
theorem involution_centralizer_max_ambient {G E : Type*} [Group G] [Group E]
    [Finite G] [Finite E] [IsElementaryAbelian 2 E]
    (M : Subgroup G) {n : ℕ} (hn : 2 ≤ n)
    (e : M ≃* E × DihedralGroup (2 ^ n)) (x : G) (hxM : x ∈ M)
    (hx2 : x ^ 2 = 1) (hxZ : x ∉ M ⊓ centralizer (M : Set G)) :
    M ⊓ centralizer ({x} : Set G) ∈ elementaryAbelianMaxSubgroups M := by
  let xM : M := ⟨x,hxM⟩
  have hsq : (e xM) ^ 2 = 1 := by rw [← map_pow, show xM ^ 2 = 1 from Subtype.ext hx2,map_one]
  have hnc : e xM ∉ center (E × DihedralGroup (2 ^ n)) := by
    intro h
    apply hxZ
    refine ⟨hxM,?_⟩
    intro a ha
    exact congrArg Subtype.val (show (⟨a,ha⟩ : M) * xM = xM * ⟨a,ha⟩ from
      e.injective (by simpa only [map_mul] using mem_center_iff.mp h (e ⟨a,ha⟩)))
  have hm := involution_centralizer_max hn (e xM) hsq hnc
  refine (maxFamily_equiv_iff M e.symm _).mpr ⟨_,hm,?_⟩
  apply le_antisymm
  · rintro a ⟨ha,hac⟩
    refine ⟨e ⟨a,ha⟩,mem_centralizer_singleton_iff.mpr ?_,?_⟩
    · simpa only [← map_mul] using congrArg e (show (⟨a,ha⟩ : M)*xM=xM*⟨a,ha⟩ from
        Subtype.ext (mem_centralizer_singleton_iff.mp hac))
    · exact congrArg Subtype.val (e.symm_apply_apply _)
  · rintro a ⟨b,hb,rfl⟩
    refine ⟨(e.symm b).property,mem_centralizer_singleton_iff.mpr ?_⟩
    exact congrArg Subtype.val (show e.symm b * xM = xM * e.symm b from e.injective (by
      simpa only [map_mul,e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hb))

/-- The same family bound in a supplied elementary-by-dihedral overgroup. -/
theorem max_family_card_le_ambient {G E : Type*} [Group G] [Group E]
    [Finite G] [Finite E] [IsElementaryAbelian 2 E]
    (M : Subgroup G) {n : ℕ} (hn : 2 ≤ n)
    (e : M ≃* E × DihedralGroup (2 ^ n)) :
    Nat.card {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups M} ≤ 2 ^ (n - 1) := by
  have hE : (⊤ : Subgroup E) ∈ elementaryAbelianMaxSubgroups ⊤ :=
    ⟨le_rfl, IsElementaryAbelian.of_injective (⊤ : Subgroup E).subtype
      (⊤ : Subgroup E).subtype_injective, fun _ _ _ => card_le_of_le le_top⟩
  let f : {A : Subgroup (DihedralGroup (2 ^ n)) // A ∈ elementaryAbelianMaxSubgroups ⊤} →
      {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups M} := fun A =>
    ⟨((⊤ : Subgroup E).prod A.val).map (M.subtype.comp e.symm.toMonoidHom),
      (maxFamily_equiv_prod_iff M e.symm _).mpr ⟨⊤,hE,A.val,A.property,rfl⟩⟩
  have hf : Function.Surjective f := by
    rintro ⟨A,hA⟩
    obtain ⟨B,hB,C,hC,heq⟩ := (maxFamily_equiv_prod_iff M e.symm A).mp hA
    have hBtop : B = ⊤ := eq_of_le_of_card_ge le_top (hB.2.2 ⊤ le_top hE.2.1)
    subst B
    exact ⟨⟨C,hC⟩,Subtype.ext heq.symm⟩
  exact (Nat.card_le_card_of_surjective f hf).trans (max_family_card_le hn)

end Theory.GroupTheory.ElementaryDihedral
