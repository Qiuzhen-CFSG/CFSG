module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.FiveCore.SourceCompletion.Quaternion
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The five-displacement decomposition in J.4.1(3)

For the original Sylow five-subgroup, put Q₅ = [Q,B₅]. Coprime action
splits Q into Q₅ and its quaternion centralizer, and splits U into [U,B₅]
and Z. Since [Q,U] = Z and Q normalizes Q₅, the latter splitting forces
U ≤ Q₅. In the literal quotient H/U, the images of Q₅ and C_Q(B₅) are
disjoint by coprime action on the elementary abelian Q/U. The fixed image
has order four and Q/U has order sixty-four, so the moving image has order
sixteen. All maps retain the original subgroup inclusions and quotient.

Source: Aschbacher–Smith, J.4.1(3), printed p.440 (PDF p.451).
-/

@[expose] public section
noncomputable section

open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)
  (B5 : Sylow 5 d.toTypeRuSetup.H)

abbrev Q₅ : Subgroup G := ⁅d.toTypeRuSetup.Q,B5Image B5⁆

theorem Q₅_le_Q : Q₅ d B5 ≤ d.toTypeRuSetup.Q :=
  le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans d.ru2.six.normalized)

theorem Q₅_normalized : d.toTypeRuSetup.Q ≤ normalizer (Q₅ d B5) :=
  normalizer_commutator_ge_left _ _

theorem Q_eq_Q₅_sup_CQ : d.toTypeRuSetup.Q = Q₅ d B5 ⊔ CQ B5 := by
  apply eq_commutator_sup_centralizer_of_solvable_coprime
  · exact (map_subtype_le _).trans d.ru2.six.normalized
  · let := (isPGroup_pCoreIn 2 d.toTypeRuSetup.H).isNilpotent
    infer_instance
  · rw [B5Image_card d.card_Z B5,d.ru2.card_Q d.card_Z]
    decide

theorem U_eq_commutator_sup_Z :
    d.toTypeRuSetup.U = ⁅d.toTypeRuSetup.U,B5Image B5⁆ ⊔ d.toTypeRuSetup.Z := by
  have he : d.toTypeRuSetup.U ⊓ centralizer (B5Image B5 : Set G) = d.toTypeRuSetup.Z := by
    apply le_antisymm
    · intro u hu
      have hh : u ∈ CQ B5 ⊓ d.toTypeRuSetup.U := ⟨⟨d.ru2.six.kernel_le hu.1,hu.2⟩,hu.1⟩
      rwa [five_centralizer_inf_U] at hh
    · intro z hz
      exact ⟨d.ru2.natural.kernel_le hz,((five_centralizer_inf_U B5).symm ▸ hz).1.2⟩
  rw [← he]
  apply eq_commutator_sup_centralizer_of_solvable_coprime
  · exact (map_subtype_le _).trans d.ru2.natural.normalized
  · let := d.elementary_U
    exact Group.isSolvable_of_comm fun x y => mul_comm x y
  · rw [B5Image_card d.card_Z B5,d.ru2.card_U d.card_Z]
    decide

theorem U_le_Q₅ : d.toTypeRuSetup.U ≤ Q₅ d B5 := by
  have hMU : ⁅d.toTypeRuSetup.U,B5Image B5⁆ ≤ d.toTypeRuSetup.U :=
    le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans d.ru2.natural.normalized)
  have hM5 : ⁅d.toTypeRuSetup.U,B5Image B5⁆ ≤ Q₅ d B5 :=
    commutator_mono d.ru2.six.kernel_le le_rfl
  have hZQ : d.toTypeRuSetup.Z ≤ centralizer (d.toTypeRuSetup.Q : Set G) :=
    le_centralizer_iff.mpr (pCoreIn_le 2 _)
  have he := commutator_eq_of_centralizing_sup
    (show d.toTypeRuSetup.Z ⊔ ⁅d.toTypeRuSetup.U,B5Image B5⁆ = d.toTypeRuSetup.U by
      rw [sup_comm]; exact (U_eq_commutator_sup_Z d B5).symm)
    hZQ ((hMU.trans d.ru2.six.kernel_le).trans d.toTypeRuSetup.Q.le_normalizer)
  have hZ5 : d.toTypeRuSetup.Z ≤ Q₅ d B5 := by
    rw [← d.commutator_Q_U,← he]
    exact (commutator_mono le_rfl hM5).trans
      (le_normalizer_iff_commutator_le_right.mp (Q₅_normalized d B5))
  rw [U_eq_commutator_sup_Z d B5]
  exact sup_le hM5 hZ5

instance U_normal : (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.H).Normal :=
  normal_subgroupOf_of_le_normalizer d.ru2.natural.normalized

abbrev Hat := d.toTypeRuSetup.H ⧸ d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.H

def hatMap : d.toTypeRuSetup.H →* Hat d :=
  QuotientGroup.mk' (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.H)

abbrev hat (A : Subgroup G) : Subgroup (Hat d) :=
  (A.subgroupOf d.toTypeRuSetup.H).map (hatMap d)

theorem hatMap_eq_one (h : d.toTypeRuSetup.H) :
    hatMap d h = 1 ↔ (h:G) ∈ d.toTypeRuSetup.U := QuotientGroup.eq_one_iff _

theorem hat_sup {A B : Subgroup G} (hA : A ≤ d.toTypeRuSetup.H)
    (hB : B ≤ d.toTypeRuSetup.H) : hat d (A ⊔ B) = hat d A ⊔ hat d B := by
  rw [hat,subgroupOf_sup hA hB,Subgroup.map_sup]

theorem hat_commutator {A B : Subgroup G} (hA : A ≤ d.toTypeRuSetup.H)
    (hB : B ≤ d.toTypeRuSetup.H) : hat d ⁅A,B⁆ = ⁅hat d A,hat d B⁆ := by
  have he : ⁅A,B⁆.subgroupOf d.toTypeRuSetup.H =
      ⁅A.subgroupOf d.toTypeRuSetup.H,B.subgroupOf d.toTypeRuSetup.H⁆ := by
    apply (Subgroup.map_injective d.toTypeRuSetup.H.subtype_injective)
    rw [map_subgroupOf_eq_of_le ((Subgroup.commutator_le_sup _ _).trans (sup_le hA hB)),
      map_commutator,map_subgroupOf_eq_of_le hA,map_subgroupOf_eq_of_le hB]
  rw [hat,he,map_commutator]

theorem hat_card (A : Subgroup G) (hA : A ≤ d.toTypeRuSetup.H) :
    Nat.card (hat d A) * Nat.card (A ⊓ d.toTypeRuSetup.U : Subgroup G) = Nat.card A := by
  let f := (hatMap d).comp (inclusion hA)
  have hk : f.ker = (A ⊓ d.toTypeRuSetup.U).subgroupOf A := by
    ext a
    change hatMap d (inclusion hA a) = 1 ↔ (a:G) ∈ A ⊓ d.toTypeRuSetup.U
    rw [hatMap_eq_one]
    exact ⟨fun h => ⟨a.property,h⟩,fun h => h.2⟩
  have hr : f.range = hat d A := by
    rw [MonoidHom.range_comp]
    congr 1
    exact (inclusion_range hA)
  have hh := f.ker.index_mul_card
  rw [index_ker,hr,hk,Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at hh
  exact hh

theorem hat_Q_elementary : IsElementaryAbelian 2 (hat d d.toTypeRuSetup.Q) := by
  have hlift (x : hat d d.toTypeRuSetup.Q) :
      ∃ q : d.toTypeRuSetup.Q, hatMap d (inclusion (pCoreIn_le 2 _) q) = (x:Hat d) := by
    obtain ⟨h,hh,he⟩ := x.property
    exact ⟨⟨h,hh⟩,he⟩
  have hs (q : d.toTypeRuSetup.Q) : (q:G)^2 ∈ d.toTypeRuSetup.U := by
    change ((q^2 : d.toTypeRuSetup.Q):G) ∈ d.toTypeRuSetup.U
    apply (d.ru2.six.coordinates_eq_one_iff (q^2)).mp
    rw [map_pow]
    change (2:ℕ) • (d.ru2.six.coordinates q).toAdd = 0
    ext j
    exact CharTwo.two_nsmul _
  refine {toIsMulCommutative := ⟨⟨?_⟩⟩,exponent_dvd_p := ?_}
  · intro x y
    obtain ⟨a,ha⟩ := hlift x
    obtain ⟨b,hb⟩ := hlift y
    apply Subtype.ext
    change (x:Hat d)*(y:Hat d) = (y:Hat d)*(x:Hat d)
    rw [← ha,← hb,← commutatorElement_eq_one_iff_mul_comm,← map_commutatorElement]
    apply (hatMap_eq_one d _).mpr
    apply (d.ru2.six.coordinates_eq_one_iff ⁅a,b⁆).mp
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    obtain ⟨a,ha⟩ := hlift x
    apply Subtype.ext
    change (x:Hat d)^2 = 1
    rw [← ha,← map_pow]
    exact (hatMap_eq_one d _).mpr (hs a)

theorem hat_Q_card : Nat.card (hat d d.toTypeRuSetup.Q) = 64 := by
  have h := hat_card d d.toTypeRuSetup.Q (pCoreIn_le 2 _)
  rw [inf_of_le_right d.ru2.six.kernel_le,d.ru2.card_U d.card_Z,d.ru2.card_Q d.card_Z] at h
  omega

theorem hat_CQ_card : Nat.card (hat d (CQ B5)) = 4 := by
  have h := hat_card d (CQ B5) ((five_centralizer_le_HC B5).trans inf_le_left)
  rw [five_centralizer_inf_U,d.card_Z,five_centralizer_card] at h
  omega

theorem hat_mono {A B : Subgroup G} (h : A ≤ B) : hat d A ≤ hat d B :=
  map_mono (comap_mono h)

theorem hat_B5_card : Nat.card (hat d (B5Image B5)) = 5 := by
  have hd : Disjoint (B5Image B5) d.toTypeRuSetup.U := by
    apply disjoint_of_coprime_natCard
    rw [B5Image_card d.card_Z B5,d.ru2.card_U d.card_Z]
    decide
  have hc := hat_card d (B5Image B5) (map_subtype_le _)
  rw [hd.eq_bot,card_bot,mul_one,B5Image_card d.card_Z B5] at hc
  exact hc

theorem hat_Q_split :
    hat d d.toTypeRuSetup.Q = hat d (CQ B5) ⊔ hat d (Q₅ d B5) ∧
    Disjoint (hat d (CQ B5)) (hat d (Q₅ d B5)) := by
  have hCQH := (five_centralizer_le_HC B5).trans inf_le_left
  have h5H := (Q₅_le_Q d B5).trans (pCoreIn_le 2 _)
  have hgen : hat d d.toTypeRuSetup.Q = hat d (CQ B5) ⊔ hat d (Q₅ d B5) := by
    calc
      _ = hat d (Q₅ d B5 ⊔ CQ B5) := congrArg (hat d) (Q_eq_Q₅_sup_CQ d B5)
      _ = _ := by rw [hat_sup d h5H hCQH,sup_comm]
  refine ⟨hgen,?_⟩
  let : IsElementaryAbelian 2 (hat d d.toTypeRuSetup.Q) := hat_Q_elementary d
  have hn : hat d (B5Image B5) ≤ normalizer (hat d d.toTypeRuSetup.Q) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [← hat_commutator d (pCoreIn_le 2 _) (map_subtype_le _)]
    exact hat_mono d (Q₅_le_Q d B5)
  have hcop : Nat.Coprime (Nat.card (hat d (B5Image B5)))
      (Nat.card (hat d d.toTypeRuSetup.Q)) := by
    rw [hat_B5_card,hat_Q_card]; decide
  have hd := commutator_disjoint_centralizer_of_coprime
    (hat d d.toTypeRuSetup.Q) (hat d (B5Image B5)) hn hcop
  have hC : hat d (CQ B5) ≤ hat d d.toTypeRuSetup.Q ⊓
      centralizer (hat d (B5Image B5) : Set (Hat d)) := by
    refine le_inf (hat_mono d inf_le_left) ?_
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← hat_commutator d hCQH (map_subtype_le _),
      commutator_eq_bot_iff_le_centralizer.mpr (show CQ B5 ≤ centralizer (B5Image B5 : Set G) from inf_le_right)]
    simp only [hat,bot_subgroupOf,Subgroup.map_bot]
  have he : ⁅hat d d.toTypeRuSetup.Q,hat d (B5Image B5)⁆ = hat d (Q₅ d B5) :=
    (hat_commutator d (pCoreIn_le 2 _) (map_subtype_le _)).symm
  rw [he] at hd
  exact hd.symm.mono_left hC

theorem hat_Q₅_card : Nat.card (hat d (Q₅ d B5)) = 16 := by
  let : IsElementaryAbelian 2 (hat d d.toTypeRuSetup.Q) := hat_Q_elementary d
  have hCQ : hat d (CQ B5) ≤ hat d d.toTypeRuSetup.Q := hat_mono d inf_le_left
  have h5 : hat d (Q₅ d B5) ≤ hat d d.toTypeRuSetup.Q := hat_mono d (Q₅_le_Q d B5)
  have hcentral : hat d (Q₅ d B5) ≤ centralizer (hat d (CQ B5) : Set (Hat d)) := by
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hCQ hy⟩ : hat d d.toTypeRuSetup.Q) ⟨x,h5 hx⟩)
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (hat d (CQ B5)) (hat d (Q₅ d B5))
    (hcentral.trans (Subgroup.centralizer_le_normalizer _))
  rw [(hat_Q_split d B5).2.eq_bot,card_bot,one_mul,← (hat_Q_split d B5).1,
    hat_Q_card,hat_CQ_card] at hc
  omega

theorem hat_Q₅_elementary : IsElementaryAbelian 2 (hat d (Q₅ d B5)) := by
  let := hat_Q_elementary d
  exact IsElementaryAbelian.of_le (hat_mono d (Q₅_le_Q d B5))

/-- J.4.1(3) on the original subgroups and the literal H/U quotient. -/
theorem five_decomposition (c : Centralizers.Choices d) :
    d.toTypeRuSetup.U ≤ Q₅ d B5 ∧
    IsElementaryAbelian 2 (hat d (Q₅ d B5)) ∧
    Nat.card (hat d (Q₅ d B5)) = 16 ∧
    Nonempty (CQ B5 ≃* QuaternionGroup 2) ∧
    hat d d.toTypeRuSetup.Q = hat d (CQ B5) ⊔ hat d (Q₅ d B5) ∧
    Disjoint (hat d (CQ B5)) (hat d (Q₅ d B5)) :=
  ⟨U_le_Q₅ d B5,hat_Q₅_elementary d B5,hat_Q₅_card d B5,
    five_centralizer_quaternion c B5,(hat_Q_split d B5).1,(hat_Q_split d B5).2⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
