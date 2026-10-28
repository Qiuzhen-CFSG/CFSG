module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.Geometry
public import Theory.Mathieu.M12.ValueBoundParabolics.SecondQuotient

/-!
# The second two-core, its quotient, and the local Sylow normalizer

Conjugation on the three nonidentity elements of the fixed natural four
is onto S₃. Its kernel has order 64 and equals the intrinsic two-core;
its actual image in the carrier is the centralizer of that four. Finally,
the index-three Sylow normalizer is the Sylow subgroup itself, since a
larger normalizer would contradict the computed two-core order.
Source: Aschbacher--Smith, F.1.12(I)(13), p.263, and 14.2.21, p.988.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
open M12SmallPair.FirstCore
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def naturalLabel : Fin 3 → Carrier := ![z, v, z * v]

theorem naturalLabel_injective : Function.Injective naturalLabel := by decide +kernel

theorem mem_natural_iff_label (g : Carrier) :
    g ∈ natural ↔ g = 1 ∨ ∃ i, g = naturalLabel i := by
  rw [mem_natural]
  simp [naturalLabel, Fin.exists_fin_succ]

def naturalRepresentation : secondParabolic →* Equiv.Perm Carrier :=
  conjugationPermHom.comp secondParabolic.subtype

theorem natural_stable (g : secondParabolic) (i : Fin 3) :
    ∃ j, naturalRepresentation g (naturalLabel i) = naturalLabel j := by
  have hi : naturalLabel i ∈ natural :=
    (mem_natural_iff_label _).mpr (Or.inr ⟨i, rfl⟩)
  have hm := (Subgroup.mem_set_normalizer_iff.mp g.property (naturalLabel i)).mp hi
  rcases (mem_natural_iff_label _).mp hm with he | he
  · have hn : ∀ i, naturalLabel i ≠ 1 := by decide +kernel
    exact (hn i ((MulAut.conj (g : Carrier)).injective
      (he.trans (map_one (MulAut.conj (g : Carrier))).symm))).elim
  · exact he

/-- Conjugation on the three nonidentity elements of the marked normal four. -/
def secondQuotientMap : secondParabolic →* Equiv.Perm (Fin 3) :=
  restrictAction naturalRepresentation naturalLabel naturalLabel_injective natural_stable

theorem secondQuotientMap_eq (g : secondParabolic) (s : Equiv.Perm (Fin 3))
    (h : ∀ i, (g : Carrier) * naturalLabel i * (g : Carrier)⁻¹ = naturalLabel (s i)) :
    secondQuotientMap g = s := by
  apply Equiv.ext
  intro i
  apply naturalLabel_injective
  exact (restrictAction_spec naturalRepresentation naturalLabel naturalLabel_injective
    natural_stable g i).symm.trans (h i)

theorem secondQuotientMap_surjective : Function.Surjective secondQuotientMap := by
  let l := movement (QuaternionSwapModel.leftEmbedding (QuaternionGroup.a 1))
  have hl : l ∈ secondParabolic := (movement_mem_overlap _).2
  apply surjective_of_two_images secondQuotientMap
    ⟨secondActor, secondActor_mem_secondParabolic⟩ ⟨l, hl⟩
    (List.formPerm [0, 1, 2]) (Equiv.swap 1 2)
  · apply secondQuotientMap_eq
    decide +kernel
  · apply secondQuotientMap_eq
    change ∀ i, l * naturalLabel i * l⁻¹ = naturalLabel ((Equiv.swap 1 2) i)
    dsimp only [l]
    rw [movement_left]
    decide +kernel
  · decide +kernel

variable (m : InnerModel)
include m

theorem card_secondKernel : Nat.card secondQuotientMap.ker = 64 := by
  have h := secondQuotientMap.ker.card_mul_index
  rw [Subgroup.index_ker, secondQuotientMap.range_eq_top_of_surjective secondQuotientMap_surjective,
    Subgroup.card_top, Nat.card_perm, Nat.card_fin, card_secondParabolic m] at h
  norm_num [Nat.factorial] at h
  change Nat.card secondQuotientMap.ker * 6 = 384 at h
  omega

theorem second_pCore_eq_kernel : pCore 2 secondParabolic = secondQuotientMap.ker := by
  have hkerLe : secondQuotientMap.ker ≤ pCore 2 secondParabolic :=
    le_sSup ⟨inferInstance, IsPGroup.of_card (n := 6) (card_secondKernel m)⟩
  have himageNormal : ((pCore 2 secondParabolic).map secondQuotientMap).Normal :=
    Subgroup.Normal.map inferInstance secondQuotientMap secondQuotientMap_surjective
  have himageLe : (pCore 2 secondParabolic).map secondQuotientMap ≤ pCore 2 (Equiv.Perm (Fin 3)) :=
    le_sSup ⟨himageNormal, pCore_isPGroup.map secondQuotientMap⟩
  apply le_antisymm ?_ hkerLe
  intro x hx
  apply MonoidHom.mem_ker.mpr
  have h := himageLe (Subgroup.mem_map.mpr ⟨x,hx,rfl⟩)
  simpa only [local_perm_three_core_eq_bot, Subgroup.mem_bot] using h

def secondCoreQuotient : secondParabolic ⧸ pCore 2 secondParabolic ≃* Equiv.Perm (Fin 3) :=
  (QuotientGroup.quotientMulEquivOfEq (second_pCore_eq_kernel m)).trans
    (QuotientGroup.quotientKerEquivOfSurjective secondQuotientMap secondQuotientMap_surjective)

theorem card_secondCore : Nat.card (pCore 2 secondParabolic) = 64 := by
  rw [second_pCore_eq_kernel m, card_secondKernel m]

theorem secondCore_mem_iff (g : secondParabolic) :
    g ∈ pCore 2 secondParabolic ↔ (g : Carrier) ∈ Subgroup.centralizer (natural : Set Carrier) := by
  rw [second_pCore_eq_kernel m, MonoidHom.mem_ker]
  constructor
  · intro hg x hx
    rcases (mem_natural_iff_label x).mp hx with rfl | ⟨i,rfl⟩
    · simp
    · have h := restrictAction_spec naturalRepresentation naturalLabel
        naturalLabel_injective natural_stable g i
      change (g : Carrier) * naturalLabel i * (g : Carrier)⁻¹ = naturalLabel (secondQuotientMap g i) at h
      rw [hg] at h
      have he := congrArg (fun x : Carrier => x * (g : Carrier)) h
      simpa only [Equiv.Perm.one_apply, mul_assoc, inv_mul_cancel, mul_one] using he.symm
  · intro hg
    apply secondQuotientMap_eq
    intro i
    change (g : Carrier) * naturalLabel i * (g : Carrier)⁻¹ = naturalLabel i
    have h := hg (naturalLabel i) ((mem_natural_iff_label _).mpr (Or.inr ⟨i,rfl⟩))
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]

theorem secondCore_image : (pCore 2 secondParabolic).map secondParabolic.subtype =
    Subgroup.centralizer (natural : Set Carrier) := by
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (secondCore_mem_iff m x).mp hx
  · intro hg
    have hn : g ∈ secondParabolic := Subgroup.centralizer_le_normalizer _ hg
    exact ⟨⟨g,hn⟩,(secondCore_mem_iff m _).mpr hg,rfl⟩

theorem second_sylow_normalizer :
    secondParabolic ⊓ Subgroup.normalizer (overlap : Set Carrier) = overlap := by
  let T := (commonSylow m).subtype (show overlap ≤ secondParabolic from inf_le_right)
  have hT : Nat.card T = 128 := by
    change Nat.card (overlap.subgroupOf secondParabolic) = 128
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show overlap ≤ secondParabolic from inf_le_right)).toEquiv, card_overlap m]
  have hi : (T : Subgroup secondParabolic).index = 3 := by
    have h := (T : Subgroup secondParabolic).index_mul_card
    rw [card_secondParabolic m,hT] at h
    omega
  have hn : Subgroup.normalizer ((T : Subgroup secondParabolic) : Set secondParabolic) = T := by
    have hd := Subgroup.index_dvd_of_le (T : Subgroup secondParabolic).le_normalizer
    rw [hi] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · have hn : (T : Subgroup secondParabolic).Normal :=
        Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp h)
      have hl : (T : Subgroup secondParabolic) ≤ pCore 2 secondParabolic := le_sSup ⟨hn,T.isPGroup'⟩
      have hb := Subgroup.card_le_of_le hl
      rw [hT,card_secondCore m] at hb
      omega
    · apply (Subgroup.eq_of_le_of_card_ge (T : Subgroup secondParabolic).le_normalizer _).symm
      have hm := (Subgroup.normalizer ((T : Subgroup secondParabolic) : Set secondParabolic)).index_mul_card
      rw [h,card_secondParabolic m] at hm
      rw [hT]
      omega
  change Subgroup.normalizer (overlap.subgroupOf secondParabolic : Set secondParabolic) =
    overlap.subgroupOf secondParabolic at hn
  rw [← Subgroup.subgroupOf_normalizer_eq (show overlap ≤ secondParabolic from inf_le_right)] at hn
  ext g
  constructor
  · rintro ⟨hg,hgN⟩
    exact (show (⟨g,hg⟩ : secondParabolic) ∈ overlap.subgroupOf secondParabolic from hn ▸ hgN)
  · intro hg
    exact ⟨hg.2,Subgroup.le_normalizer hg⟩

end Sporadic.Mathieu.M12ExceptionalExtension.SecondCoordinates
