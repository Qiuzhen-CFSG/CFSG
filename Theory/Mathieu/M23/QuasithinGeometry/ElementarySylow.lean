module

public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow.Checks

/-!
# Elementary subgroups of order sixteen in native M23

An E16 inside the enumerated Sylow group cannot contain an exceptional
involution: its sixteen commuting elements would inject into a set of size
twelve. The union-of-two-subgroups lemma then places it in one of the two
E16 candidates. Their intersection has order four. Sylow conjugacy supplies
the global coverage theorem using conjugators in native M23.

Source: Aschbacher–Smith, H.14.2(1), printed p.397. The connection with the
intrinsic heptad and quintet cores is made in `CommonFour.Cores`.
-/

@[expose] public section
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.ElementarySylow
open FusionCertificate
set_option maxRecDepth 100000

private theorem exceptional_card_bound (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hAS : A ≤ subgroup)
    (k : Fin 8) (g : A) (hg : (g.val : Equiv.Perm (Fin 23)) = perm (exceptionalIndex k)) :
    Nat.card A ≤ 12 := by
  have witnesses (a : A) : ∃ j, (a.val : Equiv.Perm (Fin 23)) = perm (commutingIndex k j) := by
    obtain ⟨i, hi⟩ := exists_perm ⟨a.val.val, hAS a.property⟩
    have hs : ∀ x, pointTable i (pointTable i x) = x := by
      have hp := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p a
      have he := congrArg (fun z : A => (z.val : Equiv.Perm (Fin 23))) hp
      rw [pow_two] at he
      change a.val.val * a.val.val = 1 at he
      rw [← hi] at he
      exact fun x => Equiv.congr_fun he x
    have hc : ∀ x, pointTable (exceptionalIndex k) (pointTable i x) =
        pointTable i (pointTable (exceptionalIndex k) x) := by
      have he := congrArg (fun z : A => (z.val : Equiv.Perm (Fin 23)))
        (hA.toIsMulCommutative.is_comm.comm g a)
      change g.val.val * a.val.val = a.val.val * g.val.val at he
      rw [hg, ← hi] at he
      exact fun x => Equiv.congr_fun he x
    obtain ⟨j, rfl⟩ := exceptional_commuting k i hs hc
    exact ⟨j, hi.symm⟩
  classical
  let f : A → Fin 12 := fun a => (witnesses a).choose
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact ((witnesses a).choose_spec.trans (congrArg (fun j => perm (commutingIndex k j)) hab)).trans
      (witnesses b).choose_spec.symm
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- An elementary subgroup of order sixteen in the certified Sylow group is one
of the two displayed candidates. -/
theorem card16_eq_candidate (A : Subgroup M23) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16) (hAS : A ≤ subgroup) : ∃ b, A = candidate b := by
  have hcover : (A : Set M23) ⊆ (candidate 0 : Set M23) ∪ candidate 1 := by
    intro a ha
    obtain ⟨i, hi⟩ := exists_perm ⟨a.val, hAS ha⟩
    have hs : ∀ x, pointTable i (pointTable i x) = x := by
      let _ := hA
      have he := congrArg (fun z : M23 => (z : Equiv.Perm (Fin 23)))
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha)
      rw [pow_two] at he
      change a.val * a.val = 1 at he
      rw [← hi] at he
      exact fun x => Equiv.congr_fun he x
    rcases square_cases i hs with ⟨b, j, rfl⟩ | ⟨k, rfl⟩
    · fin_cases b
      · exact Or.inl ⟨j, hi⟩
      · exact Or.inr ⟨j, hi⟩
    · have hb := exceptional_card_bound A hA hAS k ⟨a, ha⟩ hi.symm
      omega
  rcases SubgroupClass.subset_union.mp hcover with h | h
  · exact ⟨0, Subgroup.eq_of_le_of_card_ge h (by rw [candidate_card, hcard])⟩
  · exact ⟨1, Subgroup.eq_of_le_of_card_ge h (by rw [candidate_card, hcard])⟩

/-- The four-group common to the two elementary Sylow candidates. -/
noncomputable def common : Subgroup M23 := candidate 0 ⊓ candidate 1

def commonIndex : Fin 4 → Fin 128 := ![0, 51, 93, 110]
private def commonPosition : Fin 2 → Fin 4 → Fin 16 := ![![0, 5, 10, 15], ![0, 6, 11, 13]]
private theorem common_position : ∀ (b : Fin 2) (i : Fin 4),
    candidateIndex b (commonPosition b i) = commonIndex i := by decide +kernel
private theorem common_injective : Function.Injective commonIndex := by decide +kernel
private theorem common_exhaustive : ∀ (i j : Fin 16),
    candidateIndex 0 i = candidateIndex 1 j → ∃ k, candidateIndex 0 i = commonIndex k := by
  decide +kernel

/-- The intersection is the literal four listed native permutations. -/
theorem mem_common (g : M23) :
    g ∈ common ↔ ∃ i, perm (commonIndex i) = (g : Equiv.Perm (Fin 23)) := by
  constructor
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    obtain ⟨k, hk⟩ := common_exhaustive i j (perm_injective (hi.trans hj.symm))
    exact ⟨k, hk ▸ hi⟩
  · rintro ⟨i, hi⟩
    constructor
    · exact ⟨commonPosition 0 i, (congrArg perm (common_position 0 i)).trans hi⟩
    · exact ⟨commonPosition 1 i, (congrArg perm (common_position 1 i)).trans hi⟩

theorem common_card : Nat.card common = 4 := by
  let f : Fin 4 → common := fun i =>
    ⟨⟨perm (commonIndex i), rawSubgroup_le (perm_mem _)⟩,
      (mem_common _).mpr ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact common_injective (perm_injective
        (congrArg (fun x : common => (x.val : Equiv.Perm (Fin 23))) h))
    · intro g
      obtain ⟨i, hi⟩ := (mem_common g.val).mp g.property
      exact ⟨i, Subtype.ext (Subtype.ext hi)⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf).symm).trans (Nat.card_fin 4)

/-- Global fusion into the two actual subgroups of the certified Sylow group. -/
theorem card16_conjugate_candidate (A : Subgroup M23) (hA : IsElementaryAbelian 2 A)
    (hcard : Nat.card A = 16) :
    ∃ (g : M23) (b : Fin 2), A = (candidate b).map (MulAut.conj g).toMonoidHom := by
  let _ := hA
  obtain ⟨P, hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M23 sylow P
  have hP : (P : Subgroup M23) = subgroup.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rfl
  let B := A.map (MulAut.conj g⁻¹).toMonoidHom
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBc : Nat.card B = 16 :=
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).trans hcard
  have hBS : B ≤ subgroup := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨x, hx, hxa⟩ := (hP ▸ hAP ha)
    have he : (MulAut.conj g⁻¹) a = x := by
      rw [← hxa]
      simp [MulAut.conj_apply, mul_assoc]
    exact he ▸ hx
  obtain ⟨b, hb⟩ := card16_eq_candidate B hB hBc hBS
  refine ⟨g, b, ?_⟩
  rw [← hb, Subgroup.map_map]
  have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id M23 := by
    ext a
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, Subgroup.map_id]

/-- Every native E16 contains an M23-conjugate of the common four-group. -/
theorem card16_contains_common_conjugate (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    ∃ g : M23, common.map (MulAut.conj g).toMonoidHom ≤ A := by
  obtain ⟨g, b, rfl⟩ := card16_conjugate_candidate A hA hcard
  refine ⟨g, Subgroup.map_mono ?_⟩
  fin_cases b
  · exact inf_le_left
  · exact inf_le_right

end Sporadic.Mathieu.M23Geometry.ElementarySylow
