module

public import Theory.SpecificGroups.SymmetricSeven.LocalResidualModels

/-!
# Coordinates for index-three Sylow overgroups of S₇

The standard Sylow subgroup fixes `6`, preserves `{0,1}`, and preserves the
three pairs `{01,23,45}`. Two overgroups are the lifted S₆ parabolics; the
third permutes `{0,1,6}` and preserves the matching `{23,45}` on its complement.
Restriction at the fixed point identifies the first two with the existing
literal S₆ groups, including their embedded two-residuals. Sixteen explicit
words provide small certificates for subsequent local geometry checks.

Source: Aschbacher–Smith, I.5 and the final proof of 15.3.1, printed p.1155
(combined manuscript of 1 March 2004).
-/

@[expose] public section

open Equiv Subgroup
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels
namespace Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
instance : MulAction S7 (Finset (Fin 7)) where
  smul g s := s.image g
  one_smul s := by change s.image (1 : S7) = s; simp
  mul_smul g h s := by change s.image (g * h) = (s.image h).image g; simp [Finset.image_image]
instance : MulAction S7 (Finset (Finset (Fin 7))) where
  smul g s := s.image (fun t => t.image g)
  one_smul s := by change s.image (fun t => t.image (1 : S7)) = s; simp
  mul_smul g h s := by
    change s.image (fun t => t.image (g * h)) = (s.image (fun t => t.image h)).image (fun t => t.image g)
    simp only [Finset.image_image]
    congr 1
    funext t
    simp [Function.comp_def, Finset.image_image]
/-- The lifted duad stabilizer. -/
def duadOvergroup : Subgroup S7 :=
  MulAction.stabilizer S7 (6 : Fin 7) ⊓
    MulAction.stabilizer S7 ({0,1} : Finset (Fin 7))

/-- The lifted three-pair stabilizer. -/
def synthemeOvergroup : Subgroup S7 :=
  MulAction.stabilizer S7 (6 : Fin 7) ⊓
    MulAction.stabilizer S7 ({{0,1},{2,3},{4,5}} : Finset (Finset (Fin 7)))

/-- The matching stabilizer on four letters, allowing all permutations of the other three. -/
def cubicOvergroup : Subgroup S7 :=
  MulAction.stabilizer S7 ({{2,3},{4,5}} : Finset (Finset (Fin 7)))

def standardTwo : Subgroup S7 := duadOvergroup ⊓ synthemeOvergroup

instance (g : S7) : Decidable (g ∈ duadOvergroup) :=
  inferInstanceAs (Decidable (g 6 = 6 ∧ ({0,1} : Finset _).image g = {0,1}))
instance (g : S7) : Decidable (g ∈ synthemeOvergroup) :=
  inferInstanceAs (Decidable (g 6 = 6 ∧
    ({{0,1},{2,3},{4,5}} : Finset (Finset _)).image (fun t => t.image g) =
      {{0,1},{2,3},{4,5}}))
instance (g : S7) : Decidable (g ∈ cubicOvergroup) :=
  inferInstanceAs (Decidable (({{2,3},{4,5}} : Finset (Finset _)).image
    (fun t => t.image g) = {{2,3},{4,5}}))
instance (g : S7) : Decidable (g ∈ standardTwo) :=
  inferInstanceAs (Decidable (g ∈ duadOvergroup ∧ g ∈ synthemeOvergroup))

theorem liftSix_apply_castSucc (g : S6) (i : Fin 6) : liftSix g i.castSucc = (g i).castSucc := by
  change finSumFinEquiv ((Equiv.Perm.sumCongrHom _ _) (g, 1)
    (finSumFinEquiv.symm i.castSucc)) = _
  have h : finSumFinEquiv.symm i.castSucc = Sum.inl i := by
    apply finSumFinEquiv.injective
    simp
  rw [h]
  rfl

theorem liftSix_apply_last (g : S6) : liftSix g 6 = 6 := rfl
private theorem restrict_bound (g : S7) (hg : g 6 = 6) (i : Fin 6) :
    (g i.castSucc).val < 6 := by
  have hn : g i.castSucc ≠ 6 := by
    rw [← hg]
    intro h
    have hh := congrArg Fin.val (g.injective h)
    simp only [Fin.val_castSucc] at hh
    omega
  have hv := (g i.castSucc).isLt
  have hh : (g i.castSucc).val ≠ 6 := fun h => hn (Fin.ext h)
  omega
private def restrict (g : S7) (hg : g 6 = 6) : S6 where
  toFun i := ⟨(g i.castSucc).val, restrict_bound g hg i⟩
  invFun i := ⟨(g⁻¹ i.castSucc).val, restrict_bound g⁻¹
    (by change g.symm 6 = 6; exact g.symm_apply_eq.mpr hg.symm) i⟩
  left_inv i := by
    apply Fin.ext
    change (g.symm (g i.castSucc)).val = i.val
    simp
  right_inv i := by
    apply Fin.ext
    change (g (g.symm i.castSucc)).val = i.val
    simp

theorem mem_liftSix_range (g : S7) : g ∈ liftSix.range ↔ g 6 = 6 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact liftSix_apply_last g
  · intro hg
    refine ⟨restrict g hg, ?_⟩
    apply Equiv.ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (liftSix_apply_last _).trans hg.symm
    · rw [liftSix_apply_castSucc]
      rfl


private theorem lift_finset (g : S6) (s : Finset (Fin 6)) :
    (s.image Fin.castSucc).image (liftSix g) = (s.image g).image Fin.castSucc := by
  simp only [Finset.image_image]
  congr 1
  funext i
  exact liftSix_apply_castSucc g i
private theorem castSet_inj : Function.Injective (fun s : Finset (Fin 6) =>
    s.image Fin.castSucc) := Finset.image_injective (Fin.castSucc_injective 6)
private theorem lift_partition (g : S6) (s : Finset (Finset (Fin 6))) :
    (s.image (fun t => t.image Fin.castSucc)).image (fun t => t.image (liftSix g)) =
      (s.image (fun t => t.image g)).image (fun t => t.image Fin.castSucc) := by
  simp only [Finset.image_image]
  congr 1
  funext t
  exact lift_finset g t

theorem liftSix_mem_duadOvergroup (g : S6) : liftSix g ∈ duadOvergroup ↔ g ∈ duadStabilizer := by
  change liftSix g 6 = 6 ∧ _ ↔ _
  rw [liftSix_apply_last, eq_self, true_and]
  change ((pair 0 1).image Fin.castSucc).image (liftSix g) =
    (pair 0 1).image Fin.castSucc ↔ _
  rw [lift_finset, castSet_inj.eq_iff]
  rfl

theorem liftSix_mem_synthemeOvergroup (g : S6) : liftSix g ∈ synthemeOvergroup ↔ g ∈ synthemeStabilizer := by
  change liftSix g 6 = 6 ∧ _ ↔ _
  rw [liftSix_apply_last, eq_self, true_and]
  change (baseSyntheme.image (fun t => t.image Fin.castSucc)).image
    (fun t => t.image (liftSix g)) = baseSyntheme.image (fun t => t.image Fin.castSucc) ↔ _
  rw [lift_partition, (Finset.image_injective castSet_inj).eq_iff]
  rfl

theorem duadOvergroup_eq_map : duadOvergroup = duadStabilizer.map liftSix := by
  ext g
  constructor
  · intro hg
    obtain ⟨a, rfl⟩ := (mem_liftSix_range g).mpr hg.1
    exact ⟨a, (liftSix_mem_duadOvergroup a).mp hg, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (liftSix_mem_duadOvergroup a).mpr ha

theorem synthemeOvergroup_eq_map : synthemeOvergroup = synthemeStabilizer.map liftSix := by
  ext g
  constructor
  · intro hg
    obtain ⟨a, rfl⟩ := (mem_liftSix_range g).mpr hg.1
    exact ⟨a, (liftSix_mem_synthemeOvergroup a).mp hg, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact (liftSix_mem_synthemeOvergroup a).mpr ha

theorem standardTwo_eq_map : standardTwo = borel.map liftSix := by
  rw [standardTwo, duadOvergroup_eq_map, synthemeOvergroup_eq_map, ← Subgroup.map_inf _ _ liftSix liftSix_injective]
  rfl

theorem standardTwo_card : Nat.card standardTwo = 16 := by
  rw [standardTwo_eq_map, Subgroup.card_map_of_injective liftSix_injective, borel_order]

theorem duadOvergroup_card : Nat.card duadOvergroup = 48 := by
  rw [duadOvergroup_eq_map, card_map_of_injective liftSix_injective, duadStabilizer_order]

theorem synthemeOvergroup_card : Nat.card synthemeOvergroup = 48 := by
  rw [synthemeOvergroup_eq_map, card_map_of_injective liftSix_injective, synthemeStabilizer_order]

theorem standardTwo_index : standardTwo.index = 315 := by
  have h := standardTwo.card_mul_index
  rw [standardTwo_card] at h
  have hc : Nat.card S7 = 5040 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  rw [hc] at h
  omega

/-- The flag stabilizer, extended by the fixed seventh point, is Sylow in S₇. -/
noncomputable def standardSylow : Sylow 2 S7 :=
  (IsPGroup.of_card (show Nat.card standardTwo = 2 ^ 4 by
    rw [standardTwo_card]; decide)).toSylow (by rw [standardTwo_index]; decide)

@[simp] theorem standardSylow_coe : (standardSylow : Subgroup S7) = standardTwo := rfl

/-- Four binary choices enumerate the actual sixteen permutations of the Sylow subgroup. -/
def sylowWord (i : Fin 16) : S7 :=
  (swap 0 1) ^ (i.val % 2) * (swap 2 3) ^ ((i.val / 2) % 2) *
    (swap 4 5) ^ ((i.val / 4) % 2) * (swap 2 4 * swap 3 5) ^ (i.val / 8)

theorem sylowWord_mem : ∀ i, sylowWord i ∈ standardTwo := by decide +kernel

theorem sylowWord_injective : Function.Injective sylowWord := by decide +kernel

noncomputable def sylowEquiv : Fin 16 ≃ standardTwo :=
  Equiv.ofBijective (fun i => ⟨sylowWord i, sylowWord_mem i⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨fun i j h =>
      sylowWord_injective (congrArg Subtype.val h), by
        simpa only [← Nat.card_eq_fintype_card, Nat.card_fin] using standardTwo_card.symm⟩)

theorem standardTwo_le_cubic : standardTwo ≤ cubicOvergroup := by
  intro g hg
  obtain ⟨i, hi⟩ := sylowEquiv.surjective ⟨g, hg⟩
  have he : sylowWord i = g := congrArg Subtype.val hi
  rw [← he]
  exact (show ∀ i, sylowWord i ∈ cubicOvergroup by decide +kernel) i

theorem residual_duadOvergroup :
    (pResidual 2 duadOvergroup).map duadOvergroup.subtype = duadResidual7 := by
  rw [duadOvergroup_eq_map, ← map_embedded_pResidual,
    ResidualPairRecognition.residual_duad]
  rfl

theorem residual_synthemeOvergroup :
    (pResidual 2 synthemeOvergroup).map synthemeOvergroup.subtype = synthemeResidual7 := by
  rw [synthemeOvergroup_eq_map, ← map_embedded_pResidual,
    ResidualPairRecognition.residual_syntheme]
  rfl

end Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
