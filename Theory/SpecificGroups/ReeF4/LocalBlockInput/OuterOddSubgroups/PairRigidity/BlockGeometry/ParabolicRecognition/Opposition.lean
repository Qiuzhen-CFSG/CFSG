module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.Basic
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.Parabolics
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.SplitGeneration
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.WeylOpposition

/-!
# Opposition transport for the signed Ree parabolic candidates

The already constructed fixed Weyl representative conjugates each root curve to
its negative. Negation preserves Levi support, including the nonsimple roots of
the Suzuki block. Hence opposition exchanges the signed simple blocks, their
unipotent overgroups, the intrinsic normalizers, and the parabolic candidates.

The three recognition assertions therefore need only be proved for the positive
sign. These transport theorems do not assume or establish a Borel identification,
a parabolic lattice, local indices, or the reverse root intersection.

Source: GLS3, Theorems 2.3.4–2.3.8 and 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.LocalBlockInput.PairRigidity
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup LargeLocalSeeds
open PairNormalization
variable {m : ℕ}
noncomputable local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

/-- Opposition exchanges the split blocks without changing their Levi side. -/
theorem splitSimpleBlock_map_opposition (m : ℕ) (s : Side) (positive : Bool) :
    (splitSimpleBlock m s positive).map (MulAut.conj (splitOpposition m)).toMonoidHom =
      splitSimpleBlock m s (!positive) := by
  rw [splitSimpleBlock, MonoidHom.map_closure, splitSimpleBlock]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨r, t, hr, rfl⟩, rfl⟩
    refine ⟨-r, t, ?_, splitOpposition_conj_root m r t⟩
    exact (isSimpleBlockRoot_neg_iff s positive r).mpr hr
  · rintro ⟨r, t, hr, rfl⟩
    refine ⟨rootGeneratorInGroup m (-r) t,
      ⟨-r, t, (by simpa only [Bool.not_not] using (isSimpleBlockRoot_neg_iff s (!positive) r).mpr hr), rfl⟩, ?_⟩
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, neg_neg] using
      splitOpposition_conj_root m (-r) t

/-- The same concrete representative exchanges the actual twist-fixed blocks. -/
theorem simpleBlock_map_opposition (d : LocalBlockInput m) (s : Side) (positive : Bool) :
    (simpleBlock d s positive).map (MulAut.conj (opposition d)).toMonoidHom =
      simpleBlock d s (!positive) := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    change splitOpposition m * y.val * (splitOpposition m)⁻¹ ∈ splitSimpleBlock m s (!positive)
    rw [← splitSimpleBlock_map_opposition m s positive]
    exact ⟨y.val, hy, rfl⟩
  · intro x hx
    refine ⟨(opposition d)⁻¹ * x * opposition d, ?_, ?_⟩
    · have hx' : x.val ∈ splitSimpleBlock m s (!positive) := hx
      rw [← splitSimpleBlock_map_opposition m s positive] at hx'
      obtain ⟨y, hy, he⟩ := hx'
      change (splitOpposition m)⁻¹ * x.val * splitOpposition m ∈ splitSimpleBlock m s positive
      rw [← he]
      change (splitOpposition m)⁻¹ * (splitOpposition m * y * (splitOpposition m)⁻¹) *
        splitOpposition m ∈ splitSimpleBlock m s positive
      have hc : (splitOpposition m)⁻¹ * (splitOpposition m * y * (splitOpposition m)⁻¹) *
          splitOpposition m = y := by group
      rw [hc]
      exact hy
    · simp [MulAut.conj_apply, mul_assoc]

private theorem opposition_inv (d : LocalBlockInput m) : (opposition d)⁻¹ = opposition d :=
  Subtype.ext (splitOpposition_inv m)

private theorem map_opposition_twice (d : LocalBlockInput m) (H : Subgroup d.fixedGroup) :
    (H.map (MulAut.conj (opposition d)).toMonoidHom).map
      (MulAut.conj (opposition d)).toMonoidHom = H := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj (opposition d)).toMonoidHom.comp
      (MulAut.conj (opposition d)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    change opposition d * (opposition d * x * (opposition d)⁻¹) * (opposition d)⁻¹ = x
    have hw : opposition d * opposition d = 1 := by
      nth_rw 1 [← opposition_inv d]
      exact inv_mul_cancel _
    calc
      _ = (opposition d * opposition d) * x * (opposition d * opposition d)⁻¹ := by group
      _ = x := by rw [hw, one_mul, inv_one, mul_one]
  rw [he, Subgroup.map_id]

/-- Opposition exchanges the two specified fixed unipotent subgroups. -/
theorem signedUnipotent_map_opposition (d : LocalBlockInput m) (positive : Bool) :
    (signedUnipotent d positive).map (MulAut.conj (opposition d)).toMonoidHom =
      signedUnipotent d (!positive) := by
  cases positive
  · change (oppositeUnipotent d).map _ = standardUnipotent d
    rw [← opposition_map_unipotent d, map_opposition_twice]
  · exact opposition_map_unipotent d

/-- Normalizer functoriality transports the intrinsic normalizers, without a torus identity. -/
theorem signedBorelNormalizer_map_opposition (d : LocalBlockInput m) (positive : Bool) :
    (signedBorelNormalizer d positive).map (MulAut.conj (opposition d)).toMonoidHom =
      signedBorelNormalizer d (!positive) := by
  rw [signedBorelNormalizer, map_normalizer_eq_of_bijective _ (MulAut.conj _).bijective,
    signedUnipotent_map_opposition, signedBorelNormalizer]

/-- Opposition preserves the side and reverses the sign of a parabolic candidate. -/
theorem signedParabolic_map_opposition (d : LocalBlockInput m) (s : Side) (positive : Bool) :
    (signedParabolic d s positive).map (MulAut.conj (opposition d)).toMonoidHom =
      signedParabolic d s (!positive) := by
  rw [signedParabolic, Subgroup.map_sup, signedBorelNormalizer_map_opposition,
    simpleBlock_map_opposition, signedParabolic]

/-- Each signed candidate has the same order as its positive counterpart. -/
theorem signedParabolic_card_eq_positive (d : LocalBlockInput m) (s : Side) (positive : Bool) :
    Nat.card (signedParabolic d s positive) = Nat.card (signedParabolic d s true) := by
  cases positive
  · have he := signedParabolic_map_opposition d s true
    simp only [Bool.not_true] at he
    rw [← he]
    exact Subgroup.card_map_of_injective (MulAut.conj _).injective
  · rfl

/-- A size distinction for the positive candidates supplies the distinction for both signs. -/
theorem signedParabolic_card_ne_of_positive (d : LocalBlockInput m)
    (h : Nat.card (signedParabolic d .suzuki true) ≠ Nat.card (signedParabolic d .linear true))
    (positive : Bool) :
    Nat.card (signedParabolic d .suzuki positive) ≠ Nat.card (signedParabolic d .linear positive) := by
  rwa [signedParabolic_card_eq_positive d .suzuki positive,
    signedParabolic_card_eq_positive d .linear positive]

/-- The positive-unipotent intersection identity supplies both signed identities. -/
theorem opposite_parabolic_inf_of_positive (d : LocalBlockInput m)
    (h : ∀ s, signedUnipotent d true ⊓ signedParabolic d s false = simpleBlock d s true)
    (s : Side) (positive : Bool) :
    signedUnipotent d positive ⊓ signedParabolic d s (!positive) = simpleBlock d s positive := by
  cases positive
  · have he := congrArg (fun H : Subgroup d.fixedGroup =>
      H.map (MulAut.conj (opposition d)).toMonoidHom) (h s)
    rw [Subgroup.map_inf _ _ _ (MulAut.conj (opposition d)).injective] at he
    simpa only [signedUnipotent_map_opposition, signedParabolic_map_opposition,
      simpleBlock_map_opposition, Bool.not_true, Bool.not_false] using he
  · exact h s

/-- It also suffices to intersect the negative unipotent subgroup with each
positive parabolic. This orientation uses only the positive root Borel. -/
theorem opposite_parabolic_inf_of_negative (d : LocalBlockInput m)
    (h : ∀ s, signedUnipotent d false ⊓ signedParabolic d s true = simpleBlock d s false)
    (s : Side) (positive : Bool) :
    signedUnipotent d positive ⊓ signedParabolic d s (!positive) = simpleBlock d s positive := by
  apply opposite_parabolic_inf_of_positive d _ s positive
  intro t
  have he := congrArg (fun H : Subgroup d.fixedGroup =>
    H.map (MulAut.conj (opposition d)).toMonoidHom) (h t)
  rw [Subgroup.map_inf _ _ _ (MulAut.conj (opposition d)).injective] at he
  simpa only [signedUnipotent_map_opposition, signedParabolic_map_opposition,
    simpleBlock_map_opposition, Bool.not_true, Bool.not_false] using he

/-- Recognition of maximal overgroups for the positive normalizer supplies both signs. -/
theorem maximal_overgroups_of_positive (d : LocalBlockInput m)
    (h : ∀ P, IsCoatom P ∧ signedBorelNormalizer d true ≤ P ↔
      ∃ s, P = signedParabolic d s true) (positive : Bool) (P : Subgroup d.fixedGroup) :
    IsCoatom P ∧ signedBorelNormalizer d positive ≤ P ↔
      ∃ s, P = signedParabolic d s positive := by
  cases positive
  · let a := MulAut.conj (opposition d)
    have hcoat : IsCoatom (P.map a.toMonoidHom) ↔ IsCoatom P :=
      OrderIso.isCoatom_iff a.mapSubgroup P
    have hle : signedBorelNormalizer d true ≤ P.map a.toMonoidHom ↔
        signedBorelNormalizer d false ≤ P := by
      have he := signedBorelNormalizer_map_opposition d false
      simp only [Bool.not_false] at he
      rw [← he]
      exact a.mapSubgroup.le_iff_le
    rw [← hcoat, ← hle, h]
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      have he := congrArg (fun H : Subgroup d.fixedGroup => H.map a.toMonoidHom) hs
      simpa only [a, map_opposition_twice, signedParabolic_map_opposition, Bool.not_true] using he
    · rintro ⟨s, rfl⟩
      exact ⟨s, signedParabolic_map_opposition d s false⟩
  · exact h P

end ReeF4.LocalBlockInput.PairRigidity
end
