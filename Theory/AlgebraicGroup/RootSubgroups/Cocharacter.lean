module

public import Theory.AlgebraicGroup.RootSubgroups.Defs
public import Theory.AlgebraicGroup.Tori.Character.Duality

universe u

/-!
Canonical integral pairings between torus characters and cocharacters.

GLS3, Remarks 1.9.6 defines the pairing as the unique exponent `m` for
which `χ(h(t)) = t ^ m`.  Laurent-character coordinates make this assignment
an additive homomorphism on the full character lattice.  For realized root
data, the chosen root cocharacter computes `RootGroupData.weightPairing` on
every torus character and recovers the Cartan pairing on root weights.
-/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A character paired with a cocharacter is a unique integral Laurent power.
This is the character--cocharacter pairing core of GLS3, Remarks 1.9.6. -/
public theorem weightCocharacterEquation_existsUnique
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (χ : TorusWeight T) (h : ClosedSubgroupTorusCocharacter T) :
    ∃! m : ℤ, WeightCocharacterEquation T χ h m := by
  let χh : TorusCharacter (KMult k) := TorusCharacter.pullback h χ
  let z : Fin 1 → ℤ :=
    (dLaurentCharacterAddEquiv (k := k) 1).symm (Additive.ofMul χh)
  let m := z 0
  have hzfun : z = fun _ => m := by
    funext i
    fin_cases i
    rfl
  have hzadd :=
    (dLaurentCharacterAddEquiv (k := k) 1).apply_symm_apply (Additive.ofMul χh)
  have hzchar : dLaurentCharacter (k := k) 1 z = χh :=
    congrArg Additive.toMul hzadd
  have hmchar : dLaurentCharacter (k := k) 1 (fun _ => m) = χh := by
    rw [← hzfun]
    exact hzchar
  refine ⟨m, ?_, ?_⟩
  · intro t
    change χh.pointCharacter t = (dPointEquiv 1 t 0 : k) ^ m
    rw [← hmchar, TorusCharacter.pointCharacter_dLaurentCharacter]
    change (↑(∏ i, (dPointEquiv 1 t i) ^ m) : k) = _
    simp
  · intro n hn
    have hnchar : dLaurentCharacter (k := k) 1 (fun _ => n) = χh := by
      apply TorusCharacter.pointCharacter_injective
      ext t
      rw [TorusCharacter.pointCharacter_dLaurentCharacter]
      change (↑(∏ i, (dPointEquiv 1 t i) ^ n) : k) =
        (dPointEquiv 1 ((χ.comp h).onPoints t) 0 : k)
      have hnt := hn t
      change (dPointEquiv 1 ((χ.comp h).onPoints t) 0 : k) =
        (dPointEquiv 1 t 0 : k) ^ n at hnt
      simpa using hnt.symm
    have hexponents :=
      dLaurentCharacter_injective (k := k) 1 (hmchar.trans hnchar.symm)
    exact (congrFun hexponents 0).symm

/-- Evaluation on a fixed cocharacter, expressed as an additive integral
functional on the full character lattice. -/
public noncomputable def characterCocharacterPairing
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (h : ClosedSubgroupTorusCocharacter T) :
    Additive (TorusWeight T) →+ ℤ :=
  (Pi.evalAddMonoidHom (fun _ : Fin 1 => ℤ) 0).comp
    ((dLaurentCharacterAddEquiv (k := k) 1).symm.toAddMonoidHom.comp
      (TorusCharacter.pullback h).toAdditive)

/-- The canonical character--cocharacter functional satisfies the defining
Laurent-power equation. -/
public theorem characterCocharacterPairing_spec
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (χ : TorusWeight T) (h : ClosedSubgroupTorusCocharacter T) :
    WeightCocharacterEquation T χ h
      (characterCocharacterPairing T h (Additive.ofMul χ)) := by
  let χh : TorusCharacter (KMult k) := TorusCharacter.pullback h χ
  let z : Fin 1 → ℤ :=
    (dLaurentCharacterAddEquiv (k := k) 1).symm (Additive.ofMul χh)
  let m := z 0
  have hzfun : z = fun _ => m := by
    funext i
    fin_cases i
    rfl
  have hzadd :=
    (dLaurentCharacterAddEquiv (k := k) 1).apply_symm_apply
      (Additive.ofMul χh)
  have hzchar : dLaurentCharacter (k := k) 1 z = χh :=
    congrArg Additive.toMul hzadd
  have hmchar : dLaurentCharacter (k := k) 1 (fun _ => m) = χh := by
    rw [← hzfun]
    exact hzchar
  have hpairing :
      characterCocharacterPairing T h (Additive.ofMul χ) = m := by
    rfl
  intro t
  change χh.pointCharacter t =
    (dPointEquiv 1 t 0 : k) ^
      characterCocharacterPairing T h (Additive.ofMul χ)
  rw [← hmchar, TorusCharacter.pointCharacter_dLaurentCharacter]
  change (↑(∏ i, (dPointEquiv 1 t i) ^ m) : k) = _
  rw [hpairing]
  simp

/-- The canonical character--coroot functional attached to a root-group datum. -/
public noncomputable def RootGroupData.characterCorootPairing
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (β : D.Root) :
    Additive (TorusWeight T) →+ ℤ :=
  characterCocharacterPairing T (D.rootCocharacter β)

/-- A realized datum's stored weight pairing is exactly the canonical pairing
with its chosen root cocharacter. -/
public theorem RootGroupData.IsRealization.weightPairing_eq_characterCorootPairing
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization)
    (χ : TorusWeight T) (β : D.Root) :
    D.weightPairing χ β =
      D.characterCorootPairing β (Additive.ofMul χ) := by
  exact (weightCocharacterEquation_existsUnique T χ (D.rootCocharacter β)).unique
    (hD.weightPairing_spec χ β)
    (characterCocharacterPairing_spec T χ (D.rootCocharacter β))

/-- Pairing with a root cocharacter sends the trivial character to zero. -/
public theorem RootGroupData.IsRealization.weightPairing_one
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization) (β : D.Root) :
    D.weightPairing 1 β = 0 := by
  rw [hD.weightPairing_eq_characterCorootPairing]
  exact map_zero (D.characterCorootPairing β)

/-- The realized character--coroot pairing is additive in the character
lattice, whose addition is multiplication of torus characters. -/
public theorem RootGroupData.IsRealization.weightPairing_mul
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization)
    (χ ψ : TorusWeight T) (β : D.Root) :
    D.weightPairing (χ * ψ) β =
      D.weightPairing χ β + D.weightPairing ψ β := by
  rw [hD.weightPairing_eq_characterCorootPairing,
    hD.weightPairing_eq_characterCorootPairing,
    hD.weightPairing_eq_characterCorootPairing]
  exact map_add (D.characterCorootPairing β)
    (Additive.ofMul χ) (Additive.ofMul ψ)

/-- Multiplying an arbitrary representation weight by an actual root shifts
each coroot coordinate by the corresponding Cartan integer.  This is the
coordinate formula used along root strings. -/
public theorem RootGroupData.IsRealization.weightPairing_mul_rootWeight
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization)
    (χ : TorusWeight T) (α β : D.Root) :
    D.weightPairing (χ * D.rootWeight α) β =
      D.weightPairing χ β + D.pairing α β := by
  rw [hD.weightPairing_mul, hD.weightPairing_rootWeight]

/-- Inverting a torus character negates each coroot coordinate. -/
public theorem RootGroupData.IsRealization.weightPairing_inv
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization)
    (χ : TorusWeight T) (β : D.Root) :
    D.weightPairing χ⁻¹ β = -D.weightPairing χ β := by
  rw [hD.weightPairing_eq_characterCorootPairing,
    hD.weightPairing_eq_characterCorootPairing]
  exact map_neg (D.characterCorootPairing β) (Additive.ofMul χ)

/-- Canonical character--coroot evaluation recovers the realized Cartan
pairing on actual root weights. -/
public theorem RootGroupData.IsRealization.characterCorootPairing_rootWeight
    [IsAlgClosed k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    {D : RootGroupData K T} (hD : D.IsRealization) (α β : D.Root) :
    D.characterCorootPairing β (Additive.ofMul (D.rootWeight α)) =
      D.pairing α β := by
  rw [← hD.weightPairing_eq_characterCorootPairing,
    hD.weightPairing_rootWeight]

end Theory.AlgebraicGroup
