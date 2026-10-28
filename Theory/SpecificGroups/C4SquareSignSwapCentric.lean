module

public import Theory.SpecificGroups.C4SquareSignSwapCentricEnumeration
public import Theory.SpecificGroups.C4SquareSignSwapCentricAutomorphisms

/-!
# Intrinsic centric classification in the sign-and-swap model

The checked subgroup enumeration and automorphism certificates reduce a centric
subgroup outside `transfer` to one of the ten exceptional candidates.  The
candidate calculations then give the four intrinsic alternatives.
-/

namespace C4SquareSignSwap

private theorem map_symm_map (e : Model ≃* Model) (H : Subgroup Model) :
    (H.map e.symm.toMonoidHom).map e.toMonoidHom = H := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id H using 1
  ext x
  simp

private theorem map_map_symm (e : Model ≃* Model) (H : Subgroup Model) :
    (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id H using 1
  ext x
  simp

private theorem normal_map_conj (N : Subgroup Model) [N.Normal] (g : Model) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply] using (inferInstance : N.Normal).conj_mem y hy g
  · intro hx
    have hx' : g⁻¹ * x * g ∈ N := by
      simpa only [inv_inv] using (inferInstance : N.Normal).conj_mem x hx g⁻¹
    exact ⟨g⁻¹ * x * g, hx', by simp [MulAut.conj_apply, mul_assoc]⟩

private theorem centralProduct_transport (X Y : Subgroup Model) (e : Model ≃* Model)
    (hXY : X.map e.toMonoidHom = Y)
    (hcase :
      ∃ B C : Subgroup Model,
        Nonempty (B ≃* Multiplicative (ZMod 4)) ∧
        Nonempty (C ≃* QuaternionGroup 2) ∧
        Y = B ⊔ C ∧ Nat.card (B ⊓ C : Subgroup Model) = 2 ∧
        (∀ b : Model, b ∈ B → ∀ c : Model, c ∈ C → b * c = c * b) ∧
        B ⊓ C ≤ (Subgroup.center Y).map Y.subtype) :
    ∃ B C : Subgroup Model,
      Nonempty (B ≃* Multiplicative (ZMod 4)) ∧
      Nonempty (C ≃* QuaternionGroup 2) ∧
      X = B ⊔ C ∧ Nat.card (B ⊓ C : Subgroup Model) = 2 ∧
      (∀ b : Model, b ∈ B → ∀ c : Model, c ∈ C → b * c = c * b) ∧
      B ⊓ C ≤ (Subgroup.center X).map X.subtype := by
  rcases hcase with ⟨B₀, C₀, hB₀, hC₀, hjoin, hinter, hcomm, hcenter⟩
  let B := B₀.map e.symm.toMonoidHom
  let C := C₀.map e.symm.toMonoidHom
  have hBmap : B.map e.toMonoidHom = B₀ := by
    exact map_symm_map e B₀
  have hCmap : C.map e.toMonoidHom = C₀ := by
    exact map_symm_map e C₀
  have hX : X = Y.map e.symm.toMonoidHom := by
    rw [← hXY, map_map_symm]
  have hjoin' : X = B ⊔ C := by
    rw [hX]
    change Y.map e.symm.toMonoidHom =
      B₀.map e.symm.toMonoidHom ⊔ C₀.map e.symm.toMonoidHom
    rw [← Subgroup.map_sup, hjoin]
  have hcard' : Nat.card (B ⊓ C : Subgroup Model) = 2 := by
    calc
      Nat.card (B ⊓ C : Subgroup Model) =
          Nat.card ((B ⊓ C).map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
      _ = Nat.card (B₀ ⊓ C₀ : Subgroup Model) := by
        rw [Subgroup.map_inf B C e.toMonoidHom (fun x y h => e.injective h), hBmap, hCmap]
      _ = 2 := hinter
  have hcomm' : ∀ b : Model, b ∈ B → ∀ c : Model, c ∈ C → b * c = c * b := by
    intro b hb c hc
    rcases Subgroup.mem_map.mp hb with ⟨b₀, hb₀, hb_eq⟩
    rcases Subgroup.mem_map.mp hc with ⟨c₀, hc₀, hc_eq⟩
    apply e.injective
    have hb' : e b = b₀ := by simp [← hb_eq]
    have hc' : e c = c₀ := by simp [← hc_eq]
    calc
      e (b * c) = e b * e c := map_mul e b c
      _ = b₀ * c₀ := by rw [hb', hc']
      _ = c₀ * b₀ := hcomm b₀ hb₀ c₀ hc₀
      _ = e c * e b := by rw [hc', hb']
      _ = e (c * b) := (map_mul e c b).symm
  have hcenter' : B ⊓ C ≤ (Subgroup.center X).map X.subtype := by
    intro z hz
    have hzB₀ : e z ∈ B₀ := by
      rw [← hBmap]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hz.1
    have hzC₀ : e z ∈ C₀ := by
      rw [← hCmap]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hz.2
    have hzY : e z ∈ Y := by
      rw [hjoin]
      exact Subgroup.mem_sup_left hzB₀
    have hzX : z ∈ X := by
      have hzYmap : e z ∈ X.map e.toMonoidHom := hXY.symm ▸ hzY
      rcases Subgroup.mem_map.mp hzYmap with ⟨x, hx, hxe⟩
      have hxe' : x = z := e.injective hxe
      simpa [hxe'] using hx
    have hzYcenter : e z ∈ (Subgroup.center Y).map Y.subtype :=
      hcenter ⟨hzB₀, hzC₀⟩
    rcases Subgroup.mem_map.mp hzYcenter with ⟨zy, hzy, hzy_eq⟩
    refine ⟨⟨z, hzX⟩, ?_, rfl⟩
    change (⟨z, hzX⟩ : X) ∈ Subgroup.center X
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    apply e.injective
    have hxY : e (x : Model) ∈ Y := by
      exact hXY.symm ▸ Subgroup.mem_map_of_mem e.toMonoidHom x.property
    have hcommY := Subgroup.mem_center_iff.mp hzy ⟨e (x : Model), hxY⟩
    simpa [map_mul, ← hzy_eq] using congrArg Subtype.val hcommY
  refine ⟨B, C, ?_, ?_, hjoin', hcard', hcomm', hcenter'⟩
  · rcases hB₀ with ⟨eB⟩
    exact ⟨(Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).trans
      (hBmap ▸ eB)⟩
  · rcases hC₀ with ⟨eC⟩
    exact ⟨(Subgroup.equivMapOfInjective C e.toMonoidHom e.injective).trans
      (hCmap ▸ eC)⟩

/-- Every centric subgroup outside `transfer` is one of the four intrinsic
exceptional types. -/
public theorem centric_classification (X : Subgroup Model)
    (hc : Subgroup.centralizer (X : Set Model) ≤ X)
    (haut : ¬ IsPGroup 2 (MulAut X))
    (hout : ¬ X ≤ transfer) :
    (IsElementaryAbelian 2 X ∧ Nat.card X = 8) ∨
    (∃ B C : Subgroup Model,
      Nonempty (B ≃* Multiplicative (ZMod 4)) ∧
      Nonempty (C ≃* QuaternionGroup 2) ∧
      X = B ⊔ C ∧ Nat.card (B ⊓ C : Subgroup Model) = 2 ∧
      (∀ b : Model, b ∈ B → ∀ c : Model, c ∈ C → b * c = c * b) ∧
      B ⊓ C ≤ (Subgroup.center X).map X.subtype) ∨
    X = inverterCore ∨ X = extraspecialCore := by
  obtain ⟨i, g, hXi⟩ := centricCandidate_complete X hc hout
  let e : Model ≃* Model := MulAut.conj g
  have hXie : X.map e.toMonoidHom = centricCandidate i := hXi
  by_cases hi : centricExceptionalIndex i
  · rcases centricCandidate_exceptional_cases i hi with hEA | hCP | hcore
    · left
      rcases hEA with ⟨hEA, hcard⟩
      let _ : IsElementaryAbelian 2 (centricCandidate i) := hEA
      have hEA' : IsElementaryAbelian 2 X := by
        have hmap : IsElementaryAbelian 2
            ((centricCandidate i).map e.symm.toMonoidHom) :=
          IsElementaryAbelian.map (p := 2) e.symm.toMonoidHom
            (A := centricCandidate i)
        have := hmap
        rw [← hXie, map_map_symm] at this
        exact this
      have hcard' : Nat.card X = 8 := by
        calc
          Nat.card X = Nat.card (X.map e.toMonoidHom) :=
            (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
          _ = Nat.card (centricCandidate i) := by rw [hXie]
          _ = 8 := hcard
      exact ⟨hEA', hcard'⟩
    · exact Or.inr (Or.inl (centralProduct_transport X (centricCandidate i) e hXie hCP))
    · rcases hcore with hi11 | hi31
      · apply Or.inr (Or.inr (Or.inl ?_))
        apply Subgroup.map_injective (f := e.toMonoidHom) (fun x y h => e.injective h)
        rw [hXie, hi11, normal_map_conj]
      · apply Or.inr (Or.inr (Or.inr ?_))
        apply Subgroup.map_injective (f := e.toMonoidHom) (fun x y h => e.injective h)
        rw [hXie, hi31, normal_map_conj]
  · exfalso
    apply haut
    have hp := centricCandidate_isPGroup_mulAut i hi
    have heq : X ≃* centricCandidate i := by
      exact hXie ▸ Subgroup.equivMapOfInjective X e.toMonoidHom e.injective
    exact hp.of_equiv (MulAut.congr heq).symm

end C4SquareSignSwap
