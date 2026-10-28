module
public import ABG.ChapterII.Section3.QSylowNormalSL2
public import ABG.ChapterII.Section3.WreathedSL2Radius
public import ABG.ChapterII.Section1.SemidihedralEmbeddedLayer
public import ABG.ChapterII.Section1.WreathedQuaternionUnique
public import ABG.ChapterII.Section2.SylowShapeTransport

/-!
# Actual Sylow extension data in a core-free enlarged Q-group

For a finite Q-group with trivial odd core and a supplied normal SL2(F)
subgroup, choose an actual Sylow two-subgroup R and its actual intersection
A with that subgroup. The field two-part has exponent n at least two.
Either the center of R has order two and lies in A, with R equal to A or
semidihedral with an exterior involution, or its center has order 2^(r+1)
for r<n. In the latter branch A and the center generate R, or R is wreathed
of height n, r=n-1, and an exterior element has square generating that center.
The two full extensions have index two over their central quaternion layer.

The linked largest quaternion witness from the enlarged Q definition is
identified with the canonical quaternion subgroup in its actual overgroup.
The proved semidihedral and wreathed embedding calculations give the center
and exterior generators. Transporting the normal Sylow restriction through
the supplied SL2 equivalence computes the exact two-part of |F|-1 or |F|+1.
This preserves proper quaternion overgroups and fields of orders three and
nine, without assuming either full Sylow shape for the original group.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pp25--26.
These are the original-group geometry and parameter inputs for recognizing
the concrete linear or unitary determinant level and its index-two extension.
-/

namespace ABG
open GorensteinWalter
universe u

public theorem qGroup_sylow_normal_sl2_extension_data
    {H : Type u} [Group H] [Finite H] (hH : IsQGroup H)
    (hcore : pPrimeCore 2 H = ⊥) (L0 : Subgroup H) [L0.Normal]
    (F : Type u) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ∃ (R : Sylow 2 H) (n : ℕ), 2 ≤ n ∧
      ((Nat.card F % 4 = 1 ∧ 2 ^ n ∣ Nat.card F - 1 ∧ Odd ((Nat.card F - 1) / 2 ^ n)) ∨
        (Nat.card F % 4 = 3 ∧ 2 ^ n ∣ Nat.card F + 1 ∧ Odd ((Nat.card F + 1) / 2 ^ n))) ∧
      let A := L0.comap (R : Subgroup H).subtype
      (Subgroup.center R ≤ A ∧ Nat.card (Subgroup.center R) = 2 ∧
        (A = ⊤ ∨ (A.index = 2 ∧ Stellmacher.IsSemidihedralGroup R ∧
          ∃ a : R, a ∉ A ∧ a ^ 2 = 1))) ∨
      (∃ r < n, Nat.card (Subgroup.center R) = 2 ^ (r + 1) ∧
        (A ⊔ Subgroup.center R = ⊤ ∨
          (r = n - 1 ∧ (A ⊔ Subgroup.center R).index = 2 ∧
            IsWreathedOfHeight R n ∧ ∃ a : R,
              a ∉ A ⊔ Subgroup.center R ∧ Subgroup.zpowers (a ^ 2) = Subgroup.center R))) := by
  obtain ⟨S, iS, hS, R, f, Y, hf, hY, hlink⟩ :=
    qGroup_exists_sylow_embedding_normal_sl2 hH hcore L0 F hF eL0
  let : Group S := iS
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, n, hp, hpodd, hn, he⟩ := hF
    rw [he]
    exact hpodd.pow
  let A := L0.comap (R : Subgroup H).subtype
  rcases hS with hS | ⟨n, hS⟩
  · have hfin : Finite S := by
      obtain ⟨m, _, hc, _⟩ := hS
      exact Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    let := hfin
    obtain ⟨Y0, hY0, hY0i, hmax⟩ := QuasiDihedral.exists_largest_quaternion hS
    have heY : Y0 = Y := (hY.2 Y0 hY0).2
      (le_antisymm (hY.2 Y0 hY0).1 (Subgroup.card_le_of_le (hmax Y hY.1)))
    have hYi : Y.index = 2 := heY ▸ hY0i
    obtain ⟨hCA, n, hn, hAc, hCc, hcases⟩ :=
      QuasiDihedral.embedded_quaternion_layer_data hS f hf Y hY.1 hYi A hlink
    let T := BenderSuzuki.External.hallSylowSubgroupOfNormal R L0
    let eA : A ≃* T := {
      toFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val, x.property⟩, x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
    let U := T.mapSurjective (f := eL0.toMonoidHom) eL0.surjective
    have hUc : Nat.card U = 2 ^ (n + 1) := by
      change Nat.card ((T : Subgroup L0).map eL0.toMonoidHom) = _
      rw [Subgroup.card_map_of_injective eL0.injective]
      exact (Nat.card_congr eA.symm.toEquiv).trans hAc
    refine ⟨R, n, hn, GorensteinWalter.sl2_sylow_two_part_of_card F hodd U n hn hUc,
      Or.inl ⟨hCA, hCc, ?_⟩⟩
    rcases hcases with hA | ⟨_, hi, hR, ha⟩
    · exact Or.inl hA
    · exact Or.inr ⟨hi, hR, ha⟩
  · obtain ⟨P⟩ := Wreathed.nonempty_presentation hS
    let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
    have heY : P.Y = Y := (hY.2 P.Y P.quaternion_subgroup.1).2
      (le_antisymm (hY.2 P.Y P.quaternion_subgroup.1).1
        (Subgroup.card_le_of_le (P.quaternion_le_Y Y hY.1)))
    have hlink' : A.map f = P.Y := hlink.trans heY.symm
    obtain ⟨hfield, r, hr, hc, hcases⟩ :=
      wreathed_sylow_sl2_radius_data P R L0 F hodd eL0 f hf hlink'
    refine ⟨R, n, P.height, hfield, Or.inr ⟨r, hr, hc, ?_⟩⟩
    rcases hcases with hA | ⟨hfs, hrn, hi, ha⟩
    · exact Or.inl hA
    · refine Or.inr ⟨hrn, hi, ?_, ha⟩
      exact wreathed_equiv (MulEquiv.ofBijective f ⟨hf, hfs⟩).symm hS

end ABG
