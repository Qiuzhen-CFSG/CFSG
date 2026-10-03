module

public import Theory.PPrimeCore
public import Theory.GroupAction.Quotient

/-!
# Prime-complement cores through coprime kernels

For a surjective homomorphism of finite groups whose kernel has order coprime
to p, the inverse image of the codomain p'-core is exactly the domain p'-core.
No solvability or centrality assumption is needed.

The inverse image is normal, and its order is the product of the codomain
core's order and the kernel's order, hence coprime to p. It therefore lies
inside the domain core. Conversely the image of the domain core is normal
of coprime order, so lies inside the codomain core.

This supplies the quotient identification for the odd-core supplement in
Alperin--Brauer--Gorenstein II.3 Lemma 2, article pages 23--24, and applies
independently to every prime.
-/

public theorem pPrimeCore_comap_eq_of_surjective_coprime
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hker : Nat.Coprime p (Nat.card f.ker)) :
    (pPrimeCore p H).comap f = pPrimeCore p G := by
  let C := pPrimeCore p H
  let D := C.comap f
  have hDc : Nat.Coprime p (Nat.card D) := by
    have hcardQ : Nat.card (D ⧸ f.ker.subgroupOf D) = Nat.card C :=
      card_quotient_subgroupOf_comap_eq f hf C
    have hcardK : Nat.card (f.ker.subgroupOf D) = Nat.card f.ker :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.ker_le_comap f C)).toEquiv
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (f.ker.subgroupOf D)
    rw [hcardQ, hcardK] at hcard
    rw [hcard]
    exact Nat.Coprime.mul_right (pPrimeCore_coprime_card (p := p) (G := H)) hker
  apply le_antisymm (show D ≤ pPrimeCore p G from le_sSup ⟨inferInstance, hDc⟩)
  apply Subgroup.map_le_iff_le_comap.mp
  have hmapN : ((pPrimeCore p G).map f).Normal :=
    Subgroup.Normal.map inferInstance f hf
  have hmapc : Nat.Coprime p (Nat.card ((pPrimeCore p G).map f)) :=
    Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (pPrimeCore p G) f) pPrimeCore_coprime_card
  exact le_sSup ⟨hmapN, hmapc⟩
