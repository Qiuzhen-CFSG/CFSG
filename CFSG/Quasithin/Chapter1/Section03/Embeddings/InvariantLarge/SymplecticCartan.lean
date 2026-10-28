module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.G2.Source.RawCartan
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.OuterReduction

/-!
# The actual symplectic Cartan clause of A.3.15

The original field and Cartan factors live in Aut(D), and the equality
FBD = HBD is a set-product identity. Since B is inside D and the binary
symplectic inner-diagonal group is inner, that identity puts F inside the
inner group. The concrete field/inner separation theorem kills F, even
with the source's automorphism-conjugate convention for field elements.
Consequently B acts through H and normalizes the actual Sylow intersection.
No normalizer-containment, torus alignment or action conclusion is assumed.

Source: Aschbacher–Smith A.3.15(5), pp.50–51, and 1.3.4, p.511;
GLS3 Definition 2.5.13 for the field-automorphism convention.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.SymplecticAction
open Theory.SpecificGroups.SymplecticFour Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {D F : Type*} [Group D] [Field F] [Finite F]

/-- The literal A.3.15(5) factors for the binary symplectic carrier. In
characteristic two its inner-diagonal subgroup is the inner subgroup. -/
structure RawCartan (n : ℕ) (U B : Subgroup D) where
  model : D ≃* Sp F
  field_card : Nat.card F = 2^n
  degree : 1 < n
  field : Subgroup (MulAut D)
  cartan : Subgroup (MulAut D)
  innerPart : Subgroup (MulAut D)
  f : ℕ
  field_cyclic : IsCyclic field
  field_order : Nat.card field = f
  field_divides : f ∣ n
  field_type : ∀ a ∈ field, ∃ (c : MulAut (Sp F)) (σ : F ≃+* F),
    MulAut.congr model a = c * fieldAutomorphism σ * c⁻¹
  cartan_structure : EvenActions.G2.Source.RawCartan.IsCartan innerPart U cartan
  invariant : field ≤ normalizer cartan
  contained : ∀ b ∈ B.map (MulAut.conj : D →* MulAut D),
    ∃ a ∈ field, ∃ h ∈ cartan, b = a * h
  product : (field : Set (MulAut D)) * B.map (MulAut.conj : D →* MulAut D) *
      (MulAut.innerSubgroup D : Set (MulAut D)) =
    (cartan : Set (MulAut D)) * B.map (MulAut.conj : D →* MulAut D) *
      (MulAut.innerSubgroup D : Set (MulAut D))
  inner_part : innerPart = (field ⊔ B.map (MulAut.conj : D →* MulAut D) ⊔
      MulAut.innerSubgroup D) ⊓ MulAut.innerSubgroup D

variable {n : ℕ} {U B : Subgroup D}

theorem RawCartan.field_eq_bot (c : RawCartan (F := F) n U B) : c.field = ⊥ := by
  let : CharP F 2 := EvenProjective.charTwo_of_card c.field_card
  have hcI : c.cartan ≤ MulAut.innerSubgroup D := by
    intro a ha
    have hh := c.cartan_structure.inside ha
    rw [c.inner_part] at hh
    exact hh.2
  have hBI : B.map (MulAut.conj : D →* MulAut D) ≤ MulAut.innerSubgroup D := by
    rintro _ ⟨b, _, rfl⟩
    exact ⟨b, rfl⟩
  apply le_antisymm _ bot_le
  intro a ha
  have hprod : a ∈ (c.field : Set (MulAut D)) * B.map (MulAut.conj : D →* MulAut D) *
      (MulAut.innerSubgroup D : Set (MulAut D)) :=
    ⟨a, ⟨a, ha, 1, one_mem _, mul_one _⟩, 1, one_mem _, mul_one _⟩
  rw [c.product] at hprod
  obtain ⟨hb, ⟨h, hh, b, hb, rfl⟩, d, hd, he⟩ := hprod
  have hai : a ∈ MulAut.innerSubgroup D := by
    rw [← he]
    exact mul_mem (mul_mem (hcI hh) (hBI hb)) hd
  have haim : MulAut.congr c.model a ∈ MulAut.innerSubgroup (Sp F) := by
    obtain ⟨d, rfl⟩ := hai
    rw [MulAut.congr_conj]
    exact ⟨_, rfl⟩
  obtain ⟨z, σ, hz⟩ := c.field_type a ha
  have hσi : fieldAutomorphism σ ∈ MulAut.innerSubgroup (Sp F) := by
    have hn : z ∈ normalizer (MulAut.innerSubgroup (Sp F) : Set (MulAut (Sp F))) :=
      by rw [normalizer_eq_top]; exact mem_top z
    apply (mem_normalizer_iff.mp hn _).mpr
    rwa [hz] at haim
  have hσ := InvolutionNormalForms.field_eq_one_of_inner σ hσi
  apply mem_bot.mpr
  apply (MulAut.congr c.model).injective
  rw [map_one, hz, hσ]
  have hh : fieldAutomorphism (1 : F ≃+* F) = 1 := map_one fieldAutomorphismHom
  rw [hh, mul_one, mul_inv_cancel]

theorem RawCartan.normalizes (c : RawCartan (F := F) n U B) : B ≤ normalizer U := by
  apply le_normalizer_iff.mpr
  intro b hb u hu
  obtain ⟨a, ha, z, hz, he⟩ := c.contained _ (mem_map_of_mem (MulAut.conj : D →* MulAut D) hb)
  have ha1 : a = 1 := mem_bot.mp (show a ∈ (⊥ : Subgroup (MulAut D)) from c.field_eq_bot ▸ ha)
  have he' : MulAut.conj b = z := by simpa only [ha1, one_mul] using he
  have hm := mem_map_of_mem (MulAut.conj b).toMonoidHom hu
  rw [he', c.cartan_structure.preserves z hz] at hm
  simpa only [← he', MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hm

/-- Return from D's subgroup coordinates to the original Sylow intersection. -/
theorem RawCartan.normalizes_ambient {J : Type*} [Group J]
    (D B S : Subgroup J) (hBD : B ≤ D)
    (c : RawCartan (F := F) n (S.subgroupOf D) (B.subgroupOf D)) :
    B ≤ normalizer (S ⊓ D : Subgroup J) := by
  apply le_normalizer_iff.mpr
  intro b hb x hx
  have hn := c.normalizes (show (⟨b, hBD hb⟩ : D) ∈ B.subgroupOf D from hb)
  have hh := (mem_normalizer_iff.mp hn (⟨x, hx.2⟩ : D)).mp hx.1
  exact ⟨hh, D.mul_mem (D.mul_mem (hBD hb) hx.2) (D.inv_mem (hBD hb))⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.SymplecticAction
