module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.LocalPlanes.Geometry

/-!
# Cubic centralizers in the actual local planes

Coprime lifting puts an aligned plane inside C_P(D)V. Since V is contained
in the plane, the product decomposition restricts to C_A(D)V. Its two factors
intersect trivially, because the complementary cubic has no fixed tensor
vector. Their orders give |C_A(D)| = 32/16 = 2 and hence an actual involution
as generator. All maps use ambient multiplication.

Source: Aschbacher–Smith, 15.3.61(2), printed p.1150.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
variable {G : Type*} [Group G] {I Y P V : Subgroup G}
  {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
  [(V.subgroupOf P).Normal]

omit [(V.subgroupOf P).Normal] in
/-- The centralizer product decomposition restricts to every subgroup
containing V in the fixed-quotient block. -/
theorem aligned_subgroup_eq_product
    (hcentral : V ≤ centralizer (P : Set G))
    (A D : Subgroup G) (hVA : V ≤ A) (hAB : A ≤ fusionBlock P V D) :
    (A : Set G) = ((A ⊓ centralizer (D : Set G) : Subgroup G) : Set G) * (V : Set G) := by
  ext x
  constructor
  · intro hx
    have h := hAB hx
    change x ∈ (fusionBlock P V D : Set G) at h
    rw [fusionBlock_eq_product P V D hcentral] at h
    obtain ⟨c, hc, v, hv, hcv⟩ := h
    have hcA : c ∈ A := by
      have hh := A.mul_mem hx (A.inv_mem (hVA hv))
      rwa [← hcv, mul_inv_cancel_right] at hh
    exact ⟨c, ⟨hcA, hc.2⟩, v, hv, hcv⟩
  · rintro ⟨c, hc, v, hv, rfl⟩
    exact A.mul_mem hc.1 (hVA hv)

/-- Multiplication gives the actual centralizer-times-V equivalence. -/
noncomputable def alignedSubgroupEquiv (d : LayerActions I Y P V hIP hIV)
    (hcentral : V ≤ centralizer (P : Set G))
    (j : Fin 2) (A D : Subgroup G) (hAP : A ≤ P) (hVA : V ≤ A)
    (hAB : A ≤ fusionBlock P V D)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic j) :
    A ≃* (A ⊓ centralizer (D : Set G) : Subgroup G) × V := by
  let C := A ⊓ centralizer (D : Set G)
  have hc : ∀ c : C, ∀ v : V, Commute (c : G) (v : G) := by
    intro c v
    exact hcentral v.property c (hAP c.property.1)
  let f : C × V →* A := (C.subtype.noncommCoprod V.subtype hc).codRestrict A
    (fun x => A.mul_mem x.1.property.1 (hVA x.2.property))
  have hd : Disjoint C V :=
    (centralizer_disjoint_lower d j D himage).mono_left inf_le_right
  have hi : Function.Injective f := by
    intro x y h
    exact Subgroup.mul_injective_of_disjoint hd (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro x
    have hx : (x : G) ∈
        ((A ⊓ centralizer (D : Set G) : Subgroup G) : Set G) * (V : Set G) := by
      rw [← aligned_subgroup_eq_product hcentral A D hVA hAB]
      exact x.property
    obtain ⟨c, hc, v, hv, he⟩ := hx
    exact ⟨(⟨c, hc⟩, ⟨v, hv⟩), Subtype.ext he⟩
  exact (MulEquiv.ofBijective f ⟨hi, hs⟩).symm

/-- The actual local-plane centralizer of the assigned cubic has order two. -/
theorem aligned_centralizer_card (d : LayerActions I Y P V hIP hIV)
    (hcentral : V ≤ centralizer (P : Set G))
    (j : Fin 2) (A D : Subgroup G) (hAP : A ≤ P) (hVA : V ≤ A)
    (hAB : A ≤ fusionBlock P V D) (hA : Nat.card A = 32)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic j) :
    Nat.card (A ⊓ centralizer (D : Set G) : Subgroup G) = 2 := by
  have he := Nat.card_congr (alignedSubgroupEquiv d hcentral j A D hAP hVA hAB himage).toEquiv
  rw [hA, Nat.card_prod, d.card_lower] at he
  omega

/-- Produce a source involution generating C_A(D), with the whole plane
expressed as its product with V. -/
theorem exists_aligned_generator (d : LayerActions I Y P V hIP hIV)
    (hcentral : V ≤ centralizer (P : Set G))
    (j : Fin 2) (A D : Subgroup G) (hAP : A ≤ P) (hVA : V ≤ A)
    (hAB : A ≤ fusionBlock P V D) (hA : Nat.card A = 32)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic j) :
    ∃ a : G, a ∈ A ⊓ centralizer (D : Set G) ∧ orderOf a = 2 ∧
      zpowers a = A ⊓ centralizer (D : Set G) ∧ a ∉ V ∧ A = zpowers a ⊔ V := by
  obtain ⟨a, ha, ha2, hgen⟩ := exists_generator_of_card_two
    (A ⊓ centralizer (D : Set G))
    (aligned_centralizer_card d hcentral j A D hAP hVA hAB hA himage)
  have haV : a ∉ V := by
    intro hv
    have he := disjoint_def.mp (centralizer_disjoint_lower d j D himage) ha.2 hv
    simp [he] at ha2
  refine ⟨a, ha, ha2, hgen, haV, ?_⟩
  rw [hgen]
  apply le_antisymm _ (sup_le inf_le_left hVA)
  intro x hx
  have hm : x ∈ ((A ⊓ centralizer (D : Set G) : Subgroup G) : Set G) * (V : Set G) := by
    rw [← aligned_subgroup_eq_product hcentral A D hVA hAB]
    exact hx
  obtain ⟨c, hc, v, hv, rfl⟩ := hm
  exact mul_mem (mem_sup_left hc) (mem_sup_right hv)

/-- Source-local alignment, fixed quotient, block containment and the actual
centralizer generators. The local product equivalence and PairingFormula
remain explicit inputs to be discharged by their independent owners. -/
theorem exists_localPlane_cubic_data [Finite G]
    (Z ZS Y V : Subgroup G) (g : G)
    [(Z.subgroupOf (closureU Z ZS)).Normal]
    [(V.subgroupOf (pairP Z ZS g)).Normal]
    {hIP : pairI Z ZS g ≤ normalizer (pairP Z ZS g : Set G)}
    {hIV : pairI Z ZS g ≤ normalizer (V : Set G)}
    (d : LayerActions (pairI Z ZS g) Y (pairP Z ZS g) V hIP hIV)
    (hf : PairingFormula d) (a : centralizerH Z)
    (e : (fixedLift Z ZS a ⊔ V : Subgroup G) ≃* CentralProductModel)
    (hLP : fixedLift Z ZS a ⊔ V ≤ pairP Z ZS g)
    (hcentral : V ≤ centralizer (pairP Z ZS g : Set G))
    (D : Fin 2 → Subgroup G) (hDI : ∀ j, D j ≤ pairI Z ZS g)
    (hD : ∀ j, Nat.card (D j) = 3)
    (himage : ∀ j, ((D j).subgroupOf (pairI Z ZS g)).map d.actor = complementaryCubic j) :
    ∃ σ : Equiv.Perm (Fin 2), ∀ i,
      let A := localPlane (fixedLift Z ZS a ⊔ V) e i
      V ≤ A ∧ A ≤ summandPreimage d (σ i) ∧
      (∀ x ∈ A, ∀ b ∈ D (σ i), MulAut.conj b x / x ∈ V) ∧
      A ≤ fusionBlock (pairP Z ZS g) V (D (σ i)) ∧
      Nat.card (A ⊓ centralizer (D (σ i) : Set G) : Subgroup G) = 2 ∧
      ∃ ai : G, ai ∈ A ⊓ centralizer (D (σ i) : Set G) ∧ orderOf ai = 2 ∧
        zpowers ai = A ⊓ centralizer (D (σ i) : Set G) ∧ ai ∉ V ∧ A = zpowers ai ⊔ V := by
  obtain ⟨σ, hσ⟩ := exists_plane_permutation d hf _ hLP e
  refine ⟨σ, fun i => ?_⟩
  dsimp only
  let A := localPlane (fixedLift Z ZS a ⊔ V) e i
  have hAP : A ≤ pairP Z ZS g := (localPlane_le _ e i).trans hLP
  have hVP : V ≤ pairP Z ZS g := le_sup_right.trans hLP
  have hVA : V ≤ A := lower_le_localPlane d _ hLP le_sup_right hcentral e i
  have hAB : A ≤ fusionBlock (pairP Z ZS g) V (D (σ i)) := by
    rw [fusionBlock_eq_summandPreimage d hVP (σ i) (D (σ i)) (hDI _) (hD _) (himage _)]
    exact hσ i
  refine ⟨hVA, hσ i, ?_, hAB,
    aligned_centralizer_card d hcentral (σ i) A (D (σ i)) hAP hVA hAB
      (localPlane_card _ e i) (himage _),
    exists_aligned_generator d hcentral (σ i) A (D (σ i)) hAP hVA hAB
      (localPlane_card _ e i) (himage _)⟩
  intro x hx
  exact (fixed_quotient_iff d (σ i) (D (σ i)) (hDI _) (himage _) ⟨x, hAP hx⟩).mpr
    ((mem_summandPreimage d (σ i) ⟨x, hAP hx⟩).mp (hσ i hx))

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
