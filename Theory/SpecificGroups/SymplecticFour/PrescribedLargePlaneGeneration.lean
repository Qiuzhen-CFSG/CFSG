module
public import Theory.SpecificGroups.SymplecticFour.SmallPlaneGeneration
import all Theory.SpecificGroups.SymplecticFour.SmallPlaneGeneration
import all Theory.SpecificGroups.SymplecticFour.IndividualMoverGeneration

/-!
# A large upper plane actor and two prescribed lower roots

An upper-plane subgroup of order greater than q² contains a nonidentity
first-root element: otherwise its other two coordinates would embed it
in F². It also contains an element with nonzero off-diagonal coordinate.
The prescribed opposite first root enlarges the nonidentity element to
the full first root, and the cross-shear calculation generates Sp₄ with
the two unchanged lower long roots.

The internal imports reuse the frozen long-root Weyl word and cross-shear
calculation. No new shear or root position is chosen, and the public
statement contains only the literal original subgroup and prescribed roots.
Source: MS93 (5.6)(a), printed p.917, as used in (5.12)(3), p.927.
-/

public noncomputable section
open Subgroup Matrix Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.PrescribedLargePlaneGeneration
open CentralRootGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem nonzero_first_root_of_large
    (A : Subgroup (unipotent (F := F))) (hAP : A ≤ wing true)
    (hcard : Nat.card F^2 < Nat.card A) :
    ∃ s : F, s ≠ 0 ∧ element 0 s 0 0 ∈ A := by
  classical
  by_contra! hn
  have zero_of_mem (s : F) (hs : element 0 s 0 0 ∈ A) : s=0 := by
    by_contra hh
    exact hn s hh hs
  let p : A → F × F := fun x =>
    (x.val.val.val (.inl 1) (.inr 0),x.val.val.val (.inl 1) (.inr 1))
  have hp : Function.Injective p := by
    intro x y he
    obtain ⟨⟨b,u,w,v⟩,hx⟩ := element_surjective x.val
    obtain ⟨⟨c,z,t,a⟩,hy⟩ := element_surjective y.val
    have hxA : element b u w v ∈ A := by simpa only [hx] using x.property
    have hyA : element c z t a ∈ A := by simpa only [hy] using y.property
    have hb : b=0 := (element_mem_wing true _ _ _ _).mp (hAP hxA)
    have hc : c=0 := (element_mem_wing true _ _ _ _).mp (hAP hyA)
    subst b
    subst c
    change (x.val.val.val (.inl 1) (.inr 0),x.val.val.val (.inl 1) (.inr 1)) =
      (y.val.val.val (.inl 1) (.inr 0),y.val.val.val (.inl 1) (.inr 1)) at he
    simp only [←hx,←hy,element_matrix] at he
    change (w,v)=(t,a) at he
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    have hh := A.mul_mem hxA hyA
    rw [element_mul] at hh
    simp only [zero_mul,mul_zero,add_zero,CharTwo.add_self_eq_zero] at hh
    have huz := CharTwo.add_eq_zero.mp (zero_of_mem _ hh)
    apply Subtype.ext
    rw [←hx,←hy,huz]
  exact hcard.not_ge (by simpa only [Nat.card_prod,pow_two] using Nat.card_le_card_of_injective p hp)

private theorem nonzero_cross_coordinate_of_large
    (A : Subgroup (unipotent (F := F))) (hAP : A ≤ wing true)
    (hcard : Nat.card F^2 < Nat.card A) :
    ∃ u w v : F, element 0 u w v ∈ A ∧ w ≠ 0 := by
  classical
  by_contra! hn
  let p : A → F × F := fun x =>
    (x.val.val.val (.inl 0) (.inr 0),x.val.val.val (.inl 1) (.inr 1))
  have hp : Function.Injective p := by
    intro x y he
    obtain ⟨⟨b,u,w,v⟩,hx⟩ := element_surjective x.val
    obtain ⟨⟨c,z,t,a⟩,hy⟩ := element_surjective y.val
    have hxA : element b u w v ∈ A := by simpa only [hx] using x.property
    have hyA : element c z t a ∈ A := by simpa only [hy] using y.property
    have hb : b=0 := (element_mem_wing true _ _ _ _).mp (hAP hxA)
    have hc : c=0 := (element_mem_wing true _ _ _ _).mp (hAP hyA)
    subst b
    subst c
    have hw : w=0 := hn u w v hxA
    have ht : t=0 := hn z t a hyA
    subst w
    subst t
    change (x.val.val.val (.inl 0) (.inr 0),x.val.val.val (.inl 1) (.inr 1)) =
      (y.val.val.val (.inl 0) (.inr 0),y.val.val.val (.inl 1) (.inr 1)) at he
    simp only [←hx,←hy,element_matrix] at he
    change (u,v)=(z,a) at he
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    apply Subtype.ext
    rw [←hx,←hy]
  exact hcard.not_ge (by simpa only [Nat.card_prod,pow_two] using Nat.card_le_card_of_injective p hp)

/-- Every upper-plane actor above q² generates with the two prescribed
lower long roots, without changing either root by a further shear. -/
theorem large_plane_and_prescribed_roots_generate (hq : 2 < Nat.card F)
    (A : Subgroup (Sp F))
    (hAP : A ≤ (wing true).map (unipotent (F := F)).subtype)
    (hcard : Nat.card F^2 < Nat.card A) :
    (A ⊔ RootSubgroup.group 1) ⊔ RootSubgroup.group 3=⊤ := by
  let E := A.subgroupOf unipotent
  have hAU : A ≤ unipotent := hAP.trans (map_subtype_le _)
  have hEm : E.map unipotent.subtype=A := map_subgroupOf_eq_of_le hAU
  have hEP : E ≤ wing true := (map_le_map_iff_of_injective unipotent.subtype_injective).mp
    (hEm.symm ▸ hAP)
  have hEc : Nat.card F^2 < Nat.card E := by
    rw [←card_map_of_injective unipotent.subtype_injective,hEm]
    exact hcard
  let H := (A ⊔ RootSubgroup.group 1) ⊔ RootSubgroup.group 3
  have hE (x : unipotent (F := F)) (hx : x ∈ E) : x.val ∈ H :=
    mem_sup_left (mem_sup_left (hEm ▸ mem_map_of_mem unipotent.subtype hx))
  have h1 (t : F) : rootElement 1 t ∈ H :=
    mem_sup_left (mem_sup_right (subset_closure ⟨t,rfl⟩))
  have h3 (t : F) : rootElement 3 t ∈ H := mem_sup_right (subset_closure ⟨t,rfl⟩)
  obtain ⟨s,hs,hsE⟩ := nonzero_first_root_of_large E hEP hEc
  have hsH : rootElement 0 s ∈ H := by
    simpa [element,RootSubgroup.element_zero] using hE _ hsE
  have hswap : rootElement 0 s * rootElement 1 s⁻¹ * rootElement 0 s ∈ H :=
    H.mul_mem (H.mul_mem hsH (h1 _)) hsH
  have h0 (t : F) : rootElement 0 t ∈ H := by
    have hh := H.mul_mem (H.mul_mem hswap (h1 (t/s^2))) (H.inv_mem hswap)
    rw [IndividualMoverGeneration.long_swap _ _ hs,mul_div_cancel₀ _ (pow_ne_zero _ hs)] at hh
    exact hh
  obtain ⟨u,w,v,hx,hw⟩ := nonzero_cross_coordinate_of_large E hEP hEc
  exact SmallPlaneGeneration.cross_shear_generates hq H h0 h1 h3 (hE _ hx) hw

end Theory.SpecificGroups.SymplecticFour.PrescribedLargePlaneGeneration
