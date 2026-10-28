module

public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Quotients
public import Theory.GroupTheory.EmbeddedCenterMap
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.FieldTheory.Finiteness

/-!
# The plane and center-intersection geometry

The literal plane lies in E. The two identities in 12.8.10(1),(6)
therefore give equal cuts E∩V₂Z(U) = E∩V₂Z(U)^g. The disjoint point lines
have order two, so the two kernel intersections have equal orders.
Counting V₂/(V₂∩Z(U)) gives the nonzero line V₂hat and proves that the
conjugate commutator center V₁^g has exactly this image.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the proof
of Lemma 12.8.11(3–5), printed p.854 / PDF p.871. The earlier center
identities and seed-center intersection are explicit source inputs.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

private theorem inf_sup_of_le_of_normalizes (A B C : Subgroup G)
    (hA : A ≤ C) (hn : A ≤ normalizer (B : Set G)) :
    C ⊓ (A ⊔ B) = A ⊔ (C ⊓ B) := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (A : Set G) * (B : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right A B hn]
      exact hx.2
    obtain ⟨a,ha,b,hb,he⟩ := hx'
    have hbC : b ∈ C := by
      have := C.mul_mem (C.inv_mem (hA ha)) hx.1
      rwa [← he, inv_mul_cancel_left] at this
    rw [← he]
    exact mul_mem_sup ha ⟨hbC,hb⟩
  · exact sup_le (le_inf hA le_sup_left)
      (le_inf inf_le_left (inf_le_right.trans le_sup_right))

/-- The marked plane lies in both centralizers and hence in E. -/
theorem plane_le_E (F : InvariantFlag T V n) [IsMulCommutative V]
    (g : G) (hg : g ∈ F.Gi 2) : F.Vi 2 ≤ F.E g := by
  have hPW : F.Vi 2 ≤ F.W := by
    refine le_inf ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)) ?_
    intro a ha b hb
    exact congrArg Subtype.val (mul_comm (⟨b,F.le_seed 2 hb⟩ : V) ⟨a,F.le_seed 2 ha⟩)
  refine le_inf hPW ?_
  intro a ha
  refine ⟨g*a*g⁻¹, hPW ((mem_normalizer_iff.mp hg a).mp ha), ?_⟩
  simp [mul_assoc]

private theorem ZU_le_W (F : InvariantFlag T V n) : F.ZU ≤ F.W := by
  refine le_inf (map_subtype_le _) ?_
  rintro z ⟨u, hu, rfl⟩ a ha
  exact congrArg Subtype.val (mem_center_iff.mp hu
    ⟨a, (F.le_seed 2).trans (le_conjugateSpanBy V F.H) ha⟩)

/-- The conjugate centralizer is the literal intersection in U^g. -/
theorem X_eq_conjugate_U_inf (F : InvariantFlag T V n) (g : G)
    (hg : g ∈ F.Gi 2) :
    F.X g = conjugate F.U g ⊓ centralizer (F.Vi 2 : Set G) := by
  change (F.U ⊓ centralizer (F.Vi 2 : Set G)).map (MulAut.conj g⁻¹).toMonoidHom = _
  rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective]
  have he := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (centralizer (F.Vi 2 : Set G) : Set G)).inv_mem
      (normalizer_le_normalizer_centralizer _ hg))
  change _ ⊓ ((centralizer (F.Vi 2 : Set G)).map (MulAut.conj g⁻¹ : G →* G)) = _
  rw [he]
  rfl

/-- The center-intersection cuts of 12.8.10(1),(6), restricted to the actual E. -/
theorem E_inf_centers (F : InvariantFlag T V n) (g : G) (hg : g ∈ F.Gi 2) :
    F.E g ⊓ F.ZU = F.ZU ⊓ conjugate F.U g ∧
      F.E g ⊓ conjugate F.ZU g = conjugate F.ZU g ⊓ F.U := by
  have hZ := ZU_le_W F
  have hZg := F.conjugate_ZU_le_X g
  have hX := F.X_le_plane_centralizer g hg
  have heq := X_eq_conjugate_U_inf F g hg
  constructor
  · apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans (inf_le_right.trans (heq.le.trans inf_le_left)))
    · intro a ha
      exact ⟨⟨hZ ha.1, heq.ge ⟨ha.2, (hZ ha.1).2⟩⟩, ha.1⟩
  · apply le_antisymm
    · exact le_inf inf_le_right (inf_le_left.trans (inf_le_left.trans inf_le_left))
    · intro a ha
      exact ⟨⟨⟨ha.2, hX (hZg ha.1)⟩,hZg ha.1⟩,ha.1⟩

/-- The two cuts through V₂ agree, derived from the exact earlier center
intersections rather than assumed as a transvection premise. -/
theorem E_plane_center_cuts (F : InvariantFlag T V n) [IsMulCommutative V]
    (g : G) (hg : g ∈ F.Gi 2)
    (hZ : F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1)
    (hZg : conjugate F.ZU g ⊓ F.U =
      (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g) :
    F.E g ⊓ (F.Vi 2 ⊔ conjugate F.ZU g) = F.E g ⊓ (F.Vi 2 ⊔ F.ZU) := by
  have hP := plane_le_E F g hg
  have hpn : F.Vi 2 ≤ normalizer (F.ZU : Set G) :=
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)).trans
      (F.U_le_H.trans ((le_normalizer_conjugateSpanBy V F.H).trans
        (normalizer_le_normalizer_characteristic_image F.U (center F.U))))
  have hpc : F.Vi 2 ≤ centralizer (conjugate F.ZU g : Set G) :=
    le_centralizer_iff.mp ((F.conjugate_ZU_le_X g).trans (F.X_le_plane_centralizer g hg))
  rw [inf_sup_of_le_of_normalizes _ _ _ hP (hpc.trans (centralizer_le_normalizer _)),
    inf_sup_of_le_of_normalizes _ _ _ hP hpn,
    (E_inf_centers F g hg).1, (E_inf_centers F g hg).2, hZ, hZg]
  have hP1 : F.Vi 1 ≤ F.Vi 2 := F.monotone (by omega)
  have hP1g : conjugate (F.Vi 1) g ≤ F.Vi 2 := by
    rintro a ⟨b,hb,rfl⟩
    exact (mem_normalizer_iff.mp ((normalizer (F.Vi 2 : Set G)).inv_mem hg) b).mp (hP1 hb)
  rw [← sup_assoc, sup_eq_left.mpr (hP1g.trans le_sup_left),
    ← sup_assoc, sup_eq_left.mpr (hP1.trans le_sup_left)]

/-- Counting the actual central-quotient image retains the embedded kernel. -/
theorem card_hatImage_mul_card_inf (F : InvariantFlag T V n) (A : Subgroup G)
    (hA : A ≤ F.U) :
    Nat.card (hatImage F A) * Nat.card (A ⊓ F.ZU : Subgroup G) = Nat.card A := by
  have hc := (hatMap F A hA).ker.index_mul_card
  rw [index_ker, MonoidHom.range_eq_top.mpr (hatMap_surjective F A hA), card_top,
    hatMap_ker, ← card_map_of_injective (K := F.ZU.subgroupOf A) A.subtype_injective,
    subgroupOf_map_subtype, inf_comm] at hc
  exact hc

/-- The additive and multiplicative images have exactly the same carrier. -/
theorem card_hatSpace (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (A : Subgroup G) : Nat.card (hatSpace F A) = Nat.card (hatImage F A) := by
  exact Nat.card_congr {
    toFun := fun a => ⟨a.val.toMul,a.property⟩
    invFun := fun a => ⟨Additive.ofMul a.val,a.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

/-- V₂hat has order two, using the precise center intersection of 12.8.8(3). -/
theorem card_plane_hat (F : InvariantFlag T V n) (hn : 2 ≤ n)
    (hVZ : V ⊓ F.ZU = F.Vi 1) : Nat.card (hatImage F (F.Vi 2)) = 2 := by
  have hi : F.Vi 2 ⊓ F.ZU = F.Vi 1 := by
    apply le_antisymm
    · rw [← hVZ]
      exact inf_le_inf (F.le_seed 2) le_rfl
    · exact le_inf (F.monotone (by omega)) (hVZ.ge.trans inf_le_right)
  have hc := card_hatImage_mul_card_inf F (F.Vi 2)
    ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))
  rw [hi, F.card 1 (by omega), F.card 2 hn] at hc
  omega

/-- The center of the conjugate extraspecial factor, V₁^g, maps onto exactly
V₂hat. Its disjointness from Z(U) proves that its image is nontrivial. -/
theorem conjugate_point_hat_eq_plane (F : InvariantFlag T V n) [Finite G]
    (hn : 2 ≤ n) (g : G) (hg : g ∈ F.Gi 2)
    (hVZ : V ⊓ F.ZU = F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU) :
    hatImage F (conjugate (F.Vi 1) g) = hatImage F (F.Vi 2) := by
  have hP : conjugate (F.Vi 1) g ≤ F.Vi 2 := by
    rintro a ⟨b,hb,rfl⟩
    exact (mem_normalizer_iff.mp ((normalizer (F.Vi 2 : Set G)).inv_mem hg) b).mp
      (F.monotone (by omega : 1 ≤ 2) hb)
  have hc := card_hatImage_mul_card_inf F (conjugate (F.Vi 1) g)
    (hP.trans ((F.le_seed 2).trans (le_conjugateSpanBy V F.H)))
  rw [hdis.eq_bot, card_bot, mul_one,
    show Nat.card (conjugate (F.Vi 1) g) = Nat.card (F.Vi 1) from
      card_map_of_injective (MulAut.conj g⁻¹).injective,
    F.card 1 (by omega)] at hc
  apply eq_of_le_of_card_ge (map_mono (comap_mono hP))
  change Nat.card (hatImage F (F.Vi 2)) ≤ Nat.card (hatImage F (conjugate (F.Vi 1) g))
  rw [card_plane_hat F hn hVZ, hc]
  norm_num

/-- A nonzero vector spanning the plane image inside the actual Ehat. -/
theorem exists_plane_hat_generator (F : InvariantFlag T V n)
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (hn : 2 ≤ n) (g : G) (hg : g ∈ F.Gi 2) (hVZ : V ⊓ F.ZU = F.Vi 1) :
    ∃ v : hatSpace F (F.E g), (v : Additive F.Uhat) ≠ 0 ∧
      Submodule.span (ZMod 2) {(v : Additive F.Uhat)} = hatSpace F (F.Vi 2) := by
  have hc : Nat.card (hatSpace F (F.Vi 2)) = 2 :=
    (card_hatSpace F _).trans (card_plane_hat F hn hVZ)
  obtain ⟨v,hv,huniq⟩ := (Nat.card_eq_two_iff' (0 : hatSpace F (F.Vi 2))).mp hc
  have hvE : (v : Additive F.Uhat) ∈ hatSpace F (F.E g) :=
    (map_mono (f := QuotientGroup.mk' (center F.U)) (comap_mono (plane_le_E F g hg)))
      (show v.val.toMul ∈ hatImage F (F.Vi 2) from v.property)
  refine ⟨⟨v,hvE⟩, fun he => hv (Subtype.ext he), le_antisymm ?_ ?_⟩
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr v.property)
  · intro e he
    by_cases hzero : e = 0
    · rw [hzero]; exact Submodule.zero_mem _
    · have heq := huniq ⟨e,he⟩ (fun he0 => hzero (congrArg Subtype.val he0))
      rw [show e = (v : Additive F.Uhat) from congrArg Subtype.val heq]
      exact Submodule.mem_span_singleton_self _

/-- Symmetry of the disjoint central lines is justified by conjugating the
literal plane-center intersection. -/
theorem point_disjoint_conjugate_center (F : InvariantFlag T V n)
    [IsMulCommutative V] (hn : 2 ≤ n) (g : G) (hg : g ∈ F.Gi 2)
    (hVZ : V ⊓ F.ZU = F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU) :
    Disjoint (F.Vi 1) (conjugate F.ZU g) := by
  have hi : F.Vi 2 ⊓ F.ZU = F.Vi 1 := by
    apply le_antisymm
    · rw [← hVZ]; exact inf_le_inf (F.le_seed 2) le_rfl
    · exact le_inf (F.monotone (by omega)) (F.point_le_ZU (by omega))
  have hPi : F.Vi 2 ⊓ conjugate F.ZU g = conjugate (F.Vi 1) g := by
    simp only [conjugate, ← hi]
    rw [map_inf _ _ (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective]
    have he : (F.Vi 2).map (MulAut.conj g⁻¹).toMonoidHom = F.Vi 2 :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (F.Vi 2 : Set G)).inv_mem hg)
    rw [he]
  apply disjoint_iff.mpr
  apply le_antisymm ?_ bot_le
  intro a ha
  exact hdis.le_bot ⟨hPi.le ⟨F.monotone (by omega : 1 ≤ 2) ha.1, ha.2⟩,
    F.point_le_ZU (by omega) ha.1⟩

/-- The two intersections that occur in the rank count have the same order,
by 12.8.10(1),(6) and the two disjoint central lines of order two. -/
theorem card_E_inf_centers_eq (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] (hn : 2 ≤ n) (g : G) (hg : g ∈ F.Gi 2)
    (hVZ : V ⊓ F.ZU = F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (hZ : F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1)
    (hZg : conjugate F.ZU g ⊓ F.U =
      (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g) :
    Nat.card (F.E g ⊓ F.ZU : Subgroup G) =
      Nat.card (F.E g ⊓ conjugate F.ZU g : Subgroup G) := by
  let C := F.ZU ⊓ conjugate F.ZU g
  have hC : C ≤ centralizer (F.Vi 2 : Set G) :=
    inf_le_left.trans ((ZU_le_W F).trans inf_le_right)
  have hPC : F.Vi 2 ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp hC).trans (centralizer_le_normalizer _)
  have hP1 : F.Vi 1 ≤ F.Vi 2 := F.monotone (by omega)
  have hP1g : conjugate (F.Vi 1) g ≤ F.Vi 2 := by
    rintro a ⟨b,hb,rfl⟩
    exact (mem_normalizer_iff.mp ((normalizer (F.Vi 2 : Set G)).inv_mem hg) b).mp (hP1 hb)
  have hd : Disjoint C (F.Vi 1) :=
    (point_disjoint_conjugate_center F hn g hg hVZ hdis).symm.mono_left inf_le_right
  have hdg : Disjoint C (conjugate (F.Vi 1) g) := hdis.symm.mono_left inf_le_left
  rw [(E_inf_centers F g hg).1, (E_inf_centers F g hg).2, hZ, hZg,
    card_sup_eq_mul_of_normalizes_of_disjoint C _ (hP1.trans hPC) hd,
    card_sup_eq_mul_of_normalizes_of_disjoint C _ (hP1g.trans hPC) hdg]
  rw [show Nat.card (conjugate (F.Vi 1) g) = Nat.card (F.Vi 1) from
    card_map_of_injective (MulAut.conj g⁻¹).injective]

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
