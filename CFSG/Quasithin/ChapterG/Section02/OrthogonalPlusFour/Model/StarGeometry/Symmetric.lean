module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Model.Points
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Ordered symmetric-group marking in G.2.6

The supplied ordered SL₂ factors identify the actual L-image with A₃ × A₃:
its odd order forces both signs to be trivial, and the inclusion has equal
orders. The actual U-image is a Sylow elementary four-group. Its projections
are the two Sylow subgroups of order two, and their product is exactly that
image. In particular the intersections with the ordered factors are retained.
Source: Aschbacher–Smith, G.2.6(5), printed p.336.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
namespace Hypothesis

private abbrev S3 := Equiv.Perm (Fin 3)
private theorem S3_card : Nat.card S3 = 6 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem S3_sylow_card (P : Sylow 2 S3) : Nat.card P = 2 := by
  rw [P.card_eq_multiplicity, S3_card]
  decide +kernel

private theorem map_fst_prod (A B : Subgroup S3) :
    (A.prod B).map (MonoidHom.fst S3 S3) = A := by
  ext x
  constructor
  · rintro ⟨⟨a,b⟩, ⟨ha, _⟩, rfl⟩
    exact ha
  · intro hx
    exact ⟨(x,1), ⟨hx, B.one_mem⟩, rfl⟩

private theorem map_snd_prod (A B : Subgroup S3) :
    (A.prod B).map (MonoidHom.snd S3 S3) = B := by
  ext x
  constructor
  · rintro ⟨⟨a,b⟩, ⟨_, hb⟩, rfl⟩
    exact hb
  · intro hx
    exact ⟨(1,x), ⟨A.one_mem, hx⟩, rfl⟩

private theorem four_subgroup_split (P : Subgroup (S3 × S3))
    (hp : IsPGroup 2 P) (hc : Nat.card P = 4) :
    P = (P.map (MonoidHom.fst S3 S3)).prod (P.map (MonoidHom.snd S3 S3)) ∧
      Nat.card (P.map (MonoidHom.fst S3 S3)) = 2 ∧
      Nat.card (P.map (MonoidHom.snd S3 S3)) = 2 := by
  obtain ⟨A, hA⟩ := (hp.map (MonoidHom.fst S3 S3)).exists_le_sylow
  obtain ⟨B, hB⟩ := (hp.map (MonoidHom.snd S3 S3)).exists_le_sylow
  have he : P = (A : Subgroup S3).prod B := eq_of_le_of_card_ge
    (le_prod_iff.mpr ⟨hA, hB⟩) (by
      rw [Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod,
        S3_sylow_card A, S3_sylow_card B, hc])
  rw [he, map_fst_prod, map_snd_prod]
  exact ⟨rfl, S3_sylow_card A, S3_sylow_card B⟩

variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

/-- The actual marked image under the existing ordered comparison. -/
def symmetricImage (A : Subgroup G) : Subgroup (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  (d.modelImage A).map pairPermEquiv.toMonoidHom

theorem symmetricImage_card (A : Subgroup G) :
    Nat.card (d.symmetricImage A) = Nat.card (d.modelImage A) :=
  card_map_of_injective pairPermEquiv.injective

/-- Both ordered alternating factors are precisely the original L-image. -/
theorem symmetricImage_L :
    d.symmetricImage D.L = (alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3)) := by
  have hc : Nat.card (d.symmetricImage D.L) = 9 :=
    (d.symmetricImage_card D.L).trans d.modelImage_L_card
  have even_of_pow (a : S3) (ha : a ^ 9 = 1) : a ∈ alternatingGroup (Fin 3) := by
    change Equiv.Perm.sign a = 1
    have hs := congrArg Equiv.Perm.sign ha
    rw [map_pow, map_one, Int.units_pow_eq_pow_mod_two] at hs
    simpa using hs
  apply eq_of_le_of_card_ge
  · intro a ha
    have hp : a ^ 9 = 1 := by
      have ht := congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, ha⟩ : d.symmetricImage D.L)))
      simpa only [hc, coe_pow, coe_one] using ht
    exact ⟨even_of_pow a.1 (congrArg Prod.fst hp),
      even_of_pow a.2 (congrArg Prod.snd hp)⟩
  · rw [Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod, hc]
    rw [nat_card_alternatingGroup, Nat.card_fin]
    decide

theorem symmetricImage_U_card : Nat.card (d.symmetricImage D.U) = 4 :=
  (d.symmetricImage_card D.U).trans d.modelImage_U_card

theorem symmetricImage_U_elementary : IsElementaryAbelian 2 (d.symmetricImage D.U) := by
  let := d.modelImage_U_elementary
  exact IsElementaryAbelian.map pairPermEquiv.toMonoidHom

/-- The actual U-image, exhibited as a Sylow subgroup on the symmetric carrier. -/
def symmetricUSylow : Sylow 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) :=
  Sylow.ofCard (d.symmetricImage D.U) (by
    rw [d.symmetricImage_U_card, Nat.card_prod, S3_card]
    decide +kernel)

theorem symmetricUSylow_coe : (d.symmetricUSylow : Subgroup _) = d.symmetricImage D.U := rfl

/-- Projection to the first ordered symmetric factor. -/
def symmetricUFirst : Subgroup (Equiv.Perm (Fin 3)) :=
  (d.symmetricImage D.U).map (MonoidHom.fst _ _)

/-- Projection to the second ordered symmetric factor. -/
def symmetricUSecond : Subgroup (Equiv.Perm (Fin 3)) :=
  (d.symmetricImage D.U).map (MonoidHom.snd _ _)

/-- The projected involutions occur independently, not as a diagonal subgroup. -/
theorem symmetricImage_U_split :
    d.symmetricImage D.U = d.symmetricUFirst.prod d.symmetricUSecond ∧
      Nat.card d.symmetricUFirst = 2 ∧ Nat.card d.symmetricUSecond = 2 :=
  four_subgroup_split _ (d.modelImage_U_isPGroup.map pairPermEquiv.toMonoidHom)
    d.symmetricImage_U_card

theorem symmetricImage_U_inf_first :
    d.symmetricImage D.U ⊓ (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ =
      d.symmetricUFirst.prod ⊥ := by
  rw [d.symmetricImage_U_split.1]
  ext a
  simp only [mem_inf, mem_prod, mem_top, mem_bot]
  constructor
  · exact fun h => ⟨h.1.1, h.2.2⟩
  · intro h
    exact ⟨⟨h.1, h.2 ▸ d.symmetricUSecond.one_mem⟩, trivial, h.2⟩

theorem symmetricImage_U_inf_second :
    d.symmetricImage D.U ⊓ (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod ⊤ =
      (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod d.symmetricUSecond := by
  rw [d.symmetricImage_U_split.1]
  ext a
  simp only [mem_inf, mem_prod, mem_top, mem_bot, and_true]
  constructor
  · exact fun h => ⟨h.2, h.1.2⟩
  · intro h
    exact ⟨⟨h.1 ▸ d.symmetricUFirst.one_mem, h.2⟩, h.1⟩

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
