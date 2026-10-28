module

public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.HolomorphGeometry.Centralizers
public import Theory.PPrimeCore

/-!
# Coverage inside the actual automorphism group of A₆

The computed finite Sylow model has center of order two. An equivalence
with an actual Sylow subgroup of Aut(A₆) therefore excludes a faithful
central four-group in that Sylow subgroup. Applied to conjugation, this
excludes a surjection onto Aut(A₆). Since its order is 1440, a subgroup
isomorphic to S₆ already exhausts any proper subgroup containing it.
The final lemma carries this order argument through the actual quotient
by O_{3′}(I), and proves equality of subgroups in that quotient.

`SylowModel` isolates the intermediate model input for these lemmas.
The parent `RawQuotient` module discharges it with the proved equivalence
from Theory.SpecificGroups.AlternatingSix.ShadowLocal.Identification.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of 15.4.18,
printed pp.1162–1163; the Aut(A₆) Sylow calculation on pp.567–570.
-/

@[expose] public section

open Subgroup
open AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.RawQuotient

/-- Only the unmarked equivalence from the independent Sylow identification is used. -/
def SylowModel : Prop := ∀ P : Sylow 2 AutA6, Nonempty (Holomorph.Model ≃* P)

theorem model_center_card : Nat.card (center Holomorph.Model) = 2 := by
  rw [Holomorph.center_model, ← Holomorph.centralEmbedding_range,
    ← Nat.card_congr (MonoidHom.ofInjective Holomorph.centralEmbedding_injective).toEquiv]
  simp [Holomorph.C2, Nat.card_eq_fintype_card]

theorem sylow_center_card_of_model (model : SylowModel) (P : Sylow 2 AutA6) :
    Nat.card (center (P : Subgroup AutA6)) = 2 := by
  obtain ⟨e⟩ := model P
  exact (Nat.card_congr (Subgroup.centerCongr e).toEquiv).symm.trans model_center_card

variable {I : Type*} [Group I] [Finite I]

/-- A central four-group in a Sylow subgroup obstructs surjectivity onto Aut(A6). -/
theorem not_surjective_of_central_four (model : SylowModel)
    (S : Sylow 2 I) (Z : Subgroup I) (hZS : Z ≤ (S : Subgroup I))
    (hSZ : (S : Subgroup I) ≤ centralizer (Z : Set I)) (hZ : Nat.card Z = 4)
    (f : I →* AutA6) (hker : Disjoint Z f.ker) : ¬ Function.Surjective f := by
  intro hf
  let P : Sylow 2 AutA6 := S.mapSurjective hf
  let A : Subgroup AutA6 := Z.map f
  have hAP : A ≤ (P : Subgroup AutA6) := Subgroup.map_mono hZS
  have hfinj : Function.Injective (f.subgroupMap Z) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.ker_subgroupMap, Subgroup.subgroupOf_eq_bot]
    exact hker.symm
  have hA : Nat.card A = 4 :=
    (Nat.card_congr (MulEquiv.ofBijective (f.subgroupMap Z)
      ⟨hfinj, f.subgroupMap_surjective Z⟩).toEquiv).symm.trans hZ
  have hc (x : AutA6) (hx : x ∈ A) (y : AutA6) (hy : y ∈ (P : Subgroup AutA6)) :
      y * x = x * y := by
    obtain ⟨z, hz, rfl⟩ := hx
    obtain ⟨s, hs, rfl⟩ := hy
    rw [← map_mul, ← map_mul, (hSZ hs z hz).symm]
  let j : A → center (P : Subgroup AutA6) := fun x =>
    ⟨⟨x, hAP x.property⟩, mem_center_iff.mpr fun y =>
      Subtype.ext (hc x x.property y y.property)⟩
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : center (P : Subgroup AutA6) => z.val.val) h)
  have hle := Nat.card_le_card_of_injective j hj
  rw [hA, sylow_center_card_of_model model P] at hle
  omega

/-- A subgroup of order 720 exhausts a proper subgroup of Aut(A6). The actual
quotient by the kernel is retained, so this proves coverage in the star quotient. -/
theorem coverage_of_proper_action (f : I →* AutA6)
    (hker : f.ker = pPrimeCore 3 I) (hn : ¬ Function.Surjective f)
    (H : Subgroup (I ⧸ pPrimeCore 3 I)) (eH : H ≃* Equiv.Perm (Fin 6)) :
    H = ⊤ := by
  let e : (I ⧸ pPrimeCore 3 I) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have hH : Nat.card H = 720 := by
    rw [Nat.card_congr eH.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    norm_num [Nat.factorial]
  have hd : 720 ∣ Nat.card (I ⧸ pPrimeCore 3 I) := hH ▸ H.card_subgroup_dvd_card
  have hc : Nat.card (I ⧸ pPrimeCore 3 I) ≤ 1440 := by
    rw [Nat.card_congr e.toEquiv, ← card_aut]
    exact f.range.card_le_card_group
  have hne : Nat.card (I ⧸ pPrimeCore 3 I) ≠ 1440 := by
    intro he
    apply hn
    apply MonoidHom.range_eq_top.mp
    apply f.range.eq_top_of_card_eq
    rw [← Nat.card_congr e.toEquiv, he, card_aut]
  have hpos : 0 < Nat.card (I ⧸ pPrimeCore 3 I) := Nat.card_pos
  obtain ⟨n, hcard⟩ := hd
  have hc' : Nat.card (I ⧸ pPrimeCore 3 I) = 720 := by omega
  exact H.eq_top_of_card_eq (hH.trans hc'.symm)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.ComponentBranch.AlternatingLocals.RawQuotient
