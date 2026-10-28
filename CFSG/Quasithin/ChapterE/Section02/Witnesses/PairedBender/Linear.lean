module
public import Theory.GroupTheory.TwoConjugateProduct.Witness
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearTwo.Source
public import GorensteinWalter.SL2ProjectiveCover

/-!
# Marked paired linear quotient witnesses

Apply the genuine first-factor SL₂ witness to the original first projection.
Its perfectness makes the original two-conjugate subgroup the product with
the second projection. Marked multiplication transports the prescribed
Sylow and Borel, and the exact relative Borel core is the two-group kernel.
The quotient retains the field-degree divisibility and concrete Borel image.

Source: Aschbacher–Smith E.2.7, printed p.219.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedBender
variable {H : Type*} [Group H] [Finite H]

structure LinearWitness (T : Sylow 2 H) (M V : Subgroup H) (n : ℕ) where
  pair : QuotientLift.Pair T M V
  degree : ℕ
  degree_gt_one : 1 < degree
  degree_dvd : degree ∣ n
  model : pair.subgroup ⧸ (M.subgroupOf pair.subgroup).normalCore ≃*
    SL(2,GaloisField 2 degree)
  borel_model : ((M.subgroupOf pair.subgroup).map (QuotientGroup.mk' _)).map model.toMonoidHom =
    SpecialLinearGroup.rankOneBorel (GaloisField 2 degree)

namespace ProductPair
open TwoConjugateProduct
variable {M V : Subgroup H} {T : Sylow 2 H} {L : Type*} [Group L]
def toPair (w : TwoConjugateProduct.ProductPair (T : Subgroup H) M V L) :
    QuotientLift.Pair T M V := by
  have hp : IsPGroup 2 (M.subgroupOf w.subgroup).normalCore := w.core_eq.symm ▸ w.kernel_two
  let P : Sylow 2 (M.subgroupOf w.subgroup).normalCore := default
  have hP : (P : Subgroup (M.subgroupOf w.subgroup).normalCore) = ⊤ :=
    (P.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  refine ⟨w.subgroup,w.le,w.conjugator,w.generate,w.sylow,?_,⟨P,?_⟩⟩
  · rw [w.sylow_eq,subgroupOf_map_subtype]
  · rw [hP]
    infer_instance
end ProductPair

omit [Finite H] in
theorem exists_linear_product
    {G A F : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [Field F] [Finite F] [CharP F 2] {n : ℕ} (hF : Nat.card F = 2^n)
    (e : G ≃* SL(2,F)) (S : Sylow 2 G) (S2 M2 : Subgroup A)
    (V : Subgroup (G × A)) [IsElementaryAbelian 2 V]
    (hVS : V ≤ (S : Subgroup G).prod S2)
    (hVM : V.map (MonoidHom.snd G A) ≤ M2)
    (hc : 4 ≤ Nat.card (V.map (MonoidHom.fst G A)))
    (T : Sylow 2 H) (M : Subgroup H) (f : G × A →* H)
    (hf : Function.Injective f)
    (hT : (T : Subgroup H).comap f = (S : Subgroup G).prod S2)
    (hM : M.comap f = (normalizer (S : Set G)).prod M2) :
    Nonempty (LinearWitness T M (V.map f) n) := by
  obtain ⟨w⟩ := SpecialLinearGroup.TwoConjugateWitness.exists_of_equiv hF e S
    (V.map (MonoidHom.fst G A)) (le_prod_iff.mp hVS).1 hc
  have hlarge : 3 < Nat.card (GaloisField 2 w.degree) := by
    rw [GaloisField.card 2 w.degree (by have := w.degree_gt_one; omega)]
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (by have := w.degree_gt_one; omega : 2 ≤ w.degree)
    omega
  let : Group.IsPerfect SL(2,GaloisField 2 w.degree) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three _ hlarge
  let : Group.IsPerfect w.subgroup :=
    Group.IsPerfect.ofSurjective (f := w.model.symm.toMonoidHom) w.model.symm.surjective
  let w₀ : TwoConjugateProduct.CoreFreePair (S : Subgroup G)
      (normalizer (S : Set G)) (V.map (MonoidHom.fst G A)) :=
    ⟨w.subgroup,w.le,w.conjugator,w.generate,w.sylow,w.sylow_eq,w.corefree⟩
  let : IsElementaryAbelian 2 (V.map (MonoidHom.snd G A)) := IsElementaryAbelian.map _
  let z := w₀.product (IsElementaryAbelian.isPGroup 2 _) S2 M2
    (le_prod_iff.mp hVS).2 hVM
  let u := z.map f hf (T : Subgroup H) M hT hM
  let d := u.quotientEquiv.trans w.model
  have hb : ((M.subgroupOf u.subgroup).map (QuotientGroup.mk' _)).map d.toMonoidHom =
      SpecialLinearGroup.rankOneBorel (GaloisField 2 w.degree) := by
    change ((M.subgroupOf u.subgroup).map (QuotientGroup.mk' _)).map
      (w.model.toMonoidHom.comp u.quotientEquiv.toMonoidHom) = _
    rw [← Subgroup.map_map,u.quotient_borel]
    exact w.borel_model
  exact ⟨⟨ProductPair.toPair u,w.degree,w.degree_gt_one,w.degree_dvd,d,hb⟩⟩
end CFSG.Quasithin.ChapterE.Witnesses.PairedBender
