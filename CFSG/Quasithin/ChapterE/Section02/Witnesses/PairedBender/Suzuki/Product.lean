module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.PairedBender.Linear
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.BenderPlacement.OriginalModels
public import Theory.SpecificGroups.Suzuki.SchurCoverReduction
public import Theory.ElementaryAbelian.Injective
/-!
# The marked quotient of the paired Suzuki construction

A genuine first-factor Suzuki witness is perfect, so the two conjugates
of the original elementary subgroup generate its product with the second
projection. The prescribed Sylow and Borel pullbacks identify the original
maximal intersection and its normal core. The resulting literal quotient
is the Suzuki witness, with the same odd degree divisor and Borel marking.

Source: Aschbacher–Smith E.2.7, printed p.219.
-/

public section
noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.PairedBender.Suzuki
variable {H : Type*} [Group H] [Finite H]

private theorem model_witness
    {G : Type*} [Group G] [Finite G] {m : ℕ} (hm : 0<m)
    (e : G ≃* SuzukiMatrixGroup m) (S : Sylow 2 G) (U : Subgroup G)
    [IsElementaryAbelian 2 U] (hUS : U ≤ S) (hc : 4≤Nat.card U) :
    Nonempty (BenderPlacement.SuzukiWitness S (normalizer (S : Set G)) U m) := by
  let W := U.map e.toMonoidHom
  let Q := S.mapSurjective (f:=e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hcW : 4≤Nat.card W := by rw [card_map_of_injective e.injective]; exact hc
  have hr : 1<primeRank 2 W := by
    by_contra h
    have ht : IsElementaryAbelian 2 (⊤ : Subgroup W) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup W).subtype Subtype.val_injective
    have hh := (primeRank_le_iff_elementary_card_le W).mp (Nat.le_of_not_gt h) ⊤ ht
    rw [card_top,pow_one] at hh
    omega
  obtain ⟨w⟩ := Witnesses.Suzuki.source_witness_of_le_sylow hm Q W (map_mono hUS) hr
  have hS : (S : Subgroup G).comap e.symm.toMonoidHom = Q :=
    comap_equiv_eq_map_symm e.symm (S : Subgroup G)
  have hM : (normalizer (S : Set G)).comap e.symm.toMonoidHom =
      normalizer (Q : Set (SuzukiMatrixGroup m)) := by
    change (normalizer ((S : Subgroup G) : Set G)).comap e.symm.toMonoidHom = _
    rw [comap_normalizer_eq_of_surjective (f:=e.symm.toMonoidHom) _ e.symm.surjective,hS]
    rfl
  have hW : W.map e.symm.toMonoidHom = U := by
    rw [Subgroup.map_map]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext x; exact e.symm_apply_apply x
    rw [he,Subgroup.map_id]
  have result := BenderPlacement.SuzukiWitness.map_model w e.symm.toMonoidHom e.symm.injective
    S (normalizer (S : Set G)) hS hM
  rw [hW] at result
  exact ⟨result⟩

/-- Construct the original marked Suzuki quotient from the actual first projection. -/
theorem exists_product
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    {m : ℕ} (hm : 0<m) (e : G ≃* SuzukiMatrixGroup m)
    (S : Sylow 2 G) (S2 M2 : Subgroup A)
    (V : Subgroup (G × A)) [IsElementaryAbelian 2 V]
    (hVS : V ≤ (S : Subgroup G).prod S2)
    (hVM : V.map (MonoidHom.snd G A) ≤ M2)
    (hc : 4 ≤ Nat.card (V.map (MonoidHom.fst G A)))
    (T : Sylow 2 H) (M : Subgroup H) (f : G × A →* H)
    (hf : Function.Injective f)
    (hT : (T : Subgroup H).comap f = (S : Subgroup G).prod S2)
    (hM : M.comap f = (normalizer (S : Set G)).prod M2) :
    Nonempty (BenderPlacement.OriginalWitness T M (V.map f) (2*m+1)) := by
  let : IsElementaryAbelian 2 (V.map (MonoidHom.fst G A)) := IsElementaryAbelian.map _
  obtain ⟨w⟩ := model_witness hm e S (V.map (MonoidHom.fst G A)) (le_prod_iff.mp hVS).1 hc
  let : Group.IsPerfect (SuzukiMatrixGroup w.parameter) := SchurCover.isPerfect _ w.positive
  let : Group.IsPerfect w.pair.subgroup :=
    Group.IsPerfect.ofSurjective (f:=w.equiv.symm.toMonoidHom) w.equiv.symm.surjective
  have hS0 : (w.pair.sylow : Subgroup w.pair.subgroup) = (S : Subgroup G).subgroupOf w.pair.subgroup := by
    apply Subgroup.map_injective w.pair.subgroup.subtype_injective
    rw [w.pair.sylow_eq,subgroupOf_map_subtype]
  let w₀ : TwoConjugateProduct.CoreFreePair (S : Subgroup G)
      (normalizer (S : Set G)) (V.map (MonoidHom.fst G A)) :=
    ⟨w.pair.subgroup,w.pair.le,w.pair.conjugator,w.pair.generate,w.pair.sylow,hS0,w.core_eq_bot⟩
  let : IsElementaryAbelian 2 (V.map (MonoidHom.snd G A)) := IsElementaryAbelian.map _
  let z := w₀.product (IsElementaryAbelian.isPGroup 2 _) S2 M2
    (le_prod_iff.mp hVS).2 hVM
  let u := z.map f hf (T : Subgroup H) M hT hM
  let d := u.quotientEquiv.trans w.equiv
  have hb : ∃c:SuzukiMatrixGroup w.parameter,
      ((M.subgroupOf u.subgroup).map (QuotientGroup.mk' _)).map d.toMonoidHom =
        (SuzukiBorelSubgroup w.parameter).map (MulAut.conj c).toMonoidHom := by
    change ∃c, ((M.subgroupOf u.subgroup).map (QuotientGroup.mk' _)).map
      (w.equiv.toMonoidHom.comp u.quotientEquiv.toMonoidHom) = _
    rw [←Subgroup.map_map,u.quotient_borel]
    exact w.borel_conjugate
  exact ⟨⟨ProductPair.toPair u,2*w.parameter+1,by omega,w.degree_dvd,
    .suzuki w.parameter w.positive rfl d hb⟩⟩
end CFSG.Quasithin.ChapterE.Witnesses.PairedBender.Suzuki
