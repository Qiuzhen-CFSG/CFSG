module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Normalizer.Source
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Normalizer
public import Theory.GroupTheory.OddInvolutionEndpointModels
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# The normalizer in the first closure case

For S = N_T(H₁), the exchanged factors give H₀ = O²(H)S and
H₀/O₂(H₀) ≅ S₃ × S₃. If O²(H) is normal in Mc, then N_Mc(S)
normalizes H₀. Its two-residual is a {2,3}-group; the rank-two pair
placement theorem puts it in H₀. The already proved N_H(S)=T then
places this residual in T, and the Sylow supplement gives N_Mc(S)=T.

The source application derives the three-rank bound from the original
maximal two-local Mc. It retains p=3, the maximal-prime choice and exactly
the first closure alternative as explicit branch premises. Their source
assembly remains with qt-e-suitable-odd-normalizer; the independent
quintic exclusion is owned by qt-e-14615-quintic-exclusion.

Source: Aschbacher--Smith 14.6.16, printed p.1035. The pair placement
replaces the coordinate-line argument with its proved rank consequence.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

/-- The intrinsic two-core quotient of H₀ is the actual symmetric-three pair
when the exchanged-factor prime is three. -/
theorem exchanged_zero_quotient_pair
    (a : LocalQuotientAction H U Z) (T : Subgroup G)
    (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T 3 H0 H1 H2) :
    Nonempty ((H0 ⧸ pCore 2 H0) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  let : (H0.subgroupOf H).Normal := normal_of_index_eq_two d.index
  let e0 := subgroupOfEquivOfLe d.zero_le
  let eq := QuotientGroup.congr (pCore 2 (H0.subgroupOf H)) (pCore 2 H0) e0
    (pCore_map_iso 2 e0)
  let ei := (Normal.isSubnormal (inferInstance : (H0.subgroupOf H).Normal)).quotientCoreImageEquiv 2
  have he : actorImage H H0 = actorImage H H1 ⊔ actorImage H H2 := by
    unfold actorImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup (d.first_le.trans d.zero_le)
      (d.second_le.trans d.zero_le), d.join_eq]
  obtain ⟨ec,_⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting
    (actorImage H H1) (actorImage H H2) d.actors_disjoint
    (fun x hx y hy => (d.actors_commute x hx y hy).symm)
  obtain ⟨e1⟩ := d.first_model
  obtain ⟨e2⟩ := d.second_model
  obtain ⟨es⟩ := nonempty_dihedralThreeEquivPerm
  exact ⟨eq.symm.trans (ei.trans ((MulEquiv.subgroupCongr he).trans
    (ec.symm.trans ((e1.trans es).prodCongr (e2.trans es)))))⟩

/-- The factor stabilizer supplements O²(H) in the original H₀. -/
theorem exchanged_zero_eq_residual_sup_stabilizer
    (a : LocalQuotientAction H U Z) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    H0 = residual H ⊔ ((T : Subgroup G) ⊓ normalizer (H1 : Set G)) := by
  let : (H0.subgroupOf H).Normal := normal_of_index_eq_two d.index
  have hK : residual H ≤ H0 := by
    have hq : IsPGroup 2 (H ⧸ H0.subgroupOf H) := IsPGroup.of_card (n := 1)
      (by rw [pow_one, ← index_eq_card]; exact d.index)
    have hr : pResidual 2 H ≤ H0.subgroupOf H := sInf_le ⟨inferInstance,hq⟩
    exact fun x hx => by obtain ⟨y,hy,rfl⟩ := hx; exact hr hy
  have hn := exchanged_factor_normalizer_eq a T hTH p H0 H1 H2 d
  have hS : (T : Subgroup G) ⊓ normalizer (H1 : Set G) = (T : Subgroup G) ⊓ H0 := by
    rw [← hn, ← inf_assoc, inf_of_le_left hTH]
  rw [hS]
  apply le_antisymm _ (sup_le hK inf_le_right)
  obtain ⟨P,hP⟩ := (T.subtype hTH).exists_subgroupOf_eq_of_normal (H0.subgroupOf H)
  let P0 := P.mapSurjective (f := (subgroupOfEquivOfLe d.zero_le).toMonoidHom)
    (subgroupOfEquivOfLe d.zero_le).surjective
  have hP0 : (P0 : Subgroup H0).map H0.subtype = (T : Subgroup G) ⊓ H0 := by
    change ((P : Subgroup (H0.subgroupOf H)).map _).map H0.subtype = _
    rw [map_map]
    have hc : H0.subtype.comp (subgroupOfEquivOfLe d.zero_le).toMonoidHom =
        H.subtype.comp (H0.subgroupOf H).subtype := rfl
    rw [hc,←map_map,hP,subgroupOf_map_subtype]
    rw [Subgroup.map_inf _ _ _ H.subtype_injective]
    simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
      map_subgroupOf_eq_of_le d.zero_le]
  have hh := congrArg (map H0.subtype) (pResidual_sup_sylow_eq_top P0)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype,hP0] at hh
  calc
    H0 = (pResidual 2 H0).map H0.subtype ⊔ ((T : Subgroup G) ⊓ H0) := hh.symm
    _ ≤ residual H ⊔ ((T : Subgroup G) ⊓ H0) :=
      sup_le_sup_right (embedded_pResidual_mono 2 d.zero_le) _

/-- A closed residual and {2,3}-order give the ambient local normalizer
equality. The two-residual of the normalizer lies in H₀ by rank-two pair
placement, and the earlier H-normalizer calculation completes the proof. -/
theorem exchanged_normalizer_of_closed_residual
    (a : LocalQuotientAction H U Z) (T : Sylow 2 G) (hTH : (T : Subgroup G) ≤ H)
    (Mc H0 H1 H2 : Subgroup G) (hHMc : H ≤ Mc)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hclosure : residualClosure H Mc = residual H)
    (hrank : primeRank 3 Mc ≤ 2)
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ Nat.card Mc → q = 2 ∨ q = 3) :
    Mc ⊓ normalizer (((T : Subgroup G) ⊓ normalizer (H1 : Set G) : Subgroup G) : Set G) =
      (T : Subgroup G) := by
  let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
  let N := Mc ⊓ normalizer (S : Set G)
  let B := residual N
  have hHn := exchanged_factor_normalizer_in_H a T hTH 3 H0 H1 H2 d
  have hTN : (T : Subgroup G) ≤ N :=
    le_inf (hTH.trans hHMc) (hHn.symm.le.trans inf_le_right)
  have hBMc : B ≤ Mc := (residual_le N).trans inf_le_left
  have h0Mc : H0 ≤ Mc := d.zero_le.trans hHMc
  have h0 := exchanged_zero_eq_residual_sup_stabilizer a T hTH 3 H0 H1 H2 d
  have hNK : Mc ≤ normalizer (residual H : Set G) := by
    rw [←hclosure]
    exact le_normalizer_conjugateSpanBy _ _
  have hN0 : N ≤ normalizer (H0 : Set G) := by
    rw [h0]
    exact (le_inf (inf_le_left.trans hNK) inf_le_right).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have ho : ∃ m n : ℕ, Nat.card B ∣ 2^m * 3^n := by
    have hd : Nat.card B ∣ 6 ^ Nat.card B :=
      (Nat.dvd_pow_self_iff Nat.card_pos.ne' (by decide : (6:ℕ) ≠ 0)).mpr (by
        intro q hq
        rcases hprimes q (Nat.prime_of_mem_primeFactors hq)
          ((Nat.dvd_of_mem_primeFactors hq).trans (card_dvd_of_le hBMc)) with rfl | rfl
        · exact Nat.mem_primeFactors.mpr ⟨by decide,by decide,by decide⟩
        · exact Nat.mem_primeFactors.mpr ⟨by decide,by decide,by decide⟩)
    exact ⟨Nat.card B,Nat.card B,by simpa only [show (6:ℕ)=2*3 from rfl,mul_pow] using hd⟩
  obtain ⟨eq⟩ := exchanged_zero_quotient_pair a (T : Subgroup G) H0 H1 H2 d
  have hB0 : B ≤ H0 := NormalSymmetricThreePairRank.le_of_normalizes_quotient_pair H0 B eq
    (isPPerfect_embedded_pResidual 2 N) ((residual_le N).trans hN0)
    ((primeRank_mono 3 (sup_le h0Mc hBMc)).trans hrank) ho
  have hBT : B ≤ (T : Subgroup G) := by
    rw [←hHn]
    exact le_inf (hB0.trans d.zero_le) ((residual_le N).trans inf_le_right)
  have hh := congrArg (map N.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTN))
  simp only [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN,
    ←MonoidHom.range_eq_map,range_subtype] at hh
  apply le_antisymm _ hTN
  rw [←hh]
  exact sup_le hBT le_rfl

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))


include hG hempty hM hunique hmany hcard e hab hH

/-- Original 14.6.16 in the first closure case. The rank bound is inherited
from the actual maximal two-local Mc; no normalizer or centralization premise
is added to that branch. -/
theorem source_normalizer_first_closure_case
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2)
    (hp : p = 3) (_hmax : MaximalOddPrime (T : Subgroup G) M p)
    (hclosure : residualClosure H Mc = residual H)
    (hprimes : ∀ q : ℕ, q.Prime → q ∣ Nat.card Mc → q = 2 ∨ q = 3) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    S.relIndex (T : Subgroup G) = 2 ∧ Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
  obtain ⟨hi,_⟩ := source_exchanged_normalizer_initial
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 d
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hunique.symm ▸ Set.mem_singleton Mc
  have hr : primeRank 3 Mc ≤ 2 :=
    (hG.twoLocal_sqtk hMc.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  subst p
  exact ⟨hi,exchanged_normalizer_of_closed_residual a T hH.1.2 Mc H0 H1 H2
    hHMc d hclosure hr hprimes⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
