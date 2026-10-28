module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.PointFixed
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2SylowFixed
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Theory.GroupTheory.ElementaryPairInvolutionUnion
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Involutions and rank in a conjugate pair of natural block modules

When two conjugate elementary modules span a Sylow factor, each is its own
centralizer in that factor. A noncentral natural actor detects the full fixed
space, so every involution lies in one module. The centerless natural quotient
gives rank at most `2n`, and the Sylow fixed line bounds their intersection by
rank `n`. These are the two factor estimates used for the outside involutions
in the double-linear source configuration.

Source: Aschbacher–Smith, proof of 2.4.7, printed p.540; C.1.12 and C.5.6.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] {R L : Subgroup G} {F : Type*} [Field F]

/-- With no central layer, the actual module has the order of its natural plane. -/
theorem card_U_of_center_eq_bot {n : ℕ} (hL : IsL2EvenBlock L n)
    (hZ : center L = ⊥) : Nat.card (U L) = 2^(2*n) := by
  have hb : blockFixed L = ⊥ := by
    apply le_antisymm _ bot_le
    intro u hu
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hZ ▸ hu)
  have he : BlockModule L ≃* blockU L :=
    (QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot
  rw [U, card_map_of_injective L.subtype_injective, ← Nat.card_congr he.toEquiv]
  simpa only [Nat.mul_comm n 2] using hL.module_card

private theorem inf_centralizer_U (h : Setup R L F) (P : Subgroup G)
    (hPL : P ≤ L) (hUP : U L ≤ P) (hcore : pCore 2 L = blockU L) :
    P ⊓ centralizer (U L : Set G) = U L := by
  apply le_antisymm
  · intro r hr
    have hrL := hPL hr.1
    have hc : (⟨r,hrL⟩ : L) ∈ centralizer (blockU L : Set L) := by
      intro u hu
      apply Subtype.ext
      exact hr.2 u (mem_map.mpr ⟨u,hu,rfl⟩)
    rw [h.short.centralizer_blockU, hcore] at hc
    exact mem_map.mpr ⟨⟨r,hrL⟩,hc,rfl⟩
  · let := h.elementary
    exact le_inf hUP (le_centralizer _)

/-- Every square-one element of the Sylow factor belongs to one of its modules. -/
theorem Setup.pair_involution_union (h : Setup R L F) (P : Subgroup G) (x : G)
    (hPS : P ≤ S R) (hPL : P ≤ L)
    (hpair : U L ⊔ (U L).map (MulAut.conj x⁻¹).toMonoidHom = P)
    (hxP : x ∈ normalizer (P : Set G)) (hcore : pCore 2 L = blockU L) :
    ∀ r ∈ P, r^2=1 → r ∈ U L ∨ r ∈ (U L).map (MulAut.conj x⁻¹).toMonoidHom := by
  let V := (U L).map (MulAut.conj x⁻¹).toMonoidHom
  have hUP : U L ≤ P := le_sup_left.trans_eq hpair
  have hVP : V ≤ P := le_sup_right.trans_eq hpair
  let : IsElementaryAbelian 2 (U L) := h.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hCU := inf_centralizer_U h P hPL hUP hcore
  have hPx : P.map (MulAut.conj x⁻¹).toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (P : Set G)).inv_mem hxP)
  have hCV : P ⊓ centralizer (V : Set G) = V := by
    have he := congrArg (fun W : Subgroup G => W.map (MulAut.conj x⁻¹).toMonoidHom) hCU
    rw [map_inf _ _ _ (MulAut.conj x⁻¹).injective, hPx,
      Theory.GroupTheory.map_centralizer_equiv] at he
    exact he
  apply elementary_pair_involution_union P (U L) V hpair
    (hVP.trans (hPS.trans h.coordinates.normalizes))
  intro v hv hvU u hu hc
  have hvS := hPS (hVP hv)
  have hvc : v ∉ centralizer (U L : Set G) := by
    intro hh
    exact hvU (hCU ▸ (show v ∈ P ⊓ centralizer (U L : Set G) from ⟨hVP hv,hh⟩))
  have hfU : moduleConjugate h.coordinates.normalizes ⟨v,hvS⟩ ⟨u,hu⟩ = ⟨u,hu⟩ := by
    apply Subtype.ext
    change v*u*v⁻¹=u
    rw [hc.eq,mul_inv_cancel_right]
  have huC := h.fixed_by_noncentral_imp_fixed_by_all ⟨v,hvS⟩ hvc ⟨u,hu⟩ hfU
  apply (hCV ▸ (show u ∈ P ⊓ centralizer (V : Set G) from ?_))
  exact ⟨hUP hu, centralizer_le (hVP.trans hPS) huC⟩

variable [Finite G]

/-- The elementary subgroups of the factor lie in modules of binary rank `2n`. -/
theorem Setup.pair_primeRank_le (h : Setup R L F) {n : ℕ} (hL : IsL2EvenBlock L n)
    (P : Subgroup G) (x : G) (hPS : P ≤ S R) (hPL : P ≤ L)
    (hpair : U L ⊔ (U L).map (MulAut.conj x⁻¹).toMonoidHom = P)
    (hxP : x ∈ normalizer (P : Set G)) (hZ : center L = ⊥)
    (hcore : pCore 2 L = blockU L) : primeRank 2 P ≤ 2*n := by
  have hu := h.pair_involution_union P x hPS hPL hpair hxP hcore
  have hcard := card_U_of_center_eq_bot hL hZ
  apply (primeRank_le_iff_elementary_card_le P).mpr
  intro E hE
  let := hE
  have hEA : IsElementaryAbelian 2 (E.map P.subtype) := IsElementaryAbelian.map_subtype
  let := hEA
  have hEP : E.map P.subtype ≤ P := map_subtype_le E
  have he := le_one_of_elementwise_union (E.map P.subtype) (U L)
    ((U L).map (MulAut.conj x⁻¹).toMonoidHom) (fun e he =>
      hu e (hEP he) (elemPow_eq_one_of_isElementaryAbelian e he))
  rw [← card_map_of_injective P.subtype_injective (K := E)]
  rcases he with he | he
  · exact (card_le_of_le he).trans_eq hcard
  · exact (card_le_of_le he).trans_eq
      ((card_map_of_injective (MulAut.conj x⁻¹).injective).trans hcard)

/-- The common module is fixed by the actual Sylow group, so has rank at most `n`. -/
theorem Setup.pair_intersection_primeRank_le (h : Setup R L F) {n : ℕ}
    (hL : IsL2EvenBlock L n) (P : Sylow 2 L) (x : G)
    (hpair : U L ⊔ (U L).map (MulAut.conj x⁻¹).toMonoidHom = (P : Subgroup L).map L.subtype)
    (hZ : center L = ⊥) :
    primeRank 2 (U L ⊓ (U L).map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) ≤ n := by
  let V := (U L).map (MulAut.conj x⁻¹).toMonoidHom
  let E := U L ⊓ V
  let : IsElementaryAbelian 2 (U L) := h.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hEL : E ≤ L := inf_le_left.trans (map_subtype_le _)
  have hEU : E.subgroupOf L ≤ blockU L := by
    intro e he
    obtain ⟨u,hu,heq⟩ := (show (e:G) ∈ U L from he.1)
    exact (Subtype.ext heq : u=e) ▸ hu
  have hEC : E ≤ centralizer (((P : Subgroup L).map L.subtype) : Set G) := by
    apply le_centralizer_iff.mpr
    rw [←hpair]
    apply sup_le
    · exact (le_centralizer _).trans (centralizer_le (show E ≤ U L from inf_le_left))
    · exact (le_centralizer _).trans (centralizer_le (show E ≤ V from inf_le_right))
  have hEP : E.subgroupOf L ≤ centralizer (P : Set L) := by
    intro e he p hp
    apply Subtype.ext
    exact hEC he p (mem_map.mpr ⟨p,hp,rfl⟩)
  have hc := hL.card_le_of_sylow_fixed_disjoint_center P (E.subgroupOf L)
    hEU hEP (by rw [hZ]; exact disjoint_bot_right)
  have he : (E.subgroupOf L).map L.subtype = E := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hEL]
  have hec : Nat.card (E.subgroupOf L) = Nat.card E := by
    calc
      Nat.card (E.subgroupOf L) = Nat.card ((E.subgroupOf L).map L.subtype) :=
        (card_map_of_injective L.subtype_injective).symm
      _ = Nat.card E := congrArg (fun W : Subgroup G => Nat.card W) he
  apply (primeRank_le_iff_elementary_card_le E).mpr
  intro A _
  exact (card_le_card_group A).trans (hec ▸ hc)

/-- The complete factor estimates, on the literal ambient image of a block Sylow. -/
theorem Setup.pair_fixed_rank (h : Setup R L F) {n : ℕ} (hL : IsL2EvenBlock L n)
    (P : Sylow 2 L) (x : G)
    (hPS : (P : Subgroup L).map L.subtype ≤ S R)
    (hpair : U L ⊔ (U L).map (MulAut.conj x⁻¹).toMonoidHom = (P : Subgroup L).map L.subtype)
    (hxP : x ∈ normalizer (((P : Subgroup L).map L.subtype) : Set G))
    (hZ : center L = ⊥) (hcore : pCore 2 L = blockU L) :
    (∀ r ∈ (P : Subgroup L).map L.subtype, r^2=1 →
      r ∈ U L ∨ r ∈ (U L).map (MulAut.conj x⁻¹).toMonoidHom) ∧
    primeRank 2 ((P : Subgroup L).map L.subtype) ≤ 2*n ∧
    primeRank 2 (U L ⊓ (U L).map (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) ≤ n := by
  exact ⟨h.pair_involution_union _ x hPS (map_subtype_le _) hpair hxP hcore,
    h.pair_primeRank_le hL _ x hPS (map_subtype_le _) hpair hxP hZ hcore,
    h.pair_intersection_primeRank_le hL P x hpair hZ⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
