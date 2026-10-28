module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SplitRadical
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Family.Fixed
public import Theory.GroupTheory.PCoreImage

/-!
# The actual block core after Gaschütz splitting

The original core Q is elementary after the source Frattini argument. Its
conjugate-module supplement gives a complement in the actual Sylow S.
Gaschütz splits Q globally in KS, and two-perfection puts K∩Q inside U.
The normal two-core of K lies in Q, so O₂(K)=U. No quotient of the
commutator module, or split natural cover, is substituted for U.

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K : Subgroup G} {F : Type*} [Field F]

theorem Setup.core_commutator_le (h : Setup R K F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    ⁅K,Q R K⁆ ≤ U K := by
  have hKU : K ≤ normalizer (U K : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hD : D R K ≤ centralizer (K : Set G) := inf_le_right
  have hDU : D R K ≤ normalizer (U K : Set G) :=
    (hD.trans (centralizer_le (map_subtype_le _))).trans (Subgroup.centralizer_le_normalizer _)
  apply commutator_le.mpr
  intro k hk q hq
  rw [(h.factorization hx hnc).core] at hq
  have hm : q ∈ (U K : Set G) * (D R K : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hDU]
    exact hq
  obtain ⟨u,hu,d,hd,rfl⟩ := hm
  have hdK := hD hd k hk
  have he : ⁅k,u*d⁆ = ⁅k,u⁆ := by
    simp only [commutatorElement_def,mul_inv_rev]
    calc
      _ = k*u*(d*k⁻¹*d⁻¹)*u⁻¹ := by group
      _ = k*u*k⁻¹*u⁻¹ := by
        have hdInv : d * k⁻¹ = k⁻¹ * d := Commute.inv_right hdK.symm
        rw [hdInv,mul_inv_cancel_right]
  rw [he]
  exact le_normalizer_iff_commutator_le_right.mp hKU (commutator_mem_commutator hk hu)

/-- The Sylow input is the preceding C.5.4 assertion about the same S in KS. -/
theorem Setup.core_eq_module_of_sylow
    (h : Setup R K F) {x : G} (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (hphi : Phi R K = ⊥)
    (hSylow : ∃ P : Sylow 2 (K ⊔ S R : Subgroup G),
      (P : Subgroup (K ⊔ S R : Subgroup G)).map (K ⊔ S R).subtype = S R) :
    K.pCoreIn 2 = U K := by
  let N := K ⊔ S R
  have hKN : K ≤ N := le_sup_left
  have hSN : S R ≤ N := le_sup_right
  have hQN : Q R K ≤ N := pCoreIn_le 2 N
  have hUN : U K ≤ N := h.module_le.trans hSN
  let V := (U K).map (MulAut.conj x⁻¹).toMonoidHom
  have hVN : V ≤ N := (h.conjugate_le hx).trans hSN
  let Q' := (Q R K).subgroupOf N
  have hQ' : Q' = pCore 2 N := by
    change ((pCore 2 N).map N.subtype).comap N.subtype = _
    exact comap_map_eq_self_of_injective N.subtype_injective _
  let : Q'.Normal := hQ' ▸ inferInstance
  let := h.core_elementary hx hnc hphi
  let : IsElementaryAbelian 2 Q' := IsElementaryAbelian.subgroupOf hQN
  let := h.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hVN
  have hQtwo : IsPGroup 2 Q' := hQ'.symm ▸ pCore_isPGroup
  have hKtwo : IsPPerfect 2 (K.subgroupOf N) :=
    h.short.twoPerfect.of_surjective (subgroupOfEquivOfLe hKN).symm.toMonoidHom
      (subgroupOfEquivOfLe hKN).symm.surjective
  have hcomm : ⁅K.subgroupOf N,Q'⁆ ≤ (U K).subgroupOf N := by
    apply (Subgroup.map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hKN,map_subgroupOf_eq_of_le hQN,
      map_subgroupOf_eq_of_le hUN]
    exact h.core_commutator_le hx hnc
  obtain ⟨P,hP⟩ := hSylow
  have hPeq : (P : Subgroup N) = (S R).subgroupOf N :=
    (map_injective N.subtype_injective) (hP.trans (map_subgroupOf_eq_of_le hSN).symm)
  have hVP : V.subgroupOf N ≤ P := hPeq ▸ subgroupOf_mono N (h.conjugate_le hx)
  have hspan : (P : Subgroup N) = Q' ⊔ V.subgroupOf N := by
    rw [hPeq,← subgroupOf_sup hQN hVN]
    exact congrArg (fun A : Subgroup G => A.subgroupOf N)
      ((h.factorization hx hnc).span.trans (sup_comm _ _))
  have hinter := radical_intersection_le_of_sylow_supplement Q' (K.subgroupOf N)
    ((U K).subgroupOf N) (V.subgroupOf N) hQtwo hKtwo hcomm P hVP hspan
  have hKnorm : N ≤ normalizer (K : Set G) := sup_le K.le_normalizer h.normalizes
  have hcore : K.pCoreIn 2 ≤ Q R K := pCoreIn_mono_of_normalizes hKN hKnorm
  apply le_antisymm
  · intro k hk
    exact hinter (show (⟨k,hQN (hcore hk)⟩ : N) ∈ K.subgroupOf N ⊓ Q' from
      ⟨pCoreIn_le 2 K hk,hcore hk⟩)
  · exact map_mono blockU_le_core
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
