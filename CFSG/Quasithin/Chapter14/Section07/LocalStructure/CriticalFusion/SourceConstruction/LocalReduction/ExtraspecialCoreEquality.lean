module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialPointCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialChiefSylow
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.PCoreCentralImage

/-!
# Residual core equality in the extraspecial branch

The literal point-core duality first gives
O₂(H) = O₂(L₁) C_H(U). In the central alternative of 14.7.20(2), this
makes [O₂(K),K] lie in O₂(L₁). The central Sylow image in K/O₂(L₁)
is trivial by transfer and two-perfectness, proving O₂(L₁) = O₂(K).

If L₁ moves C_H(U)/U, its moved chief interval is absorbed modulo
O₂(L₁). The already proved localization of K-movement above and below
that interval, together with residual commutator idempotence, gives the
same core equality. All cores and subgroup inclusions are in the original
group, and point normality is derived from the extraspecial hypothesis.

The original Heisenberg application combines these conclusions with the
literal order-four and order-sixteen point-central alternatives, preserving
their action kernels and Sylow markings. Those alternatives still require
exclusion; this module does not assert unconditional 14.7.20(2) or (3).
The earlier Structural1222 and Theorem12213 implications remain explicit,
with final discharge retained by qt-d-14775-source.

Source: Aschbacher–Smith, 14.7.20(1)–(3), printed p.1049.
-/

public noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem coreEq_point_normalized
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    F.H ≤ normalizer ((F.Li L 1).pCoreIn 2 : Set G) :=
  ((normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn).trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 (F.Li L 1)))

omit [Finite G] in
private theorem coreEq_point_le_residual
    (hn : ((F.Li L 1).subgroupOf F.H).Normal) :
    (F.Li L 1).pCoreIn 2 ≤ (K F).pCoreIn 2 :=
  pCoreIn_mono_of_normalizes (pointResidual_le F)
    ((map_subtype_le _).trans
      ((normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn))

/-- The intrinsic point core supplements the full U-centralizer in O₂(H). -/
theorem extraspecial_point_core_supplement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3) :
    (F.Li L 1).pCoreIn 2 ⊔ centralizer (F.U : Set G) = F.H.pCoreIn 2 := by
  obtain ⟨X,aX,mX,ρ,sU,sN,hd,_,_⟩ :=
    extraspecial_point_core_duality h hab structural previous hex hcard hexp
  let : Finite X := Finite.of_surjective (fun u : F.U => (sU.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp sU.onto)
  let N := (F.Li L 1).pCoreIn 2
  let C := centralizer (F.U : Set G)
  let QH := F.H.pCoreIn 2
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hNQ : N ≤ QH :=
    pCoreIn_mono_of_normalizes ((F.Li_le L 1).trans inf_le_right)
      ((normal_subgroupOf_iff_le_normalizer ((F.Li_le L 1).trans inf_le_right)).mp hn)
  have hCQ : C ≤ QH := centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) sU
  have hjoin : N ⊔ C ≤ QH := sup_le hNQ hCQ
  let : (C.subgroupOf QH).Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 F.H).trans (sU.normalized.trans (normalizer_le_normalizer_centralizer _)))
  have hN : (N ⊓ C).relIndex N = 64 := by
    change Nat.card (N ⧸ (N ⊓ C).subgroupOf N) = 64
    let := sN.kernel_normal
    rw [Nat.card_congr sN.quotientEquiv.toEquiv]
    change Nat.card (Module.Dual (ZMod 2) X) = 64
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,Subspace.dual_finrank_eq,hd]
    rfl
  have hQ := extraspecial_core_centralizer_index h hab structural previous hex hcard hexp QH (Or.inl rfl)
  rw [inf_relIndex_left] at hN hQ
  have hrel : C.relIndex (N ⊔ C) = C.relIndex N := by
    have he := relIndex_sup_right (N.subgroupOf QH) (C.subgroupOf QH)
    rw [←subgroupOf_sup hNQ hCQ,relIndex_subgroupOf hjoin,relIndex_subgroupOf hNQ] at he
    exact he
  have hm := relIndex_mul_relIndex C (N ⊔ C) QH le_sup_right hjoin
  rw [hrel,hN,hQ] at hm
  have hone : (N ⊔ C).relIndex QH = 1 := by omega
  exact le_antisymm hjoin (Subgroup.relIndex_eq_one.mp hone)

private theorem coreEq_of_centralizer_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ (F.Li L 1).pCoreIn 2) :
    (F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2 := by
  let N := (F.Li L 1).pCoreIn 2
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  have hHN : F.H ≤ normalizer (N : Set G) := coreEq_point_normalized hn
  have hNH : N ≤ F.H := (pCoreIn_le 2 _).trans ((F.Li_le L 1).trans inf_le_right)
  have hNK : N ≤ K F := (pCoreIn_le 2 _).trans (pointResidual_le F)
  have hKH : K F ≤ F.H := map_subtype_le _
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  have hCH : centralizer (F.U : Set G) ≤ F.H :=
    (centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) s).trans (pCoreIn_le 2 _)
  have hQK : ⁅F.H.pCoreIn 2,K F⁆ ≤ N := by
    rw [←extraspecial_point_core_supplement h hab structural previous hex hcard hexp]
    exact commutator_sup_le_of_relative_normal F.H N _ (K F) N hHN hNH hCH
      (le_normalizer_iff_commutator_le_left.mp (hKH.trans hHN)) hc
  have hPQ : (K F).pCoreIn 2 ≤ F.H.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hKH (le_normalizer_embedded_pResidual 2 F.H)
  have hPK : ⁅(K F).pCoreIn 2,K F⁆ ≤ N := (commutator_mono hPQ le_rfl).trans hQK
  let R := N.subgroupOf (K F)
  let : R.Normal := normal_subgroupOf_of_le_normalizer (hKH.trans hHN)
  have hp : IsPPerfect 2 (K F) := isPPerfect_embedded_pResidual 2 F.H
  have hcomm : ⁅pCore 2 (K F),(⊤ : Subgroup (K F))⁆ ≤ R := by
    intro x hx
    have hm := mem_map_of_mem (K F).subtype hx
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype] at hm
    exact hPK hm
  have hle := pCore_le_of_commutator_le_of_coprime_index hp
    (show Nat.Coprime 2 (pCore 2 (K F)).index by rw [index_eq_card,hcard]; decide) R hcomm
  apply le_antisymm (coreEq_point_le_residual hn)
  rintro _ ⟨x,hx,rfl⟩
  exact hle hx

/-- In the central alternative of 14.7.20(2), the two literal residual cores agree. -/
theorem extraspecial_core_eq_of_centralizer_central
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U) :
    (F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2 :=
  coreEq_of_centralizer_commutator h hab structural previous hex hcard hexp
    (hc.trans (span_le_point_core h hab
      (pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp)))


omit [Finite G] in
private theorem coreEq_chief_captured
    (hn : ((F.Li L 1).subgroupOf F.H).Normal)
    (N B : NormalNode F.H) (hNB : N ⋖ B)
    (hBQ : B.val.map F.H.subtype ≤ F.H.pCoreIn 2)
    (hm : ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype) :
    B.val.map F.H.subtype ≤ N.val.map F.H.subtype ⊔ (F.Li L 1).pCoreIn 2 := by
  let P : NormalNode F.H := ⟨((F.Li L 1).pCoreIn 2).subgroupOf F.H,
    normal_subgroupOf_of_le_normalizer (coreEq_point_normalized hn)⟩
  have hLH : F.Li L 1 ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hBH : B.val.map F.H.subtype ≤ F.H := map_subtype_le _
  have hBN : F.H ≤ normalizer (B.val.map F.H.subtype : Set G) := by
    have he : (B.val.map F.H.subtype).subgroupOf F.H = B.val :=
      comap_map_eq_self_of_injective F.H.subtype_injective B.val
    exact (normal_subgroupOf_iff_le_normalizer hBH).mp (by rw [he]; exact B.property)
  have hc : ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤
      B.val.map F.H.subtype ⊓ (F.Li L 1).pCoreIn 2 := by
    have hb : ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ B.val.map F.H.subtype :=
      le_normalizer_iff_commutator_le_right.mp (hLH.trans hBN)
    have hl : ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ F.Li L 1 :=
      le_normalizer_iff_commutator_le_left.mp
        (hBH.trans ((normal_subgroupOf_iff_le_normalizer hLH).mp hn))
    exact le_inf hb ((le_inf hl (hb.trans hBQ)).trans (inf_pCoreIn_le_of_le 2 hLH))
  have hnode : B ≤ N ⊔ P := by
    obtain he | he := hNB.eq_or_eq (c := N ⊔ (B ⊓ P)) le_sup_left
      (sup_le hNB.le inf_le_left)
    · exfalso
      apply hm
      intro x hx
      obtain ⟨b,hb,hbx⟩ := (hc hx).1
      have hbP : b ∈ P.val := by
        change F.H.subtype b ∈ (F.Li L 1).pCoreIn 2
        rw [hbx]
        exact (hc hx).2
      have hbN : b ∈ N.val := (he ▸ (show B ⊓ P ≤ N ⊔ (B ⊓ P) from le_sup_right)) ⟨hb,hbP⟩
      exact ⟨b,hbN,hbx⟩
    · rw [←he]
      exact sup_le le_sup_left (inf_le_right.trans le_sup_right)
  have hh := map_mono (f := F.H.subtype) hnode
  change B.val.map F.H.subtype ≤ (N.val ⊔ P.val).map F.H.subtype at hh
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le
    ((pCoreIn_le 2 _).trans hLH)] at hh
  exact hh

/-- The faithful chief interval also forces O₂(L₁)=O₂(K): its moved
point action absorbs that interval modulo the point core, and residual
commutator idempotence removes both central flanking sections. -/
theorem extraspecial_core_eq_of_point_movement
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)))
    (hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27)
    (hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3)
    (hm : ¬ ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U) :
    (F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2 := by
  obtain ⟨N,B,hNB,_,hBC,hmove,_,_,hupper,hlower⟩ :=
    extraspecial_exists_point_moved_chief h hab structural previous hex hcard hexp hm
  have hn := pointResidual_normal_of_extraspecial_residual h hab structural previous hex hcard hexp
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  obtain ⟨ρ,⟨s⟩⟩ := exists_section F
  let P := (F.Li L 1).pCoreIn 2
  let C := centralizer (F.U : Set G)
  have hCQ : C ≤ F.H.pCoreIn 2 :=
    centralizer_U_le_core_of_escape h structural (h.flag_escape F previous) s
  have hPH : P ≤ F.H := (pCoreIn_le 2 _).trans ((F.Li_le L 1).trans inf_le_right)
  have hHP : F.H ≤ normalizer (P : Set G) := coreEq_point_normalized hn
  have hUP : F.U ≤ P := span_le_point_core h hab hn
  have hbound := coreEq_chief_captured hn N B hNB (hBC.trans hCQ) hmove
  have hBK : ⁅B.val.map F.H.subtype,K F⁆ ≤ P :=
    (commutator_mono hbound le_rfl).trans
      (commutator_sup_le_of_relative_normal F.H (N.val.map F.H.subtype) P (K F) P hHP
        (map_subtype_le _) hPH (hlower.trans hUP)
        (le_normalizer_iff_commutator_le_left.mp ((map_subtype_le _).trans hHP)))
  have hid : ⁅⁅C,K F⁆,K F⁆ = ⁅C,K F⁆ :=
    commutator_isPPerfect_idempotent (K F) C (isPPerfect_embedded_pResidual 2 F.H)
      ((isPGroup_pCoreIn 2 F.H).to_le hCQ)
      ((map_subtype_le _).trans (s.normalized.trans (normalizer_le_normalizer_centralizer _)))
  apply coreEq_of_centralizer_commutator h hab structural previous hex hcard hexp
  rw [←hid]
  exact (commutator_mono hupper le_rfl).trans hBK

/-- Source 14.7.20(3) is discharged in both the central and the faithful
chief branches. The only remaining branches retain the literal point-central
interval, exact kernel, and order-four Sylow obstruction. -/
theorem extraspecial_centralizer_core_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (((F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2) ∧
      (⁅centralizer (F.U : Set G),K F⁆ ≤ F.U ∨
        ∃ N B : NormalNode F.H, N ⋖ B ∧
          F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
          ¬ ⁅F.Li L 1,B.val.map F.H.subtype⁆ ≤ N.val.map F.H.subtype ∧
          Nat.card (Section N B) = 64 ∧ (sectionAction N B).ker = pCore 2 F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U)) ∨
    (⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U ∧
      ∃ N B : NormalNode F.H, N ⋖ B ∧
        F.U ≤ N.val.map F.H.subtype ∧ B.val.map F.H.subtype ≤ centralizer (F.U : Set G) ∧
        ¬ ⁅B.val.map F.H.subtype,K F⁆ ≤ N.val.map F.H.subtype ∧
        pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ≤ (sectionAction N B).ker ∧
        ((Nat.card (Section N B) = 4 ∧
          (sectionAction N B).ker.relIndex (pResidual 2 F.H) = 3 ∧
          IsElementaryAbelian 2 (star F (T : Subgroup G)) ∧
          Nat.card (star F (T : Subgroup G)) = 4 ∧
          Nat.card (star F (F.Ri L 1)) = 2) ∨
         (Nat.card (Section N B) = 16 ∧
          (sectionAction N B).ker = pCore 2 F.H ⊔ (F.Li L 1).subgroupOf F.H ∧
          ⁅centralizer (F.U : Set G),K F⁆ ≤ B.val.map F.H.subtype ∧
          ⁅N.val.map F.H.subtype,K F⁆ ≤ F.U))) := by
  classical
  obtain ⟨e⟩ := he
  have hex : IsExtraspecial 3 ((K F) ⧸ pCore 2 (K F)) :=
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2)).of_mulEquiv e.symm
  have hcard : Nat.card ((K F) ⧸ pCore 2 (K F)) = 27 :=
    (Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3))
  have hexp : Monoid.exponent ((K F) ⧸ pCore 2 (K F)) = 3 :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (HeisenbergPrime.exponent (by decide : 3 ≠ 2))
  by_cases hc : ⁅centralizer (F.U : Set G),K F⁆ ≤ F.U
  · exact Or.inl ⟨extraspecial_core_eq_of_centralizer_central h hab structural previous
      hex hcard hexp hc,Or.inl hc⟩
  by_cases hp : ⁅centralizer (F.U : Set G),F.Li L 1⁆ ≤ F.U
  · obtain ⟨N,B,hNB,hUN,hBC,hm,hker,h4 | h16⟩ := extraspecial_point_central_interval_kernels
      h hab structural previous hex hcard hexp hp hc
    · exact Or.inr ⟨hp,N,B,hNB,hUN,hBC,hm,hker,Or.inl ⟨h4.1,h4.2,
        extraspecial_four_interval_star_orders h hab structural previous hex hcard hexp
          N B hNB hUN hBC hp hm h4.1⟩⟩
    · exact Or.inr ⟨hp,N,B,hNB,hUN,hBC,hm,hker,Or.inr h16⟩
  · exact Or.inl ⟨extraspecial_core_eq_of_point_movement h hab structural previous hex hcard hexp hp,
      Or.inr (extraspecial_exists_point_moved_chief h hab structural previous hex hcard hexp hp)⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
