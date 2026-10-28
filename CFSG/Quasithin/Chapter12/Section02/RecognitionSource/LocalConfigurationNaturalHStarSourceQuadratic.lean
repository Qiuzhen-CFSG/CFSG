module
public import Theory.SpecificGroups.Alternating.FiveConjugateSylow
public import Theory.Representation.BinaryPermutation.FiveQuadraticActors
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceTISeed
public import Theory.Representation.BinaryConjugationSection.QuadraticCommutator
public import Theory.ElementaryAbelian.Join

/-!
# Quadratic A₅ Sylow actions on the original H-star core sections

If two conjugate images of V generate a two-group through a map with kernel
in O₂(H), their original join is a two-group. Its mutual normalizer contains
the nontrivial V∩O₂(H). The elementary TI-pair theorem makes this join abelian.
Since O₂(H) normalizes both conjugates, their second commutators on O₂(H)
vanish. A surjective A₅ marking then yields a quadratic Sylow four-group
on every marked core section. This excludes an embedded five-point core.

The final application uses the exact source omega module and derives movement
from the residual A₅ identification. The remaining identification, V-image
containment, and source module alternatives stay with qt-d-12213-hstar-natural.
These lemmas do not assert the full nonsolvable exclusion.

Source: Aschbacher–Smith, 12.2.7 and 12.2.19, printed pp.797 and 801–802;
I.6.2(1), printed pp.424–425.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H : Subgroup G}

theorem chosen_hstar_pair_commutes_of_two_image_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (N : Subgroup G) (hNH : N ≤ H) (hVN : V ≤ N)
    {Q : Type*} [Group Q] (f : N →* Q)
    (hk : f.ker ≤ (H.pCoreIn 2).subgroupOf N) (g : N)
    (hp : IsPGroup 2 (((V ⊔ V.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf N).map f)) :
    V ≤ centralizer (V.map (MulAut.conj (g : G)).toMonoidHom : Set G) := by
  let A := V.map (MulAut.conj (g : G)).toMonoidHom
  let I := V ⊔ A
  have hAN : A ≤ N := by
    rintro _ ⟨v,hv,rfl⟩
    exact N.mul_mem (N.mul_mem g.property (hVN hv)) (N.inv_mem g.property)
  have hIN : I ≤ N := sup_le hVN hAN
  have hkP : IsPGroup 2 f.ker := ((isPGroup_pCoreIn 2 H).comap_subtype).to_le hk
  have hiP : IsPGroup 2 (I.subgroupOf N) :=
    (hp.comap_of_ker_isPGroup f hkP).to_le (Subgroup.map_le_iff_le_comap.mp le_rfl)
  have hi : IsPGroup 2 I := by
    have hm := hiP.map N.subtype
    rwa [map_subgroupOf_eq_of_le hIN] at hm
  let := D.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  rcases hTI.eq_or_disjoint_conjugate (g : G) with he | hd
  · rw [he]
    exact le_centralizer V
  have hn := chosen_hstar_core_normalizes_conjugate_at h D structural hH
    (⟨g,hNH g.property⟩ : H)
  have hu : V ⊓ normalizer (A : Set G) ≠ ⊥ := by
    intro he
    exact chosen_hstar_intersection_ne_bot_at h D structural hH
      (bot_unique ((inf_le_inf_left V hn).trans_eq he))
  exact (ti_pair_directProduct_of_isPGroup V A hd.symm hTI
    (hTI.map_equiv (MulAut.conj (g : G)))
    (card_map_of_injective (MulAut.conj (g : G)).injective).symm hu hi).1

theorem chosen_hstar_pair_triple_commutator_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (N : Subgroup G) (hNH : N ≤ H) (hVN : V ≤ N)
    {Q : Type*} [Group Q] (f : N →* Q)
    (hk : f.ker ≤ (H.pCoreIn 2).subgroupOf N) (g : N)
    (hp : IsPGroup 2 (((V ⊔ V.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf N).map f))
    (S : Subgroup G) (hSQ : S ≤ H.pCoreIn 2) :
    ⁅V ⊔ V.map (MulAut.conj (g : G)).toMonoidHom,
      ⁅V ⊔ V.map (MulAut.conj (g : G)).toMonoidHom,S⁆⁆ = ⊥ := by
  let A := V.map (MulAut.conj (g : G)).toMonoidHom
  let I := V ⊔ A
  let := D.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.sup_of_le_centralizer
    (le_centralizer_iff.mp (chosen_hstar_pair_commutes_of_two_image_at h D structural hTI hH N hNH hVN f hk g hp))
  have hnA := chosen_hstar_core_normalizes_conjugate_at h D structural hH
    (⟨g,hNH g.property⟩ : H)
  have hnV := chosen_hstar_core_normalizes_conjugate_at h D structural hH 1
  have hnV' : H.pCoreIn 2 ≤ normalizer (V : Set G) := by
    simpa using hnV
  have hnA' : H.pCoreIn 2 ≤ normalizer (A : Set G) := by
    simpa [A] using hnA
  have hnI : S ≤ normalizer (I : Set G) := hSQ.trans
    ((le_inf hnV' hnA').trans (normalizer_inf_normalizer_le_normalizer_sup V A))
  have hc : ⁅I,S⁆ ≤ I := le_normalizer_iff_commutator_le_left.mp hnI
  apply le_bot_iff.mp
  exact (commutator_mono le_rfl hc).trans_eq (commutator_self_eq_bot_iff.mpr inferInstance)

omit [Finite G] in
private theorem pair_image (N V : Subgroup G) (hVN : V ≤ N)
    {Q : Type*} [Group Q] (f : N →* Q) (g : N) :
    ((V ⊔ V.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf N).map f =
      (V.subgroupOf N).map f ⊔ ((V.subgroupOf N).map f).map
        (MulAut.conj (f g)).toMonoidHom := by
  have hAN : V.map (MulAut.conj (g : G)).toMonoidHom ≤ N := by
    rintro _ ⟨v,hv,rfl⟩
    exact N.mul_mem (N.mul_mem g.property (hVN hv)) (N.inv_mem g.property)
  have hc : (V.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf N =
      (V.subgroupOf N).map (MulAut.conj g).toMonoidHom :=
    (conj_smul_subgroupOf hVN g).symm
  rw [subgroupOf_sup hVN hAN, Subgroup.map_sup, hc, map_map, map_map]
  congr 2
  apply MonoidHom.ext
  intro x
  change f (g * x * g⁻¹) = f g * f x * (f g)⁻¹
  simp only [map_mul,map_inv]

theorem chosen_hstar_exists_quadratic_five_sylow_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (N : Subgroup G) (hNH : N ≤ H) (hVN : V ≤ N)
    (f : N →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hk : f.ker ≤ (H.pCoreIn 2).subgroupOf N)
    (hm : ¬ V.subgroupOf N ≤ f.ker)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) W)
    (S Z : Subgroup G) (hSQ : S ≤ H.pCoreIn 2)
    (C : Representation.BinaryConjugationSection N S Z (ρ.comp f)) :
    ∃ P : Sylow 2 (alternatingGroup (Fin 5)),
      Representation.BinaryOffender.IsQuadratic ρ (P : Subgroup _) := by
  let := D.elementary
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hVN
  let : IsElementaryAbelian 2 ((V.subgroupOf N).map f) := IsElementaryAbelian.map _
  have hne : (V.subgroupOf N).map f ≠ ⊥ := fun he => hm ((Subgroup.map_eq_bot_iff _).mp he)
  obtain ⟨b,P,hP⟩ := Theory.SpecificGroups.Alternating.FiveConjugateSylow.exists_conjugate_generating_sylow
    ((V.subgroupOf N).map f) hne
  obtain ⟨g,hg⟩ := hf b
  have he : ((V ⊔ V.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf N).map f =
      (P : Subgroup _) := by rw [pair_image N V hVN f g, hg, hP]
  have hp : IsPGroup 2 (((V ⊔ V.map (MulAut.conj (g : G)).toMonoidHom).subgroupOf N).map f) :=
    he.symm ▸ P.isPGroup'
  have hc := chosen_hstar_pair_triple_commutator_at h D structural hTI hH N hNH hVN f hk g hp S hSQ
  refine ⟨P, ?_⟩
  rw [← he]
  exact Representation.BinaryConjugationSection.isQuadratic_of_triple_commutator_le
    N S Z _ ρ f C (hc.le.trans bot_le)

theorem chosen_hstar_no_five_permutation_summand_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (N : Subgroup G) (hNH : N ≤ H) (hVN : V ≤ N)
    (f : N →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hk : f.ker ≤ (H.pCoreIn 2).subgroupOf N)
    (hm : ¬ V.subgroupOf N ≤ f.ker)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) W)
    (S Z : Subgroup G) (hSQ : S ≤ H.pCoreIn 2)
    (C : Representation.BinaryConjugationSection N S Z (ρ.comp f))
    (j : BinaryPermutation.core (Fin 5) →ₗ[ZMod 2] W)
    (hj : Function.Injective j)
    (he : ∀ a v, j (BinaryPermutation.alternatingCoreRepresentation (Fin 5) a v) = ρ a (j v)) :
    False := by
  obtain ⟨P,hP⟩ := chosen_hstar_exists_quadratic_five_sylow_at h D structural hTI hH N hNH hVN
    f hf hk hm ρ S Z hSQ C
  apply BinaryPermutation.FiveQuadraticActors.sylow_not_quadratic P
  intro a ha b hb v
  apply hj
  rw [he, map_sub, he]
  exact hP a ha b hb (j v)
/-- Application to the exact V_Z/C_{V_Z}(K) of 12.2.19. The source residual
identification discharges the quotient-rank and movement premises. -/
theorem chosen_hstar_seed_no_five_permutation_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (e : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* alternatingGroup (Fin 5))
    (N : Subgroup G) (hNH : N ≤ H) (hVN : V ≤ N)
    (f : N →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hk : f.ker ≤ (H.pCoreIn 2).subgroupOf N)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) W)
    (C : Representation.BinaryConjugationSection N (hstarSeedModule T V H)
      (hstarSeedModule T V H ⊓ centralizer ((pResidual 2 H).map H.subtype : Set G)) (ρ.comp f))
    (j : BinaryPermutation.core (Fin 5) →ₗ[ZMod 2] W)
    (hj : Function.Injective j)
    (he : ∀ a v, j (BinaryPermutation.alternatingCoreRepresentation (Fin 5) a v) = ρ a (j v)) :
    False := by
  have hm := chosen_movement_of_quotient_rank_at h D structural hnone hTI hH
    (chosen_hstar_quotient_rank_of_residual_identification_at h D structural hTI hH (fun _ => ⟨e⟩))
  have hm' : ¬ V.subgroupOf N ≤ f.ker := by
    intro hv
    apply hm
    intro v hv'
    exact hk (hv (show (⟨v,hVN hv'⟩ : N) ∈ V.subgroupOf N from hv'))
  exact chosen_hstar_no_five_permutation_summand_at h D structural hTI hH N hNH hVN f hf hk hm'
    ρ _ _ (chosen_hstar_seed_le_core h hH) C j hj he

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
