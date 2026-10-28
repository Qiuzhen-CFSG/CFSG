module

public import CFSG.Quasithin.Chapter13.Section07.PlusAction.OriginalKernelSylow
public import Theory.SpecificGroups.Alternating.FiveSylowRadical
public import Theory.GroupTheory.PCoreQuotientInnerSupplement

/-!
# The original A₅ point radical acts inner

Let K be the normal A₅ component in the plus kernel and P=L₁T. The
intersection K∩P is a two-group, so P preserves the quotient image of
K∩T. If L₁ acts nontrivially modulo O₂(K), the normal two-actor theorem
for an A₅ Sylow stabilizer makes O₂(P) act inner on that same quotient.
Sylow lifting and the exact quotient-action kernel then give
O₂(P)=(K∩T)O₂(KO₂(P)).

This is the structural radical step in Aschbacher–Smith 13.7.4(1),
printed p.937. All normalizers, cores and quotient maps below belong to
the original setup. The final theorem supplies primitive-component
normality from the earlier proved source result.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- Under the contrary noncentral L₁-action, every element of the original
point radical induces an inner automorphism on K/O₂(K). -/
theorem source_normal_alternatingFive_radical_inner
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hnon : ¬ ⁅K,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤ K.pCoreIn 2) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let P := F.L₁ ⊔ (T : Subgroup G)
    ∀ r : P.pCoreIn 2,
      quotientAut (pCore 2 K)
        (K.normalizerMonoidHom ⟨r,hKn (h.local_le (pCoreIn_le 2 P r.property))⟩) ∈
          MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  have hPK : P ≤ normalizer (K : Set G) := h.local_le.trans hKn
  have hKP : IsPGroup 2 (K ⊓ P : Subgroup G) :=
    (isPGroup_pCoreIn 2 P).to_le ((inf_le_inf_right P hKC).trans
      (source_kernel_inf_point_le_radical d h eL hne))
  let q₀ := QuotientGroup.mk' (pCore 2 K)
  let q := eK.toMonoidHom.comp q₀
  let a : P →* MulAut (alternatingGroup (Fin 5)) := (MulAut.congr eK).toMonoidHom.comp
    ((quotientAut (pCore 2 K)).comp (K.normalizerMonoidHom.comp (inclusion hPK)))
  have ha (x : P) (k : K) : a x (q k) =
      q (K.normalizerMonoidHom ⟨x,hPK x.property⟩ k) := by
    change eK ((quotientAut (pCore 2 K) (K.normalizerMonoidHom
      ⟨x,hPK x.property⟩)) (eK.symm (eK (q₀ k)))) = _
    rw [eK.symm_apply_apply,quotientAut_apply_mk]
    rfl
  have hnona : ∃ b : F.L₁, a (inclusion (show F.L₁ ≤ P from le_sup_left) b) ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hnon
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl k hk
    let l' : F.L₁ := ⟨l,hl⟩
    let k' : K := ⟨k,hk⟩
    let n : K := K.normalizerMonoidHom ⟨l,hPK (mem_sup_left hl)⟩ k'
    have hfix : q n = q k' := by
      have hh := congrArg (fun b : MulAut (alternatingGroup (Fin 5)) => b (q k'))
        (hall l')
      rw [ha] at hh
      exact hh
    have hfix₀ : q₀ n = q₀ k' := eK.injective hfix
    have hcore : n * k'⁻¹ ∈ pCore 2 K := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q₀ (n * k'⁻¹) = 1
      rw [map_mul,map_inv,hfix₀,mul_inv_cancel]
    exact mem_map_of_mem K.subtype hcore
  have hinner := Theory.SpecificGroups.Alternating.FiveSylowRadical.pCore_action_inner
    T K P F.L₁ hPK le_sup_right hKP le_sup_left
    (isPPerfect_embedded_pResidual 2 _) q
    (eK.surjective.comp (QuotientGroup.mk'_surjective _)) a ha hnona
  dsimp only
  intro r
  obtain ⟨r₀,hr₀,he⟩ := r.property
  change (r₀ : G) = (r : G) at he
  have hi := hinner ⟨r₀,hr₀⟩
  change MulAut.congr eK (quotientAut (pCore 2 K)
    (K.normalizerMonoidHom ⟨r₀,hPK r₀.property⟩)) ∈ _ at hi
  rw [←MulAut.map_innerSubgroup_congr eK,mem_map_equiv] at hi
  simpa only [MulEquiv.symm_apply_apply,he] using hi

/-- Literal primitive-component application, with normality discharged. -/
theorem source_primitive_alternatingFive_radical_inner
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (eJ : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (hnon : ¬ ⁅J.map H.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤
      (J.map H.subtype).pCoreIn 2) :
    let K := J.map H.subtype
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let P := F.L₁ ⊔ (T : Subgroup G)
    ∃ hn : H ≤ normalizer (K : Set G), ∀ r : P.pCoreIn 2,
      quotientAut (pCore 2 K)
        (K.normalizerMonoidHom ⟨r,hn (h.local_le (pCoreIn_le 2 P r.property))⟩) ∈
          MulAut.innerSubgroup (K ⧸ pCore 2 K) := by
  have hd : 3 ∣ Nat.card (J ⧸ pCore 2 J) := by
    rw [Nat.card_congr eJ.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hn := source_primitive_kernel_normalizes_of_three_dvd d h hne J hJ hs hJC hd
  let e := J.equivMapOfInjective H.subtype H.subtype_injective
  let eK := (QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans eJ
  exact ⟨hn,source_normal_alternatingFive_radical_inner d h eL hne hJC hn eK hnon⟩

/-- The exact radical factorization on printed p.937, for the original
normal A₅ kernel actor under contrary noncentral action. -/
theorem source_normal_alternatingFive_radical_factor
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hnon : ¬ ⁅K,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤ K.pCoreIn 2) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    R = (K ⊓ (T : Subgroup G)) ⊔ (K ⊔ R).pCoreIn 2 := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let P := F.L₁ ⊔ (T : Subgroup G)
  let R := P.pCoreIn 2
  have hRK : R ≤ normalizer (K : Set G) :=
    ((pCoreIn_le 2 P).trans h.local_le).trans hKn
  have hc : center (K ⧸ pCore 2 K) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hh : eK x ∈ center (alternatingGroup (Fin 5)) := (centerCongr eK ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact eK.injective (hh.trans eK.map_one.symm)
  obtain ⟨S,hS⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K
    (h.T_le_H.trans hKn)
  have hSm : (S : Subgroup K).map K.subtype = K ⊓ (T : Subgroup G) := by
    rw [hS,subgroupOf_map_subtype,inf_comm]
  have hSR : (S : Subgroup K).map K.subtype ≤ R := by
    rw [hSm]
    exact (le_inf (inf_le_left.trans hKC) (inf_le_right.trans le_sup_right)).trans
      (source_kernel_inf_point_le_radical d h eL hne)
  have hi := source_normal_alternatingFive_radical_inner d h eL hne hKC hKn eK hnon
  have hh := Subgroup.sup_core_factor_of_inner_action K R hRK (isPGroup_pCoreIn 2 P)
    hc S hSR hi
  rwa [hSm] at hh

/-- The selected primitive A₅ component satisfies the literal radical
factorization, with its normality supplied by the source hypotheses. -/
theorem source_primitive_alternatingFive_radical_factor
    (d : Section08.SourceCompletion.NaturalSetup T L V V₁ V₂ V₃ M G₁)
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hne : ⁅V₃,G₁.pCoreIn 2⁆ ≠ ⊥)
    (J : Subgroup H) (hJ : J.IsCComponent) (hs : IsSimpleGroup (J ⧸ pCore 2 J))
    (hJC : J.map H.subtype ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (eJ : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5))
    (hnon : ¬ ⁅J.map H.subtype,(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).L₁⁆ ≤
      (J.map H.subtype).pCoreIn 2) :
    let K := J.map H.subtype
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let R := (F.L₁ ⊔ (T : Subgroup G)).pCoreIn 2
    R = (K ⊓ (T : Subgroup G)) ⊔ (K ⊔ R).pCoreIn 2 := by
  have hd : 3 ∣ Nat.card (J ⧸ pCore 2 J) := by
    rw [Nat.card_congr eJ.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hn := source_primitive_kernel_normalizes_of_three_dvd d h hne J hJ hs hJC hd
  let e := J.equivMapOfInjective H.subtype H.subtype_injective
  let eK := (QuotientGroup.congr _ _ e.symm (pCore_map_iso 2 e.symm)).trans eJ
  exact source_normal_alternatingFive_radical_factor d h eL hne hJC hn eK hnon

end CFSG.Quasithin.Chapter13.Section07.PlusAction.Original
