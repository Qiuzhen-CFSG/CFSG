module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.ActorAlternatives.Kernels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.ActorAlternatives.Reindex
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.ActorAlternatives.Normalization
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.ActorAlternatives.SplitAction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.SecondActor.Faithfulness
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.RankBounds
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Selection
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Five-primary actor alternatives at the genuine critical endpoint

The endpoint is the literal conjugate Uγ from the critical pair. Its elementary
abelian structure descends to H/O₂(H). Its action on U_H/V₁ is quadratic because
U_H normalizes the abelian Uγ. The earlier conjugate-core placement for Vγ,
together with H=P(L₁T) and O₂(H*)=1, makes Uγ* faithful on the generated
five-factors. Faithfulness is thus derived, not added to the source inputs.

`endpoint_split_alternatives` derives factor normalization, then constructs
`RankOneFactors` or `RankTwoFactors` from the supplied factorization. In the
first case an explicit permutation selects the unique moved factor and the
whole displacement has order four. In the second case the two complementary
involution subgroups have cross-fixed supports, each full displacement is a
plane, and both the full displacement order and the fixed index are sixteen.
The output also proves that the P-fixed complement is fixed by the endpoint.

The earlier source inputs are explicit: elementary V and abelian V_H
(13.8.2), the flag containments, mutual normalization and the actual Dγ kernel
(F.9.13), and the strict Dγ, offender bound and conjugate-core placement for
the endpoint selected in 13.8.8(2). The numerical bound is precisely
|Ũ_H : C_{Ũ_H}(Uγ*)| ≤ |Uγ*|² from D.2.1; it imposes no minimality among
offenders. Solvable minimal membership in the genuine Hz is retained, with
its generation consequence already in `ReducedFive`. No faithfulness on P*,
factor normalization, actor rank or alternative is an input.

`exists_rank_alternatives` gives the requested disjunction. The subsequent
F.9.16 equality-case application and exclusion of its rank-two branch belong
to the final five-factor assembly, not to this actor construction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.4(6),
13.8.8(2), and 13.8.13, printed pp.947, 949 and 951.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.ActorAlternatives
variable {G : Type*} [Group G]
variable {L T H V V₁ V₃ : Subgroup G} (c : CriticalGeometry.CriticalPair L T H V)

/-- The actual endpoint star image is elementary abelian when the source
normal closure U_H is elementary abelian. -/
theorem endpoint_star_elementary [IsElementaryAbelian 2 (Source.UH H V₃)]
    (hUγH : c.Ugamma V₃ ≤ H) :
    IsElementaryAbelian 2 (Source.starImage H (c.Ugamma V₃)) := by
  let : IsElementaryAbelian 2 (c.Ugamma V₃) :=
    IsElementaryAbelian.map (MulAut.conj (c.gb : G)).toMonoidHom
  let : IsElementaryAbelian 2 ((c.Ugamma V₃).subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hUγH
  exact IsElementaryAbelian.map (QuotientGroup.mk' (pCore 2 H))

/-- Mutual local normalization gives quadraticity for the prescribed action
on the entire source quotient. No support restriction is substituted for it. -/
theorem endpoint_quadratic [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.UH H V₃)]
    (a : StarAction H (Source.UH H V₃) V₁)
    (hUγH : c.Ugamma V₃ ≤ H)
    (hn : Source.UH H V₃ ≤ normalizer (c.Ugamma V₃ : Set G)) :
    commutatorAction₂ (a.actors (c.Ugamma V₃))
      (Source.UH H V₃ ⧸ V₁.subgroupOf (Source.UH H V₃)) = ⊥ := by
  have hUγ : IsMulCommutative (c.Ugamma V₃) :=
    Subgroup.map_isMulCommutative (Source.UH H V₃) (MulAut.conj (c.gb : G)).toMonoidHom
  have hdouble : ⁅⁅Source.UH H V₃, c.Ugamma V₃⁆, c.Ugamma V₃⁆ ≤ V₁ :=
    (quadratic_of_normalizes_abelian _ _ hn hUγ).le.trans bot_le
  rw [a.actors_eq]
  exact quotient_conjugation_quadratic_of_double_commutator_le
    H (Source.UH H V₃) V₁ (c.Ugamma V₃) a.normalizes hUγH inferInstance hdouble
      (a.action.comp (QuotientGroup.mk' (pCore 2 H))) a.conjugation

/-- The source conjugate-core placement of Vγ proves joint faithfulness of
Uγ* on the actual five-factors, using their generation of the supplied P. -/
theorem endpoint_faithful_on_factors [Finite G]
    {L₁ M Vα : Subgroup G} [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (a : StarAction H (Source.UH H V₃) V₁)
    (r : ReducedFive H L₁ T M Vα) (f : Factorization a r.P)
    (hUV : Source.UH H V₃ ≤ Source.VH H V) (h : H)
    (hplace : c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    Source.starImage H (c.Ugamma V₃) ⊓
      centralizer ((⨆ i, Source.starImage H (f.factor i) : Subgroup (Source.Hstar H)) :
        Set (Source.Hstar H)) = ⊥ := by
  have hUVγ : c.Ugamma V₃ ≤ c.Vgamma := map_mono hUV
  have hstar : Source.starImage H (c.Ugamma V₃) ≤ Source.starImage H c.Vgamma :=
    map_mono (subgroupOf_mono H hUVγ)
  rw [← f.star_generated r.P_le]
  apply bot_unique
  exact (inf_le_inf_right _ hstar).trans_eq
    (Localization.SecondActor.star_faithful_on_P_of_core_placement r h hplace)

private theorem endpoint_le_of_core_placement {L₁ M Vα : Subgroup G}
    (r : ReducedFive H L₁ T M Vα) (h : H)
    (hplace : c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    c.Vgamma ≤ H := by
  have hJ : L₁ ⊔ T ≤ H := r.generated ▸ le_sup_right
  intro v hv
  have hc : (h : G) * v * (h : G)⁻¹ ∈ H :=
    ((pCoreIn_le 2 (L₁ ⊔ T)).trans hJ) (hplace (mem_map_of_mem _ hv))
  have hb := H.mul_mem (H.mul_mem (H.inv_mem h.property) hc) h.property
  simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hb

private theorem source_UH_elementary [IsElementaryAbelian 2 V]
    [IsMulCommutative (Source.VH H V)] (hV₃ : V₃ ≤ V) :
    IsElementaryAbelian 2 (Source.UH H V₃) := by
  let : IsElementaryAbelian 2 (Source.VH H V) := by
    let : IsMulCommutative (closure {x | ∃ h ∈ H, ∃ v ∈ V, h * v * h⁻¹ = x}) :=
      (inferInstance : IsMulCommutative (Source.VH H V))
    change IsElementaryAbelian 2 (closure {x | ∃ h ∈ H, ∃ v ∈ V, h * v * h⁻¹ = x})
    apply IsElementaryAbelian.closure_of_isMulCommutative
    rintro x ⟨h, _, v, hv, rfl⟩
    rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian v hv, mul_one, mul_inv_cancel]
  exact IsElementaryAbelian.of_le (B := Source.VH H V)
    (conjugateSpanBy_mono hV₃ le_rfl)

variable [Finite G] {L₁ M Vα G₁ : Subgroup G}
variable [(V₁.subgroupOf (Source.UH H V₃)).Normal]
variable [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]

/-- Construct the alternatives and their split-support identities for the actual
endpoint selected in 13.8.8(2). The explicit earlier conclusions are the local
normalization and kernel identities from F.9.13, strict Dγ, the whole-quotient
quadratic offender bound, and the conjugate-core placement. Elementary
abelianness, nontriviality, quadraticity, faithfulness on P* and normalization
of the supplied factors are all derived before the split calculation.

The factors are preserved up to a displayed permutation in rank one, and
exactly in rank two. The latter includes BOTH order-sixteen conclusions on
the entire quotient; `RankTwoSplitData` additionally retains the full-support
identities and fixation of the P-fixed complement. -/
theorem endpoint_split_alternatives
    (a : StarAction H (Source.UH H V₃) V₁) (ha : Function.Injective a.action)
    (r : ReducedFive H L₁ T M Vα) (f : Factorization a r.P)
    (_hminimal : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (_hsolvable : Group.IsSolvable H)
    (hV₃ : V₃ ≤ V) (_hV₁ : V₁ ≤ Source.UH H V₃)
    (hn : Source.UH H V₃ ≤ normalizer (c.Ugamma V₃ : Set G))
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ =
      c.Ugamma V₃ ⊓ Source.QH H)
    (hproper : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (hbound : (FixedPoints.subgroup (a.actors (c.Ugamma V₃))
      (Source.Utilde H V₃ V₁)).index ≤ (Nat.card (Source.starImage H (c.Ugamma V₃))) ^ 2)
    (hplacement : ∃ h : H,
      c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    (∃ (e : Equiv.Perm (Fin f.count)) (s : RankOneFactors a r.P (c.Ugamma V₃)),
      s.factors = f.reindex e ∧ SplitAction.RankOneSplitData s) ∨
    (∃ s : RankTwoFactors a r.P (c.Ugamma V₃),
      s.factors = f ∧ SplitAction.RankTwoSplitData s) := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := source_UH_elementary hV₃
  obtain ⟨h, hplace⟩ := hplacement
  have hUV : Source.UH H V₃ ≤ Source.VH H V := conjugateSpanBy_mono hV₃ le_rfl
  have hUγH : c.Ugamma V₃ ≤ H :=
    (map_mono hUV).trans (endpoint_le_of_core_placement c r h hplace)
  let : IsElementaryAbelian 2 (Source.starImage H (c.Ugamma V₃)) :=
    endpoint_star_elementary c hUγH
  have hne := CriticalGeometry.starImage_ne_bot_of_Dgamma_lt H (Source.UH H V₃)
    (c.Ugamma V₃) V₁ hUγH hDγ hproper
  have hfaith : Source.starImage H (c.Ugamma V₃) ⊓
      centralizer (Source.starImage H r.P : Set _) = ⊥ := by
    rw [f.star_generated r.P_le]
    exact endpoint_faithful_on_factors c a r f hUV h hplace
  have hquad := endpoint_quadratic c a hUγH hn
  have hnorm := f.star_normalizes_of_quadratic_offender a ha r.P_le r.Pstar_normal
    (Source.starImage H (c.Ugamma V₃)) hne hfaith hquad hbound
  exact SplitAction.normalized_split_alternatives ha f r.P_le hne hfaith hnorm hbound

/-- The actor alternatives in the five-primary paragraph of 13.8.13, from
an explicit factorization and the permitted earlier source conclusions.
The rank-two branch is retained for the subsequent F.9.16 argument. -/
theorem exists_rank_alternatives
    (a : StarAction H (Source.UH H V₃) V₁) (ha : Function.Injective a.action)
    (r : ReducedFive H L₁ T M Vα) (f : Factorization a r.P)
    (hminimal : Minimal (· ∈ Source.Hz L₁ T G₁ M) H)
    (hsolvable : Group.IsSolvable H)
    (hV₃ : V₃ ≤ V) (hV₁ : V₁ ≤ Source.UH H V₃)
    (hn : Source.UH H V₃ ≤ normalizer (c.Ugamma V₃ : Set G))
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ =
      c.Ugamma V₃ ⊓ Source.QH H)
    (hproper : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (hbound : (FixedPoints.subgroup (a.actors (c.Ugamma V₃))
      (Source.Utilde H V₃ V₁)).index ≤ (Nat.card (Source.starImage H (c.Ugamma V₃))) ^ 2)
    (hplacement : ∃ h : H,
      c.Vgamma.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    Nonempty (RankOneFactors a r.P (c.Ugamma V₃)) ∨
      Nonempty (RankTwoFactors a r.P (c.Ugamma V₃)) := by
  rcases endpoint_split_alternatives c a ha r f hminimal hsolvable hV₃ hV₁ hn hDγ
    hproper hbound hplacement with ⟨_, s, _, _⟩ | ⟨s, _, _⟩
  · exact Or.inl ⟨s⟩
  · exact Or.inr ⟨s⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.ActorAlternatives
end
