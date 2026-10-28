module

public import CFSG.Quasithin.ChapterB.Section02.Baumann.Basic
public import CFSG.Quasithin.ChapterB.Section02.Baumann.Conjugacy
public import CFSG.Quasithin.ChapterB.Section02.Baumann.Dimension
public import CFSG.Quasithin.ChapterB.Section02.Baumann.EnlargedModule
public import CFSG.Quasithin.ChapterB.Section02.Baumann.Sylow

/-!
# Assembly of Baumann's argument

Under (a)–(d), the residual/Frattini argument gives normality of Q = C_R(V)
inside LR and equality of the LR- and I-conjugacy families of J(R). These
preliminary conclusions are available before hypothesis (e), as needed in B.2.19.

Adding (e), J(R) ≤ I, gives L ≤ I and the generation of I by those conjugates.
Maximum elementary replacements then make W = α(R)V an elementary module
normalized by LR, with W = C_W(Xᵢ)V for every generator. The fixed-space
dimension argument yields C_W(L) = C_W(I) and W = C_W(L)V. This proves the
alpha decomposition, from which the core containment and both Sylow conclusions
follow. `lemma_B_2_18` discharges every intermediate premise from (a)–(e).

The no-strong-offender premise is the quantitative condition on every nontrivial
elementary subgroup of the actual action quotient R*. Its translation from the
FF* definition belongs to B.1.4 and the parent section assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma B.2.18, printed pp.80–81.
-/

namespace CFSG.Quasithin.ChapterB.BaumannArgument

open Stellmacher Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Convert the two fixed-space identities into the source alpha decomposition.
The premises are the output of the dimension argument, whose source-hypothesis
discharge is separate from this group-theoretic final step. -/
public theorem alpha_decomposition_of_fixed_space (V R L I : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V]
    (hVR : V ≤ R) (hno : NoStrongOffenders V R)
    (hJI : elementaryAbelianMaxJ R ≤ I)
    (hfixed : (thompsonAlpha R ⊔ V) ⊓ centralizer (L : Set G) =
      (thompsonAlpha R ⊔ V) ⊓ centralizer (I : Set G))
    (hsplit : thompsonAlpha R ⊔ V =
      ((thompsonAlpha R ⊔ V) ⊓ centralizer (L : Set G)) ⊔ V) :
    thompsonAlpha R = (thompsonAlpha R ⊓ centralizer (L : Set G)) ⊔
      (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) := by
  let W := thompsonAlpha R ⊔ V
  let U := W ⊓ centralizer (L : Set G)
  let _ : IsElementaryAbelian 2 W := alpha_sup_elementary V R hVR hno
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ W from inf_le_left)
  have hUC : U ≤ centralizer (elementaryAbelianMaxJ R : Set G) := by
    change W ⊓ centralizer (L : Set G) ≤ _
    rw [hfixed]
    exact inf_le_right.trans (centralizer_le hJI)
  have hUa : U ≤ thompsonAlpha R :=
    elementary_centralizer_maxJ_le_omegaCenter R U
      (inf_le_left.trans (alpha_sup_le V R hVR)) hUC
  have hUeq : U = thompsonAlpha R ⊓ centralizer (L : Set G) :=
    le_antisymm (le_inf hUa inf_le_right) (inf_le_inf_right _ le_sup_left)
  have hFa : V ⊓ centralizer (elementaryAbelianMaxJ R : Set G) ≤ thompsonAlpha R := by
    rw [← alpha_inf_eq_fixed V R hVR]
    exact inf_le_left
  apply le_antisymm _ (sup_le inf_le_left hFa)
  intro a ha
  have haW : a ∈ W := (show thompsonAlpha R ≤ W from le_sup_left) ha
  rw [show W = U ⊔ V from hsplit] at haW
  obtain ⟨u, hu, v, hv, huv⟩ := mem_sup_of_normal_right.mp haW
  have hva : v ∈ thompsonAlpha R := by
    have hm := (thompsonAlpha R).mul_mem ((thompsonAlpha R).inv_mem (hUa hu)) ha
    rw [← huv] at hm
    simpa only [inv_mul_cancel_left] using hm
  have hvF : v ∈ V ⊓ centralizer (elementaryAbelianMaxJ R : Set G) := by
    rw [← alpha_inf_eq_fixed V R hVR]
    exact ⟨hva, hv⟩
  exact huv ▸ mul_mem_sup (hUeq ▸ hu) hvF

variable {ι : Type*} [Fintype ι]

/-- The enlarged-module and dimension arguments discharge both fixed-space
premises and give the alpha decomposition from precisely (a)–(e). -/
public theorem alpha_decomposition (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (X : ι → Subgroup G) (h : HypothesesAD V R X)
    (hJI : elementaryAbelianMaxJ R ≤ ⨆ i, X i) :
    thompsonAlpha R =
      (thompsonAlpha R ⊓ centralizer (pResidual 2 G : Set G)) ⊔
        (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) := by
  have hLI := residual_le_generated V R X h hJI
  obtain ⟨hW, hsupp⟩ := enlarged_module V R X h
    (generated_eq_sSup_conjugates V R X h hJI) hLI
    (internal_conjugate_generators V R X h)
  let _ : IsElementaryAbelian 2 (thompsonAlpha R ⊔ V : Subgroup G) :=
    alpha_sup_elementary V R h.V_le_R h.no_strong
  obtain ⟨hfixed, hsplit⟩ := fixed_space_eq_and_supplement V (thompsonAlpha R ⊔ V)
    X (pResidual 2 G) le_sup_right ((generated_le_join V R X h).trans hW)
    hLI h.codimension_sum hsupp
  exact alpha_decomposition_of_fixed_space V R (pResidual 2 G) (⨆ i, X i)
    h.V_le_R h.no_strong hJI hfixed hsplit

end CFSG.Quasithin.ChapterB.BaumannArgument

namespace CFSG.Quasithin.ChapterB
open Stellmacher Subgroup BaumannArgument
variable {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]

/-- The two preliminary conclusions of B.2.18 using only (a)–(d).
Normality is relative to LR, and hypothesis (e) is not needed. -/
public theorem lemma_B_2_18_preliminary (V R : Subgroup G) [V.Normal]
    (X : ι → Subgroup G) (h : HypothesesAD V R X) :
    ((R ⊓ centralizer (V : Set G)).subgroupOf (pResidual 2 G ⊔ R)).Normal ∧
      conjugatesBy (pResidual 2 G ⊔ R) (elementaryAbelianMaxJ R) =
        conjugatesBy (⨆ i, X i) (elementaryAbelianMaxJ R) :=
  ⟨centralizer_normal_in_join V R (pResidual 2 G) h.normalizes,
    conjugates_join_eq_generated V R X h⟩

/-- B.2.18 (Baumann's Argument): core containment, the alpha decomposition,
and both Sylow conclusions. The quantitative no-strong-offender condition
in (c) is certified by `noStrongOffenders_iff_quotient`; (e) is the separate
inclusion of J(R) in the generated subgroup. Every intermediate conjugacy,
invariance and fixed-space premise is discharged from these hypotheses. -/
public theorem lemma_B_2_18 (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (X : ι → Subgroup G) (h : HypothesesAD V R X)
    (hJI : elementaryAbelianMaxJ R ≤ ⨆ i, X i) :
    (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ baumann R ∧
      thompsonAlpha R =
        (thompsonAlpha R ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) ∧
      (IsSylowSubgroupIn (R ⊓ centralizer (V : Set G))
          ((pResidual 2 G ⊔ R) ⊓ centralizer (V : Set G)) →
        IsSylowSubgroupIn (baumann R ⊓ centralizer (V : Set G))
            ((pResidual 2 G ⊔ baumann R) ⊓ centralizer (V : Set G)) ∧
          (IsSylowSubgroupIn ((baumann R).map (actionMap V))
              ((pResidual 2 G).map (actionMap V) ⊔ (baumann R).map (actionMap V)) →
            IsSylowSubgroupIn (baumann R) (pResidual 2 G ⊔ baumann R))) := by
  have hd := alpha_decomposition V R X h hJI
  refine ⟨core_le_baumann_of_decomposition V R (pResidual 2 G) h.core_le hd, hd, ?_⟩
  intro hQ
  exact ⟨sylow_centralizer_of_decomposition V R (pResidual 2 G) hd hQ,
    sylow_lift_of_decomposition V R (pResidual 2 G) h.R_two hd hQ⟩

/-- B.2.18(1): the two-core of L lies in the Baumann subgroup. -/
public theorem lemma_B_2_18_1 (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (X : ι → Subgroup G) (h : HypothesesAD V R X)
    (hJI : elementaryAbelianMaxJ R ≤ ⨆ i, X i) :
    (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ baumann R :=
  (lemma_B_2_18 V R X h hJI).1

/-- B.2.18(2): the source alpha decomposition. -/
public theorem lemma_B_2_18_2 (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (X : ι → Subgroup G) (h : HypothesesAD V R X)
    (hJI : elementaryAbelianMaxJ R ≤ ⨆ i, X i) :
    thompsonAlpha R =
      (thompsonAlpha R ⊓ centralizer (pResidual 2 G : Set G)) ⊔
        (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) :=
  (lemma_B_2_18 V R X h hJI).2.1

/-- B.2.18(3): transfer of the Sylow centralizer condition, followed by
Sylow lifting when the action image of the Baumann subgroup is Sylow. -/
public theorem lemma_B_2_18_3 (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (X : ι → Subgroup G) (h : HypothesesAD V R X)
    (hJI : elementaryAbelianMaxJ R ≤ ⨆ i, X i)
    (hQ : IsSylowSubgroupIn (R ⊓ centralizer (V : Set G))
      ((pResidual 2 G ⊔ R) ⊓ centralizer (V : Set G))) :
    IsSylowSubgroupIn (baumann R ⊓ centralizer (V : Set G))
        ((pResidual 2 G ⊔ baumann R) ⊓ centralizer (V : Set G)) ∧
      (IsSylowSubgroupIn ((baumann R).map (actionMap V))
          ((pResidual 2 G).map (actionMap V) ⊔ (baumann R).map (actionMap V)) →
        IsSylowSubgroupIn (baumann R) (pResidual 2 G ⊔ baumann R)) :=
  (lemma_B_2_18 V R X h hJI).2.2 hQ

end CFSG.Quasithin.ChapterB
