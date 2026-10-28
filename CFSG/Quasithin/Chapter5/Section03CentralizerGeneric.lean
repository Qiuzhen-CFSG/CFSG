module

public import CFSG.Quasithin.Chapter5.Section03
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The generic centralizer argument in §5.3

This file contains conditional reductions toward Aschbacher--Smith, Lemmas
5.3.5--5.3.7 (combined manuscript, printed pp. 660--661). It does not yet
establish these source results: the genuine Lie-amalgam geometry, local
characteristic-two deductions and local intersection bounds remain obligations.

Burnside fusion for normal subgroups of a Sylow subgroup is proved by Sylow
conjugacy inside a subgroup normalizer. The action on two candidates factors
through a two-group, so the two-residual acts trivially. Together with the
Sylow subgroup it generates the Sylow normalizer. This is `O²`, not `O₂`.
The existing conditional interfaces are retained for final source assembly.
The subgroup-conjugacy orbit assertion 5.3.6(2), including its cardinality
`q + 1`, also remains to be established from the actual local model.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter5.Section03

open Subgroup MulAction

open scoped Pointwise

/-! ### The p-core step -/

/-- A normal Sylow `p`-subgroup is the ambient image of the `p`-core.

The equality is stated for `pCoreIn`, so it can be used without changing the
ambient group when a local subgroup is viewed inside `G`.
-/
theorem pCoreIn_eq_of_normal_sylow
    {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    (H S : Subgroup G) (hS : IsPGroup p S) (hSH : S ≤ H)
    (hnormal : H ≤ normalizer (S : Set G))
    (P : Sylow p H)
    (hP : (P : Subgroup H).map H.subtype = S) :
    H.pCoreIn p = S := by
  have hSP : S ≤ H.pCoreIn p :=
    le_pCoreIn_of_normalizes hS hSH hnormal
  have hcore : H.pCoreIn p ≤ (P : Subgroup H).map H.subtype :=
    pCoreIn_le_sylow H P
  rw [hP] at hcore
  exact le_antisymm hcore hSP

/-! ### Lemma 5.3.5 -/

/-- The normalizer calculation for `Z(S)`.

`hcore` is the p-core calculation in `C_G(Z(S))`; `hAcontrol` is the local
fact that a normalizer of `Z(S)` permutes the two maximal elementary abelian
subgroups of `S`.  The proof itself only uses the resulting normalizer
containments, and hence remains applicable to the exact 5.2/F.4.29 models.
-/
theorem normalizer_center_sylow_eq_inter
    {G : Type*} [Group G]
    (M₁ M₂ S V₁ V₂ ZS : Subgroup G)
    (hcore : pCoreIn 2 (centralizer (ZS : Set G)) = S)
    (hcenter_core : normalizer (ZS : Set G) ≤ normalizer (S : Set G))
    (hAcontrol : ∀ g : G,
      g ∈ normalizer (pCoreIn 2 (centralizer (ZS : Set G)) : Set G) →
      g ∈ normalizer (V₁ : Set G) ∧ g ∈ normalizer (V₂ : Set G))
    (hN₁ : normalizer (V₁ : Set G) ≤ M₁)
    (hN₂ : normalizer (V₂ : Set G) ≤ M₂)
    (h12S : M₁ ⊓ M₂ ≤ normalizer (S : Set G))
    (hScenter : normalizer (S : Set G) ≤ normalizer (ZS : Set G)) :
    normalizer (ZS : Set G) = M₁ ⊓ M₂ := by
  have hleft : normalizer (ZS : Set G) ≤ M₁ ⊓ M₂ := by
    intro g hg
    have hgcore : g ∈ normalizer
        (pCoreIn 2 (centralizer (ZS : Set G)) : Set G) := by
      rw [hcore]
      exact hcenter_core hg
    exact ⟨hN₁ (hAcontrol g hgcore).1, hN₂ (hAcontrol g hgcore).2⟩
  have hright : M₁ ⊓ M₂ ≤ normalizer (ZS : Set G) :=
    h12S.trans hScenter
  exact le_antisymm hleft hright

/-! ### Lemma 5.3.6 -/

/-- Burnside fusion for subgroups normalized by a Sylow subgroup.
Conjugate the two Sylow subgroups inside the normalizer of the target. -/
theorem normal_subgroup_fusion {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) (A B : Subgroup G)
    (hA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (g : G) (hg : A.map (MulAut.conj g).toMonoidHom = B) :
    ∃ n ∈ normalizer (T : Set G), A.map (MulAut.conj n).toMonoidHom = B := by
  have h2 : ((g • T : Sylow p G) : Subgroup G) ≤ normalizer (B : Set G) := by
    rw [← hg]
    exact (map_mono hA).trans (A.le_normalizer_map (MulAut.conj g).toMonoidHom)
  obtain ⟨h, hh⟩ := exists_smul_eq (normalizer (B : Set G))
    ((g • T).subtype h2) (T.subtype hB)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hh
  refine ⟨h * g, Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hh), ?_⟩
  have hcomp : (MulAut.conj ((h : G) * g)).toMonoidHom =
      (MulAut.conj (h : G)).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, ← map_map, hg]
  exact mem_normalizer_iff_map_conj_eq.mp h.property


/-- A Sylow subgroup and the p-residual generate a finite group. -/
theorem sylow_sup_pResidual_eq_top {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T : Sylow p G) : (T : Subgroup G) ⊔ pResidual p G = ⊤ := by
  let f := QuotientGroup.mk' (pResidual p G)
  have hf := QuotientGroup.mk'_surjective (pResidual p G)
  have hp := (Subgroup.isPGroup_quotient_pResidual (G := G) p).to_subgroup ⊤
  have ht : (T : Subgroup G).map f = ⊤ :=
    ((T.mapSurjective hf).is_maximal' hp le_top).symm
  have he := congrArg (Subgroup.comap f) ht
  simpa only [comap_map_eq, f, QuotientGroup.ker_mk', comap_top] using he

private theorem residual_kills_action {G X : Type*} [Group G] [MulAction G X]
    (hp : IsPGroup 2 (Equiv.Perm X)) :
    pResidual 2 G ≤ (MulAction.toPermHom G X).ker := by
  let f := MulAction.toPermHom G X
  exact sInf_le ⟨inferInstance,
    (hp.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm⟩

/-- An overgroup of a Sylow subgroup fixes an invariant pair if the
Sylow subgroup does. The two-residual lies in the permutation action kernel. -/
theorem sylow_overgroup_fixes_two_candidates {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (N : Subgroup G) (hTN : (T : Subgroup G) ≤ N) (A B : Subgroup G) (hne : A ≠ B)
    (hA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hperm : ∀ g ∈ N, ∀ V ∈ ({A, B} : Set (Subgroup G)),
      V.map (MulAut.conj g).toMonoidHom ∈ ({A, B} : Set (Subgroup G))) :
    ∀ g ∈ N, A.map (MulAut.conj g).toMonoidHom = A := by
  classical
  let : MulAction N (Subgroup G) := MulAction.compHom (Subgroup G)
    (MulAut.conj.comp N.subtype)
  let X : SubMulAction N (Subgroup G) :=
    { carrier := {A, B}
      smul_mem' := fun g _ hV => hperm g g.property _ hV }
  let : Fintype X := ((Set.finite_singleton B).insert A).fintype
  have hcard : Fintype.card X = 2 := by
    change Fintype.card ({A, B} : Set (Subgroup G)) = 2
    simp [hne]
  have hp : IsPGroup 2 (Equiv.Perm X) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_eq_fintype_card, Fintype.card_perm, hcard]; rfl)
  let f := MulAction.toPermHom N X
  have hT : (T.subtype hTN : Subgroup N) ≤ f.ker := by
    intro t ht
    apply MonoidHom.mem_ker.mpr
    apply Equiv.ext
    intro V
    apply Subtype.ext
    change V.val.map (MulAut.conj (t : G)).toMonoidHom = V.val
    rcases V.property with h | h
    · rw [h]
      exact mem_normalizer_iff_map_conj_eq.mp (hA ht)
    · have hVB : V.val = B := h
      rw [hVB]
      exact mem_normalizer_iff_map_conj_eq.mp (hB ht)
  have hall : (⊤ : Subgroup N) ≤ f.ker := by
    rw [← sylow_sup_pResidual_eq_top (T.subtype hTN)]
    exact sup_le hT (residual_kills_action hp)
  intro g hg
  have he := Equiv.congr_fun (MonoidHom.mem_ker.mp (hall (mem_top ⟨g, hg⟩)))
    (⟨A, Or.inl rfl⟩ : X)
  exact congrArg Subtype.val he


/-- In particular, the Sylow normalizer fixes each of its two candidates. -/
theorem normalizer_fixes_two_candidates
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (A B : Subgroup G) (hne : A ≠ B)
    (hA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hperm : ∀ g ∈ normalizer (T : Set G), ∀ V ∈ ({A, B} : Set (Subgroup G)),
      V.map (MulAut.conj g).toMonoidHom ∈ ({A, B} : Set (Subgroup G))) :
    ∀ g ∈ normalizer (T : Set G), A.map (MulAut.conj g).toMonoidHom = A :=
  sylow_overgroup_fixes_two_candidates T _ le_normalizer A B hne hA hB hperm

/-- Burnside's fusion reduction turns a conjugacy between the two candidates
into a conjugacy in the Sylow normalizer. Both fusion and fixedness are
premises of this conditional helper. The legacy binder name `hO₂` denotes
fixedness, not a two-core assertion; the source uses the two-residual `O²`.
-/
theorem not_conjugate_of_normalizer_fusion
    {G : Type*} [Group G]
    (T V₁ V₂ : Subgroup G)
    (hfusion : ∀ g : G,
      V₁.map (MulAut.conj g).toMonoidHom = V₂ →
        ∃ n ∈ normalizer (T : Set G),
          V₁.map (MulAut.conj n).toMonoidHom = V₂)
    (hO₂ : ∀ n : G, n ∈ normalizer (T : Set G) →
      V₁.map (MulAut.conj n).toMonoidHom = V₁)
    (hne : V₁ ≠ V₂) :
    ∀ g : G, V₁.map (MulAut.conj g).toMonoidHom ≠ V₂ := by
  intro g hconj
  obtain ⟨n, hn, heq⟩ := hfusion g hconj
  exact hne ((hO₂ n hn).symm.trans heq)

/-- The two maximal elementary abelian candidates are weakly closed in `T`.

The candidate hypothesis is the `A(T) = {V₁,V₂}` calculation, while
`not_conjugate_of_normalizer_fusion` combines separately established fusion
and fixedness premises. This helper alone does not prove source 5.3.6.
-/
theorem weakly_closed_V₁_of_local_fusion
    {G : Type*} [Group G]
    (T V₁ V₂ : Subgroup G)
    (hA : ∀ g : G,
      V₁.map (MulAut.conj g).toMonoidHom ≤ T →
        V₁.map (MulAut.conj g).toMonoidHom = V₁ ∨
        V₁.map (MulAut.conj g).toMonoidHom = V₂)
    (hnotconj : ∀ g : G,
      V₁.map (MulAut.conj g).toMonoidHom ≠ V₂) :
    ∀ g : G, V₁.map (MulAut.conj g).toMonoidHom ≤ T →
      V₁.map (MulAut.conj g).toMonoidHom = V₁ :=
  weakly_closed_of_two_candidates T V₁ V₂ hA hnotconj

/-- The symmetric weak-closure statement for `V₂`. -/
theorem weakly_closed_V₂_of_local_fusion
    {G : Type*} [Group G]
    (T V₁ V₂ : Subgroup G)
    (hA : ∀ g : G,
      V₂.map (MulAut.conj g).toMonoidHom ≤ T →
        V₂.map (MulAut.conj g).toMonoidHom = V₂ ∨
        V₂.map (MulAut.conj g).toMonoidHom = V₁)
    (hnotconj : ∀ g : G,
      V₂.map (MulAut.conj g).toMonoidHom ≠ V₁) :
    ∀ g : G, V₂.map (MulAut.conj g).toMonoidHom ≤ T →
      V₂.map (MulAut.conj g).toMonoidHom = V₂ :=
  weakly_closed_of_two_candidates T V₂ V₁ hA hnotconj

/-- Two normal candidates exhaust returning conjugates, hence are weakly
closed. Burnside fusion and normalizer fixedness are proved, not assumed.
The source still has to supply its `A(T)` calculation. -/
theorem weakly_closed_normal_pair
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (V₁ V₂ : Subgroup G) (hne : V₁ ≠ V₂)
    (hV₁ : V₁ ≤ (T : Subgroup G)) (hV₂ : V₂ ≤ (T : Subgroup G))
    (hn₁ : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hn₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hA : ∀ V ∈ ({V₁, V₂} : Set (Subgroup G)), ∀ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      V.map (MulAut.conj g).toMonoidHom ∈ ({V₁, V₂} : Set (Subgroup G))) :
    ∀ V ∈ ({V₁, V₂} : Set (Subgroup G)), ∀ g : G,
      V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      V.map (MulAut.conj g).toMonoidHom = V := by
  have hperm : ∀ g ∈ normalizer (T : Set G), ∀ V ∈ ({V₁, V₂} : Set (Subgroup G)),
      V.map (MulAut.conj g).toMonoidHom ∈ ({V₁, V₂} : Set (Subgroup G)) := by
    intro g hg V hV
    apply hA V hV g
    have hVT : V ≤ (T : Subgroup G) := by
      rcases hV with rfl | hV
      · exact hV₁
      · exact hV ▸ hV₂
    exact (map_mono hVT).trans (mem_normalizer_iff_map_conj_eq.mp hg).le
  have hfix := normalizer_fixes_two_candidates T V₁ V₂ hne hn₁ hn₂ hperm
  have hnot := not_conjugate_of_normalizer_fusion (T : Subgroup G) V₁ V₂
    (normal_subgroup_fusion T V₁ V₂ hn₁ hn₂) hfix hne
  have hnot' : ∀ g : G, V₂.map (MulAut.conj g).toMonoidHom ≠ V₁ := by
    intro g he
    apply hnot g⁻¹
    rw [← he, map_map]
    have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        MonoidHom.id G := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hid, map_id]
  intro V hV g hg
  rcases hV with hV | hV
  · have he : V = V₁ := hV
    subst V
    exact (hA V₁ (Or.inl rfl) g hg).resolve_right (hnot g)
  · have he : V = V₂ := hV
    subst V
    exact (hA V₂ (Or.inr rfl) g hg).resolve_left (hnot' g)

/-! ### The nonexceptional part of Lemma 5.3.7 -/

/-- Conditional involution-centralizer elimination.

Here `R` is `O₂(C_G(z))` and `ZR` is the local subgroup representing
`Ω₁(Z(R))`.  The first branch is the equality `Z(S) = ZR`; the other two
branches are the source's conclusion `R = V₁` or `R = V₂`.  The hypotheses
`hZbranch` and `hVbranch` are the
local normalizer bounds. Neither the structural alternative nor these bounds
are established by this helper; its statement does not certify source 5.3.7.
-/
theorem centralizer_involution_le_inter_generic
    {G : Type*} [Group G]
    (M₁ M₂ S V₁ V₂ ZS ZR R Gz : Subgroup G)
    (hRcore : R = pCoreIn 2 Gz)
    (hRleS : R ≤ S)
    (hbranch : ZS = ZR ∨
      pCoreIn 2 Gz = V₁ ∨ pCoreIn 2 Gz = V₂)
    (hZbranch : ZS = ZR → R ≤ S → Gz ≤ normalizer (ZS : Set G))
    (hV₁branch : R = V₁ → R ≤ S → Gz ≤ normalizer (V₁ : Set G))
    (hV₂branch : R = V₂ → R ≤ S → Gz ≤ normalizer (V₂ : Set G))
    (hN₁ : normalizer (V₁ : Set G) ≤ M₁)
    (hN₂ : normalizer (V₂ : Set G) ≤ M₂)
    (hinter₁ : Gz ⊓ M₁ ≤ M₁ ⊓ M₂)
    (hinter₂ : Gz ⊓ M₂ ≤ M₁ ⊓ M₂)
    (hcenterN : normalizer (ZS : Set G) ≤ M₁ ⊓ M₂) :
    Gz ≤ M₁ ⊓ M₂ := by
  rcases hbranch with hZ | hV
  · intro x hx
    exact hcenterN (hZbranch hZ hRleS hx)
  · rcases hV with hV₁ | hV₂
    · have hRV₁ : R = V₁ := hRcore.trans hV₁
      have hGzM₁ : Gz ≤ M₁ := (hV₁branch hRV₁ hRleS).trans hN₁
      intro x hx
      exact hinter₁ ⟨hx, hGzM₁ hx⟩
    · have hRV₂ : R = V₂ := hRcore.trans hV₂
      have hGzM₂ : Gz ≤ M₂ := (hV₂branch hRV₂ hRleS).trans hN₂
      intro x hx
      exact hinter₂ ⟨hx, hGzM₂ hx⟩

/-- The first omega subgroup of the center of the local two-core is
normalized by the local group. No ambient normality is assumed. -/
theorem omega_center_pCoreIn_normalized {G : Type*} [Group G] (H R : Subgroup G)
    (hR : R = H.pCoreIn 2) :
    H ≤ normalizer ((((omega₁ (center R) (p := 2)).map (center R).subtype).map
      R.subtype) : Set G) := by
  have hRN : H ≤ normalizer (R : Set G) := by
    rw [hR]
    exact H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hc : ((omega₁ (center R) (p := 2)).map (center R).subtype).Characteristic := by
    let : (omega₁ (center R) (p := 2)).Characteristic := omega₁_characteristic _
    infer_instance
  exact hRN.trans (normalizer_le_normalizer_characteristic_image R _)

/-- The structural alternative in the generic centralizer argument, conditional
on the local involution-centralizer calculation in `S`. A central involution
of `R` outside `Z` forces `R` into one abelian root plane; self-centralization
then gives equality. The matrix calculation and its marked transport remain
separate source obligations. -/
theorem core_alternative_of_involution_geometry {G : Type*} [Group G]
    (H R S Z V₁ V₂ : Subgroup G)
    (hRS : R ≤ S) (hZH : Z ≤ H) (hZC : Z ≤ centralizer (S : Set G))
    (hZexp : ∀ x ∈ Z, x ^ 2 = 1)
    (hself : H ⊓ centralizer (R : Set G) ≤ R)
    (hV₁ : V₁ ≤ H) (hV₂ : V₂ ≤ H)
    (hcomm₁ : IsMulCommutative V₁) (hcomm₂ : IsMulCommutative V₂)
    (hgeometry : ∀ x ∈ S, x ^ 2 = 1 → x ∉ Z →
      S ⊓ centralizer ({x} : Set G) = V₁ ∨
      S ⊓ centralizer ({x} : Set G) = V₂) :
    Z = ((omega₁ (center R) (p := 2)).map (center R).subtype).map R.subtype ∨
      R = V₁ ∨ R = V₂ := by
  let ZR := ((omega₁ (center R) (p := 2)).map (center R).subtype).map R.subtype
  have hZR : Z ≤ ZR := by
    intro x hx
    have hxC : x ∈ centralizer (R : Set G) := centralizer_le hRS (hZC hx)
    have hxR : x ∈ R := hself ⟨hZH hx, hxC⟩
    have hxcenter : (⟨x, hxR⟩ : R) ∈ center R := by
      rw [mem_center_iff]
      intro r
      exact Subtype.ext (hxC r r.property)
    refine ⟨⟨x, hxR⟩, ⟨⟨⟨x, hxR⟩, hxcenter⟩, subset_closure ?_, rfl⟩, rfl⟩
    change (⟨⟨x, hxR⟩, hxcenter⟩ : center R) ^ (2 ^ 1) = 1
    apply Subtype.ext
    apply Subtype.ext
    simpa using hZexp x hx
  by_cases he : Z = ZR
  · exact Or.inl he
  obtain ⟨x, hxZR, hxZ⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hZR he)
  obtain ⟨r, ⟨c, hc, hcr⟩, hrx⟩ := hxZR
  subst r
  subst x
  have hcR : (c : R) ∈ center R := c.property
  have hp : (c : G) ^ 2 = 1 := by
    let : IsElementaryAbelian 2 (omega₁ (center R) (p := 2)) :=
      IsElementaryAbelian.omega₁_of_isMulCommutative _
    exact congrArg R.subtype (congrArg (center R).subtype
      (elemPow_eq_one_of_isElementaryAbelian c hc))
  have hRC : R ≤ S ⊓ centralizer ({(c : G)} : Set G) := by
    refine le_inf hRS ?_
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg R.subtype (mem_center_iff.mp hcR ⟨r, hr⟩)
  have finish (V : Subgroup G) (hVH : V ≤ H) (hcomm : IsMulCommutative V)
      (heq : S ⊓ centralizer ({(c : G)} : Set G) = V) : R = V := by
    have hRV : R ≤ V := heq ▸ hRC
    apply le_antisymm hRV
    exact (le_inf hVH ((le_centralizer_iff_isMulCommutative.mpr hcomm).trans
      (centralizer_le hRV))).trans hself
  rcases hgeometry (c : G) (hRS (c : R).property) hp hxZ with h₁ | h₂
  · exact Or.inr (Or.inl (finish V₁ hV₁ hcomm₁ h₁))
  · exact Or.inr (Or.inr (finish V₂ hV₂ hcomm₂ h₂))

/-- The normalizer calculation with characteristicity and the pair action
discharged. The p-core identity and invariant pair still have to come from
the source local structure. -/
theorem normalizer_center_eq_inter_of_pair_action
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M₁ M₂ S V₁ V₂ ZS : Subgroup G)
    (hcore : (centralizer (ZS : Set G)).pCoreIn 2 = S)
    (hZS : ZS = (center S).map S.subtype)
    (hT : (T : Subgroup G) ≤ normalizer (ZS : Set G))
    (hne : V₁ ≠ V₂)
    (hn₁ : (T : Subgroup G) ≤ normalizer (V₁ : Set G))
    (hn₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hperm : ∀ g ∈ normalizer (S : Set G), ∀ V ∈ ({V₁, V₂} : Set (Subgroup G)),
      V.map (MulAut.conj g).toMonoidHom ∈ ({V₁, V₂} : Set (Subgroup G)))
    (hN₁ : normalizer (V₁ : Set G) ≤ M₁)
    (hN₂ : normalizer (V₂ : Set G) ≤ M₂)
    (h12S : M₁ ⊓ M₂ ≤ normalizer (S : Set G)) :
    normalizer (ZS : Set G) = M₁ ⊓ M₂ := by
  have hc : normalizer (ZS : Set G) ≤ normalizer (S : Set G) := by
    rw [← hcore]
    exact (normalizer_le_normalizer_centralizer ZS).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hfix₁ := sylow_overgroup_fixes_two_candidates T _ (hT.trans hc)
    V₁ V₂ hne hn₁ hn₂ hperm
  have hperm' : ∀ g ∈ normalizer (S : Set G), ∀ V ∈ ({V₂, V₁} : Set (Subgroup G)),
      V.map (MulAut.conj g).toMonoidHom ∈ ({V₂, V₁} : Set (Subgroup G)) := by
    simpa only [Set.pair_comm V₂ V₁] using hperm
  have hfix₂ := sylow_overgroup_fixes_two_candidates T _ (hT.trans hc)
    V₂ V₁ hne.symm hn₂ hn₁ hperm'
  apply normalizer_center_sylow_eq_inter M₁ M₂ S V₁ V₂ ZS hcore hc
  · intro g hg
    rw [hcore] at hg
    exact ⟨mem_normalizer_iff_map_conj_eq.mpr (hfix₁ g hg),
      mem_normalizer_iff_map_conj_eq.mpr (hfix₂ g hg)⟩
  · exact hN₁
  · exact hN₂
  · exact h12S
  · rw [hZS]
    exact normalizer_le_normalizer_characteristic_image S (center S)

/-- Conditional assembly from local involution geometry. This derives the
core alternative and all characteristic-normalizer steps before applying the
original elimination helper. The source must still establish core containment,
self-centralization, matrix geometry and local intersection bounds. -/
theorem centralizer_le_inter_of_involution_geometry
    {G : Type*} [Group G]
    (H S Z V₁ V₂ M₁ M₂ : Subgroup G)
    (hRS : H.pCoreIn 2 ≤ S)
    (hZH : Z ≤ H) (hZC : Z ≤ centralizer (S : Set G))
    (hZexp : ∀ x ∈ Z, x ^ 2 = 1)
    (hself : H ⊓ centralizer (H.pCoreIn 2 : Set G) ≤ H.pCoreIn 2)
    (hV₁ : V₁ ≤ H) (hV₂ : V₂ ≤ H)
    (hcomm₁ : IsMulCommutative V₁) (hcomm₂ : IsMulCommutative V₂)
    (hgeometry : ∀ x ∈ S, x ^ 2 = 1 → x ∉ Z →
      S ⊓ centralizer ({x} : Set G) = V₁ ∨
      S ⊓ centralizer ({x} : Set G) = V₂)
    (hN₁ : normalizer (V₁ : Set G) ≤ M₁)
    (hN₂ : normalizer (V₂ : Set G) ≤ M₂)
    (hinter₁ : H ⊓ M₁ ≤ M₁ ⊓ M₂)
    (hinter₂ : H ⊓ M₂ ≤ M₁ ⊓ M₂)
    (hcenterN : normalizer (Z : Set G) ≤ M₁ ⊓ M₂) :
    H ≤ M₁ ⊓ M₂ := by
  have hbranch := core_alternative_of_involution_geometry H (H.pCoreIn 2) S Z V₁ V₂
    hRS hZH hZC hZexp hself hV₁ hV₂ hcomm₁ hcomm₂ hgeometry
  have hRN : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  apply centralizer_involution_le_inter_generic M₁ M₂ S V₁ V₂ Z _ (H.pCoreIn 2) H
    rfl hRS hbranch
  · intro he _
    rw [he]
    exact omega_center_pCoreIn_normalized H _ rfl
  · intro he _
    exact he ▸ hRN
  · intro he _
    exact he ▸ hRN
  · exact hN₁
  · exact hN₂
  · exact hinter₁
  · exact hinter₂
  · exact hcenterN

end CFSG.Quasithin.Chapter5.Section03
