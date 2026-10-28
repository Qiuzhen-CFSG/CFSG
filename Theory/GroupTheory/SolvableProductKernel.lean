module
public import Theory.GroupTheory.NormalizerProductKernel
public import Theory.GroupTheory.SolvableMinimalNormal
public import Theory.GroupTheory.MinimalNormalPCore
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupAction.ElementaryTwoMovingPrimeLine

/-!
# Odd chief sections above a maximal factorization kernel

The maximal kernel in a solvable group has a nontrivial odd elementary
minimal normal section. If proper Sylow overgroups have the original
normalizer product, that section supplements the original Sylow image
and is self-centralizing. A nontrivial elementary actor then moves it
outside either noncovering factor. The explicit coprime-action calculation
selects an invariant prime-order line and a fixing actor hyperplane.

Source: GLS, Number 2, G.26.18(a), printed pp.152–153. The proper-overgroup
factorization remains an explicit induction premise, used only in
`sup_sylow_eq_top`; no source factorization is assumed by the other lemmas.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A nontrivial solvable two-core-free group has an odd elementary chief subgroup. -/
theorem exists_odd_elementary_minimal_normal [Nontrivial G] [Group.IsSolvable G]
    (hcore : pCore 2 G = ⊥) :
    ∃ (r : ℕ) (Y : Subgroup G), r.Prime ∧ Odd r ∧ Y.Normal ∧ Y ≠ ⊥ ∧
      IsElementaryAbelian r Y ∧
      ∀ D : Subgroup G, D.Normal → D ≤ Y → D = ⊥ ∨ D = Y := by
  obtain ⟨U,r,hU,hUne,_,hr,_,hUp,_⟩ :=
    (⊤ : Subgroup G).exists_minimal_normal_abelian_pGroup (by exact top_ne_bot)
  let : Fact r.Prime := ⟨hr⟩
  have hUcore : U ≤ pCore r G := le_sSup ⟨hU,hUp⟩
  have hr2 : r ≠ 2 := by
    intro he
    rw [he,hcore] at hUcore
    exact hUne (bot_unique hUcore)
  have hne : pCore r G ≠ ⊥ := fun he => hUne (bot_unique (hUcore.trans he.le))
  obtain ⟨Y,hYn,hYne,_,hYe,hmin⟩ := exists_minimal_normal_le_pCore hne
  exact ⟨r,Y,hr,(Nat.odd_iff.mpr (hr.eq_two_or_odd.resolve_left hr2)),hYn,hYne,hYe,hmin⟩

omit [Finite G] in
/-- The induction premise is used only to make the selected normal section
supplement the image of the original Sylow subgroup. -/
theorem IsMaximalProductKernel.sup_sylow_eq_top (P U V S : Subgroup G)
    (h : IsMaximalProductKernel P U V S) [S.Normal]
    (hproper : ∀ D : Subgroup G, D.Normal → D ⊔ P ≠ ⊤ → NormalizerProductOn P U V D)
    (Y : Subgroup (G ⧸ S)) [Y.Normal] (hne : Y ≠ ⊥) :
    Y ⊔ P.map (QuotientGroup.mk' S) = ⊤ := by
  let q := QuotientGroup.mk' S
  let D := Y.comap q
  have hSD : S ≤ D := by
    intro s hs
    change q s ∈ Y
    rw [show q s = 1 from (QuotientGroup.eq_one_iff s).mpr hs]
    exact Y.one_mem
  have hgen : D ⊔ P = ⊤ := by
    by_contra hc
    have he : D = S := le_antisymm (h.maximal D inferInstance (hproper D inferInstance hc) hSD) hSD
    apply hne
    have hm := congrArg (map q) he
    simpa only [D,q,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S),
      QuotientGroup.map_mk'_self] using hm
  have hm := congrArg (map q) hgen
  simpa only [D,q,Subgroup.map_sup,map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective S),
    map_top_of_surjective _ (QuotientGroup.mk'_surjective S)] using hm

omit [Finite G] in
/-- An abelian normal supplement to a p-group is self-centralizing when the
ambient p-core is trivial. -/
theorem centralizer_le_of_abelian_supplement_coreFree {p : ℕ}
    (Y P : Subgroup G) [Y.Normal] [IsMulCommutative Y]
    (hP : IsPGroup p P) (hgen : Y ⊔ P = ⊤) (hcore : pCore p G = ⊥) :
    centralizer (Y : Set G) ≤ Y := by
  let C := P ⊓ centralizer (Y : Set G)
  have hPC : P ≤ normalizer (C : Set G) :=
    (le_inf P.le_normalizer (show P ≤ normalizer (centralizer (Y : Set G) : Set G) from
      le_normalizer_of_normal)).trans inf_normalizer_le_normalizer_inf
  have hYC : Y ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (Y : Set G) from inf_le_right)).trans
      (centralizer_le_normalizer _)
  have hCn : C.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hYC hPC))
  have hC : C = ⊥ := bot_unique
    ((show C ≤ pCore p G from le_sSup ⟨hCn,hP.to_le inf_le_left⟩).trans hcore.le)
  have hYY : Y ≤ centralizer (Y : Set G) := by
    intro y hy z hz
    exact congrArg Subtype.val (mul_comm (⟨z,hz⟩ : Y) ⟨y,hy⟩)
  intro x hx
  obtain ⟨y,hy,a,ha,rfl⟩ := mem_sup_of_normal_left.mp
    (show x ∈ Y ⊔ P by rw [hgen]; trivial)
  have haC : a ∈ centralizer (Y : Set G) := by
    have hh := (centralizer (Y : Set G)).mul_mem
      ((centralizer (Y : Set G)).inv_mem (hYY hy)) hx
    simpa only [inv_mul_cancel_left] using hh
  have ha1 : a = 1 := mem_bot.mp (hC ▸ (show a ∈ C from ⟨ha,haC⟩))
  simpa only [ha1,mul_one] using hy

/-- The maximal kernel produces the odd chief section and the two literal
noncoverage conclusions. The stronger supplement and self-centralizer clauses
are separately obtained from the proper-overgroup induction premise. -/
theorem IsMaximalProductKernel.odd_chief [Group.IsSolvable G]
    (P : Sylow 2 G) (U V S : Subgroup G)
    (h : IsMaximalProductKernel (P : Subgroup G) U V S) [S.Normal]
    (hPU : (P : Subgroup G) ≤ U) (hPV : (P : Subgroup G) ≤ V)
    (hfail : ¬ NormalizerProductOn (P : Subgroup G) U V ⊤) :
    ∃ (r : ℕ) (Y : Subgroup (G ⧸ S)), r.Prime ∧ Odd r ∧ Y.Normal ∧ Y ≠ ⊥ ∧
      IsElementaryAbelian r Y ∧
      (∀ D : Subgroup (G ⧸ S), D.Normal → D ≤ Y → D = ⊥ ∨ D = Y) ∧
      ¬ Y ≤ U.map (QuotientGroup.mk' S) ∧ ¬ Y ≤ V.map (QuotientGroup.mk' S) := by
  let : Nontrivial (G ⧸ S) := QuotientGroup.nontrivial_iff.mpr (h.ne_top _ _ _ _ hfail)
  obtain ⟨r,Y,hr,ho,hYn,hYne,hYe,hmin⟩ :=
    exists_odd_elementary_minimal_normal (h.pCore_quotient_eq_bot P U V S)
  let := hYn
  exact ⟨r,Y,hr,ho,hYn,hYne,hYe,hmin,h.not_covering_left _ _ _ _ hPU Y hYne,
    h.not_covering_right _ _ _ _ hPV Y hYne⟩

omit [Finite G] in
/-- A nontrivial elementary actor moves an odd chief subgroup outside every
proper overgroup of the Sylow supplement. -/
theorem commutator_not_le_of_odd_chief (Y P A U : Subgroup G) [Y.Normal]
    {r : ℕ} [Fact r.Prime] [IsElementaryAbelian r Y] (ho : Odd r)
    [IsElementaryAbelian 2 A] (hAP : A ≤ P) (hAne : A ≠ ⊥)
    (hgen : Y ⊔ P = ⊤) (hcore : pCore 2 G = ⊥) (hP : IsPGroup 2 P)
    (hmin : ∀ D : Subgroup G, D.Normal → D ≤ Y → D = ⊥ ∨ D = Y)
    (hPU : P ≤ U) (hYU : ¬ Y ≤ U) : ¬ ⁅Y,A⁆ ≤ U := by
  have hself := centralizer_le_of_abelian_supplement_coreFree Y P hP hgen hcore
  have hmove : ⁅Y,A⁆ ≠ ⊥ := by
    intro he
    have hAY : A ≤ Y :=
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)).trans hself
    have hd := (hP.to_le hAP).disjoint_of_coprime
      (IsElementaryAbelian.isPGroup r Y) (Nat.coprime_two_left.mpr ho)
    exact hAne (bot_unique ((le_inf le_rfl hAY).trans hd.eq_bot.le))
  let D := conjugateSpanBy ⁅Y,A⁆ P
  have hDY : D ≤ Y := conjugateSpanBy_le (commutator_le_left Y A) le_normalizer_of_normal
  have hYY : Y ≤ centralizer (Y : Set G) := by
    intro y hy z hz
    exact congrArg Subtype.val (mul_comm (⟨z,hz⟩ : Y) ⟨y,hy⟩)
  have hDn : D.Normal := normalizer_eq_top_iff.mp (top_unique (hgen ▸ sup_le
    ((hYY.trans (centralizer_le hDY)).trans (centralizer_le_normalizer _))
    (le_normalizer_conjugateSpanBy ⁅Y,A⁆ P)))
  have hDeq : D = Y := (hmin D hDn hDY).resolve_left
    (fun he => hmove (bot_unique ((le_conjugateSpanBy ⁅Y,A⁆ P).trans he.le)))
  intro hc
  exact hYU (hDeq ▸ (show D ≤ U from conjugateSpanBy_le hc (hPU.trans U.le_normalizer)))

/-- The selected odd line retains the literal action, the fixing hyperplane,
and failure of coverage by U; no irreducible-module choice is postulated. -/
theorem exists_odd_line_of_chief_noncoverage (Y P A U : Subgroup G) [Y.Normal]
    {r : ℕ} [Fact r.Prime] [IsElementaryAbelian r Y] (ho : Odd r)
    (hYne : Y ≠ ⊥) [IsElementaryAbelian 2 A] (hAP : A ≤ P) (hAne : A ≠ ⊥)
    (hgen : Y ⊔ P = ⊤) (hcore : pCore 2 G = ⊥) (hP : IsPGroup 2 P)
    (hmin : ∀ D : Subgroup G, D.Normal → D ≤ Y → D = ⊥ ∨ D = Y)
    (hPU : P ≤ U) (hYU : ¬ Y ≤ U) :
    ∃ (B : Subgroup A) (D : Subgroup G), B.index = 2 ∧ D ≤ Y ∧ Nat.card D = r ∧
      A ≤ normalizer (D : Set G) ∧ ⁅D,A⁆ = D ∧
      D ≤ centralizer (B.map A.subtype : Set G) ∧ ¬ D ≤ U := by
  let : Nontrivial Y := (nontrivial_iff_ne_bot Y).mpr hYne
  obtain ⟨B,D,hB,hDY,hcard,hAD,hcomm,hcent,hout⟩ :=
    GroupAction.exists_prime_subgroup_outside_of_elementary_action
      (show r ≠ 2 from fun he => by have := Nat.odd_iff.mp ho; omega) Y A U
      (IsElementaryAbelian.isPGroup r Y) (IsElementaryAbelian.exponent_eq_prime (p := r) (G := Y))
      (show A ≤ normalizer (Y : Set G) from le_normalizer_of_normal)
      (commutator_not_le_of_odd_chief Y P A U ho hAP hAne hgen hcore hP hmin hPU hYU)
  exact ⟨B,D,hB,hDY.trans (commutator_le_left Y A),hcard,hAD,hcomm,hcent,hout⟩
end Theory.GroupTheory
