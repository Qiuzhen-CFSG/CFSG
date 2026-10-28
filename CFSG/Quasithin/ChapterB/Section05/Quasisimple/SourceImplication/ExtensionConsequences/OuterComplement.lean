module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Reduction
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.Representation.BinaryOffender.SectionOffender
public import Theory.Representation.BinaryOffender.RestrictionComparison
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Ratios
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.NormalInvariants


/-!
# The outer complementary fixed-space exception in B.5.1

When V = [V,L] ⊕ C_V(L), the central denominator of the moved section
vanishes. B.1.5 restriction shows that its best offenders generate G.
If its quadratic ratio were one, the equality case would force every
original offender to centralize C_V(L), giving C_V(L) = C_V(G).

Consequently the marked B.4.2 list leaves only the binary symplectic and
symmetric-eight rows. In the former, dimension four and the retained outer
alternative give S₆: the odd symmetric natural actions have ratio one and
the G₂ natural module has dimension six. The source's derived-subgroup
marking identifies the actual L with A₆; the S₈ row already marks A₈.
Thus the literal quotient G/L has order two.

An offender outside L supplements L, so its fixed space on C_V(L) is
exactly C_V(G). The concrete B.3 offender calculations bound the moved
module's fixed codimension below by rank(A) - 1. Additivity on the direct
sum leaves precisely one dimension on the complement. The finite-vector-
space cardinality formula then gives the literal quotient of order two.

The two public theorems retain the actual ambient action and component
restriction. No additional earlier-source parameter is used. The legacy
triple-cover offender clause is unused: that row is eliminated solely by
its equality J(G,U) = L, which would give G = L here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(4)–(5),
printed pp.99 and 102–103; B.1.5, printed pp.69–70; B.3.2, printed pp.83–84.
-/

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.OuterComplement
universe u v w z
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private def trans {H : Type w} [Group H] {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) H W}
    {J X : Type*} [Group J] [AddCommGroup X] [Module (ZMod 2) X]
    {τ : Representation (ZMod 2) J X} (e : ActionEquiv ρ σ) (f : ActionEquiv σ τ) :
    ActionEquiv ρ τ where
  groupEquiv := e.groupEquiv.trans f.groupEquiv
  linearEquiv := e.linearEquiv.trans f.linearEquiv
  intertwines g v := (congrArg f.linearEquiv (e.intertwines g v)).trans
    (f.intertwines (e.groupEquiv g) (e.linearEquiv v))

private theorem central_eq_bot {L : Subgroup G} (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L)) : s.central.toSubmodule = ⊥ := by
  rw [s.central_eq]
  apply bot_unique
  intro v hv
  apply Subtype.ext
  exact (disjoint_iff.mp hc.disjoint).le ⟨v.property, fun g => congrArg Subtype.val (hv g)⟩

private noncomputable def quotientEquiv {L : Subgroup G} (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L)) :
    ActionEquiv s.action s.space.toRepresentation where
  groupEquiv := MulEquiv.refl G
  linearEquiv := s.central.toSubmodule.quotEquivOfEqBot (central_eq_bot s hc)
  intertwines g v := by
    induction v using Submodule.Quotient.induction_on with | _ v => rfl

private theorem best_subrepresentation [FiniteDimensional (ZMod 2) V]
    (W : Subrepresentation ρ) {A : Subgroup G} (hA : IsBestOffender ρ A) :
    IsBestOffender W.toRepresentation A := by
  refine ⟨hA.1, fun B hB => ?_⟩
  have h := hA.restriction_weight_le ρ hB W.toSubmodule
  simpa only [weight, (subrepresentationFixedEquiv ρ W B).finrank_eq,
    (subrepresentationFixedEquiv ρ W A).finrank_eq] using h

private theorem best_linearEquiv {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    {σ : Representation (ZMod 2) G W} (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) {A : Subgroup G}
    (hA : IsBestOffender ρ A) : IsBestOffender σ A := by
  have hd (B : Subgroup G) : fixedCodim ρ B = fixedCodim σ B := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant ρ σ
      (MonoidHom.id G) e he B
  refine ⟨hA.1, fun B hB => ?_⟩
  have h := hA.2 B hB
  have h₁ := fixedCodim_add_finrank ρ A
  have h₂ := fixedCodim_add_finrank σ A
  have h₃ := fixedCodim_add_finrank ρ B
  have h₄ := fixedCodim_add_finrank σ B
  have hf := e.finrank_eq
  rw [hd A] at h₁
  rw [hd B] at h₃
  unfold weight at h ⊢
  omega

private theorem section_generated [FiniteDimensional (ZMod 2) V] {L : Subgroup G}
    (s : MovedSection ρ L) (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L))
    (hj : offenderSubgroup ρ = ⊤) : offenderSubgroup s.action = ⊤ := by
  apply top_unique
  rw [← hj]
  apply iSup_le
  intro A
  apply iSup_le
  rintro ⟨hA, _⟩
  have h := best_subrepresentation s.space hA
  let q := quotientEquiv s hc
  let he : ActionEquiv s.space.toRepresentation s.action :=
    { groupEquiv := MulEquiv.refl G
      linearEquiv := q.linearEquiv.symm
      intertwines g v := by
        apply q.linearEquiv.injective
        simpa only [q, quotientEquiv, MulEquiv.refl_apply, LinearEquiv.apply_symm_apply] using (q.intertwines g (q.linearEquiv.symm v)).symm }
  have ha := best_linearEquiv (σ := s.action) he.linearEquiv (fun g v => he.intertwines g v) h
  exact le_iSup_of_le A (le_iSup_of_le ⟨ha, le_top⟩ le_rfl)

private theorem fixed_by_generators (C : Submodule (ZMod 2) V)
    (hj : offenderSubgroup ρ = ⊤)
    (hC : ∀ A, IsBestOffender ρ A → C ≤ fixedSpace ρ A) : C ≤ ρ.invariants := by
  have ht : offenderSubgroup ρ ≤ subspaceKernel ρ C ⊤ := by
    apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, _⟩ a ha
    exact ⟨Subgroup.mem_top _, fun v hv => hC A hA hv ⟨a, ha⟩⟩
  rw [hj] at ht
  intro v hv g
  exact (ht (Subgroup.mem_top g)).2 v hv

private theorem invariant_le_fixed (L : Subgroup G) : ρ.invariants ≤ fixedSpace ρ L :=
  fun _ h g => h g

private theorem fixed_complement_eq_of_supplement {L A : Subgroup G} [L.Normal]
    (s : MovedSection ρ L) (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L))
    (ha : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤) :
    fixedSpace ρ L ≤ fixedSpace ρ A := by
  intro v hv a
  obtain ⟨u, hu, c, hca, huc⟩ := Submodule.mem_sup.mp (ha ▸ Submodule.mem_top (x := v))
  have hd : ρ a v - v ∈ s.space.toSubmodule := by
    have hfix : ρ a c = c := hca a
    rw [← huc, map_add, hfix]
    simpa only [add_sub_add_right_eq_sub] using
      s.space.toSubmodule.sub_mem (s.space.apply_mem_toSubmodule a hu) hu
  have hf : ρ a v - v ∈ fixedSpace ρ L :=
    (fixedSubrepresentationOfNormal ρ L).toSubmodule.sub_mem
      ((fixedSubrepresentationOfNormal ρ L).apply_mem_toSubmodule a hv) hv
  exact sub_eq_zero.mp ((disjoint_iff.mp hc.disjoint).le ⟨hd, hf⟩)

private theorem ratio_ne_one [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} [L.Normal] (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L))
    (hn : ¬ IsCompl s.space.toSubmodule ρ.invariants)
    (hj : offenderSubgroup ρ = ⊤) : quadraticRatio s.action ≠ 1 := by
  intro hq
  have hC : fixedSpace ρ L ≤ ρ.invariants := by
    apply fixed_by_generators _ hj
    intro A hA
    have hU := best_subrepresentation s.space hA
    let q := quotientEquiv s hc
    let e : ActionEquiv s.space.toRepresentation s.action :=
      { groupEquiv := MulEquiv.refl G
        linearEquiv := q.linearEquiv.symm
        intertwines g v := by
          apply q.linearEquiv.injective
          simpa only [q, quotientEquiv, MulEquiv.refl_apply, LinearEquiv.apply_symm_apply] using (q.intertwines g (q.linearEquiv.symm v)).symm }
    have hS := best_linearEquiv (σ := s.action) e.linearEquiv (fun g v => e.intertwines g v) hU
    have he := ((hS.isOffender _).best_and_codim_eq_of_quadraticRatio_eq_one _ hq).2
    have hd : fixedCodim s.space.toRepresentation A = fixedCodim s.action A := by
      simpa only [Subgroup.map_id] using fixedCodim_map_equivariant _ _
        (MonoidHom.id G) e.linearEquiv (fun g v => e.intertwines g v) A
    have hle := fixedCodim_subrepresentation_le ρ s.space A
    have ha := (hA.isOffender _).2
    have hs := (fixedCodim_subrepresentation_eq_iff ρ s.space A).mp
      (by rw [hd, he]; omega)
    exact fixed_complement_eq_of_supplement s hc hs
  have heq := le_antisymm hC (invariant_le_fixed L)
  exact hn (heq ▸ hc)


variable {H : Type w} [Group H] {W : Type z} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) H W}

private noncomputable def fullAction {L : Subgroup G} {M : Subgroup H}
    (e : MarkedActionEquiv ρ ⊤ L σ M) : ActionEquiv ρ σ where
  groupEquiv := Subgroup.topEquiv.symm.trans e.action.groupEquiv
  linearEquiv := e.action.linearEquiv
  intertwines g v := e.action.intertwines ⟨g, mem_top g⟩ v

private theorem marked_map {L : Subgroup G} {M : Subgroup H}
    (e : MarkedActionEquiv ρ ⊤ L σ M) :
    L.map (fullAction e).groupEquiv.toMonoidHom = M := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    have h := e.compatible ⟨g, hg⟩
    change e.action.groupEquiv ⟨g, mem_top g⟩ ∈ M
    rw [h]
    exact (e.subgroupEquiv ⟨g, hg⟩).property
  · intro g hg
    obtain ⟨l, hl⟩ := e.subgroupEquiv.surjective ⟨g, hg⟩
    refine ⟨l, l.property, ?_⟩
    exact (e.compatible l).trans (congrArg Subtype.val hl)

private theorem marked_commutator {L : Subgroup G}
    (e : MarkedActionEquiv ρ ⊤ L σ (commutator H)) : L = commutator G := by
  apply Subgroup.map_injective (f := (fullAction e).groupEquiv.toMonoidHom)
    (fullAction e).groupEquiv.injective
  rw [marked_map, map_commutator_eq,
    MonoidHom.range_eq_top.mpr (fullAction e).groupEquiv.surjective, commutator_def]

private theorem map_commutator_natural {n : ℕ} (hn : 5 ≤ n) {L : Subgroup G}
    (hL : L = commutator G) (e : ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin n))) :
    L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin n) := by
  rw [hL, map_commutator_eq, MonoidHom.range_eq_top.mpr e.groupEquiv.surjective,
    ← commutator_def]
  exact alternatingGroup.commutator_perm_eq (by simpa using hn)

private theorem odd_natural_ratio [Finite G] [FiniteDimensional (ZMod 2) V]
    {n : ℕ} (hn : n = 5 ∨ n = 7)
    (e : ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin n)))
    (hff : IsFFModule ρ) : quadraticRatio ρ = 1 := by
  apply quadraticRatio_eq_one_of_no_strong ρ hff
  intro A hA
  have ha := (show IsOffender ρ A from ⟨hA.1, hA.2.le⟩).map_equivariant
    ρ _ e.groupEquiv.toMonoidHom e.groupEquiv.injective e.linearEquiv e.intertwines
  apply ChapterB.Offenders.Odd.not_isStrongOffender_natural hn (A.map e.groupEquiv.toMonoidHom)
  refine ⟨ha.1, ?_⟩
  rw [← fixedCodim_map_equivariant ρ _ _ e.linearEquiv e.intertwines,
    rank_map_injective _ e.groupEquiv.injective]
  exact hA.2

private theorem natural_dimension {n : ℕ} (hn : 5 ≤ n) (hN : n ≤ 8) :
    Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin n)) =
      if n = 5 ∨ n = 6 then 4 else 6 := by
  interval_cases n <;>
    first
    | simpa using BinaryPermutation.finrank_natural_odd (Fin _) (by decide)
    | simpa using BinaryPermutation.finrank_natural_even (Fin _) (by decide)

private theorem four_dimensional_outer [Finite G] [FiniteDimensional (ZMod 2) V]
    (ho : OuterNaturalAction ρ) (hd : Module.finrank (ZMod 2) V = 4)
    (hff : IsFFModule ρ) (hq : quadraticRatio ρ ≠ 1) : IsSymmetricNatural ρ 6 := by
  rcases ho with ho | ho
  · obtain ⟨n, hn, hN, ⟨e⟩⟩ := ho
    have he := e.linearEquiv.finrank_eq
    rw [natural_dimension hn hN, hd] at he
    have hn56 : n = 5 ∨ n = 6 := by split_ifs at he with h <;> omega
    rcases hn56 with rfl | rfl
    · exact False.elim (hq (odd_natural_ratio (Or.inl rfl) e hff))
    · exact ⟨e⟩
  · obtain ⟨e⟩ := ho
    have he := e.linearEquiv.finrank_eq
    rw [hd, Atlas.G2.Natural.finrank_space] at he
    omega

private theorem marked_natural [Finite G] {K : CFSG.Quasithin.GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hi : IrreducibleAlternative L s)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L))
    (hn : ¬ IsCompl s.space.toSubmodule ρ.invariants) :
    ∃ n, (n = 6 ∨ n = 8) ∧
      ∃ e : ActionEquiv s.action (BinaryPermutation.naturalRepresentation (Fin n)),
        L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin n) := by
  let := h.finite_module
  let := h.quasisimple
  let := component_normal_of_fitting_eq_sup_center L h.fitting
  have hL : L ≠ ⊤ := by
    intro he
    subst L
    exact hn (by simpa only [fixedSpace_top] using hc)
  have hj := section_generated s hc h.generated
  have hq := ratio_ne_one s hc hn h.generated
  have hs := hi.source
  rw [hj] at hs
  have hcases :
      Nonempty (MarkedActionEquiv s.action ⊤ L (symplecticNatural (k := ZMod 2) 2)
        (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) ∨
      Nonempty (MarkedActionEquiv s.action ⊤ L (BinaryPermutation.naturalRepresentation (Fin 8))
        (alternatingGroup (Fin 8))) := by
    cases hs with
    | symplecticTwo e _ => exact Or.inl ⟨e⟩
    | symmetricEight _ e _ => exact Or.inr ⟨e⟩
    | linearTwo _ he _ _ _ => exact False.elim (hL he.symm)
    | linearThree _ he _ _ => exact False.elim (hL he.symm)
    | symplectic _ _ he _ _ => exact False.elim (hL he.symm)
    | g2 _ _ he _ _ _ => exact False.elim (hL he.symm)
    | g2Two _ _ he => exact False.elim (hq he)
    | symmetric _ _ _ _ he => exact False.elim (hq he)
    | alternatingSix he _ _ _ => exact False.elim (hL he.symm)
    | alternatingSeven _ he _ _ _ _ => exact False.elim (hL he)
    | tripleSix he _ _ => exact False.elim (hL he.symm)
    | binaryLinear _ _ he _ _ => exact False.elim (hL he.symm)
    | orthogonalSix _ he _ _ _ => exact False.elim (hL he)
    | exteriorFive _ he _ _ _ _ => exact False.elim (hL he)
  rcases hcases with he | he
  · obtain ⟨e⟩ := he
    have he := (fullAction e).linearEquiv.finrank_eq
    have hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4 := by
      simpa using he
    have hff : IsFFModule s.action := by
      obtain ⟨A, hA⟩ := source_isFF h
      have hB := hA.exists_bestOffender ρ
      obtain ⟨B, _, hB⟩ := hB
      have hu := best_subrepresentation s.space hB
      let q := quotientEquiv s hc
      have ht : ∀ g v, q.linearEquiv.symm (s.space.toRepresentation g v) =
          (MovedSection.action ρ s) g (q.linearEquiv.symm v) := by
        intro g v
        apply q.linearEquiv.injective
        simpa only [q, quotientEquiv, MulEquiv.refl_apply, LinearEquiv.apply_symm_apply]
          using (q.intertwines g (q.linearEquiv.symm v)).symm
      exact ⟨B, (best_linearEquiv q.linearEquiv.symm ht hu).isOffender _⟩
    obtain ⟨en⟩ := four_dimensional_outer (hi.extension.resolve_left hL).2 hd hff hq
    exact ⟨6, Or.inl rfl, en, map_commutator_natural (by decide) (marked_commutator e) en⟩
  · obtain ⟨e⟩ := he
    exact ⟨8, Or.inr rfl, fullAction e, marked_map e⟩


private theorem natural_rank_bound {n : ℕ} (hn : n = 6 ∨ n = 8)
    {A : Subgroup (Equiv.Perm (Fin n))} (hA : IsElementaryTwo A) :
    rank A ≤ fixedCodim (BinaryPermutation.naturalRepresentation (Fin n)) A + 1 := by
  by_cases hs : fixedCodim (BinaryPermutation.naturalRepresentation (Fin n)) A < rank A
  · rcases hn with rfl | rfl
    · have he := (ChapterB.Offenders.Six.isStrongOffender_natural_iff A).mp ⟨hA, hs⟩
      rw [he.rank_eq, he.fixedCodim_eq, ChapterB.Offenders.Six.rank_D,
        ChapterB.Offenders.Six.fixedCodim_D.2.2.2]
    · have he := (ChapterB.Offenders.Eight.isStrongOffender_natural_iff A).mp ⟨hA, hs⟩
      rw [he.rank_eq, he.fixedCodim_eq, ChapterB.Offenders.Eight.rank_D,
        ChapterB.Offenders.Eight.fixedCodim_D.2.2.2]
  · omega

private theorem rank_bound_of_natural [FiniteDimensional (ZMod 2) V]
    {n : ℕ} (hn : n = 6 ∨ n = 8)
    (e : ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin n)))
    {A : Subgroup G} (hA : IsElementaryTwo A) : rank A ≤ fixedCodim ρ A + 1 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.2
  have ha : IsElementaryTwo (A.map e.groupEquiv.toMonoidHom) := by
    refine ⟨?_, IsElementaryAbelian.map _⟩
    intro hb
    apply hA.1
    apply Subgroup.map_injective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.injective
    simpa only [Subgroup.map_bot] using hb
  have hb := natural_rank_bound hn ha
  rwa [rank_map_injective _ e.groupEquiv.injective,
    ← fixedCodim_map_equivariant ρ _ _ e.linearEquiv e.intertwines] at hb

private theorem fixedCodim_complement [FiniteDimensional (ZMod 2) V]
    (U C : Subrepresentation ρ) (hc : IsCompl U.toSubmodule C.toSubmodule)
    (A : Subgroup G) :
    fixedCodim U.toRepresentation A + fixedCodim C.toRepresentation A = fixedCodim ρ A := by
  let e := U.toSubmodule.prodEquivOfIsCompl C.toSubmodule hc
  have he : ∀ g v, e ((U.toRepresentation.prod C.toRepresentation) g v) = ρ g (e v) := by
    intro g v
    change ρ g v.1 + ρ g v.2 = ρ g (v.1 + v.2)
    exact (map_add _ _ _).symm
  have h := fixedCodim_map_equivariant (U.toRepresentation.prod C.toRepresentation) ρ
    (MonoidHom.id G) e he A
  simpa only [Subgroup.map_id, fixedCodim_prod] using h

private theorem index_two_of_marking {n : ℕ} (hn : 5 ≤ n) {L : Subgroup G}
    (e : ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin n)))
    (hm : L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin n)) : L.index = 2 := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [← Subgroup.index_map_equiv L e.groupEquiv]
  change (L.map e.groupEquiv.toMonoidHom).index = 2
  rw [hm]
  exact alternatingGroup.index_eq_two

private theorem supplement_of_index_two {L A : Subgroup G} (hL : L.index = 2) (hA : ¬ A ≤ L) :
    L ⊔ A = ⊤ := by
  obtain ⟨a, ha, hal⟩ := SetLike.not_le_iff_exists.mp hA
  apply top_unique
  intro g _
  by_cases hg : g ∈ L
  · exact (show L ≤ L ⊔ A from le_sup_left) hg
  · have hga : g * a⁻¹ ∈ L := (Subgroup.mul_mem_iff_of_index_two hL).mpr
      (iff_of_false hg (fun h => hal (by simpa using L.inv_mem h)))
    have h := (L ⊔ A).mul_mem ((show L ≤ L ⊔ A from le_sup_left) hga) ((show A ≤ L ⊔ A from le_sup_right) ha)
    simpa using h

private theorem exists_outer_offender {L : Subgroup G} (hj : offenderSubgroup ρ = ⊤)
    (hL : L ≠ ⊤) : ∃ A, IsBestOffender ρ A ∧ ¬ A ≤ L := by
  by_contra! h
  apply hL
  apply top_unique
  rw [← hj]
  exact iSup_le fun A => iSup_le fun hA => h A hA.1

private theorem fixed_restriction_eq {L A : Subgroup G} [L.Normal] (ha : L ⊔ A = ⊤) :
    fixedSpace (fixedSubrepresentationOfNormal ρ L).toRepresentation A =
      ρ.invariants.comap (fixedSpace ρ L).subtype := by
  have ht : L ⊔ A ≤ subspaceKernel ρ (fixedSpace ρ L ⊓ fixedSpace ρ A) ⊤ := by
    apply sup_le
    · intro g hg
      exact ⟨mem_top _, fun v hv => hv.1 ⟨g, hg⟩⟩
    · intro g hg
      exact ⟨mem_top _, fun v hv => hv.2 ⟨g, hg⟩⟩
  rw [ha] at ht
  ext v
  constructor
  · intro hv g
    exact (ht (mem_top g)).2 v ⟨v.property, fun a => congrArg Subtype.val (hv a)⟩
  · intro hv a
    exact Subtype.ext (hv a)

private theorem fixed_quotient_card [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} [L.Normal] (s : MovedSection ρ L)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L))
    (hn : ¬ IsCompl s.space.toSubmodule ρ.invariants)
    (hj : offenderSubgroup ρ = ⊤) {n : ℕ} (hN : n = 6 ∨ n = 8)
    (e : ActionEquiv s.action (BinaryPermutation.naturalRepresentation (Fin n)))
    (hm : L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin n)) :
    Nat.card ((fixedSpace ρ L) ⧸ ρ.invariants.comap (fixedSpace ρ L).subtype) = 2 := by
  have hL : L ≠ ⊤ := by
    intro he
    subst L
    exact hn (by simpa only [fixedSpace_top] using hc)
  obtain ⟨A, hA, hal⟩ := exists_outer_offender hj hL
  have hindex := index_two_of_marking (by rcases hN with rfl | rfl <;> decide) e hm
  have hsup := supplement_of_index_two hindex hal
  let C := fixedSubrepresentationOfNormal ρ L
  have hd := fixedCodim_complement s.space C hc A
  have hbound := rank_bound_of_natural hN e hA.1
  let hq := quotientEquiv s hc
  have hdim : fixedCodim s.action A = fixedCodim s.space.toRepresentation A := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant _ _ (MonoidHom.id G)
      hq.linearEquiv (fun g v => hq.intertwines g v) A
  rw [hdim] at hbound
  have hav := (hA.isOffender _).2
  have hle : fixedCodim C.toRepresentation A ≤ 1 := by omega
  have hnzero : fixedCodim C.toRepresentation A ≠ 0 := by
    intro hz
    have ht := (fixedCodim_eq_zero_iff C.toRepresentation A).mp hz
    have hinv : fixedSpace ρ L ≤ ρ.invariants := by
      intro v hv
      have hx : (⟨v, hv⟩ : C.toSubmodule) ∈ fixedSpace C.toRepresentation A := by
        rw [ht]; trivial
      rw [fixed_restriction_eq hsup] at hx
      exact hx
    exact hn ((le_antisymm hinv (invariant_le_fixed L)) ▸ hc)
  have hd1 : fixedCodim C.toRepresentation A = 1 := by omega
  change Module.finrank (ZMod 2) (_ ⧸ fixedSpace C.toRepresentation A) = 1 at hd1
  rw [fixed_restriction_eq hsup] at hd1
  change Module.finrank (ZMod 2) ((fixedSpace ρ L) ⧸
    ρ.invariants.comap (fixedSpace ρ L).subtype) = 1 at hd1
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd1]
  rfl


private noncomputable def alternatingRestriction {n : ℕ} {L : Subgroup G}
    (e : ActionEquiv ρ (BinaryPermutation.naturalRepresentation (Fin n)))
    (hm : L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin n)) :
    ActionEquiv (ρ.comp L.subtype) (alternatingNatural n) where
  groupEquiv := (e.groupEquiv.subgroupMap L).trans (MulEquiv.subgroupCongr hm)
  linearEquiv := e.linearEquiv
  intertwines g v := by
    exact e.intertwines g v

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences.OuterComplement

namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
universe u v
variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- The exceptional outer action identifies the actual component with the
alternating subgroup, and its actual quotient has order two. -/
public theorem outer_complement_action [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hi : IrreducibleAlternative L s)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L))
    (hn : ¬ IsCompl s.space.toSubmodule ρ.invariants) :
    ∃ n, (n = 6 ∨ n = 8) ∧
      ∃ e : ActionEquiv s.action (BinaryPermutation.naturalRepresentation (Fin n)),
        L.map e.groupEquiv.toMonoidHom = alternatingGroup (Fin n) ∧
          Nat.card (G ⧸ L) = 2 := by
  obtain ⟨n, hN, e, hm⟩ := OuterComplement.marked_natural h s hi hc hn
  exact ⟨n, hN, e, hm,
    OuterComplement.index_two_of_marking (by rcases hN with rfl | rfl <;> decide) e hm⟩

/-- B.5.1(4b), together with the actual component action required in (5).
There are no additional earlier-source parameters. -/
public theorem outer_complement [Finite G] {K : CFSG.Quasithin.GroupClass.{u}}
    {L : Subgroup G} (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hi : IrreducibleAlternative L s)
    (hc : IsCompl s.space.toSubmodule (fixedSpace ρ L))
    (hn : ¬ IsCompl s.space.toSubmodule ρ.invariants) :
    (IsSymmetricNatural s.space.toRepresentation 6 ∨
      IsSymmetricNatural s.space.toRepresentation 8) ∧
    Nat.card ((fixedSpace ρ L) ⧸ ρ.invariants.comap (fixedSpace ρ L).subtype) = 2 ∧
    (IsAlternatingNatural (s.action.comp L.subtype) 6 ∨
      IsAlternatingNatural (s.action.comp L.subtype) 8) := by
  let := h.finite_module
  let := h.quasisimple
  let := component_normal_of_fitting_eq_sup_center L h.fitting
  obtain ⟨n, hN, e, hm, _⟩ := outer_complement_action h s hi hc hn
  have hcard := OuterComplement.fixed_quotient_card s hc hn h.generated hN e hm
  have hnature : IsSymmetricNatural s.space.toRepresentation n :=
    ⟨OuterComplement.trans (actionSymm (OuterComplement.quotientEquiv s hc)) e⟩
  have halt : IsAlternatingNatural (s.action.comp L.subtype) n :=
    ⟨OuterComplement.alternatingRestriction e hm⟩
  rcases hN with rfl | rfl
  · exact ⟨Or.inl hnature, hcard, Or.inl halt⟩
  · exact ⟨Or.inr hnature, hcard, Or.inr halt⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
