module

public import Theory.GroupTheory.SymmetricFourModelCoreData
public import Theory.GroupTheory.SmallElementaryCoreOvergroupBound

/-!
# Normalizer rigidity for the symmetric-four models

Let P be isomorphic to S4 or C2 × S4, and let Q be its ambient two-core.
If N = N_G(Q) is solvable, Q is self-centralizing in G, and a Sylow
two-subgroup of N lies in P, then N = P. In particular, normality of P
in N is not an assumption.

Normality of the internal core gives P ≤ N. The model computation makes
Q elementary abelian of order four or eight, with |P| = 6|Q|. Pulling the
given Sylow subgroup back along P → N shows that its order is 2|Q|.
Apply the small elementary-core overgroup bound inside N to obtain
|N| ≤ 6|Q| = |P|; the containment then gives equality. The imported
overgroup bound uses conjugation on Q and its small automorphism group.

This supplies the normalizer argument in Stellmacher Section 11,
`refs/latex/stellmacher-n-group.tex`, lines 2076–2081, independently of the
graph-theoretic hypotheses used by its consumers.
-/

private theorem le_core_normalizer {G : Type*} [Group G] (P : Subgroup G) :
    P ≤ Subgroup.normalizer ((pCore 2 P).map P.subtype : Set G) := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 P))).mp
  change (Subgroup.comap P.subtype ((pCore 2 P).map P.subtype)).Normal
  rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
  infer_instance

public theorem normalizer_twoCore_eq_of_symmetric_four_model
    {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    (hsolv : Group.IsSolvable (Subgroup.normalizer
      ((pCore 2 P).map P.subtype : Set G)))
    (hcent : Subgroup.centralizer ((pCore 2 P).map P.subtype : Set G) ≤
      (pCore 2 P).map P.subtype)
    (hSylow : ∃ T : Sylow 2 (Subgroup.normalizer
      ((pCore 2 P).map P.subtype : Set G)),
      (T : Subgroup _).map (Subgroup.normalizer
        ((pCore 2 P).map P.subtype : Set G)).subtype ≤ P)
    (hModel : Nonempty (P ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (P ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) :
    Subgroup.normalizer ((pCore 2 P).map P.subtype : Set G) = P := by
  let Q := (pCore 2 P).map P.subtype
  let N := Subgroup.normalizer (Q : Set G)
  have hPN : P ≤ N := le_core_normalizer P
  have hQN : Q ≤ N := Subgroup.le_normalizer
  let coreInNormalizer := Q.subgroupOf N
  let : coreInNormalizer.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQN).mpr le_rfl
  let : Group.IsSolvable N := hsolv
  obtain ⟨hElementary, hCards⟩ := symmetric_four_model_twoCore_data hModel
  let : IsElementaryAbelian 2 (pCore 2 P) := hElementary
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 2 coreInNormalizer := IsElementaryAbelian.subgroupOf hQN
  have hCoreCard : Nat.card coreInNormalizer = Nat.card (pCore 2 P) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQN).toEquiv]
    exact Subgroup.card_subtype P (pCore 2 P)
  have hCoreCent : Subgroup.centralizer (coreInNormalizer : Set N) ≤ coreInNormalizer := by
    intro element hElement
    apply hcent
    rw [Subgroup.mem_centralizer_iff]
    intro coreElement hCoreElement
    have hComm := Subgroup.mem_centralizer_iff.mp hElement
      ⟨coreElement, hQN hCoreElement⟩ hCoreElement
    exact congrArg Subtype.val hComm
  obtain ⟨T, hTP⟩ := hSylow
  let inclusion : P →* N := Subgroup.inclusion hPN
  have hinj : Function.Injective inclusion := Subgroup.inclusion_injective hPN
  have hTrange : (T : Subgroup N) ≤ inclusion.range := by
    intro element hElement
    have hElementP : (element : G) ∈ P :=
      hTP (Subgroup.mem_map_of_mem N.subtype hElement)
    exact ⟨⟨element, hElementP⟩, Subtype.ext rfl⟩
  let sylowInModel := T.comapOfInjective inclusion hinj hTrange
  have hTcard : Nat.card T = Nat.card sylowInModel := by
    change Nat.card (T : Subgroup N) = Nat.card ((T : Subgroup N).comap inclusion)
    conv_lhs => rw [← Subgroup.map_comap_eq_self hTrange]
    exact Subgroup.card_map_of_injective hinj
  have hSylowCard : Nat.card T = 2 * Nat.card coreInNormalizer := by
    rw [hTcard, sylowInModel.card_eq_multiplicity, hCoreCard]
    rcases hCards with ⟨hQ, hP⟩ | ⟨hQ, hP⟩
    · rw [hQ, hP]
      rw [show 24 = 2 ^ 3 * 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    · rw [hQ, hP]
      rw [show 48 = 2 ^ 4 * 3 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have hNcard : Nat.card N ≤ Nat.card P := by
    have hSmall := card_le_six_mul_of_small_elementary_core coreInNormalizer
      (by rw [hCoreCard]; exact hCards.imp And.left And.left) hCoreCent ⟨T, hSylowCard⟩
    have hRatio : Nat.card P = 6 * Nat.card coreInNormalizer := by
      rw [hCoreCard]
      rcases hCards with ⟨hQ, hP⟩ | ⟨hQ, hP⟩ <;> omega
    rwa [← hRatio] at hSmall
  exact (Subgroup.eq_of_le_of_card_ge hPN hNcard).symm
