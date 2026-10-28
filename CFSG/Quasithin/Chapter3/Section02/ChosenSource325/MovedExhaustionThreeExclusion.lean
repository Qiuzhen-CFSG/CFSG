module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionThreeModels
public import Theory.Representation.BinaryOffender.PermutedSupports

/-!
# Excluding a normal three-support in the repeated two-type orbit

For an odd group X commuting with a two-group D, every invariant summand
moved by X contributes at least a binary plane to [C(D),X]. Choose a nonzero
D-fixed vector in the X-moved part; its X-span cannot be a fixed binary line.
Two disjoint moved summands therefore contribute at least four dimensions.

D.2.13 gives a centralizing hyperplane D of a noncyclic starred actor A and
an order-three support X with dim([C(D),X]) = 2. If X is normal in the whole
faithful action, it moves both members of the permuted complementary pair.
The starred actor stabilizes that pair in the repeated-copy case, so the
four-dimensional lower bound is a contradiction. This supplies a direct
exclusion of the three-core branch in place of its later model analysis.

`SeedAlternativesMovedExhaustionThreeModels` proves normality from the actual
chosen-seed hypotheses and applies the exclusion to the original action.
The component and section-FF branches, exhaustion and Source325 assembly
remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.2.13(5), D.3.12 and D.3.14--17,
printed pp.184--185 and202--203, applied in3.2.5, printed p.580.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open Representation.BinaryOffender
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

omit [Finite H] in
private theorem invariant_fixedfree_finrank_ge_two
    (ρ : Representation (ZMod 2) H E) (X : Subgroup H)
    (P : Submodule (ZMod 2) E) (hP : X ≤ subspaceStabilizer ρ P)
    (hn : P ≠ ⊥) (hd : Disjoint P (fixedSpace ρ X)) :
    2 ≤ Module.finrank (ZMod 2) P := by
  by_contra! hsmall
  have hpos : 0 < Module.finrank (ZMod 2) P :=
    Nat.pos_of_ne_zero (fun h => hn (Submodule.finrank_eq_zero.mp h))
  have hdim : Module.finrank (ZMod 2) P = 1 := by omega
  have hfix : P ≤ fixedSpace ρ X := by
    intro v hv x
    by_cases hz : v = 0
    · rw [hz,map_zero]
    have hm : ρ x.val v ∈ P := (hP x.property v).2 hv
    rw [eq_span_singleton_of_mem_of_finrank_eq_one hdim hv hz] at hm
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
    have ha0 : a ≠ 0 := by
      intro he
      have hh := congrArg (ρ x.val⁻¹) ha
      rw [he,zero_smul,map_zero,←Module.End.mul_apply,←map_mul,
        inv_mul_cancel,map_one,Module.End.one_apply] at hh
      exact hz hh.symm
    have ha1 : a = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha0
    change ρ x.val v = v
    simpa only [ha1,one_smul] using ha.symm
  exact hn (bot_unique (fun v hv => Submodule.disjoint_def.mp hd v hv (hfix hv)))

/-- A commuting two-group has at least a binary plane of odd movement
in every nontrivially moved invariant summand. -/
theorem fixed_odd_support_finrank_ge_two
    (ρ : Representation (ZMod 2) H E) (X D : Subgroup H)
    (ho : Odd (Nat.card X)) (hp : IsPGroup 2 D)
    (hc : D ≤ centralizer (X : Set H))
    (I : Submodule (ZMod 2) E)
    (hXI : X ≤ subspaceStabilizer ρ I) (hDI : D ≤ subspaceStabilizer ρ I)
    (hm : ¬ I ≤ fixedSpace ρ X) :
    2 ≤ Module.finrank (ZMod 2)
      (subspaceCommutator ρ (I ⊓ fixedSpace ρ D) X) := by
  let R := subspaceCommutator ρ I X
  let P := subspaceCommutator ρ (I ⊓ fixedSpace ρ D) X
  have hR : R ≠ ⊥ := fun he => hm ((subspaceCommutator_eq_bot_iff ρ I X).mp he)
  have hRI : R ≤ I := subspaceCommutator_le_of_invariant ρ hXI
  have hDR : D ≤ subspaceStabilizer ρ R :=
    subspaceCommutator_invariant_normalizer ρ hDI
      (hc.trans (Subgroup.centralizer_le_normalizer _))
  have hdis : Disjoint (subspaceCommutator ρ ⊤ X) (fixedSpace ρ X) :=
    by
      have he : subspaceCommutator ρ ⊤ X =
          Representation.RegularCyclicNormalClosure.displacementSpan ρ X ⊤ := by
        unfold subspaceCommutator Representation.RegularCyclicNormalClosure.displacementSpan
        congr 1
        ext v
        constructor <;> rintro ⟨x,hx,w,hw,he⟩ <;> exact ⟨x,hx,w,hw,he.symm⟩
      rw [he]
      exact (Representation.GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) ho).symm.disjoint
  have hRX : Disjoint R (fixedSpace ρ X) :=
    hdis.mono_left (subspaceCommutator_mono_left ρ le_top X)
  obtain ⟨v,hv,hvn,hvD⟩ := PermutedSupports.exists_nonzero_fixed ρ D hp R hR hDR
  have hPn : P ≠ ⊥ := by
    intro he
    have hfix := (subspaceCommutator_eq_bot_iff ρ (I ⊓ fixedSpace ρ D) X).mp he
    exact hvn (Submodule.disjoint_def.mp hRX v hv (hfix ⟨hRI hv,hvD⟩))
  have hXD : X ≤ subspaceStabilizer ρ (fixedSpace ρ D) :=
    le_stabilizer_fixedSpace_of_commutator_eq_bot ρ X D
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc))
  have hXP : X ≤ subspaceStabilizer ρ P :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ _ (fun x hx v hv =>
        ⟨(hXI hx v).2 hv.1,(hXD hx v).2 hv.2⟩)) X.le_normalizer
  exact invariant_fixedfree_finrank_ge_two ρ X P hXP hPn
    (hdis.mono_left (subspaceCommutator_mono_left ρ le_top X))

/-- Two disjoint invariant summands moved by an odd group force at least
four dimensions in its movement on the fixed space of a commuting two-group. -/
theorem fixed_odd_support_finrank_ge_four
    (ρ : Representation (ZMod 2) H E) (X D : Subgroup H)
    (ho : Odd (Nat.card X)) (hp : IsPGroup 2 D)
    (hc : D ≤ centralizer (X : Set H))
    (I J : Submodule (ZMod 2) E) (hd : Disjoint I J)
    (hXI : X ≤ subspaceStabilizer ρ I) (hXJ : X ≤ subspaceStabilizer ρ J)
    (hDI : D ≤ subspaceStabilizer ρ I) (hDJ : D ≤ subspaceStabilizer ρ J)
    (hIm : ¬ I ≤ fixedSpace ρ X) (hJm : ¬ J ≤ fixedSpace ρ X) :
    4 ≤ Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ D) X) := by
  let P := subspaceCommutator ρ (I ⊓ fixedSpace ρ D) X
  let Q := subspaceCommutator ρ (J ⊓ fixedSpace ρ D) X
  have hP := fixed_odd_support_finrank_ge_two ρ X D ho hp hc I hXI hDI hIm
  have hQ := fixed_odd_support_finrank_ge_two ρ X D ho hp hc J hXJ hDJ hJm
  have hPI : P ≤ I := (subspaceCommutator_mono_left ρ inf_le_left X).trans
    (subspaceCommutator_le_of_invariant ρ hXI)
  have hQJ : Q ≤ J := (subspaceCommutator_mono_left ρ inf_le_left X).trans
    (subspaceCommutator_le_of_invariant ρ hXJ)
  have hPQ : Disjoint P Q := hd.mono hPI hQJ
  have he := P.finrank_sup_add_finrank_inf_eq Q
  rw [hPQ.eq_bot,finrank_bot,add_zero] at he
  have hh := Submodule.finrank_mono (sup_le
    (subspaceCommutator_mono_left ρ (show I ⊓ fixedSpace ρ D ≤ fixedSpace ρ D from inf_le_right) X)
    (subspaceCommutator_mono_left ρ (show J ⊓ fixedSpace ρ D ≤ fixedSpace ρ D from inf_le_right) X))
  change Module.finrank (ZMod 2) (P ⊔ Q : Submodule (ZMod 2) E) ≤ _ at hh
  change 2 ≤ Module.finrank (ZMod 2) P at hP
  change 2 ≤ Module.finrank (ZMod 2) Q at hQ
  omega

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open Representation.BinaryOffender ChapterD
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- A normal order-three support moved by a noncyclic starred actor has
an actual centralizing hyperplane whose fixed-space movement is a plane. -/
theorem exists_centralizing_hyperplane_for_moved_three
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    {A : Subgroup H} (hA : A ∈ QhatStar ρ) (hr : 1 < rank A)
    (X : Subgroup H) (hX : Nat.card X = 3) (hXP : X ≤ pCore 3 H)
    (hAX : A ≤ normalizer (X : Set H)) (hXA : ⁅X,A⁆ = X) :
    ∃ D : Subgroup H, D ≤ A ∧ D ≤ centralizer (X : Set H) ∧
      rank D + 1 = rank A ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ (fixedSpace ρ D) X) = 2 := by
  classical
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  have hXn : X ≠ ⊥ := by intro he; rw [he,card_bot] at hX; omega
  have hgen := eq_iSup_hyperplane_centralizer_commutator (by decide : (3 : ℕ) ≠ 2)
    X A (pCore_isPGroup.to_le hXP) hAX hXA.symm
  obtain ⟨D,hi,hm⟩ : ∃ D : Subgroup A, D.index = 2 ∧
      ⁅X ⊓ centralizer (D.map A.subtype : Set H),A⁆ ≠ ⊥ := by
    by_contra! hn
    apply hXn
    rw [hgen]
    exact le_bot_iff.mp (iSup₂_le fun D hi => (hn D hi).le)
  let D₀ := D.map A.subtype
  let Y := ⁅X ⊓ centralizer (D₀ : Set H),A⁆
  let Z := ⁅pCore 3 H ⊓ centralizer (D₀ : Set H),A⁆
  have hYX : Y ≤ X := (commutator_mono inf_le_left le_rfl).trans hXA.le
  have hYZ : Y ≤ Z := commutator_mono (inf_le_inf_right _ hXP) le_rfl
  have hZn : Z ≠ ⊥ := fun he => hm (bot_unique (hYZ.trans he.le))
  obtain ⟨n,hcardD⟩ := ((IsElementaryAbelian.isPGroup 2 A).to_subgroup D).exists_card_eq
  have hc := D.card_mul_index
  rw [hi,hcardD,hA.1.2.1.card_eq_two_pow_rank] at hc
  have hn : n + 1 = rank A := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    change 2 ^ (n + 1) = 2 ^ rank A
    rw [pow_succ]
    exact hc
  have hDr : rank D₀ + 1 = rank A := by
    change Nat.log 2 (Nat.card (D.map A.subtype)) + 1 = rank A
    rw [card_map_of_injective A.subtype_injective,hcardD,Nat.log_pow (by decide : 1 < 2)]
    exact hn
  have hs := source_lemma_D_2_13_noncyclic_support ρ hf hA hr D₀ (map_subtype_le D) hDr hZn
  have hYcard : Nat.card Y = 3 := by
    have hd := card_dvd_of_le hYX
    rw [hX] at hd
    rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with he | he
    · exact (hm (Subgroup.card_eq_one.mp he)).elim
    · exact he
  have hYXeq : Y = X := eq_of_le_of_card_ge hYX (by rw [hYcard,hX])
  have hYZeq : Y = Z := eq_of_le_of_card_ge hYZ (by rw [hYcard,hs.1])
  have hAc : A ≤ centralizer (D₀ : Set H) := by
    intro a ha d hd
    exact congrArg Subtype.val (mul_comm (⟨d,map_subtype_le D hd⟩ : A) ⟨a,ha⟩)
  have hYC : Y ≤ centralizer (D₀ : Set H) :=
    (commutator_mono inf_le_right le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp
        (hAc.trans (centralizer (D₀ : Set H)).le_normalizer))
  refine ⟨D₀,map_subtype_le D,le_centralizer_iff.mp (hYXeq ▸ hYC),hDr,?_⟩
  rw [←hYXeq,hYZeq]
  exact hs.2.2.1

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325

namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open Representation.BinaryOffender ChapterD
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private theorem map_action_product (ρ : Representation (ZMod 2) H E)
    (I : Submodule (ZMod 2) E) (x y : H) :
    I.map (ρ (x*y)) = (I.map (ρ y)).map (ρ x) := by
  rw [map_mul]
  exact Submodule.map_comp (ρ y) (ρ x) I

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private theorem map_action_eq_of_stabilizes (ρ : Representation (ZMod 2) H E)
    (I : Submodule (ZMod 2) E) (a : H) (ha : a ∈ subspaceStabilizer ρ I) :
    I.map (ρ a) = I := by
  apply le_antisymm
  · rintro _ ⟨v,hv,rfl⟩
    exact (ha v).2 hv
  · intro v hv
    refine ⟨ρ a⁻¹ v,((subspaceStabilizer ρ I).inv_mem ha v).2 hv,?_⟩
    rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- The stabilizer of one member of a permuted pair stabilizes the other. -/
theorem pair_second_stabilized
    (ρ : Representation (ZMod 2) H E) (I : Submodule (ZMod 2) E) (t a : H)
    (hne : I ≠ I.map (ρ t))
    (hp : ∀ g : H, I.map (ρ g) = I ∨ I.map (ρ g) = I.map (ρ t))
    (ha : I.map (ρ a) = I) : (I.map (ρ t)).map (ρ a) = I.map (ρ t) := by
  rcases hp (a*t) with he | he
  · rw [map_action_product] at he
    exact (hne ((Submodule.map_injective_of_injective
      (GoldschmidtONan.action_injective (ρ := ρ) a)) (ha.trans he.symm))).elim
  · rwa [map_action_product] at he

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- An element of order dividing three cannot interchange a permuted pair. -/
private theorem cube_one_stabilizes_pair
    (ρ : Representation (ZMod 2) H E) (I : Submodule (ZMod 2) E) (t x : H)
    (hne : I ≠ I.map (ρ t))
    (hp : ∀ g : H, I.map (ρ g) = I ∨ I.map (ρ g) = I.map (ρ t))
    (hx : x ^ 3 = 1) : I.map (ρ x) = I := by
  rcases hp x with he | he
  · exact he
  have htwo : (I.map (ρ t)).map (ρ x) = I := by
    rcases hp (x*x) with h2 | h2
    · rwa [map_action_product,he] at h2
    · rw [map_action_product,he] at h2
      exact (hne ((Submodule.map_injective_of_injective
        (GoldschmidtONan.action_injective (ρ := ρ) x)) (he.trans h2.symm))).elim
  have hthree : I.map (ρ (x ^ 3)) = I.map (ρ t) := by
    rw [show x ^ 3 = x*(x*x) by simp only [pow_succ,pow_zero,one_mul,mul_assoc],map_action_product,map_action_product,he,htwo,he]
  rw [hx,map_one] at hthree
  change I.map LinearMap.id = I.map (ρ t) at hthree
  rw [Submodule.map_id] at hthree
  exact (hne hthree).elim

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- A faithful normal actor moves both members of a swapped complementary pair. -/
theorem normal_actor_moves_pair
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    (X : Subgroup H) [X.Normal] (hX : X ≠ ⊥)
    (I : Submodule (ZMod 2) E) (t : H) (hc : IsCompl I (I.map (ρ t))) :
    ¬ I ≤ fixedSpace ρ X ∧ ¬ I.map (ρ t) ≤ fixedSpace ρ X := by
  have hnot : ¬ I ≤ fixedSpace ρ X := by
    intro hI
    have hJ : I.map (ρ t) ≤ fixedSpace ρ X := by
      rintro _ ⟨v,hv,rfl⟩
      exact Representation.le_comap_invariants ρ X t (hI hv)
    have hfull : (⊤ : Submodule (ZMod 2) E) ≤ fixedSpace ρ X :=
      hc.sup_eq_top ▸ sup_le hI hJ
    apply hX
    apply bot_unique
    intro x hx
    apply hf
    rw [map_one]
    ext v
    exact hfull Submodule.mem_top ⟨x,hx⟩
  refine ⟨hnot,?_⟩
  intro hJ
  apply hnot
  intro v hv
  have hh := Representation.le_comap_invariants ρ X t⁻¹
    (hJ (Submodule.mem_map.mpr ⟨v,hv,rfl⟩))
  change ρ t⁻¹ (ρ t v) ∈ fixedSpace ρ X at hh
  simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using hh

/-- A normal order-three support is impossible in the two-type enlargement:
the hyperplane support plane meets both invariant summands in at least a plane. -/
theorem no_normal_three_support_on_stable_pair
    (ρ : Representation (ZMod 2) H E) (hf : Function.Injective ρ)
    {A : Subgroup H} (hA : A ∈ QhatStar ρ) (hr : 1 < rank A)
    (X : Subgroup H) [X.Normal] (hX : Nat.card X = 3)
    (hXP : X ≤ pCore 3 H) (hXA : ⁅X,A⁆ = X)
    (I : Submodule (ZMod 2) E) (t : H) (hc : IsCompl I (I.map (ρ t)))
    (hn : I ≠ I.map (ρ t))
    (hp : ∀ g : H, I.map (ρ g) = I ∨ I.map (ρ g) = I.map (ρ t))
    (hAI : A ≤ subspaceStabilizer ρ I) : False := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  obtain ⟨D,hDA,hDX,_,hd⟩ := exists_centralizing_hyperplane_for_moved_three
    ρ hf hA hr X hX hXP (by rw [normalizer_eq_top]; exact le_top) hXA
  have hXI : X ≤ subspaceStabilizer ρ I := by
    apply le_subspaceStabilizer
    intro x hx v hv
    have hx3 : x ^ 3 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : X))
      rw [hX] at hh
      exact congrArg Subtype.val hh
    rw [←cube_one_stabilizes_pair ρ I t x hn hp hx3]
    exact Submodule.mem_map.mpr ⟨v,hv,rfl⟩
  have hsecond (Y : Subgroup H) (hY : Y ≤ subspaceStabilizer ρ I) :
      Y ≤ subspaceStabilizer ρ (I.map (ρ t)) := by
    apply le_subspaceStabilizer
    intro y hy v hv
    rw [←pair_second_stabilized ρ I t y hn hp
      (map_action_eq_of_stabilizes ρ I y (hY hy))]
    exact Submodule.mem_map.mpr ⟨v,hv,rfl⟩
  have hXn : X ≠ ⊥ := by intro he; rw [he,card_bot] at hX; omega
  obtain ⟨hIm,hJm⟩ := normal_actor_moves_pair ρ hf X hXn I t hc
  have hfour := fixed_odd_support_finrank_ge_four ρ X D
    (by rw [hX]; decide) ((IsElementaryAbelian.isPGroup 2 A).to_le hDA) hDX
    I (I.map (ρ t)) hc.disjoint hXI (hsecond X hXI)
    (hDA.trans hAI) (hsecond D (hDA.trans hAI)) hIm hJm
  omega

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
