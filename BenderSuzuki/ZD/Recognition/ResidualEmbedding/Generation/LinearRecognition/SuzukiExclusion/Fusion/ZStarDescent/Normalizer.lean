module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.Contracts
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.ZStarDescent.Quotient
public import Theory.GroupTheory.PGroup.SelfCentralizingFrattiniImage
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.SubgroupProductCard

/-!
# The normalizer calculation in the Suzuki Z-star descent

Write A₀ for the distinguished closure, A = A₀ ∩ M, and Q = N_M(A₀U).
The centralizer clauses identify C_G(A₀U) with T. The Sylow geometry then
identifies Q with N_G(T), gives the source decomposition Q = S N_D(A₀U),
and makes S normal and self-centralizing in Q. This proves |Q| divides
|S||D| and hence the required prime-divisor exclusion for its image in M/A.

For the odd core, the regular S-orbit on A₀u shows A₀ ≤ [S,S] ≤ Φ(S).
The Burnside basis-kernel theorem consequently gives O₂′(Q̄) = 1 through
the actual map Q → Q̄. This replaces the source's abbreviated calculation
with O²(C_D̄(T̄)); it does not confuse that residual with O₂′. The supplied
Sylow geometry already contains everything needed for this argument, so
no additional torus or model-centralizer hypotheses enter these theorems.

The final theorem applies both calculations to the published quotient-Sylow
construction. Weak closure remains an explicit input of that consumer;
its producer and the full Proposition 14.1 assembly remain separate.

Source: GLS, Volume 4, Chapter 2, Lemmas 14.3 and 14.6 and the conclusion
of Proposition 14.1, `refs/KGroup/GLS4/Chapter2.tex`, lines 2620–2630.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion.ZStarDescent
open Subgroup Theory.GroupTheory PFAppendixIII
open scoped Pointwise commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

private theorem U_le_S (g : LocalGeometry Z M z t m) : g.U ≤ g.S := by
  rw [g.U_eq]
  exact inf_le_left.trans g.T_lt_S.le

private theorem A_le_S (g : LocalGeometry Z M z t m) (s : SylowGeometry g) :
    closure (Z ∩ (M : Set G)) ≤ g.S := by
  rw [← s.S_center]
  exact map_subtype_le _

/-- The source centralizer T is the full ambient centralizer of A₀U. -/
public theorem centralizer_AU (g : LocalGeometry Z M z t m) (hU : Nat.card g.U = 2) :
    centralizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) = g.T := by
  have hne : g.U ≠ ⊥ := (one_lt_card_iff_ne_bot _).mp (by omega)
  obtain ⟨u, hu, hu1⟩ := g.U.bot_or_exists_ne_one.resolve_left hne
  have he : centralizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) =
      centralizer (closure (Z ∩ (M : Set G)) : Set G) ⊓ centralizer (g.U : Set G) := by
    apply le_antisymm
    · exact le_inf (centralizer_le (show closure (Z ∩ (M : Set G)) ≤ closure (Z ∩ (M : Set G)) ⊔ g.U from le_sup_left)) (centralizer_le (show g.U ≤ closure (Z ∩ (M : Set G)) ⊔ g.U from le_sup_right))
    · apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)
  rw [he]
  apply le_antisymm
  · rw [← g.centralizer_U u hu hu1]
    exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hu))
  · apply le_inf
    · rw [← g.centralizer_U u hu hu1]
      exact inf_le_left
    · intro x hx
      apply mem_centralizer_iff.mpr
      intro v hv
      by_cases hv1 : v = 1
      · simp [hv1]
      · have hh : x ∈ centralizer ({v} : Set G) := by
          have ht := hx
          rw [← g.centralizer_U v hv hv1] at ht
          exact ht.2
        exact (mem_centralizer_singleton_iff.mp hh).symm

private theorem normalizerAU_le_normalizer_T (g : LocalGeometry Z M z t m)
    (hU : Nat.card g.U = 2) :
    normalizerAU g ≤ (normalizer (g.T : Set G)).subgroupOf M := by
  intro x hx
  have hn := normalizer_le_normalizer_centralizer
    (closure (Z ∩ (M : Set G)) ⊔ g.U) hx
  rwa [centralizer_AU g hU] at hn

private theorem S_le_normalizer_AU (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) :
    g.S ≤ normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) := by
  let A := closure (Z ∩ (M : Set G))
  have hA : M ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer distinguishedClosure_le).mp
      (distinguishedClosure_normal d.minimal.disconnected)
  apply le_normalizer_iff_commutator_le_right.mpr
  apply commutator_le.mpr
  intro x hx y hy
  have hyconj : x * y * x⁻¹ ∈ A ⊔ g.U := by
    have hmap : A ⊔ g.U ≤ (A ⊔ g.U).comap (MulAut.conj x).toMonoidHom := by
      apply sup_le
      · intro a ha
        exact (show A ≤ A ⊔ g.U from le_sup_left) ((mem_normalizer_iff.mp (hA (g.S_le_M hx)) a).mp ha)
      · intro v hv
        by_cases hv1 : v = 1
        · simp [hv1]
        · obtain ⟨a, ha, he⟩ := (s.U_orbits v hv hv1 (MulAut.conj x v)).mp ⟨x, hx, rfl⟩
          change MulAut.conj x v ∈ A ⊔ g.U
          rw [he]
          exact (A ⊔ g.U).mul_mem ((show A ≤ A ⊔ g.U from le_sup_left) ha) ((show g.U ≤ A ⊔ g.U from le_sup_right) hv)
    exact hmap hy
  exact (A ⊔ g.U).mul_mem hyconj ((A ⊔ g.U).inv_mem hy)

private theorem normalizer_T_le_M (g : LocalGeometry Z M z t m) (s : SylowGeometry g) :
    normalizer (g.T : Set G) ≤ M := by
  intro x hx
  change _ ∈ (normalizer (g.T : Set G) : Set G) at hx
  rw [s.normalizer_product] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact M.mul_mem (g.S_le_M ha) hb.1.1

/-- The source normalizer Q is the restriction of the full normalizer of T. -/
public theorem normalizerAU_eq_normalizer_T (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (hU : Nat.card g.U = 2) :
    normalizerAU g = (normalizer (g.T : Set G)).subgroupOf M := by
  apply le_antisymm (normalizerAU_le_normalizer_T g hU)
  intro x hx
  change (x : G) ∈ normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G)
  change _ ∈ (normalizer (g.T : Set G) : Set G) at hx
  rw [s.normalizer_product] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  change a * b = (x : G) at hab
  rw [← hab]
  apply (normalizer _).mul_mem (S_le_normalizer_AU d g s ha)
  have hA : M ≤ normalizer (closure (Z ∩ (M : Set G)) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer distinguishedClosure_le).mp
      (distinguishedClosure_normal d.minimal.disconnected)
  exact (normalizer_inf_normalizer_le_normalizer_sup _ _) ⟨hA hb.1.1, hb.2⟩

/-- Regularity on A₀u expresses every element of A₀ as a commutator in S. -/
public theorem distinguishedClosure_le_S_commutator (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hU : Nat.card g.U = 2) :
    closure (Z ∩ (M : Set G)) ≤ (_root_.commutator g.S).map g.S.subtype := by
  have hne : g.U ≠ ⊥ := (one_lt_card_iff_ne_bot _).mp (by omega)
  obtain ⟨u, hu, hu1⟩ := g.U.bot_or_exists_ne_one.resolve_left hne
  intro a ha
  obtain ⟨x, hx, he⟩ := (s.U_orbits u hu hu1 (a * u)).mpr ⟨a, ha, rfl⟩
  have hc : ⁅(⟨x, hx⟩ : g.S), ⟨u, U_le_S g hu⟩⁆ ∈ _root_.commutator g.S :=
    commutator_mem_commutator (mem_top _) (mem_top _)
  refine ⟨_, hc, ?_⟩
  change x * u * x⁻¹ * u⁻¹ = a
  change x * u * x⁻¹ = a * u at he
  rw [he]
  group

private theorem normalizerAU_S_le (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) :
    g.S.subgroupOf M ≤ normalizerAU g := by
  intro x hx
  exact S_le_normalizer_AU d g s hx

/-- S is normal relative to the actual subgroup Q of M. -/
public theorem normalizerAU_S_normal
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (hU : Nat.card g.U = 2) :
    ((g.S.subgroupOf M).subgroupOf (normalizerAU g)).Normal := by
  have hnS : g.S ≤ normalizer (g.T : Set G) := by
    obtain ⟨V, hV⟩ := g.S_sylow
    rw [← hV]
    exact map_subtype_le _
  have hn := (normal_subgroupOf_iff_le_normalizer hnS).mp s.S_normal
  apply normal_subgroupOf_of_le_normalizer
  intro x hx
  rw [← subgroupOf_normalizer_eq g.S_le_M]
  exact hn (normalizerAU_le_normalizer_T g hU hx)

/-- T is normal relative to the actual subgroup Q of M. -/
public theorem normalizerAU_T_normal (g : LocalGeometry Z M z t m) (hU : Nat.card g.U = 2) :
    ((g.T.subgroupOf M).subgroupOf (normalizerAU g)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  intro x hx
  rw [← subgroupOf_normalizer_eq (g.T_lt_S.le.trans g.S_le_M)]
  exact normalizerAU_le_normalizer_T g hU hx

private theorem normalizerAU_S_selfCentralizing (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (hU : Nat.card g.U = 2) :
    centralizer (((g.S.subgroupOf M).subgroupOf (normalizerAU g)) : Set (normalizerAU g)) ≤
      (g.S.subgroupOf M).subgroupOf (normalizerAU g) := by
  intro x hx
  have hc : ((x : M) : G) ∈ centralizer (g.S : Set G) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    have he := mem_centralizer_iff.mp hx
      (⟨⟨y, g.S_le_M hy⟩, S_le_normalizer_AU d g s hy⟩ : normalizerAU g) hy
    exact congrArg (fun q : normalizerAU g => ((q : M) : G)) he
  have hAU : closure (Z ∩ (M : Set G)) ⊔ g.U ≤ g.S :=
    sup_le (A_le_S g s) (U_le_S g)
  have ht := centralizer_le hAU hc
  rw [centralizer_AU g hU] at ht
  exact g.T_lt_S.le ht

/-- The literal ambient image of Q has the source factorization S N_D(A₀U). -/
public theorem normalizerAU_product (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (hU : Nat.card g.U = 2) :
    ((normalizerAU g).map M.subtype : Set G) =
      (g.S : Set G) * ((residualPairStabilizer M t ⊓
        normalizer ((closure (Z ∩ (M : Set G)) ⊔ g.U : Subgroup G) : Set G) : Subgroup G) : Set G) := by
  have hA : M ≤ normalizer (closure (Z ∩ (M : Set G)) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer distinguishedClosure_le).mp
      (distinguishedClosure_normal d.minimal.disconnected)
  apply Set.Subset.antisymm
  · rintro x ⟨q, hq, rfl⟩
    have hn := normalizerAU_le_normalizer_T g hU hq
    change (q : G) ∈ (normalizer (g.T : Set G) : Set G) at hn
    rw [s.normalizer_product] at hn
    obtain ⟨a, ha, b, hb, hab⟩ := hn
    refine ⟨a, ha, b, ⟨hb.1, ?_⟩, hab⟩
    exact normalizer_inf_normalizer_le_normalizer_sup _ _ ⟨hA hb.1.1, hb.2⟩
  · rintro x ⟨a, ha, b, hb, rfl⟩
    refine ⟨⟨a * b, M.mul_mem (g.S_le_M ha) hb.1.1⟩, ?_, rfl⟩
    exact (normalizer _).mul_mem (S_le_normalizer_AU d g s ha) hb.2

/-- The normalizer order divides the product of the Sylow and pair-stabilizer orders. -/
public theorem normalizerAU_card_dvd (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (hU : Nat.card g.U = 2) :
    Nat.card (normalizerAU g) ∣ Nat.card g.S * Nat.card (residualPairStabilizer M t) := by
  rw [normalizerAU_eq_normalizer_T d g s hU,
    Nat.card_congr (subgroupOfEquivOfLe (normalizer_T_le_M g s)).toEquiv]
  have he := card_set_mul_mul_card_inf g.S
    (residualPairStabilizer M t ⊓ normalizer (g.U : Set G))
  rw [← s.normalizer_product] at he
  exact (Dvd.intro _ he).trans (Nat.mul_dvd_mul_left _ (card_dvd_of_le inf_le_left))

/-- An odd prime absent from D is also absent from the literal image of Q in M/A. -/
public theorem prime_not_dvd_normalizerAU_image (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (hU : Nat.card g.U = 2)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpD : ¬ p ∣ Nat.card (residualPairStabilizer M t)) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    ¬ p ∣ Nat.card ((normalizerAU g).map (QuotientGroup.mk' A)) := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  change ¬ p ∣ Nat.card ((normalizerAU g).map (QuotientGroup.mk' A))
  intro hp
  have hd := hp.trans ((card_map_dvd (normalizerAU g) (QuotientGroup.mk' A)).trans
    (normalizerAU_card_dvd d g s hU))
  have hS : IsPGroup 2 g.S := by
    obtain ⟨V, hV⟩ := s.S_sylow
    exact hV ▸ V.isPGroup'
  obtain ⟨n, hn⟩ := hS.exists_card_dvd_pow
  rcases (Fact.out : p.Prime).dvd_mul.mp hd with hs | hd
  · have hptwo := (Fact.out : p.Prime).dvd_of_dvd_pow (hs.trans hn)
    exact hp2 ((Nat.dvd_prime Nat.prime_two).mp hptwo |>.resolve_left
      (Fact.out : p.Prime).ne_one)
  · exact hpD hd

/-- The literal image of Q in M/A has trivial odd core, with no extra source premises. -/
public theorem normalizerAU_image_oddCore_eq_bot (d : Context Z M z t m)
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g) (hU : Nat.card g.U = 2) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    pPrimeCore 2 ((normalizerAU g).map (QuotientGroup.mk' A)) = ⊥ := by
  let A := (closure (Z ∩ (M : Set G))).subgroupOf M
  let : A.Normal := distinguishedClosure_normal d.minimal.disconnected
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Q := normalizerAU g
  let P := (g.S.subgroupOf M).subgroupOf Q
  let : P.Normal := normalizerAU_S_normal g s hU
  have hS : IsPGroup 2 g.S := by
    obtain ⟨V, hV⟩ := s.S_sylow
    exact hV ▸ V.isPGroup'
  let : Fact (IsPGroup 2 g.S) := ⟨hS⟩
  let pi := QuotientGroup.mk' A
  let e : P ≃* g.S :=
    (subgroupOfEquivOfLe (normalizerAU_S_le d g s)).trans
      (subgroupOfEquivOfLe g.S_le_M)
  apply pPrimeCore_eq_bot_of_selfCentralizing_frattini_image 2 P
    (hS.comap_subtype.comap_subtype)
    (normalizerAU_S_selfCentralizing d g s hU)
    (pi.subgroupMap Q) (pi.subgroupMap_surjective Q)
  intro x hx
  have hxpi : pi (x : M) = 1 := congrArg Subtype.val hx
  have hxA : ((x : M) : G) ∈ closure (Z ∩ (M : Set G)) :=
    (QuotientGroup.eq_one_iff (N := A) (x : M)).mp hxpi
  obtain ⟨y, hy, he⟩ := distinguishedClosure_le_S_commutator g s hU hxA
  have hyPhi : y ∈ frattini g.S := commutator_le_frattini_of_isPGroup (p := 2) hy
  have hw := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom) e.symm.surjective hyPhi
  refine ⟨e.symm y, hw, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact he

/-- The two normalizer calculations discharge the local premises of the
published quotient-Sylow construction. -/
public theorem quotient_pCore_sylow_of_sylowGeometry
    (d : Context Z M z t m) (g : LocalGeometry Z M z t m)
    (s : SylowGeometry g) (hU : Nat.card g.U = 2) (hweak : QuotientFusion d g)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (hpD : ¬ p ∣ Nat.card (residualPairStabilizer M t)) :
    let A := (closure (Z ∩ (M : Set G))).subgroupOf M
    letI : A.Normal := distinguishedClosure_normal d.minimal.disconnected
    ∃ R : Sylow p (M ⧸ A), (R : Subgroup (M ⧸ A)) = pCore p (M ⧸ A) := by
  exact quotient_pCore_sylow_of_normalizer d g s hU hweak p
    (normalizerAU_image_oddCore_eq_bot d g s hU)
    (prime_not_dvd_normalizerAU_image d g s hU p hp2 hpD)

end BenderSuzuki.ZD.SuzukiExclusion.ZStarDescent
