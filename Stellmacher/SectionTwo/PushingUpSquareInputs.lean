module

public import Stellmacher.SectionTwo.TwoFourInitialReduction
public import Stellmacher.SectionTwo.LemmaTwoFiveDefs
public import Stellmacher.SectionTwo.VSubgroupElementaryAbelian
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Theory.Frattini.PGroupMap

/-!
# The Section 2 core inputs to square control

Under the hypotheses of Stellmacher (2.5), write `Z` for the canonical module
inside the Sylow subgroup `S` and `Q` for the pullback of the ambient 2-core.
Then `Z` is elementary abelian, `Z ≤ Q`, `Q = C_S(Z)`, and `Q` has index two
in `S`. Moreover, the quotient of `S` by the embedded Frattini subgroup of
`Q` is not elementary abelian.

The accepted initial reduction gives the centralizer equality; canonical
module elementarity supplies the containment. The specified quotient map
has kernel the module centralizer, so its restriction to `S` has kernel
`Q` and image a Sylow subgroup of `SL₂(2)`, of order two. For the last
assertion, the embedded `Φ(Q)` is normal in the ambient group, since `Q`
is the ambient core viewed inside `S`. Frattini monotonicity gives
`Φ(Q) ≤ Φ(S)`. If the quotient were elementary, these subgroups would be
equal. The characteristic-subgroup hypothesis would then force `Φ(S)=1`,
making `S` elementary and contradicting its proper module centralizer.

These are the precise finite-group inputs to the `n=1` square argument in
Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.4), journal p.16,
as used for (2.5) of `refs/latex/stellmacher-n-group.tex`. The canonical
module is retained throughout; no identification with the smaller
core-residual commutator or additional distance-two structure is required.
-/

open scoped Pointwise
namespace Stellmacher.SectionTwo
universe u

private theorem square_control_core_inputs
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q)
    (hker : q.ker = cSubgroup S)
    (hbar : Nonempty (barG ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) :
    let Z := vSubgroupInSylow S
    let Q := pushingUpQ S
    IsElementaryAbelian 2 Z ∧ Z ≤ Q ∧
      Q = Subgroup.centralizer (Z : Set S) ∧ Q.index = 2 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z := vSubgroupInSylow S
  let Q := pushingUpQ S
  obtain ⟨hVQ, hVe⟩ := vSubgroup_le_twoCore_and_elementaryAbelian h S
  let _ : IsElementaryAbelian 2 (vSubgroup S) := hVe
  have hVS : vSubgroup S ≤ (S : Subgroup G) := hVQ.trans (fitting_pCore_le_sylow S)
  have hZe : IsElementaryAbelian 2 Z := by
    exact IsElementaryAbelian.subgroupOf hVS
  have hZmap : Z.map (S : Subgroup G).subtype = vSubgroup S :=
    Subgroup.map_subgroupOf_eq_of_le hVS
  have hZQ : Z ≤ Q := fun _ hz => hVQ hz
  have hcore := (two_four_initial_reduction h S hP hunique).1
  have hQC : Q = Subgroup.centralizer (Z : Set S) := by
    ext s
    change (s : G) ∈ pCore 2 G ↔ s ∈ Subgroup.centralizer (Z : Set S)
    rw [hcore]
    constructor
    · intro hs
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hs.2 (z : G) hz
    · intro hs
      refine ⟨s.property, ?_⟩
      change (s : G) ∈ Subgroup.centralizer (vSubgroup S : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzmap : z ∈ Z.map (S : Subgroup G).subtype := by rwa [hZmap]
      obtain ⟨zS, hzS, rfl⟩ := hzmap
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hs zS hzS)
  let qS : S →* barG := q.comp (S : Subgroup G).subtype
  have hqSker : qS.ker = Q := by
    ext s
    change q (s : G) = 1 ↔ (s : G) ∈ pCore 2 G
    rw [← MonoidHom.mem_ker, hker, hcore]
    exact ⟨fun hs => ⟨s.property, hs⟩, fun hs => hs.2⟩
  let T : Sylow 2 barG := S.mapSurjective hq
  have hTcard : Nat.card T = 2 := by
    rw [T.card_eq_multiplicity,
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hbar]
    have hf6 : Nat.factorization 6 2 = 1 := by
      change Nat.factorization (3 * 2) 2 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    simp [hf6]
  have hrange : qS.range = (T : Subgroup barG) := by
    ext g
    simp [qS, T]
  have hQi : Q.index = 2 := by
    rw [← hqSker, Subgroup.index_ker, hrange]
    exact hTcard
  exact ⟨hZe, hZQ, hQC, hQi⟩

private theorem frattini_map_equiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  exact e.mapSubgroup.map_radical

private theorem frattini_image_normal
    {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) [f.range.Normal] :
    ((frattini A).map f).Normal := by
  let e : A ≃* f.range := MonoidHom.ofInjective hf
  have he := frattini_map_equiv e
  have hEq : (frattini A).map f = (frattini f.range).map f.range.subtype := by
    rw [← he, Subgroup.map_map]
    rfl
  rw [hEq]
  infer_instance

private theorem core_frattini_ambient_normal
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G) :
    (((frattini (pushingUpQ S)).map (pushingUpQ S).subtype).map
      (S : Subgroup G).subtype).Normal := by
  let Q := pushingUpQ S
  let f : Q →* G := (S : Subgroup G).subtype.comp Q.subtype
  have hf : Function.Injective f :=
    (S : Subgroup G).subtype_injective.comp Q.subtype_injective
  have hQmap : Q.map (S : Subgroup G).subtype = pCore 2 G :=
    Subgroup.map_subgroupOf_eq_of_le (fitting_pCore_le_sylow S)
  have hrange : f.range = pCore 2 G := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hQmap
  let _ : f.range.Normal := by rw [hrange]; exact pCore_normal
  have hn := frattini_image_normal f hf
  simpa [f, Q, Subgroup.map_map] using hn

private theorem not_elementary_quotient_of_normal_frattini_layer
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hSne : ¬ IsElementaryAbelian 2 S)
    (N : Subgroup S) [N.Normal]
    (hN : (N.map (S : Subgroup G).subtype).Normal)
    (hNphi : N ≤ frattini S) :
    ¬ IsElementaryAbelian 2 (S ⧸ N) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  intro hElem
  let _ : IsElementaryAbelian 2 (S ⧸ N) := hElem
  let _ : Fact (IsPGroup 2 (S ⧸ N)) := ⟨S.isPGroup'.to_quotient N⟩
  have hPhiQuot : frattini (S ⧸ N) = ⊥ :=
    frattini_eq_bot_of_isElementaryAbelian (p := 2)
  have hPhiN : frattini S ≤ N := by
    have hh := frattini_le_comap_frattini_of_surjective
      (QuotientGroup.mk'_surjective N)
    simpa [hPhiQuot, MonoidHom.comap_bot, QuotientGroup.ker_mk'] using hh
  have hPhiEq : frattini S = N := le_antisymm hPhiN hNphi
  have hPhiBot : frattini S = ⊥ := by
    by_contra hne
    apply hP (frattini S) inferInstance hne
    rwa [hPhiEq]
  exact hSne ((frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hPhiBot)

private theorem not_elementary_of_proper_centralizer
    {H : Type*} [Group H] (Q Z : Subgroup H)
    (hQC : Q = Subgroup.centralizer (Z : Set H)) (hQi : Q.index = 2) :
    ¬ IsElementaryAbelian 2 H := by
  intro hElem
  have hQtop : Q = ⊤ := by
    rw [hQC]
    apply top_unique
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact hElem.toIsMulCommutative.is_comm.comm z x
  have hidx := hQi
  rw [hQtop, Subgroup.index_top] at hidx
  omega

private theorem core_frattini_quotient_not_elementary
    {G : Type u} [Group G] [Finite G] (S : Sylow 2 G)
    (hP : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hQC : pushingUpQ S = Subgroup.centralizer (vSubgroupInSylow S : Set S))
    (hQi : (pushingUpQ S).index = 2) :
    let Q := pushingUpQ S
    let _ : Q.Normal := (pCore_normal (p := 2) (G := G)).comap (S : Subgroup G).subtype
    let N := (frattini Q).map Q.subtype
    ¬ IsElementaryAbelian 2 (S ⧸ N) := by
  let Q := pushingUpQ S
  let _ : Q.Normal := (pCore_normal (p := 2) (G := G)).comap (S : Subgroup G).subtype
  let N := (frattini Q).map Q.subtype
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  let _ : Fact (IsPGroup 2 Q) := ⟨S.isPGroup'.to_subgroup Q⟩
  apply not_elementary_quotient_of_normal_frattini_layer S hP
    (not_elementary_of_proper_centralizer (pushingUpQ S) (vSubgroupInSylow S) hQC hQi)
    N (core_frattini_ambient_normal S)
  exact frattini_map_le_of_isPGroup (p := 2) Q.subtype

/-- The exact core and Frattini-quotient data used for square control. -/
public theorem pushing_up_square_control_inputs
    {G : Type u} [Group G] [Finite G]
    (h : Hypotheses G) (S : Sylow 2 G)
    (hcharacteristic : ∀ K : Subgroup S, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (S : Subgroup G).subtype).Normal)
    (hunique : IsUniqueMaximalContaining (S : Subgroup G) (⊤ : Subgroup G))
    {barG : Type u} [Group barG] [Finite barG]
    (q : G →* barG) (hq : Function.Surjective q)
    (hker : q.ker = cSubgroup S)
    (hbar : Nonempty (barG ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) :
    let Q := pushingUpQ S
    let Z := vSubgroupInSylow S
    let _ : Q.Normal := (pCore_normal (p := 2) (G := G)).comap (S : Subgroup G).subtype
    IsElementaryAbelian 2 Z ∧ Z ≤ Q ∧
      Q = Subgroup.centralizer (Z : Set S) ∧ Q.index = 2 ∧
      ¬ IsElementaryAbelian 2 (S ⧸ (frattini Q).map Q.subtype) := by
  obtain ⟨hZe, hZQ, hQC, hQi⟩ :=
    square_control_core_inputs h S hcharacteristic hunique q hq hker hbar
  exact ⟨hZe, hZQ, hQC, hQi,
    core_frattini_quotient_not_elementary S hcharacteristic hQC hQi⟩

end Stellmacher.SectionTwo
