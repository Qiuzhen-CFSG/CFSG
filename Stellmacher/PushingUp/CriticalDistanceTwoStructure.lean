module

public import Stellmacher.PushingUp.DistanceTwoCoreResidualContainment
public import Stellmacher.PushingUp.NaturalSL2TwoCommutator
public import Stellmacher.ResidualCentralLayer
public import Stellmacher.PushingUp.BaseStructureTransport
public import Stellmacher.PushingUp.NaturalSL2TwoAmbientStructure

/-!
# The distance-two pushing-up structure

When the critical distance is two, the literal local commutator
`W = [O₂(G), O²(G)]` is elementary abelian, is an irreducible section for
`G`, and satisfies `W ≤ [W,G]`. At the base vertex this gives the required
structure in the original finite group, with the permitted choice `L = ⊤`.
The shared companion also retains the canonical action quotient `SL₂(2)`,
`|W| = 4`, and the exact equality `W = [SectionTwo.vSubgroup T, M]`.
The original structural theorem remains a wrapper with its unchanged API.

The distance-two containment puts `W` inside the canonical elementary module
`Z`. Critical-pair (2.2) identifies the quotient of `Z` by its global fixed
subgroup as the natural `SL₂(2)` module. The order-three coprime splitting
then makes `U = [Z,G]` itself natural. Modulo `U`, the residual centralizes
`Z`; the residual central-layer theorem consequently gives `W ≤ U`.
The subgroup `W` is nonzero: if the residual centralized the 2-core, it would
centralize `Z`, and the residual/Sylow supplement would make the faithful
six-element action quotient a 2-group. Normality of `W` and natural
irreducibility now force `W = U`. The action transports below identify the
same quotient action with literal ambient conjugation throughout. The
natural additive equivalence identifies `U` with the four-element vector
space, and the same equality `W = U` transports its cardinality. The base
natural-data transport carries that quotient and subgroup equality to the
original supplied Sylow subgroup without claiming that its whole canonical
module has order four.

This proves the elementary, irreducible, full-commutator portion of
Stellmacher, *Pushing up*, Arch. Math. 46 (1986), (3.2), journal p.14,
specialized to `p = 2`, `n = 1`, for the pushing-up input to Theorem 2 in
`refs/latex/stellmacher-n-group.tex`. The existential conclusion allows the
full group as actor, so the narrower source subgroup `L₀Vˣ` need not be
constructed. The fixed denominator is kept explicit; no equality `W = Z`
is assumed. All finite hypotheses apply to vertex stabilizers, not to the
free amalgam or its vertex set.
-/

open scoped Pointwise commutatorElement
open BenderSuzuki External
namespace Stellmacher.PushingUp
universe u v

private theorem residual_commutator_ne_bot
    {G : Type u} [Group G] [Finite G] (Q Z : Subgroup G)
    [Z.Normal] (hZQ : Z ≤ Q)
    (hnot : ¬ IsPGroup 2 (G ⧸ Subgroup.centralizer (Z : Set G))) :
    ⁅Q, twoResidualAmbient (⊤ : Subgroup G)⁆ ≠ ⊥ := by
  intro hbot
  let C := Subgroup.centralizer (Z : Set G)
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  let R := twoResidualAmbient (⊤ : Subgroup G)
  have hRcentQ : R ≤ Subgroup.centralizer (Q : Set G) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
      Subgroup.commutator_comm]
    exact hbot
  have hRC : R ≤ C := hRcentQ.trans (Subgroup.centralizer_le hZQ)
  have hRmap : R.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    simpa [q, QuotientGroup.ker_mk'] using hRC
  let T : Sylow 2 G := default
  have hsup := twoResidualAmbient_top_sup_sylow T
  have hm := congrArg (Subgroup.map q) hsup
  rw [Subgroup.map_sup, hRmap, bot_sup_eq] at hm
  have htop : (⊤ : Subgroup G).map q = ⊤ := by
    rw [← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective C)]
  rw [htop] at hm
  have hp : IsPGroup 2 (↑((T : Subgroup G).map q)) := T.isPGroup'.map q
  rw [hm] at hp
  exact hnot (hp.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup (G ⧸ C)) ≃* (G ⧸ C)))

private noncomputable abbrev actionTransport
    {A V W : Type*} [Group A] [Group V] [Group W]
    [MulDistribMulAction A V] (e : V ≃* W) : MulDistribMulAction A W where
  smul a w := e (a • e.symm w)
  one_smul w := by
    change e ((1 : A) • e.symm w) = w
    simp
  mul_smul a b w := by
    change e ((a * b) • e.symm w) = e (a • e.symm (e (b • e.symm w)))
    simp [mul_smul]
  smul_one a := by
    change e (a • e.symm 1) = 1
    simp
  smul_mul a x y := by
    change e (a • e.symm (x * y)) = e (a • e.symm x) * e (a • e.symm y)
    simp [smul_mul']

private theorem natural_map_ambient_structure
    {G : Type u} {A : Type v} [Group G] [Group A]
    (Z : Subgroup G) (U : Subgroup Z)
    [MulDistribMulAction A U]
    (q : G →* A) (hq : Function.Surjective q)
    (eA : A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hNat : IsNaturalSL2TwoActionAlong U eA)
    (hact : ∀ (g : G) (w : U), (((q g) • w : U) : G) =
      g * (w : G) * g⁻¹) :
    IsElementaryAbelian 2 (U.map Z.subtype) ∧
      IsIrreducibleSection (⊤ : Subgroup G) ⊥ (U.map Z.subtype) ∧
      U.map Z.subtype ≤ ⁅U.map Z.subtype, (⊤ : Subgroup G)⁆ := by
  let e : U ≃* U.map Z.subtype := Subgroup.equivMapOfInjective U
    Z.subtype Z.subtype_injective
  let _ := actionTransport (A := A) e
  have hnatural : IsNaturalSL2TwoActionAlong (U.map Z.subtype) eA := by
    obtain ⟨ev, hev⟩ := hNat
    refine ⟨(MulEquiv.toAdditive e.symm).trans ev, ?_⟩
    intro a w
    change ev (Additive.ofMul (e.symm (e (a • e.symm w)))) = _
    rw [e.symm_apply_apply]
    exact hev a (e.symm w)
  let f : (⊤ : Subgroup G) →* A := q.comp (⊤ : Subgroup G).subtype
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨g, rfl⟩ := hq a
    exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩
  apply naturalSL2Two_ambient_structure_of_surjective_actor
    (⊤ : Subgroup G) (U.map Z.subtype) f hf eA hnatural
  intro g w
  have he (v : U) : ((e v : U.map Z.subtype) : G) = (v : G) := rfl
  change ((e ((q (g : G)) • e.symm w) : U.map Z.subtype) : G) = _
  rw [he, hact]
  have hw : ((e.symm w : U) : G) = (w : G) := by
    exact (he (e.symm w)).symm.trans (congrArg Subtype.val (e.apply_symm_apply w))
  rw [hw]

private theorem commutatorAction_top_eq
    {A V : Type*} [Group A] [Group V] [MulDistribMulAction A V] :
    commutatorAction (⊤ : Subgroup A) V = commutatorAction A V := by
  rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨a, v, rfl⟩
    exact ⟨(a : A), v, rfl⟩
  · rintro ⟨a, v, rfl⟩
    exact ⟨⟨a, Subgroup.mem_top a⟩, v, rfl⟩

private theorem structure_of_natural_commutator
    {G : Type u} [Group G] [Finite G]
    (T : Sylow 2 G)
    [ (Subgroup.centralizer (SectionTwo.vSubgroup T : Set G)).Normal]
    (hZQ : SectionTwo.vSubgroup T ≤ pCore 2 G)
    (hElem : IsElementaryAbelian 2 (SectionTwo.vSubgroup T))
    (hWZ : ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤ SectionTwo.vSubgroup T)
    (q : G →* (G ⧸ Subgroup.centralizer (SectionTwo.vSubgroup T : Set G)))
    (hq : Function.Surjective q)
    (hker : q.ker = SectionTwo.cSubgroup T)
    (eA : (G ⧸ Subgroup.centralizer (SectionTwo.vSubgroup T : Set G)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
    (hNat :
      let _ := SectionTwo.quotientConjugationAction T q hq hker
      let _ := commutatorAction_isInvariant (A := (G ⧸ Subgroup.centralizer (SectionTwo.vSubgroup T : Set G)))
        (G := SectionTwo.vSubgroup T)
      IsNaturalSL2TwoActionAlong
        (commutatorAction (G ⧸ Subgroup.centralizer (SectionTwo.vSubgroup T : Set G))
          (SectionTwo.vSubgroup T)) eA) :
    (IsElementaryAbelian 2 ↥(⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆) ∧
      IsIrreducibleSection (⊤ : Subgroup G) ⊥
        ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ ∧
      ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ ≤
        ⁅⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆, (⊤ : Subgroup G)⁆) ∧
    Nat.card ↥(⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆) = 4 ∧
    ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ =
      ⁅SectionTwo.vSubgroup T, (⊤ : Subgroup G)⁆ := by
  let Z := SectionTwo.vSubgroup T
  let A := G ⧸ Subgroup.centralizer (Z : Set G)
  let _ := SectionTwo.quotientConjugationAction T q hq hker
  let U₀ := commutatorAction A Z
  let _ := commutatorAction_isInvariant (A := A) (G := Z)
  let U : Subgroup G := U₀.map Z.subtype
  let W := ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆
  have hUeq : U = ⁅Z, (⊤ : Subgroup G)⁆ := by
    have h := SectionTwo.quotientConjugationAction_commutator_map T q hq hker (⊤ : Subgroup A)
    rw [commutatorAction_top_eq, Subgroup.comap_top] at h
    simpa [U, U₀, Z, ambientCommutator, Subgroup.commutator_comm] using h
  have hstructure : IsElementaryAbelian 2 U ∧
      IsIrreducibleSection (⊤ : Subgroup G) ⊥ U ∧ U ≤ ⁅U, (⊤ : Subgroup G)⁆ := by
    apply natural_map_ambient_structure Z U₀ q hq eA hNat
    intro g w
    exact SectionTwo.quotientConjugationAction_smul_coe T q hq hker g (w : Z)
  have hZnormal : Z.Normal := Subgroup.normalClosure_normal
  let _ : Z.Normal := hZnormal
  have hUnormal : U.Normal := by rw [hUeq]; infer_instance
  have hWU : W ≤ U := by
    let _ : (pCore 2 G).Normal := pCore_normal
    let _ : U.Normal := hUnormal
    let _ : IsElementaryAbelian 2 Z := hElem
    apply residual_commutator_le_of_central_layer (pCore 2 G) U Z hWZ
    rw [hUeq]
    exact Subgroup.commutator_mono le_rfl le_top
  have hWne : W ≠ ⊥ := by
    apply residual_commutator_ne_bot (pCore 2 G) Z hZQ
    intro hp
    have hcard : Nat.card A = 6 :=
      SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨eA⟩
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hcard] at hn
    have hdvd : 3 ∣ 2 ^ n := by rw [← hn]; decide
    exact (by decide : ¬ 3 ∣ 2) (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
  have hWnormal : W.Normal := by
    dsimp [W]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    let _ : (pCore 2 G).Normal := pCore_normal
    let _ : (hktPResidual 2 G).Normal := hktPResidual_normal
    infer_instance
  have hWinv : IsConjugateInvariantBy W (⊤ : Subgroup G) := by
    intro g w hw
    exact hWnormal.conj_mem w hw g
  have hWUeq : W = U := by
    rcases hstructure.2.1.2.2 W bot_le hWU hWinv with hbot | heq
    · exact False.elim (hWne hbot)
    · exact heq
  have hUcard : Nat.card U = 4 := by
    rw [Subgroup.card_map_of_injective Z.subtype_injective]
    obtain ⟨eU, _⟩ := hNat
    calc
      Nat.card U₀ = Nat.card (Fin 2 → ZMod 2) := Nat.card_congr eU.toEquiv
      _ = 4 := by norm_num [Nat.card_fun]
  refine ⟨?_, ?_, hWUeq.trans hUeq⟩
  · change IsElementaryAbelian 2 W ∧ IsIrreducibleSection (⊤ : Subgroup G) ⊥ W ∧
      W ≤ ⁅W, (⊤ : Subgroup G)⁆
    rwa [hWUeq]
  · change Nat.card W = 4
    rw [hWUeq]
    exact hUcard

/-- The distance-two structure with its canonical action quotient, exact
four-element residual commutator, and canonical-module commutator equality. -/
public theorem criticalDistance_two_structure_and_natural
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (hb : criticalDistance S = 2) :
    let V := ⁅pCore 2 M, twoResidualAmbient (⊤ : Subgroup M)⁆
    (∃ L : Subgroup M,
      IsElementaryAbelian 2 V ∧ IsIrreducibleSection L ⊥ V ∧ V ≤ ⁅V,L⁆) ∧
    (let _ : (SectionTwo.vSubgroup T).Normal := Subgroup.normalClosure_normal
     let _ : (SectionTwo.cSubgroup T).Normal := Subgroup.normal_centralizer
     IsSL2Two (M ⧸ SectionTwo.cSubgroup T) ∧ Nat.card V = 4 ∧
       V = ⁅SectionTwo.vSubgroup T, (⊤ : Subgroup M)⁆) := by
  let a := AmalgamGraph.mVertex S 1
  have ha : InMVertexOrbit S a := ⟨1, by simp [a]⟩
  obtain ⟨a', hcrit⟩ := criticalPair_exists S T hTS hP hSne a ha
  have hbpos : 0 < criticalDistance S := by omega
  obtain ⟨hV, ha'Ga, hinputs⟩ :=
    criticalPair_actionInputs S T hTS hP hSne hA a a' hcrit hbpos
  let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
  let _ := vertexQuotientConjugationAction S a
  obtain ⟨hV', ha'Ga', hsl⟩ :=
    criticalPair_sl2Two S T hTS hP hSne hA a a' hcrit hbpos
  obtain ⟨eA, hC, hNat⟩ := hsl.sl2AndNaturalModule
  have hfixed := criticalPair_fixedSpaceData S a a' ha'Ga hV hinputs
  have hCeq : vertexCenterPart S a =
      FixedPoints.subgroup (VertexActionQuotient S a) (vertexModule S a) :=
    hfixed.globalFixed_eq_centerPart.symm
  obtain ⟨_, hNaturalU⟩ := naturalSL2TwoActionAlong_commutator_of_natural_quotient
    eA (vertexCenterPart S a) hCeq hC hNat
  have hZQ : vertexModule S a ≤ pCore 2 (AmalgamGraph.stabilizer S a) := by
    rw [← Subgroup.map_le_map_iff_of_injective (AmalgamGraph.stabilizer S a).subtype_injective]
    change (vertexModule S a).map (AmalgamGraph.stabilizer S a).subtype ≤ vertexTwoCore S a
    rw [vertexZ_eq_local_vSubgroup S a]
    refine hinputs.left_Z_le_coreOmega.trans ?_
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff (vertexTwoCore S a) z).mp hz).1
  have hWZ := criticalDistance_two_coreResidual_le_vertexModule
    S T hTS hP hSne hA a a' hcrit hb
  let _ : (vertexModule S a).Normal := Subgroup.normalClosure_normal
  obtain ⟨⟨hElem, hIrred, hComm⟩, hcard, heq⟩ := structure_of_natural_commutator
    (vertexSylow S a) hZQ hV hWZ
    (vertexActionQuotientMap S a)
    (QuotientGroup.mk'_surjective (vertexActionCentralizer S a))
    (QuotientGroup.ker_mk' (vertexActionCentralizer S a)) eA hNaturalU
  refine ⟨base_structure_transport S ⊤ hElem hIrred hComm, ?_⟩
  exact base_natural_commutator_transport S T (vertexSylow S a) ⟨eA⟩ hcard heq

/-- At critical distance two, the original core-residual commutator is an
irreducible elementary abelian section with full ambient commutator. -/
public theorem criticalDistance_two_structure
    {M : Type u} [Group M] [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (hb : criticalDistance S = 2) :
    let V := ⁅pCore 2 M, twoResidualAmbient (⊤ : Subgroup M)⁆
    ∃ L : Subgroup M,
      IsElementaryAbelian 2 V ∧ IsIrreducibleSection L ⊥ V ∧ V ≤ ⁅V,L⁆ := by
  exact (criticalDistance_two_structure_and_natural S T hTS hP hSne hA hb).1

end Stellmacher.PushingUp
