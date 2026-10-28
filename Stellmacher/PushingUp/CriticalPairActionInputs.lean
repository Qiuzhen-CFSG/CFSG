module

public import Stellmacher.PushingUp.CriticalPairSL2TwoData
public import Stellmacher.PushingUp.StabilizerSL2TwoTransport
public import Stellmacher.PushingUp.SL2TwoResidualMinimal
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaActions

/-!
# Critical-pair inputs for the local SL₂(2) action

For a positive-distance critical pair, this module packages the hypotheses needed
for the quotient-action analysis in Stellmacher's proof of (2.2).  Standing
condition (A) is transported to each vertex stabilizer, where the SL₂(2)
residual theorem supplies the minimal Frattini-residual hypothesis used by the
critical-pair commutator and centralizer results.

The proof identifies the kernel of the canonical action on the vertex module
with the local centralizer.  If its quotient were a 2-group, a Sylow 2-subgroup
would map onto it and the kernel together with that Sylow subgroup would
generate the stabilizer, contradicting the local Sylow obstruction.  The
opposite endpoint has nonzero 2-group image, while the oriented triple
commutator makes this image act quadratically.  Both endpoint omega-core
inclusions and stabilizer containments come from the critical path.

Source: B. Stellmacher, *Pushing up*, Arch. Math. 46 (1986), inputs to
(2.1) in the proof of (2.2), journal p.11; see
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open AmalgamGraph
open BenderSuzuki External

universe u

variable {M : Type u} [Group M]

attribute [local instance] vertexQuotientConjugationAction

private theorem adjacent_of_mOrbit (S : Subgroup M) (a : Vertex S)
    (ha : InMVertexOrbit S a) :
    ∃ b : Vertex S, Adjacent S a b := by
  obtain ⟨g, rfl⟩ := ha
  refine ⟨act S g (hVertex S 1), ?_⟩
  exact (adjacent_act_iff S g (mVertex S 1) (hVertex S 1)).2
    (base_adjacent S)

private theorem vertexZ_le_coreOmega_of_pos [Finite M]
    (S : Subgroup M)
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S) :
    vertexZ S a ≤ omegaOneCenterAmbient (vertexTwoCore S a) := by
  obtain ⟨b, hab⟩ := adjacent_of_mOrbit S a ha
  exact
    (criticalDistance_basic S T hTS hP hSne a b ha hab).vertexZ_le_coreOmega_or_distance_zero
      |>.resolve_right (Nat.ne_of_gt hb)

private theorem vertexModule_elementaryAbelian [Finite M]
    (S : Subgroup M) (a : Vertex S)
    (hZomega : vertexZ S a ≤
      omegaOneCenterAmbient (vertexTwoCore S a)) :
    IsElementaryAbelian 2 (vertexModule S a) := by
  let G := stabilizer S a
  let V : Subgroup G := vertexModule S a
  let W : Subgroup (FreeAmalgam S) :=
    omegaOneCenterAmbient (vertexTwoCore S a)
  let hW : IsElementaryAbelian 2 W :=
    omegaOneCenterAmbient_elementaryAbelian _
  let _ : IsElementaryAbelian 2 W := hW
  have hVmap : V.map G.subtype = vertexZ S a := by
    simpa [V, G, vertexModule, vertexSylow, VertexGroup] using
      vertexZ_eq_local_vSubgroup S a
  have hVleW (x : V) : ((x : G) : FreeAmalgam S) ∈ W := by
    apply hZomega
    rw [← hVmap]
    exact Subgroup.mem_map_of_mem G.subtype x.property
  refine {
    toIsMulCommutative := ⟨⟨?_⟩⟩
    exponent_dvd_p := ?_
  }
  · intro x y
    apply Subtype.ext
    apply G.subtype_injective
    let xW : W := ⟨((x : G) : FreeAmalgam S), hVleW x⟩
    let yW : W := ⟨((y : G) : FreeAmalgam S), hVleW y⟩
    exact congrArg Subtype.val
      (hW.toIsMulCommutative.is_comm.comm xW yW)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.2
    intro x
    apply Subtype.ext
    apply G.subtype_injective
    let xW : W := ⟨((x : G) : FreeAmalgam S), hVleW x⟩
    have hxpow : xW ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 W) xW
    exact congrArg Subtype.val hxpow

private theorem oppositeImage_isPGroup_of_coreOmega [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hZomega' : vertexZ S a' ≤
      omegaOneCenterAmbient (vertexTwoCore S a')) :
    IsPGroup 2 (oppositeImage S a a' ha') := by
  have hZtwo : IsPGroup 2 (vertexZ S a') :=
    (omegaOneCenterAmbient_elementaryAbelian (vertexTwoCore S a')).isPGroup.to_le
      hZomega'
  have hsubTwo : IsPGroup 2
      ((vertexZ S a').subgroupOf (stabilizer S a)) :=
    hZtwo.of_equiv (Subgroup.subgroupOfEquivOfLe ha').symm
  exact hsubTwo.map (vertexActionQuotientMap S a)

private theorem oppositeImage_ne_bot_of_commutator [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hcomm : ⁅vertexZ S a, vertexZ S a'⁆ ≠ ⊥) :
    oppositeImage S a a' ha' ≠ ⊥ := by
  let G := stabilizer S a
  let V : Subgroup G := vertexModule S a
  let C : Subgroup G := vertexActionCentralizer S a
  let A : Subgroup G := (vertexZ S a').subgroupOf G
  let q : G →* VertexActionQuotient S a := vertexActionQuotientMap S a
  have hVmap : V.map G.subtype = vertexZ S a := by
    simpa [V, G, vertexModule, vertexSylow, VertexGroup] using
      vertexZ_eq_local_vSubgroup S a
  intro hAbot
  have hAC : A ≤ C := by
    have hker : A ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (H := A) (f := q)).mp
        (by simpa [A, q, oppositeImage] using hAbot)
    simpa [q, C, QuotientGroup.ker_mk'] using hker
  have hrev : ⁅vertexZ S a', vertexZ S a⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z' hz'
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [← hVmap] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    let z'G : G := ⟨z', ha' hz'⟩
    have hz'C : z'G ∈ C := hAC (show z'G ∈ A from hz')
    change z'G ∈ Subgroup.centralizer (V : Set G) at hz'C
    rw [Subgroup.mem_centralizer_iff] at hz'C
    exact congrArg G.subtype (hz'C v hv)
  apply hcomm
  rw [Subgroup.commutator_comm]
  exact hrev

private theorem commutatorAction_mem_endpoint_commutator [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (x : vertexModule S a)
    (hx : x ∈ commutatorAction
      (oppositeImage S a a' ha') (vertexModule S a)) :
    (((x : vertexModule S a) : stabilizer S a) : FreeAmalgam S) ∈
      ⁅vertexZ S a, vertexZ S a'⁆ := by
  let G := stabilizer S a
  let V : Subgroup G := vertexModule S a
  let A : Subgroup G := (vertexZ S a').subgroupOf G
  let q : G →* VertexActionQuotient S a := vertexActionQuotientMap S a
  let E : Subgroup (VertexActionQuotient S a) := oppositeImage S a a' ha'
  have hVmap : V.map G.subtype = vertexZ S a := by
    simpa [V, G, vertexModule, vertexSylow, VertexGroup] using
      vertexZ_eq_local_vSubgroup S a
  rw [commutatorAction_eq_closure] at hx
  change x ∈ Subgroup.closure
      {d : V | ∃ e : E, ∃ v : V, d = v⁻¹ * e • v} at hx
  refine Subgroup.closure_induction
    (p := fun y _ => (((y : V) : G) : FreeAmalgam S) ∈
      ⁅vertexZ S a, vertexZ S a'⁆)
    (x := x) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨e, v, rfl⟩
    obtain ⟨z, hzA, hze⟩ := e.property
    have hzZa' : ((z : G) : FreeAmalgam S) ∈ vertexZ S a' := hzA
    have hvZa : ((v : G) : FreeAmalgam S) ∈ vertexZ S a := by
      rw [← hVmap]
      exact Subgroup.mem_map_of_mem G.subtype v.property
    have hsmul : ((e • v : V) : G) = z * (v : G) * z⁻¹ := by
      change (((e : E).val • v : V) : G) = z * (v : G) * z⁻¹
      rw [← hze]
      exact Stellmacher.SectionTwo.quotientConjugationAction_smul_coe
        (vertexSylow S a) q
        (QuotientGroup.mk'_surjective (vertexActionCentralizer S a))
        (QuotientGroup.ker_mk' (vertexActionCentralizer S a)) z v
    change (((v : G) : FreeAmalgam S)⁻¹ *
      ((((e • v : V) : G) : FreeAmalgam S))) ∈ _
    have hsmulAmbient := congrArg Subtype.val hsmul
    rw [hsmulAmbient]
    change ((v : G) : FreeAmalgam S)⁻¹ *
        ((z : FreeAmalgam S) * ((v : G) : FreeAmalgam S) *
          (z : FreeAmalgam S)⁻¹) ∈
      ⁅vertexZ S a, vertexZ S a'⁆
    simpa [commutatorElement_def, mul_assoc] using
      (Subgroup.commutator_mem_commutator
        ((vertexZ S a).inv_mem hvZa) hzZa')
  · simp
  · intro y z _ _ hy hz
    simpa using (⁅vertexZ S a, vertexZ S a'⁆).mul_mem hy hz
  · intro y _ hy
    simpa using (⁅vertexZ S a, vertexZ S a'⁆).inv_mem hy

private theorem oppositeImage_quadratic_of_triple [Finite M]
    (S : Subgroup M) (a a' : Vertex S)
    (ha' : vertexZ S a' ≤ stabilizer S a)
    (hV : IsElementaryAbelian 2 (vertexModule S a))
    (htriple : ⁅⁅vertexZ S a', vertexZ S a⁆, vertexZ S a'⁆ = ⊥) :
    let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
    let _ := vertexQuotientConjugationAction S a
    commutatorAction₂ (oppositeImage S a a' ha')
      (vertexModule S a) = ⊥ := by
  let _ : IsElementaryAbelian 2 (vertexModule S a) := hV
  change commutatorAction₂ (oppositeImage S a a' ha')
      (vertexModule S a) = ⊥
  apply Stellmacher.SectionOne.RankOneThreeGroupAssembly.commutatorAction₂_eq_bot_of_le_fixedPoints
  intro x hx
  rw [FixedPoints.mem_subgroup]
  intro e
  obtain ⟨z, hz, hze⟩ := e.property
  apply Subtype.ext
  have hxcomm := commutatorAction_mem_endpoint_commutator
    S a a' ha' x hx
  have hxcomm' :
      (((x : vertexModule S a) : stabilizer S a) : FreeAmalgam S) ∈
        ⁅vertexZ S a', vertexZ S a⁆ := by
    rwa [Subgroup.commutator_comm]
  have hxcent :
      (((x : vertexModule S a) : stabilizer S a) : FreeAmalgam S) ∈
        Subgroup.centralizer (vertexZ S a' : Set (FreeAmalgam S)) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp htriple) hxcomm'
  rw [Subgroup.mem_centralizer_iff] at hxcent
  have hcommute := hxcent (z : FreeAmalgam S) hz
  change ((e • x : vertexModule S a) : stabilizer S a) = x
  change (((e : oppositeImage S a a' ha').val • x :
    vertexModule S a) : stabilizer S a) = x
  apply (stabilizer S a).subtype_injective
  rw [← hze]
  rw [Stellmacher.SectionTwo.quotientConjugationAction_smul_coe]
  change (z : FreeAmalgam S) *
      (((x : vertexModule S a) : stabilizer S a) : FreeAmalgam S) *
      (z : FreeAmalgam S)⁻¹ =
    (((x : vertexModule S a) : stabilizer S a) : FreeAmalgam S)
  rw [hcommute, mul_inv_cancel_right]

private theorem vertexActionQuotient_not_isPGroup [Finite M]
    (S : Subgroup M)
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (hCeq : vertexActionCentralizer S a = vertexCentralizerLocal S a) :
    ¬ IsPGroup 2 (VertexActionQuotient S a) := by
  intro htwo
  let P : Sylow 2 (stabilizer S a) := default
  let q := vertexActionQuotientMap S a
  have hPmap : (P : Subgroup (stabilizer S a)).map q = ⊤ := by
    simpa [q] using
      (sylow_map_quotient_eq_top_of_quotient_isPGroup P
        (vertexActionCentralizer S a) htwo)
  have hsup : vertexActionCentralizer S a ⊔
      (P : Subgroup (stabilizer S a)) = ⊤ := by
    have h := congrArg (Subgroup.comap q) hPmap
    rw [Subgroup.comap_top, Subgroup.comap_map_eq] at h
    change (P : Subgroup (stabilizer S a)) ⊔
        (vertexActionQuotientMap S a).ker = ⊤ at h
    rw [QuotientGroup.ker_mk'] at h
    simpa [sup_comm] using h
  exact (vertexCentralizerLocal_sup_sylow_ne_top
    S T hTS hP hSne a ha P) (by rwa [← hCeq])

private theorem criticalPair_actionInputs_of_quotient_not_two [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' : Vertex S)
    (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S)
    (hquotNotTwo : ¬ IsPGroup 2 (VertexActionQuotient S a)) :
    ∃ hV : IsElementaryAbelian 2 (vertexModule S a),
      ∃ ha' : vertexZ S a' ≤ stabilizer S a,
        CriticalPairSL2Two.ActionInputs S a a' ha' hV := by
  have hpath := criticalPair_path T hTS hP hSne a a' hcrit hb
  have hGaA := stabilizer_isSL2Two_nested_of_mOrbit S a hcrit.1 hA
  have hres : HasMinimalFrattiniResidual S a := by
    simpa [HasMinimalFrattiniResidual, vertexFrattiniResidual,
      VertexFrattiniQuotient, VertexCoreQuotient] using
        sl2Two_twoResidual_isMinimalNormal hGaA
  have hcritical :=
    criticalPair_commutator T hTS hP hSne a a' hcrit hb hres
  have ha'Orbit := hpath.opposite_inMVertexOrbit
  have hGa'A := stabilizer_isSL2Two_nested_of_mOrbit S a' ha'Orbit hA
  have hres' : HasMinimalFrattiniResidual S a' := by
    simpa [HasMinimalFrattiniResidual, vertexFrattiniResidual,
      VertexFrattiniQuotient, VertexCoreQuotient] using
        sl2Two_twoResidual_isMinimalNormal hGa'A
  have hcentral' := criticalVertex_centralizer_oddIndex
    T hTS hP hSne a' ha'Orbit hb hres'
  have hZomega := vertexZ_le_coreOmega_of_pos
    S T hTS hP hSne a hcrit.1 hb
  have hZomega' := vertexZ_le_coreOmega_of_pos
    S T hTS hP hSne a' ha'Orbit hb
  let hV : IsElementaryAbelian 2 (vertexModule S a) :=
    vertexModule_elementaryAbelian S a hZomega
  let ha' : vertexZ S a' ≤ stabilizer S a :=
    hpath.right_Z_le_left_stabilizer
  have hCeq : vertexActionCentralizer S a = vertexCentralizerLocal S a :=
    vertexActionCentralizer_eq_vertexCentralizerLocal S a
  have hquotient := isSL2Two_nested_actionQuotient
    (vertexActionCentralizer S a)
    (by rw [hCeq]; exact hcritical.centralizer_odd.core_le_centralizer)
    (by rw [hCeq]; exact hcritical.centralizer_odd.centralizer_mod_core_odd)
    hquotNotTwo hGaA
  have hopTwo := oppositeImage_isPGroup_of_coreOmega
    S a a' ha' hZomega'
  have hopNe := oppositeImage_ne_bot_of_commutator
    S a a' ha' hcritical.commutator_ne_bot
  have hquad := oppositeImage_quadratic_of_triple
    S a a' ha' hV hcritical.right_triple_commutator
  exact ⟨hV, ha', {
    critical := hcritical
    oppositeCentralizer_odd := hcentral'
    left_Z_le_right_stabilizer := hpath.left_Z_le_right_stabilizer
    left_Z_le_coreOmega := hZomega
    right_Z_le_coreOmega := hZomega'
    quotientCore_eq_bot := hquotient.1
    quotientNestedSL2 := hquotient.2
    quotient_not_two := hquotNotTwo
    oppositeImage_isPGroup := hopTwo
    oppositeImage_ne_bot := hopNe
    oppositeImage_quadratic := hquad
  }⟩

public theorem criticalPair_actionInputs [Finite M]
    (S : Subgroup M) (T : Sylow 2 M)
    (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (hA : IsSL2Two
      ((M ⧸ pCore 2 M) ⧸ frattini (M ⧸ pCore 2 M)))
    (a a' : Vertex S)
    (hcrit : IsCriticalPair S a a')
    (hb : 0 < criticalDistance S) :
    ∃ hV : IsElementaryAbelian 2 (vertexModule S a),
      ∃ ha' : vertexZ S a' ≤ stabilizer S a,
        CriticalPairSL2Two.ActionInputs S a a' ha' hV := by
  have hCeq : vertexActionCentralizer S a = vertexCentralizerLocal S a :=
    vertexActionCentralizer_eq_vertexCentralizerLocal S a
  have hquotNotTwo : ¬ IsPGroup 2 (VertexActionQuotient S a) :=
    vertexActionQuotient_not_isPGroup
      S T hTS hP hSne a hcrit.1 hCeq
  exact criticalPair_actionInputs_of_quotient_not_two
    S T hTS hP hSne hA a a' hcrit hb hquotNotTwo

end Stellmacher.PushingUp
