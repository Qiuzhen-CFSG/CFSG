module

public import Stellmacher.PushingUp.CriticalDistanceBasic
public import Stellmacher.SectionThree.SolvablePrimitiveTwoLocal.Residual
public import BenderSuzuki.External.Huppert.V.FrattiniQuotient

/-!
# The critical-vertex centralizer has odd index over the 2-core

This module defines the two nested vertex quotients, their 2-residual and
minimal-normal hypothesis, and the local copy of `C_{G_a}(Z_a)`.  It proves
clause (a) of Stellmacher, *Pushing up*, Arch. Math. 46 (1986), Lemma (1.4):
`O₂(G_a)` lies in that centralizer and has odd relative index in it.
The defining body of the local centralizer remains hidden; a membership
equivalence exposes exactly the ambient-centralizer fact used by the following
critical-pair argument.  A second narrow boundary theorem records that the
local centralizer cannot generate a vertex stabilizer together with a Sylow
2-subgroup; this is the obstruction used by the later quotient-action proof.

The proof works in the finite stabilizer of an `M`-orbit vertex.  Clause
(1.3)(e) puts `Z_a` in the center of the vertex 2-core, while conjugation
permutes the Sylow-center generators defining `Z_a`; hence the core lies in
the normal local centralizer.  The full preimage of the Frattini subgroup of
the core quotient has odd relative index over the core.  The remaining source
argument shows that the local centralizer lies in this preimage: otherwise its
nonzero normal image in the nested Frattini quotient contains the minimal
2-residual, and Sylow generation plus Frattini nongeneration makes one Sylow
center equal the join of all Sylow centers, contradicting (1.3)(d).
-/

namespace Stellmacher.PushingUp

open scoped Pointwise
open AmalgamGraph
open BenderSuzuki External

universe u

variable {M : Type u} [Group M]

public abbrev VertexCoreQuotient (S : Subgroup M) (a : Vertex S) :=
  stabilizer S a ⧸ pCore 2 (stabilizer S a)

public abbrev VertexFrattiniQuotient (S : Subgroup M) (a : Vertex S) :=
  VertexCoreQuotient S a ⧸ frattini (VertexCoreQuotient S a)

@[expose] public noncomputable def vertexFrattiniResidual (S : Subgroup M)
    (a : Vertex S) : Subgroup (VertexFrattiniQuotient S a) :=
  twoResidualAmbient (⊤ : Subgroup (VertexFrattiniQuotient S a))

@[expose] public def HasMinimalFrattiniResidual (S : Subgroup M) (a : Vertex S) : Prop :=
  SectionThree.IsMinimalNormalOver
    (⊥ : Subgroup (VertexFrattiniQuotient S a))
    (⊤ : Subgroup (VertexFrattiniQuotient S a))
    (vertexFrattiniResidual S a)

public noncomputable def vertexCentralizerLocal (S : Subgroup M)
    (a : Vertex S) : Subgroup (stabilizer S a) :=
  (Subgroup.centralizer (vertexZ S a : Set (FreeAmalgam S))).comap
    (stabilizer S a).subtype

/-- Membership in the local centralizer is ambient centralization of `Z_a`. -/
public theorem mem_vertexCentralizerLocal_iff
    (S : Subgroup M) (a : Vertex S) (x : stabilizer S a) :
    x ∈ vertexCentralizerLocal S a ↔
      (x : FreeAmalgam S) ∈
        Subgroup.centralizer (vertexZ S a : Set (FreeAmalgam S)) :=
  Iff.rfl

namespace CriticalVertexCentralizer

public structure Conclusion (S : Subgroup M) (a : Vertex S) : Prop where
  core_le_centralizer :
    pCore 2 (stabilizer S a) ≤ vertexCentralizerLocal S a
  centralizer_mod_core_odd :
    ¬ 2 ∣ ((pCore 2 (stabilizer S a)).subgroupOf
      (vertexCentralizerLocal S a)).index

end CriticalVertexCentralizer

private theorem adjacent_of_mOrbit (S : Subgroup M) (a : Vertex S)
    (ha : InMVertexOrbit S a) :
    ∃ b : Vertex S, Adjacent S a b := by
  obtain ⟨g, rfl⟩ := ha
  refine ⟨act S g (hVertex S 1), ?_⟩
  exact (adjacent_act_iff S g (mVertex S 1) (hVertex S 1)).2
    (base_adjacent S)

private theorem core_le_vertexCentralizerLocal [Finite M]
    (S : Subgroup M)
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S) :
    pCore 2 (stabilizer S a) ≤ vertexCentralizerLocal S a := by
  obtain ⟨b, hab⟩ := adjacent_of_mOrbit S a ha
  have hbasic := criticalDistance_basic S T hTS hP hSne a b ha hab
  have hZomega :
      vertexZ S a ≤ omegaOneCenterAmbient (vertexTwoCore S a) :=
    hbasic.vertexZ_le_coreOmega_or_distance_zero.resolve_right
      (Nat.ne_of_gt hb)
  intro q hq
  change (q : FreeAmalgam S) ∈
    Subgroup.centralizer (vertexZ S a : Set (FreeAmalgam S))
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzData :=
    (mem_omegaOneCenterAmbient_iff (vertexTwoCore S a) z).mp (hZomega hz)
  exact (hzData.2.2 (q : FreeAmalgam S) ⟨q, hq, rfl⟩).symm

public theorem vertexCentralizerLocal_normal [Finite M]
    (S : Subgroup M) (a : Vertex S) :
    (vertexCentralizerLocal S a).Normal := by
  let Zlocal : Subgroup (stabilizer S a) :=
    (vertexZ S a).subgroupOf (stabilizer S a)
  have hZnormal : Zlocal.Normal := vertexZ_normal_stabilizer S a
  let _ : Zlocal.Normal := hZnormal
  have hcentralizer : vertexCentralizerLocal S a =
      Subgroup.centralizer (Zlocal : Set (stabilizer S a)) := by
    ext x
    change (x : FreeAmalgam S) ∈
        Subgroup.centralizer (vertexZ S a : Set (FreeAmalgam S)) ↔ _
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx z hz
      apply Subtype.ext
      exact hx (z : FreeAmalgam S) hz
    · intro hx z hz
      let zlocal : stabilizer S a :=
        ⟨z, vertexZ_le_stabilizer S a hz⟩
      exact congrArg Subtype.val (hx zlocal hz)
  rw [hcentralizer]
  infer_instance

private theorem normalizer_le_normalizer_omegaOneCenterAmbient
    {G : Type*} [Group G] (Q : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer (omegaOneCenterAmbient Q : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  have hQmap : Q.map (MulAut.conj g).toMonoidHom = Q := by
    ext x
    rw [Subgroup.mem_map_equiv]
    simpa [MulAut.conj_symm_apply, mul_assoc] using hg (g⁻¹ * x * g)
  have hOmap : (omegaOneCenterAmbient Q).map
      (MulAut.conj g).toMonoidHom = omegaOneCenterAmbient Q := by
    rw [← omegaOneCenterAmbient_map_injective
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective, hQmap]
  intro x
  constructor
  · intro hx
    rw [← hOmap]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  · intro hx
    rw [← hOmap, Subgroup.mem_map_equiv] at hx
    simpa [MulAut.conj_apply, mul_assoc] using hx

private theorem sylowAt_smul (S : Subgroup M) (d : Vertex S)
    (x : stabilizer S d) (Td : Sylow 2 (stabilizer S d)) :
    sylowAt S d (x • Td) =
      (sylowAt S d Td).map
        (MulAut.conj (x : FreeAmalgam S)).toMonoidHom := by
  unfold sylowAt
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  change (((Td : Sylow 2 (stabilizer S d)) : Subgroup (stabilizer S d)).map
      (MulAut.conj x).toMonoidHom).map (stabilizer S d).subtype =
    (((Td : Sylow 2 (stabilizer S d)) : Subgroup (stabilizer S d)).map
      (stabilizer S d).subtype).map
        (MulAut.conj (x : FreeAmalgam S)).toMonoidHom
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem vertexZ_eq_sylowOmega_of_centralizer_sup [Finite M]
    (S : Subgroup M) (a : Vertex S)
    (P : Sylow 2 (stabilizer S a))
    (hsup : vertexCentralizerLocal S a ⊔ (P : Subgroup (stabilizer S a)) = ⊤) :
    vertexZ S a = sylowOmegaAt S a P := by
  classical
  let G : Subgroup (FreeAmalgam S) := stabilizer S a
  let C : Subgroup G := vertexCentralizerLocal S a
  let A : Subgroup (FreeAmalgam S) := sylowOmegaAt S a P
  have hAleZ : A ≤ vertexZ S a := by
    exact le_sSup ⟨P, rfl⟩
  have hCnormA : C.map G.subtype ≤ Subgroup.normalizer (A : Set (FreeAmalgam S)) := by
    have hCcentZ : C.map G.subtype ≤
        Subgroup.centralizer (vertexZ S a : Set (FreeAmalgam S)) := by
      change ((Subgroup.centralizer
        (vertexZ S a : Set (FreeAmalgam S))).comap G.subtype).map G.subtype ≤ _
      exact Subgroup.map_comap_le G.subtype
        (Subgroup.centralizer (vertexZ S a : Set (FreeAmalgam S)))
    exact hCcentZ.trans <|
      (Subgroup.centralizer_le hAleZ).trans
        (Subgroup.centralizer_le_normalizer (A : Set (FreeAmalgam S)))
  have hPnormA : (P : Subgroup G).map G.subtype ≤
      Subgroup.normalizer (A : Set (FreeAmalgam S)) := by
    change sylowAt S a P ≤
      Subgroup.normalizer (omegaOneCenterAmbient (sylowAt S a P) : Set _)
    exact Subgroup.le_normalizer.trans
      (normalizer_le_normalizer_omegaOneCenterAmbient (sylowAt S a P))
  have hGnormA : G ≤ Subgroup.normalizer (A : Set (FreeAmalgam S)) := by
    have hmapSup := congrArg (Subgroup.map G.subtype) hsup
    have hjoin : C.map G.subtype ⊔ (P : Subgroup G).map G.subtype = G := by
      simpa [C, G, Subgroup.map_sup, ← MonoidHom.range_eq_map] using hmapSup
    rw [← hjoin]
    exact sup_le hCnormA hPnormA
  apply le_antisymm
  · apply sSup_le
    rintro W ⟨T, rfl⟩
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G P T
    have hxNorm : (x : FreeAmalgam S) ∈
        Subgroup.normalizer (A : Set (FreeAmalgam S)) := hGnormA x.property
    have hAmap : A.map
        (MulAut.conj (x : FreeAmalgam S)).toMonoidHom = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxNorm
    rw [← hx]
    unfold sylowOmegaAt
    rw [sylowAt_smul,
      omegaOneCenterAmbient_map_injective
        (MulAut.conj (x : FreeAmalgam S)).toMonoidHom
        (MulAut.conj (x : FreeAmalgam S)).injective]
    exact le_of_eq hAmap
  · exact hAleZ

/-- The local centralizer and a Sylow 2-subgroup do not generate the whole
vertex stabilizer. -/
public theorem vertexCentralizerLocal_sup_sylow_ne_top [Finite M]
    (S : Subgroup M)
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (P : Sylow 2 (stabilizer S a)) :
    vertexCentralizerLocal S a ⊔ (P : Subgroup (stabilizer S a)) ≠ ⊤ := by
  intro hsup
  obtain ⟨b, hab⟩ := adjacent_of_mOrbit S a ha
  have hbasic := criticalDistance_basic S T hTS hP hSne a b ha hab
  exact hbasic.vertexZ_ne_sylowOmega P
    (vertexZ_eq_sylowOmega_of_centralizer_sup S a P hsup)

private theorem pCore_quotient_pCore_eq_bot
    (G : Type*) [Group G] [Finite G] :
    pCore 2 (G ⧸ pCore 2 G) = ⊥ := by
  let Q : Subgroup G := pCore 2 G
  let q : G →* G ⧸ Q := QuotientGroup.mk' Q
  have hmap := pCore_map_mk'_eq_of_normal_isPGroup
    (G := G) (p := 2) Q (pCore_isPGroup (G := G) (p := 2))
  have hmapbot : (pCore 2 G).map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (f := q) (H := pCore 2 G)).2
    simp [q, Q, QuotientGroup.ker_mk']
  dsimp [q, Q] at hmapbot
  exact hmap.symm.trans hmapbot

private theorem frattini_odd_of_core_eq_bot
    {G : Type*} [Group G] [Finite G] (hcore : pCore 2 G = ⊥) :
    ¬ 2 ∣ Nat.card (frattini G) := by
  let Φ : Subgroup G := frattini G
  let P : Sylow 2 Φ := default
  have hΦnil : Group.IsNilpotent Φ := by
    simpa [Φ] using (frattini_nilpotent (G := G))
  have hPnormal : (P : Subgroup Φ).Normal :=
    Group.IsNilpotent.sylow_normal hΦnil 2 P
  let _ : (P : Subgroup Φ).Characteristic :=
    Sylow.characteristic_of_normal P hPnormal
  have hPmapNormal : ((P : Subgroup Φ).map Φ.subtype).Normal := by
    infer_instance
  have hPmapCore : (P : Subgroup Φ).map Φ.subtype ≤ pCore 2 G :=
    le_sSup ⟨hPmapNormal, P.isPGroup'.map Φ.subtype⟩
  intro hdvd
  have hPne : (P : Subgroup Φ) ≠ ⊥ := P.ne_bot_of_dvd_card hdvd
  have hPmapBot : (P : Subgroup Φ).map Φ.subtype = ⊥ :=
    le_bot_iff.mp (hPmapCore.trans (le_of_eq hcore))
  exact hPne <|
    (Subgroup.map_eq_bot_iff_of_injective
      (H := (P : Subgroup Φ)) (f := Φ.subtype) Φ.subtype_injective).mp hPmapBot

private theorem critical_frattini_preimage_odd_index
    (G : Type*) [Group G] [Finite G] :
    let Q : Subgroup G := pCore 2 G
    let q : G →* G ⧸ Q := QuotientGroup.mk' Q
    let E : Subgroup G := (frattini (G ⧸ Q)).comap q
    Q ≤ E ∧ ¬ 2 ∣ (Q.subgroupOf E).index := by
  classical
  let Q : Subgroup G := pCore 2 G
  let X := G ⧸ Q
  let q : G →* X := QuotientGroup.mk' Q
  let Φ : Subgroup X := frattini X
  let E : Subgroup G := Φ.comap q
  have hQleE : Q ≤ E := by
    intro x hx
    change q x ∈ Φ
    have hxker : q x = 1 := by
      change (QuotientGroup.mk' Q) x = 1
      exact (QuotientGroup.eq_one_iff (N := Q) x).mpr hx
    simp [hxker]
  have hmapE : E.map q = Φ :=
    Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective Q) Φ
  have hindex : (Q.subgroupOf E).index = Nat.card Φ := by
    calc
      (Q.subgroupOf E).index = Nat.card (E ⧸ Q.subgroupOf E) :=
        Subgroup.index_eq_card (Q.subgroupOf E)
      _ = Nat.card (E.map q) := by
        simpa only [q] using (natCard_map_mk'_eq E Q).symm
      _ = Nat.card Φ := by rw [hmapE]
  refine ⟨hQleE, ?_⟩
  rw [hindex]
  simpa [Φ, X, Q] using
    (frattini_odd_of_core_eq_bot (pCore_quotient_pCore_eq_bot G))

private theorem pCore_quotient_frattini_eq_bot_of_pCore_eq_bot
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hcore : pCore p G = ⊥) :
    pCore p (G ⧸ frattini G) = ⊥ := by
  classical
  let Φ : Subgroup G := frattini G
  let q : G →* G ⧸ Φ := QuotientGroup.mk' Φ
  let R : Subgroup (G ⧸ Φ) := pCore p (G ⧸ Φ)
  let D : Subgroup G := R.comap q
  have hDnormal : D.Normal := by
    dsimp only [D]
    exact (pCore_normal (p := p) (G := G ⧸ Φ)).comap q
  let _ : D.Normal := hDnormal
  have hDmap : D.map q = R := by
    dsimp only [D]
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective Φ) R
  have hΦD : Φ ≤ D := by
    intro x hx
    change q x ∈ R
    have hqx : q x = 1 := by
      rw [← MonoidHom.mem_ker]
      simpa [q, Φ] using hx
    simp [hqx]
  let f : D →* G ⧸ Φ := q.comp D.subtype
  have hfker : f.ker = Φ.subgroupOf D := by
    ext x
    change q (x : G) = 1 ↔ (x : G) ∈ Φ
    simp [q]
  have hfrange : f.range = R := by
    calc
      f.range = D.map q := by
        rw [MonoidHom.range_eq_map, ← Subgroup.map_map]
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = R := hDmap
  have hfrangeP : IsPGroup p f.range := by
    rw [hfrange]
    exact pCore_isPGroup
  have hfquotP : IsPGroup p (D ⧸ f.ker) :=
    hfrangeP.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  let P : Sylow p D := default
  have hPquot : (P : Subgroup D).map (QuotientGroup.mk' f.ker) = ⊤ :=
    sylow_map_quotient_eq_top_of_quotient_isPGroup P f.ker hfquotP
  have hPsup : (P : Subgroup D) ⊔ f.ker = ⊤ := by
    have h := congrArg (Subgroup.comap (QuotientGroup.mk' f.ker)) hPquot
    simpa [Subgroup.comap_map_eq] using h
  let A : Subgroup G := (P : Subgroup D).map D.subtype
  have hAsup : A ⊔ Φ = D := by
    have h := congrArg (Subgroup.map D.subtype) hPsup
    simpa [A, Subgroup.map_sup, hfker,
      Subgroup.map_subgroupOf_eq_of_le hΦD,
      ← MonoidHom.range_eq_map] using h
  have hfrattiniArgument : Subgroup.normalizer (A : Set G) ⊔ D = ⊤ := by
    simpa [A] using Sylow.normalizer_sup_eq_top (G := G) (N := D) P
  have hnormalizerSup : Subgroup.normalizer (A : Set G) ⊔ Φ = ⊤ := by
    calc
      Subgroup.normalizer (A : Set G) ⊔ Φ =
          Subgroup.normalizer (A : Set G) ⊔ (A ⊔ Φ) := by
            symm
            rw [← sup_assoc, sup_eq_left.mpr Subgroup.le_normalizer]
      _ = Subgroup.normalizer (A : Set G) ⊔ D := by rw [hAsup]
      _ = ⊤ := hfrattiniArgument
  have hnormalizer : Subgroup.normalizer (A : Set G) = ⊤ := by
    simpa [Φ] using frattini_nongenerating hnormalizerSup
  have hAnormal : A.Normal := Subgroup.normalizer_eq_top_iff.mp hnormalizer
  have hAp : IsPGroup p A := by
    simpa [A] using P.isPGroup'.map D.subtype
  have hAcore : A ≤ pCore p G := le_sSup ⟨hAnormal, hAp⟩
  have hAbot : A = ⊥ := le_bot_iff.mp (hAcore.trans (le_of_eq hcore))
  have hDΦ : D = Φ := by
    rw [← hAsup, hAbot]
    simp
  change R = ⊥
  calc
    R = D.map q := hDmap.symm
    _ = Φ.map q := by rw [hDΦ]
    _ = ⊥ := QuotientGroup.map_mk'_self (N := Φ)

private theorem twoResidual_le_normal_of_corefree_of_minimal
    {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hcore : pCore 2 G = ⊥)
    (hminimal : SectionThree.IsMinimalNormalOver
      (⊥ : Subgroup G) (⊤ : Subgroup G)
      (twoResidualAmbient (⊤ : Subgroup G)))
    (hNne : N ≠ ⊥) :
    twoResidualAmbient (⊤ : Subgroup G) ≤ N := by
  classical
  let R : Subgroup G := twoResidualAmbient (⊤ : Subgroup G)
  have hRnormal : R.Normal := by
    dsimp [R]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact hktPResidual_normal
  let _ : R.Normal := hRnormal
  have hRNnormal : (R ⊓ N).Normal := by infer_instance
  have hmin := hminimal.2.2.2.2 (R ⊓ N) bot_le le_top
    (by simpa using hRNnormal.subgroupOf (⊤ : Subgroup G)) inf_le_left
  rcases hmin with hRNbot | hRNtop
  · exfalso
    have _hcomm : ⁅R, N⁆ = ⊥ := by
      apply le_bot_iff.mp
      calc
        ⁅R, N⁆ ≤ R ⊓ N := Subgroup.commutator_le_inf R N
        _ ≤ ⊥ := le_of_eq hRNbot
    let qR : G →* G ⧸ R := QuotientGroup.mk' R
    let fN : N →* G ⧸ R := qR.comp N.subtype
    have hfN : Function.Injective fN := by
      intro x y hxy
      change qR (x : G) = qR (y : G) at hxy
      apply Subtype.ext
      have hker : qR ((x : G) * (y : G)⁻¹) = 1 := by
        rw [map_mul, map_inv, hxy]
        simp
      have hRxy : (x : G) * (y : G)⁻¹ ∈ R :=
        (QuotientGroup.eq_one_iff ((x : G) * (y : G)⁻¹)).mp hker
      have hNxy : (x : G) * (y : G)⁻¹ ∈ N :=
        N.mul_mem x.property (N.inv_mem y.property)
      have hbot : (x : G) * (y : G)⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hRNbot]
        exact ⟨hRxy, hNxy⟩
      exact mul_inv_eq_one.mp (by simpa using hbot)
    have hquotTwo : IsPGroup 2 (G ⧸ R) := by
      let _ : (hktPResidual 2 G).Normal := hktPResidual_normal
      have hReq : R = hktPResidual 2 G :=
        SectionThree.twoResidualAmbient_top_eq_hktPResidual
      let e : (G ⧸ hktPResidual 2 G) ≃* (G ⧸ R) :=
        QuotientGroup.quotientMulEquivOfEq hReq.symm
      exact (hktPResidual_quotient_isPGroup (Q := G) (q := 2)).of_equiv e
    have hNTwo : IsPGroup 2 N := hquotTwo.of_injective fN hfN
    have hNcore : N ≤ pCore 2 G := le_sSup ⟨inferInstance, hNTwo⟩
    exact hNne (le_bot_iff.mp (hNcore.trans (le_of_eq hcore)))
  · change R ≤ N
    exact inf_eq_left.mp hRNtop

private theorem normal_sup_sylow_eq_top_of_minimal_frattini_residual
    {G : Type*} [Group G] [Finite G]
    (C : Subgroup G) [C.Normal]
    (hcoreNested : pCore 2 (G ⧸ frattini G) = ⊥)
    (hminimal : SectionThree.IsMinimalNormalOver
      (⊥ : Subgroup (G ⧸ frattini G))
      (⊤ : Subgroup (G ⧸ frattini G))
      (twoResidualAmbient (⊤ : Subgroup (G ⧸ frattini G))))
    (hCnotPhi : ¬ C ≤ frattini G)
    (T : Sylow 2 G) :
    C ⊔ (T : Subgroup G) = ⊤ := by
  classical
  let Φ : Subgroup G := frattini G
  let Y := G ⧸ Φ
  let q : G →* Y := QuotientGroup.mk' Φ
  let J : Subgroup Y := C.map q
  have hJnormal : J.Normal :=
    (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective Φ)
  let _ : J.Normal := hJnormal
  have hJne : J ≠ ⊥ := by
    intro hJbot
    apply hCnotPhi
    have hCker : C ≤ q.ker :=
      (Subgroup.map_eq_bot_iff (H := C) (f := q)).mp (by
        simpa [J] using hJbot)
    change C ≤ Φ
    change C ≤ (QuotientGroup.mk' Φ).ker at hCker
    rw [QuotientGroup.ker_mk'] at hCker
    exact hCker
  have hRJ : twoResidualAmbient (⊤ : Subgroup Y) ≤ J :=
    twoResidual_le_normal_of_corefree_of_minimal J
      (by simpa [Y, Φ] using hcoreNested)
      (by simpa [Y, Φ] using hminimal) hJne
  have hYJTwo : IsPGroup 2 (Y ⧸ J) := by
    let R : Subgroup Y := twoResidualAmbient (⊤ : Subgroup Y)
    have hRnormal : R.Normal := by
      dsimp [R]
      rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
      exact hktPResidual_normal
    let _ : R.Normal := hRnormal
    let qR : Y →* Y ⧸ R := QuotientGroup.mk' R
    have hJmapNormal : (J.map qR).Normal :=
      hJnormal.map qR (QuotientGroup.mk'_surjective R)
    let _ : (J.map qR).Normal := hJmapNormal
    have hYRtwo : IsPGroup 2 (Y ⧸ R) := by
      let _ : (hktPResidual 2 Y).Normal := hktPResidual_normal
      have hReq : R = hktPResidual 2 Y :=
        SectionThree.twoResidualAmbient_top_eq_hktPResidual
      let e : (Y ⧸ hktPResidual 2 Y) ≃* (Y ⧸ R) :=
        QuotientGroup.quotientMulEquivOfEq hReq.symm
      exact (hktPResidual_quotient_isPGroup (Q := Y) (q := 2)).of_equiv e
    have hdoubleTwo : IsPGroup 2 ((Y ⧸ R) ⧸ J.map qR) :=
      hYRtwo.to_quotient (J.map qR)
    let e : ((Y ⧸ R) ⧸ J.map qR) ≃* (Y ⧸ J) :=
      QuotientGroup.quotientQuotientEquivQuotient R J hRJ
    exact hdoubleTwo.of_equiv e
  let D : Subgroup G := C ⊔ Φ
  have hDnormal : D.Normal := by infer_instance
  let _ : D.Normal := hDnormal
  have hDmap : D.map q = J := by
    rw [show D = C ⊔ Φ from rfl, Subgroup.map_sup]
    have hPhiMap : Φ.map q = ⊥ := by
      change Φ.map (QuotientGroup.mk' Φ) = ⊥
      exact QuotientGroup.map_mk'_self Φ
    simp [hPhiMap, J]
  let eDJ : (Y ⧸ J) ≃* (G ⧸ D) :=
    (QuotientGroup.quotientMulEquivOfEq hDmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient Φ D le_sup_right)
  have hGDTwo : IsPGroup 2 (G ⧸ D) := hYJTwo.of_equiv eDJ
  let qD : G →* G ⧸ D := QuotientGroup.mk' D
  let Tbar : Sylow 2 (G ⧸ D) :=
    T.mapSurjective (QuotientGroup.mk'_surjective D)
  have htopTwo : IsPGroup 2 (⊤ : Subgroup (G ⧸ D)) :=
    hGDTwo.to_subgroup ⊤
  have hTbarTop : (Tbar : Subgroup (G ⧸ D)) = ⊤ :=
    (Tbar.is_maximal' htopTwo le_top).symm
  have hTmapTop : (T : Subgroup G).map qD = ⊤ := by
    rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective D) T]
    exact hTbarTop
  have hTDtop : (T : Subgroup G) ⊔ D = ⊤ := by
    calc
      (T : Subgroup G) ⊔ D = ((T : Subgroup G).map qD).comap qD := by
        simpa [qD, QuotientGroup.ker_mk'] using
          (Subgroup.comap_map_eq qD (T : Subgroup G)).symm
      _ = ⊤ := by rw [hTmapTop, Subgroup.comap_top]
  have hCPhiT : (C ⊔ (T : Subgroup G)) ⊔ frattini G = ⊤ := by
    rw [← hTDtop]
    simp only [D, Φ]
    ac_rfl
  exact frattini_nongenerating hCPhiT

public theorem criticalVertex_centralizer_oddIndex
    {S : Subgroup M} [Finite M]
    (T : Sylow 2 M) (hTS : (T : Subgroup M) = S)
    (hP : ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup M).subtype).Normal)
    (hSne : S ≠ ⊥)
    (a : Vertex S) (ha : InMVertexOrbit S a)
    (hb : 0 < criticalDistance S)
    (hres : HasMinimalFrattiniResidual S a) :
    CriticalVertexCentralizer.Conclusion S a := by
  classical
  let G := stabilizer S a
  let Q : Subgroup G := pCore 2 G
  let X := G ⧸ Q
  let qQ : G →* X := QuotientGroup.mk' Q
  let Φ : Subgroup X := frattini X
  let E : Subgroup G := Φ.comap qQ
  let C : Subgroup G := vertexCentralizerLocal S a
  have hQC : Q ≤ C := by
    simpa [Q, C, G] using
      (core_le_vertexCentralizerLocal S T hTS hP hSne a ha hb)
  have hCnormal : C.Normal := by
    simpa [C, G] using vertexCentralizerLocal_normal S a
  let _ : C.Normal := hCnormal
  have hCE : C ≤ E := by
    by_contra hCnotE
    let Cbar : Subgroup X := C.map qQ
    have hCbarNormal : Cbar.Normal :=
      hCnormal.map qQ (QuotientGroup.mk'_surjective Q)
    let _ : Cbar.Normal := hCbarNormal
    have hCbarNotPhi : ¬ Cbar ≤ Φ := by
      intro hCbarPhi
      apply hCnotE
      intro c hc
      change qQ c ∈ Φ
      exact hCbarPhi (Subgroup.mem_map_of_mem qQ hc)
    have hcoreX : pCore 2 X = ⊥ := by
      simpa [X, Q, G] using pCore_quotient_pCore_eq_bot G
    have hcoreNested : pCore 2 (X ⧸ Φ) = ⊥ := by
      simpa [Φ] using
        (pCore_quotient_frattini_eq_bot_of_pCore_eq_bot hcoreX)
    have hminimal : SectionThree.IsMinimalNormalOver
        (⊥ : Subgroup (X ⧸ Φ)) (⊤ : Subgroup (X ⧸ Φ))
        (twoResidualAmbient (⊤ : Subgroup (X ⧸ Φ))) := by
      simpa [HasMinimalFrattiniResidual, vertexFrattiniResidual,
        VertexFrattiniQuotient, VertexCoreQuotient, X, Φ, Q, G] using hres
    let P : Sylow 2 G := default
    let PX : Sylow 2 X :=
      P.mapSurjective (QuotientGroup.mk'_surjective Q)
    have hPX : (PX : Subgroup X) = (P : Subgroup G).map qQ :=
      Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective Q) P
    have hgenX : Cbar ⊔ (PX : Subgroup X) = ⊤ :=
      normal_sup_sylow_eq_top_of_minimal_frattini_residual
        Cbar hcoreNested hminimal hCbarNotPhi PX
    have hmapGen : (C ⊔ (P : Subgroup G)).map qQ = ⊤ := by
      rw [Subgroup.map_sup]
      simpa [Cbar, hPX] using hgenX
    have hgenQ : (C ⊔ (P : Subgroup G)) ⊔ Q = ⊤ := by
      have hcomap := congrArg (Subgroup.comap qQ) hmapGen
      rw [Subgroup.comap_top, Subgroup.comap_map_eq] at hcomap
      change (C ⊔ (P : Subgroup G)) ⊔ (QuotientGroup.mk' Q).ker = ⊤ at hcomap
      rw [QuotientGroup.ker_mk'] at hcomap
      exact hcomap
    have hQleGen : Q ≤ C ⊔ (P : Subgroup G) := hQC.trans le_sup_left
    have hgen : C ⊔ (P : Subgroup G) = ⊤ := by
      simpa [sup_eq_left.mpr hQleGen] using hgenQ
    exact (vertexCentralizerLocal_sup_sylow_ne_top S T hTS hP hSne a ha P)
      (by simpa [C, G] using hgen)
  have hodd := critical_frattini_preimage_odd_index G
  have hQE : Q ≤ E := by simpa [Q, E, Φ, qQ, X] using hodd.1
  have hQEodd : ¬ 2 ∣ Q.relIndex E := by
    change ¬ 2 ∣ (Q.subgroupOf E).index
    simpa [Q, E, Φ, qQ, X] using hodd.2
  refine ⟨by simpa [Q, C, G] using hQC, ?_⟩
  change ¬ 2 ∣ Q.relIndex C
  intro htwo
  apply hQEodd
  rw [← Subgroup.relIndex_mul_relIndex Q C E hQC hCE]
  exact dvd_mul_of_dvd_left htwo _

end Stellmacher.PushingUp
