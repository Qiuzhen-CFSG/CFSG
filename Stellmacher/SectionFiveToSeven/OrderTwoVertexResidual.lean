module

public import Stellmacher.SectionFiveToSeven.FiveTwoPStarCentralizer
public import Stellmacher.SectionFiveToSeven.Result7_5
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# Residual subnormality at an order-two vertex center

Under Hypothesis Two, when the two local subgroups generate the finite ambient
group, an order-two vertex center forces the common Sylow subgroup to be a
global Sylow subgroup. The vertex's two-residual is contained and subnormal in
the full ambient centralizer of that center.

Transport the vertex to one of the two distinguished cosets. The nontrivial
omega-center of the common Sylow subgroup lies in the distinguished vertex
center, so the order-two hypothesis makes them equal. Stabilizer invariance
then rules out alternatives (5.1)(a) and (c). In alternative (b), the vertex
cannot belong to the P1 orbit: its omega-center would be normalized by P1 and
centralized by P2, hence normal in the generated ambient group, contradicting
the trivial ambient two-core. On the P2 orbit, the P-star residual theorem
gives subnormality in the omega-centralizer. Conjugation transports both the
residual and its centralizer back to the original vertex.

This supplies the order-two-center input for subsequent neighbor transport,
without any critical-path or Section Nine hypotheses. Source: Stellmacher,
Journal of Algebra 190 (1997), (5.1)(b), the P-star definition and the opening
reduction of (5.2); the resulting residual-centralizer assertion is used on
printed p.54 (PDF p.44 of `refs/files/stellmacher-n-group.pdf`).
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven
open CosetGraphContext

universe u v
variable {H : Type u} [Group H] [Finite H]
variable {S P1 P2 : Subgroup H}

private theorem base_stabilizer (Γ : CosetGraphContext H S P1 P2)
    (coset : H → Γ.Vertex) (P : Subgroup H)
    (hact : ∀ g h, Γ.act g (coset h) = coset (h * g))
    (heq : ∀ g h, coset g = coset h ↔
      MulOpposite.op g • (P : Set H) = MulOpposite.op h • (P : Set H)) :
    Γ.stabilizer (coset 1) = P := by
  ext element
  have hmem : element ∈ Γ.stabilizer (coset 1) ↔
      Γ.act element (coset 1) = coset 1 :=
    Set.ext_iff.mp (Γ.stabilizer_def (coset 1)) element
  rw [hmem, hact, one_mul, heq]
  simp only [MulOpposite.op_one, one_smul]
  constructor
  · intro hsets
    change element ∈ (P : Set H)
    rw [← hsets]
    exact Set.mem_smul_set.mpr ⟨1, P.one_mem, by simp⟩
  · exact fun hmem ↦ op_smul_coe_set hmem

private theorem omega_ne_bot (S : Subgroup H)
    (hS : IsPGroup 2 S) (hne : S ≠ ⊥) : omegaOneCenter S ≠ ⊥ := by
  let _ : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).2 hne
  let _ : Nontrivial (Subgroup.center S) := hS.center_nontrivial
  obtain ⟨power, hpos, hcard⟩ :=
    (hS.to_subgroup (Subgroup.center S)).nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center S) := by
    rw [hcard]
    exact dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hpos)
  have hinner := omega₁_map_subtype_ne_bot (G := S) (Subgroup.center S) 2 hdvd
  intro hbot
  apply hinner
  apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
  simpa [omegaOneCenter] using hbot

private theorem base_center (Γ : CosetGraphContext H S P1 P2)
    (base : Γ.Vertex) (P : Subgroup H) (hbase : Γ.stabilizer base = P)
    (hsyl : IsSylowTwoIn S P) (hne : omegaOneCenter S ≠ ⊥)
    (hcard : Nat.card (Γ.z base) = 2) :
    Γ.z base = omegaOneCenter S ∧ NormalIn (omegaOneCenter S) P := by
  have hle : omegaOneCenter S ≤ Γ.z base := by
    obtain ⟨_, sylow, hsylow⟩ := hsyl
    change omegaOneCenter S ≤ Γ.zAt base
    rw [Γ.zAt_def]
    change omegaOneCenter S ≤ sSup {Z : Subgroup H |
      ∃ T : Sylow 2 (Γ.stabilizer base),
        Z = omegaOneCenter ((T : Subgroup (Γ.stabilizer base)).map
          (Γ.stabilizer base).subtype)}
    rw [hbase]
    exact le_sSup ⟨sylow, congrArg omegaOneCenter hsylow.symm⟩
  have hequal : Γ.z base = omegaOneCenter S := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hcard]
    exact (Subgroup.one_lt_card_iff_ne_bot (omegaOneCenter S)).mpr hne
  refine ⟨hequal, (Subgroup.map_subtype_le _).trans hsyl.1, ?_⟩
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    ((Subgroup.map_subtype_le _).trans hsyl.1)).mpr
  change P ≤ Subgroup.normalizer (omegaOneCenter S : Set H)
  rw [← hbase, ← hequal]
  exact stabilizer_le_normalizer_z Γ base

private theorem omega_not_normal_left
    (S0 : Sylow 2 H) (hyp : HypothesisTwo H S0 S P1 P2)
    (hgen : P1 ⊔ P2 = ⊤) (hne : omegaOneCenter S ≠ ⊥)
    (hP2 : P2 ≤ Subgroup.centralizer (omegaOneCenter S : Set H)) :
    ¬ NormalIn (omegaOneCenter S) P1 := by
  intro hnormal
  have hnorm : (omegaOneCenter S).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2)
      (hP2.trans (Subgroup.centralizer_le_normalizer _))
  have hp : IsPGroup 2 (omegaOneCenter S) :=
    (omegaOneCenterAmbient_elementaryAbelian S).isPGroup
  have hcore : omegaOneCenter S ≤ pCore 2 H := le_sSup ⟨hnorm, hp⟩
  exact hne (le_bot_iff.mp (hcore.trans_eq hyp.hyp1.twoCore_eq_bot))

omit [Finite H] in
private theorem subnormal_map (equiv : H ≃* H) (A P : Subgroup H)
    (hsub : SubnormalIn A P) :
    SubnormalIn (A.map equiv.toMonoidHom) (P.map equiv.toMonoidHom) := by
  let restricted : P ≃* P.map equiv.toMonoidHom :=
    P.equivMapOfInjective equiv.toMonoidHom equiv.injective
  have hmapped : ((A.subgroupOf P).map restricted.toMonoidHom).IsSubnormal :=
    hsub.2.map restricted.surjective
  refine ⟨Subgroup.map_mono hsub.1, ?_⟩
  have heq : (A.subgroupOf P).map restricted.toMonoidHom =
      (A.map equiv.toMonoidHom).subgroupOf (P.map equiv.toMonoidHom) := by
    apply Subgroup.map_injective (P.map equiv.toMonoidHom).subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_mono hsub.1)]
    have hcomp : (P.map equiv.toMonoidHom).subtype.comp restricted.toMonoidHom =
        equiv.toMonoidHom.comp P.subtype := rfl
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hsub.1]
  rwa [← heq]

omit [Finite H] in
private theorem centralizer_map (A : Subgroup H) (equiv : H ≃* H) :
    (Subgroup.centralizer (A : Set H)).map equiv.toMonoidHom =
      Subgroup.centralizer (A.map equiv.toMonoidHom : Set H) := by
  ext element
  constructor
  · rintro ⟨preimage, hpreimage, rfl⟩
    change preimage ∈ Subgroup.centralizer (A : Set H) at hpreimage
    change equiv preimage ∈ Subgroup.centralizer (A.map equiv.toMonoidHom : Set H)
    rw [Subgroup.mem_centralizer_iff] at hpreimage ⊢
    rintro _ ⟨member, hmember, rfl⟩
    simpa using congrArg equiv (hpreimage member hmember)
  · intro hmem
    refine ⟨equiv.symm element, ?_, by simp⟩
    change equiv.symm element ∈ Subgroup.centralizer (A : Set H)
    rw [Subgroup.mem_centralizer_iff] at hmem ⊢
    intro member hmember
    apply equiv.injective
    simpa using hmem (equiv member) ⟨member, hmember, rfl⟩

private theorem residual_transport (Γ : CosetGraphContext H S P1 P2)
    (base : Γ.Vertex) (actor : H)
    (hsub : SubnormalIn (Γ.e base) (Subgroup.centralizer (Γ.z base : Set H))) :
    SubnormalIn (Γ.e (Γ.act actor base))
      (Subgroup.centralizer (Γ.z (Γ.act actor base) : Set H)) := by
  have hmapped := subnormal_map (MulAut.conj actor⁻¹) _ _ hsub
  rw [centralizer_map, ← z_act] at hmapped
  have hres : Γ.e (Γ.act actor base) =
      (Γ.e base).map (MulAut.conj actor⁻¹).toMonoidHom := by
    change Γ.twoResidualAt (Γ.act actor base) =
      (Γ.twoResidualAt base).map _
    rw [Γ.twoResidualAt_def, Γ.twoResidualAt_def]
    change twoResidualIn (Γ.stabilizer (Γ.act actor base)) =
      (twoResidualIn (Γ.stabilizer base)).map _
    rw [stabilizer_act]
    exact (map_twoResidualAmbient_of_subgroup_image _ _ _ rfl).symm
  rwa [hres]

/-- An order-two vertex center forces global Sylow equality, and the vertex
two-residual is subnormal in its full ambient centralizer. -/
public theorem orderTwoVertex_residual_subnormal
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (hyp : HypothesisTwo H S0 S P1 P2) (hgen : P1 ⊔ P2 = ⊤)
    (Γ : CosetGraphContext H S P1 P2) (d : Γ.Vertex)
    (hcard : Nat.card (Γ.z d) = 2) :
    S = (S0 : Subgroup H) ∧
      Γ.e d ≤ Subgroup.centralizer (Γ.z d : Set H) ∧
      ((Γ.e d).subgroupOf (Subgroup.centralizer (Γ.z d : Set H))).IsSubnormal := by
  have hSne : omegaOneCenter S ≠ ⊥ :=
    omega_ne_bot S (S0.isPGroup'.to_le hyp.fiveOne.S_le_S0) hyp.fiveOne.S_nontrivial
  have hbase1 := base_stabilizer Γ Γ.coset₁ P1 Γ.act_coset₁ Γ.coset₁_eq_iff
  have hbase2 := base_stabilizer Γ Γ.coset₂ P2 Γ.act_coset₂ Γ.coset₂_eq_iff
  obtain ⟨actor, hd | hd⟩ := Γ.coset₁_surjective d
  · have hdact : d = Γ.act actor (Γ.coset₁ 1) := by
      simpa [Γ.act_coset₁] using hd
    have hcardbase : Nat.card (Γ.z (Γ.coset₁ 1)) = 2 := by
      rw [hdact, z_act, Subgroup.card_map_of_injective
        (MulAut.conj actor⁻¹).injective] at hcard
      exact hcard
    obtain ⟨_, hnormal⟩ := base_center Γ _ P1 hbase1
      hyp.fiveOne.P1_mem.1.2.1 hSne hcardbase
    cases hyp.fiveOne.alternative with
    | a _ hnot _ => exact (hnot hnormal).elim
    | b _ hstar =>
      exact (omega_not_normal_left S0 hyp hgen hSne hstar.1.1.1 hnormal).elim
    | c _ _ _ hnot _ _ _ _ _ _ _ _ _ => exact (hnot hnormal).elim
  · have hdact : d = Γ.act actor (Γ.coset₂ 1) := by
      simpa [Γ.act_coset₂] using hd
    have hcardbase : Nat.card (Γ.z (Γ.coset₂ 1)) = 2 := by
      rw [hdact, z_act, Subgroup.card_map_of_injective
        (MulAut.conj actor⁻¹).injective] at hcard
      exact hcard
    obtain ⟨hcenter, hnormal⟩ := base_center Γ _ P2 hbase2
      hyp.fiveOne.P2_mem.1.2.1 hSne hcardbase
    cases hyp.fiveOne.alternative with
    | a _ _ hnot => exact (hnot hnormal).elim
    | b hS hstar =>
      refine ⟨hS, ?_⟩
      have hres := pstar_residual_subnormal_in_omegaCentralizer S0 P2 (hS ▸ hstar)
      have hsub : SubnormalIn (Γ.e (Γ.coset₂ 1))
          (Subgroup.centralizer (Γ.z (Γ.coset₂ 1) : Set H)) := by
        rw [hcenter]
        change SubnormalIn (Γ.twoResidualAt (Γ.coset₂ 1)) _
        rw [Γ.twoResidualAt_def]
        change SubnormalIn (twoResidualIn (Γ.stabilizer (Γ.coset₂ 1))) _
        rw [hbase2, hS]
        exact hres
      rw [hdact]
      exact residual_transport Γ _ actor hsub
    | c _ _ _ _ hnot _ _ _ _ _ _ _ _ => exact (hnot hnormal).elim

end Stellmacher.SectionsFiveToSeven
