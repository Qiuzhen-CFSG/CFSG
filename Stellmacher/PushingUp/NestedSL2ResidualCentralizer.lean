module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Stellmacher.SectionOne.SL2ProductNormalizerRigidity
public import Stellmacher.TwoResidualSylowSupplement

/-!
# Residual centralization from the nested `SL₂(2)` quotient

This module isolates the graph-free finite-group step used in Stellmacher,
*Pushing up* (1986), proof of (3.1), journal p. 14.  Let `Q = O₂(G)` and
suppose `(G / Q) / Φ(G / Q)` is `SL₂(2)`.  An involution outside `Q`
which centralizes `Q` forces `O²(G)` to centralize `Q`.

Indeed, `O₂(G / Q) = 1`, so `Φ(G / Q)` has odd order and the involution
remains nontrivial in the nested quotient.  The normal image of `C_G(Q)`
there contains a Sylow involution.  Its normal closure is the whole
six-element `SL₂(2)`, and Frattini nongeneration then gives
`C_G(Q) Q = G`.  Thus `G / C_G(Q)` is a 2-group, so the defining intersection
for `O²(G)` lies in `C_G(Q)`.  The public conclusion is the resulting
commutator equality; quotient, Sylow, and residual-intersection lemmas remain
private implementation details.
-/

namespace Stellmacher.PushingUp

universe u

private theorem pCore_quotient_pCore_eq_bot
    {G : Type u} [Group G] :
    pCore 2 (G ⧸ pCore 2 G) = ⊥ := by
  have hmap := pCore_map_mk'_eq_of_normal_isPGroup
    (G := G) (p := 2) (pCore 2 G)
      (pCore_isPGroup (p := 2) (G := G))
  rw [← hmap]
  exact QuotientGroup.map_mk'_self (N := pCore 2 G)

private theorem frattini_odd_of_core_eq_bot
    {G : Type u} [Group G] [Finite G] (hcore : pCore 2 G = ⊥) :
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

private theorem sylow_card_two_of_isSL2Two
    {G : Type u} [Group G] [Finite G]
    (hG : IsSL2Two G) (S : Sylow 2 G) : Nat.card S = 2 := by
  have hGcard : Nat.card G = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card hG
  rw [S.card_eq_multiplicity, hGcard]
  have hf6 : Nat.factorization 6 2 = 1 := by
    change Nat.factorization (3 * 2) 2 = 1
    rw [Nat.factorization_mul (by decide) (by decide)]
    norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
  simp [hf6]

private theorem normalClosure_sylow_eq_top_of_isSL2Two
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G) (hG : IsSL2Two G) :
    Subgroup.normalClosure ((S : Subgroup G) : Set G) = ⊤ := by
  let N := Subgroup.normalClosure ((S : Subgroup G) : Set G)
  have hsquare (x : G) (hx : x ^ 2 = 1) : x ∈ N := by
    have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
      (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hx).isPGroup 2 _
    obtain ⟨T, hT⟩ := hxp.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
    have hxS : g * x * g⁻¹ ∈ (S : Subgroup G) := by
      rw [← hg]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom
        (hT (Subgroup.mem_zpowers x))
    have hconjN : g * x * g⁻¹ ∈ N := Subgroup.le_normalClosure hxS
    have hback := (inferInstance : N.Normal).conj_mem
      (g * x * g⁻¹) hconjN g⁻¹
    simpa [mul_assoc] using hback
  apply top_unique
  intro x _hx
  obtain ⟨a, b, ha, hb, hab⟩ := SectionOne.sl2_involution_products hG x
  rw [hab]
  exact N.mul_mem (hsquare a ha) (hsquare b hb)

private theorem normal_eq_top_of_isSL2Two_of_mem_involution
    {G : Type u} [Group G] [Finite G]
    (hG : IsSL2Two G) (N : Subgroup G) [N.Normal]
    {x : G} (hxN : x ∈ N) (hxne : x ≠ 1) (hxsq : x ^ 2 = 1) :
    N = ⊤ := by
  have hxorder : orderOf x = 2 := orderOf_eq_prime hxsq hxne
  have hxcard : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers, hxorder]
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (p := 2) (n := 1) (by simpa using hxcard)
  obtain ⟨S, hxS⟩ := hxp.exists_le_sylow
  have hScard : Nat.card S = 2 := sylow_card_two_of_isSL2Two hG S
  have hcardGe : Nat.card S ≤ Nat.card (Subgroup.zpowers x) := by
    rw [hScard, hxcard]
  have hzpowersS : Subgroup.zpowers x = (S : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hxS hcardGe
  have hSleN : (S : Subgroup G) ≤ N := by
    rw [← hzpowersS]
    exact Subgroup.zpowers_le.mpr hxN
  have hclosureLe :
      Subgroup.normalClosure ((S : Subgroup G) : Set G) ≤ N :=
    Subgroup.normalClosure_le_normal hSleN
  apply top_unique
  rw [← normalClosure_sylow_eq_top_of_isSL2Two S hG]
  exact hclosureLe

private theorem twoResidualAmbient_top_le_of_quotient_two
    {G : Type u} [Group G] [Finite G]
    (C : Subgroup G) (hCnormal : C.Normal)
    (hquot : let _ : C.Normal := hCnormal; IsPGroup 2 (G ⧸ C)) :
    twoResidualAmbient (⊤ : Subgroup G) ≤ C := by
  let _ : C.Normal := hCnormal
  let Ctop : Subgroup (⊤ : Subgroup G) := C.subgroupOf ⊤
  have hCtopNormal : Ctop.Normal := hCnormal.subgroupOf ⊤
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hquot
  have hCtopIndex : Ctop.index = 2 ^ n := by
    calc
      Ctop.index = C.relIndex ⊤ := rfl
      _ = C.index := Subgroup.relIndex_top_right C
      _ = Nat.card (G ⧸ C) := Subgroup.index_eq_card C
      _ = 2 ^ n := hn
  have hCtop_mem : Ctop ∈
      {N : Subgroup (⊤ : Subgroup G) |
        N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n} :=
    ⟨hCtopNormal, n, hCtopIndex⟩
  have hsInf_le : twoResidualSubgroup (⊤ : Subgroup G) ≤ Ctop :=
    sInf_le hCtop_mem
  calc
    twoResidualAmbient (⊤ : Subgroup G) =
        (twoResidualSubgroup (⊤ : Subgroup G)).map
          (⊤ : Subgroup G).subtype := rfl
    _ ≤ Ctop.map (⊤ : Subgroup G).subtype := Subgroup.map_mono hsInf_le
    _ = C := Subgroup.map_subgroupOf_eq_of_le le_top

/-- If the nested quotient by the two-core and its Frattini subgroup is
`SL₂(2)`, an involution outside the two-core which centralizes that core
forces the two-residual to centralize the core.  This is the graph-free
centralization step in Stellmacher, *Pushing up* (1986), (3.1). -/
public theorem residual_centralizes_twoCore_of_nestedSL2Two
    {G : Type u} [Group G] [Finite G]
    (z : G)
    (hzQ : z ∉ pCore 2 G)
    (hzC : z ∈ Subgroup.centralizer (pCore 2 G : Set G))
    (hzsq : z ^ 2 = 1)
    (hA : IsSL2Two
      ((G ⧸ pCore 2 G) ⧸ frattini (G ⧸ pCore 2 G))) :
    ⁅pCore 2 G, twoResidualAmbient (⊤ : Subgroup G)⁆ = ⊥ := by
  classical
  let Q : Subgroup G := pCore 2 G
  let X := G ⧸ Q
  let qQ : G →* X := QuotientGroup.mk' Q
  let Φ : Subgroup X := frattini X
  let Y := X ⧸ Φ
  let qΦ : X →* Y := QuotientGroup.mk' Φ
  let C : Subgroup G := Subgroup.centralizer (Q : Set G)
  let _ : Q.Normal := pCore_normal
  let _ : C.Normal := Subgroup.normal_centralizer
  let N : Subgroup X := C.map qQ
  have hNnormal : N.Normal :=
    (inferInstance : C.Normal).map qQ (QuotientGroup.mk'_surjective Q)
  let _ : N.Normal := hNnormal
  let K : Subgroup Y := N.map qΦ
  have hKnormal : K.Normal :=
    hNnormal.map qΦ (QuotientGroup.mk'_surjective Φ)
  let _ : K.Normal := hKnormal
  have hcoreX : pCore 2 X = ⊥ := by
    simpa [X, Q] using (pCore_quotient_pCore_eq_bot (G := G))
  have hΦodd : ¬ 2 ∣ Nat.card Φ := by
    simpa [Φ] using frattini_odd_of_core_eq_bot hcoreX
  have hzXne : qQ z ≠ 1 := by
    intro hz
    exact hzQ ((QuotientGroup.eq_one_iff (N := Q) z).mp hz)
  have hzYne : qΦ (qQ z) ≠ 1 := by
    intro hz
    have hzΦ : qQ z ∈ Φ :=
      (QuotientGroup.eq_one_iff (N := Φ) (qQ z)).mp hz
    let zΦ : Φ := ⟨qQ z, hzΦ⟩
    have hzΦne : zΦ ≠ 1 := by
      intro h
      exact hzXne (congrArg Subtype.val h)
    have hzΦsq : zΦ ^ 2 = 1 := by
      apply Subtype.ext
      simpa [zΦ] using congrArg qQ hzsq
    have hzΦorder : orderOf zΦ = 2 :=
      orderOf_eq_prime hzΦsq hzΦne
    have hdvd : orderOf zΦ ∣ Nat.card Φ := orderOf_dvd_natCard zΦ
    exact hΦodd (by simpa only [hzΦorder] using hdvd)
  have hzK : qΦ (qQ z) ∈ K := by
    apply Subgroup.mem_map_of_mem qΦ
    apply Subgroup.mem_map_of_mem qQ
    exact hzC
  have hzYsq : (qΦ (qQ z)) ^ 2 = 1 := by
    simpa using congrArg (qΦ.comp qQ) hzsq
  have hY : IsSL2Two Y := by
    simpa [Y, X, Q, Φ] using hA
  have hKtop : K = ⊤ :=
    normal_eq_top_of_isSL2Two_of_mem_involution
      hY K hzK hzYne hzYsq
  have hcomapK := congrArg (Subgroup.comap qΦ) hKtop
  have hNsupΦ : N ⊔ Φ = ⊤ := by
    dsimp only [K, qΦ] at hcomapK
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hcomapK
    exact hcomapK
  have hNtop : N = ⊤ := frattini_nongenerating (by
    simpa [Φ] using hNsupΦ)
  have hcomapN := congrArg (Subgroup.comap qQ) hNtop
  have hCsupQ : C ⊔ Q = ⊤ := by
    dsimp only [N, qQ] at hcomapN
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hcomapN
    exact hcomapN
  let qC : G →* G ⧸ C := QuotientGroup.mk' C
  have hQmapTop : Q.map qC = ⊤ := by
    have hmap := congrArg (Subgroup.map qC) hCsupQ
    simpa [qC, Subgroup.map_sup,
      Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk',
      Subgroup.map_top_of_surjective qC (QuotientGroup.mk'_surjective C)] using hmap
  have htopTwo : IsPGroup 2 (⊤ : Subgroup (G ⧸ C)) := by
    rw [← hQmapTop]
    exact (pCore_isPGroup (p := 2) (G := G)).map qC
  have hquotTwo : IsPGroup 2 (G ⧸ C) :=
    htopTwo.of_equiv Subgroup.topEquiv
  have hResidualC : twoResidualAmbient (⊤ : Subgroup G) ≤ C :=
    twoResidualAmbient_top_le_of_quotient_two C
      (inferInstance : C.Normal) hquotTwo
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Subgroup.le_centralizer_iff.mp hResidualC

end Stellmacher.PushingUp
