module

public import Stellmacher.SectionsOneToFourDefs
public import BenderSuzuki.External.Huppert.IV.Residual

/-!
# Identifying the ambient two-residual

The finite-group `p`-residual commutes with quotient maps: one inclusion uses
the quotient of a `p`-group, while the other pulls the residual of the quotient
back to the original group and applies residual minimality.  The Section 3
notation `twoResidualAmbient ⊤` is then identified with Huppert's proved
`2`-residual.  Consequently, a normal odd-prime subgroup whose quotient is a
`2`-group is the ambient two-residual; in particular this applies to a normal
complement of a Sylow `2`-subgroup.  These conversion lemmas connect
Stellmacher's notation to the general residual API used in the solvable
primitive-group proof.
-/

namespace Stellmacher.SectionThree

open BenderSuzuki.External

universe u

public theorem map_hktPResidual_quotient
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (N : Subgroup G) [N.Normal] :
    (BenderSuzuki.External.hktPResidual p G).map (QuotientGroup.mk' N) =
      BenderSuzuki.External.hktPResidual p (G ⧸ N) := by
  classical
  let R : Subgroup G := BenderSuzuki.External.hktPResidual p G
  let qN : G →* G ⧸ N := QuotientGroup.mk' N
  let Rbar : Subgroup (G ⧸ N) := R.map qN
  have hRnormal : R.Normal := BenderSuzuki.External.hktPResidual_normal
  let _ : R.Normal := hRnormal
  have hRbarNormal : Rbar.Normal :=
    hRnormal.map qN (QuotientGroup.mk'_surjective N)
  let _ : Rbar.Normal := hRbarNormal
  have hquotR : IsPGroup p (G ⧸ R) :=
    BenderSuzuki.External.hktPResidual_quotient_isPGroup
  have hquotRbar : IsPGroup p ((G ⧸ N) ⧸ Rbar) := by
    let qRbar : G ⧸ N →* (G ⧸ N) ⧸ Rbar := QuotientGroup.mk' Rbar
    let f0 : G →* (G ⧸ N) ⧸ Rbar := qRbar.comp qN
    have hRker : R ≤ f0.ker := by
      intro r hr
      change qRbar (qN r) = 1
      apply (QuotientGroup.eq_one_iff (N := Rbar) (qN r)).2
      exact Subgroup.mem_map_of_mem qN hr
    let f : G ⧸ R →* (G ⧸ N) ⧸ Rbar := QuotientGroup.lift R f0 hRker
    have hfsurj : Function.Surjective f := by
      intro y
      obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective Rbar y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
      exact ⟨QuotientGroup.mk' R g, by simp [f, f0, qRbar, qN]⟩
    exact hquotR.of_surjective f hfsurj
  apply le_antisymm
  · let Rq : Subgroup (G ⧸ N) :=
      BenderSuzuki.External.hktPResidual p (G ⧸ N)
    have hRqnormal : Rq.Normal := BenderSuzuki.External.hktPResidual_normal
    let _ : Rq.Normal := hRqnormal
    have hquotRq : IsPGroup p ((G ⧸ N) ⧸ Rq) :=
      BenderSuzuki.External.hktPResidual_quotient_isPGroup
    let qRq : G ⧸ N →* (G ⧸ N) ⧸ Rq := QuotientGroup.mk' Rq
    let f0 : G →* (G ⧸ N) ⧸ Rq := qRq.comp qN
    have hf0surj : Function.Surjective f0 :=
      (QuotientGroup.mk'_surjective Rq).comp
        (QuotientGroup.mk'_surjective N)
    let K : Subgroup G := Rq.comap qN
    have hKnormal : K.Normal := hRqnormal.comap qN
    let _ : K.Normal := hKnormal
    have hf0ker : f0.ker = K := by
      ext x
      simp [f0, K, qRq, qN, MonoidHom.mem_ker]
    let e : G ⧸ f0.ker ≃* (G ⧸ N) ⧸ Rq :=
      QuotientGroup.quotientKerEquivOfSurjective f0 hf0surj
    have hquotK : IsPGroup p (G ⧸ K) := by
      let eK : G ⧸ K ≃* G ⧸ f0.ker :=
        QuotientGroup.quotientMulEquivOfEq hf0ker.symm
      exact hquotRq.of_equiv (eK.trans e).symm
    have hRK : R ≤ K :=
      BenderSuzuki.External.hktPResidual_le K hKnormal hquotK
    change Rbar ≤ Rq
    rw [Subgroup.map_le_iff_le_comap]
    exact hRK
  · exact BenderSuzuki.External.hktPResidual_le Rbar hRbarNormal hquotRbar

public theorem twoResidualAmbient_top_eq_hktPResidual
    {Q : Type u} [Group Q] [Finite Q] :
    twoResidualAmbient (⊤ : Subgroup Q) = hktPResidual 2 Q := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · let R : Subgroup Q := hktPResidual 2 Q
    have hRnormal : R.Normal := hktPResidual_normal
    let _ : R.Normal := hRnormal
    have hRquot : IsPGroup 2 (Q ⧸ R) := hktPResidual_quotient_isPGroup
    let Rtop : Subgroup (⊤ : Subgroup Q) := R.subgroupOf ⊤
    have hRtopNormal : Rtop.Normal := hRnormal.subgroupOf ⊤
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hRquot
    have hRtopIndex : Rtop.index = 2 ^ n := by
      calc
        Rtop.index = R.relIndex ⊤ := rfl
        _ = R.index := Subgroup.relIndex_top_right R
        _ = Nat.card (Q ⧸ R) := Subgroup.index_eq_card R
        _ = 2 ^ n := hn
    have hRtop_mem : Rtop ∈
        {N : Subgroup (⊤ : Subgroup Q) |
          N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n} :=
      ⟨hRtopNormal, n, hRtopIndex⟩
    have hsInf_le : twoResidualSubgroup (⊤ : Subgroup Q) ≤ Rtop := by
      exact sInf_le hRtop_mem
    calc
      twoResidualAmbient (⊤ : Subgroup Q) =
          (twoResidualSubgroup (⊤ : Subgroup Q)).map
            (⊤ : Subgroup Q).subtype := rfl
      _ ≤ Rtop.map (⊤ : Subgroup Q).subtype := Subgroup.map_mono hsInf_le
      _ = R := Subgroup.map_subgroupOf_eq_of_le le_top
      _ = hktPResidual 2 Q := rfl
  · intro x hx
    change x ∈ (twoResidualSubgroup (⊤ : Subgroup Q)).map
      (⊤ : Subgroup Q).subtype
    refine ⟨⟨x, by simp⟩, ?_, rfl⟩
    change (⟨x, by simp⟩ : (⊤ : Subgroup Q)) ∈ sInf
      {N : Subgroup (⊤ : Subgroup Q) |
        N.Normal ∧ ∃ n : ℕ, N.index = 2 ^ n}
    rw [Subgroup.mem_sInf]
    intro R hR
    let N : Subgroup Q := R.map (⊤ : Subgroup Q).subtype
    have hNnormal : N.Normal :=
      hR.1.map (⊤ : Subgroup Q).subtype (fun x => ⟨⟨x, by simp⟩, rfl⟩)
    let _ : N.Normal := hNnormal
    obtain ⟨n, hn⟩ := hR.2
    have hN_eq : N.subgroupOf (⊤ : Subgroup Q) = R := by
      apply Subgroup.map_injective_of_ker_le
        (f := (⊤ : Subgroup Q).subtype) (H := N.subgroupOf ⊤) (K := R)
      · simp
      · simp
      · simp [N]
    have hNindex : N.index = 2 ^ n := by
      calc
        N.index = N.relIndex ⊤ := (Subgroup.relIndex_top_right N).symm
        _ = (N.subgroupOf (⊤ : Subgroup Q)).index := rfl
        _ = R.index := by rw [hN_eq]
        _ = 2 ^ n := hn
    have hquot : IsPGroup 2 (Q ⧸ N) := by
      rw [IsPGroup.iff_card]
      exact ⟨n, by simpa [← Subgroup.index_eq_card N] using hNindex⟩
    have hxN : x ∈ N := hktPResidual_le N hNnormal hquot hx
    rcases hxN with ⟨y, hy, hyx⟩
    have hy_eq : y = (⟨x, by simp⟩ : (⊤ : Subgroup Q)) := by
      exact Subtype.ext hyx
    simpa [hy_eq] using hy

public theorem twoResidualAmbient_top_eq_of_normal_pGroup_quotient_two
    {Q : Type u} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (K : Subgroup Q) (hKnormal : K.Normal) (hKp : IsPGroup p K)
    (hquot2 : let _ : K.Normal := hKnormal; IsPGroup 2 (Q ⧸ K)) :
    twoResidualAmbient (⊤ : Subgroup Q) = K := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : K.Normal := hKnormal
  rw [twoResidualAmbient_top_eq_hktPResidual]
  apply le_antisymm
  · exact hktPResidual_le K hKnormal hquot2
  · let R : Subgroup Q := hktPResidual 2 Q
    have hRnormal : R.Normal := hktPResidual_normal
    let _ : R.Normal := hRnormal
    let qR : Q →* Q ⧸ R := QuotientGroup.mk' R
    let KR : Subgroup (Q ⧸ R) := K.map qR
    have hKRp : IsPGroup p KR := IsPGroup.map hKp qR
    have hQbar2 : IsPGroup 2 (Q ⧸ R) := hktPResidual_quotient_isPGroup
    have hKR2 : IsPGroup 2 KR := hQbar2.to_subgroup KR
    have hdisj : Disjoint KR KR :=
      IsPGroup.disjoint_of_ne p 2 hp2 KR KR hKRp hKR2
    have hKRbot : KR = ⊥ := disjoint_self.mp hdisj
    change K ≤ R
    rw [← QuotientGroup.ker_mk' R]
    exact (Subgroup.map_eq_bot_iff K).mp hKRbot

public theorem twoResidualAmbient_top_eq_of_normal_complement_sylow_two
    {Q : Type u} [Group Q] [Finite Q]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (K T : Subgroup Q) (Tₛ : Sylow 2 Q)
    (hT : (Tₛ : Subgroup Q) = T)
    (hKnormal : K.Normal) (hKp : IsPGroup p K)
    (hKTtop : K ⊔ T = ⊤) :
    twoResidualAmbient (⊤ : Subgroup Q) = K := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : K.Normal := hKnormal
  let qK : Q →* Q ⧸ K := QuotientGroup.mk' K
  have hmapT : T.map qK = ⊤ := by
    have hmapSup := congrArg (fun H : Subgroup Q => H.map qK) hKTtop
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self,
      bot_sup_eq, Subgroup.map_top_of_surjective qK
        (QuotientGroup.mk'_surjective K)] at hmapSup
    exact hmapSup
  have hTp : IsPGroup 2 T := by rw [← hT]; exact Tₛ.isPGroup'
  have hmapTp : IsPGroup 2 (T.map qK) := IsPGroup.map hTp qK
  have htop2 : IsPGroup 2 (⊤ : Subgroup (Q ⧸ K)) := by
    rw [hmapT] at hmapTp
    exact hmapTp
  have hquot2 : IsPGroup 2 (Q ⧸ K) :=
    htop2.of_equiv Subgroup.topEquiv
  exact twoResidualAmbient_top_eq_of_normal_pGroup_quotient_two
    hp hp2 K hKnormal hKp hquot2

end Stellmacher.SectionThree
