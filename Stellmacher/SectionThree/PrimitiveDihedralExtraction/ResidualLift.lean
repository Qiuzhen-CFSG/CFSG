module

public import Stellmacher.SectionThree.LemmaThreeFour

/-!
# Residual functoriality used in the dihedral extraction

These finite-group lemmas lift the quotient calculation in Stellmacher (3.6)
back to the ambient group. The Huppert `2`-residual commutes with surjective
maps and is idempotent. Consequently an ambient `2`-residual is itself
`2`-residual-perfect. The final lemma says that such a subgroup lies in a
commutator subgroup once this is true modulo a normal `2`-subgroup; its proof
uses the residual's minimal characterization in the intervening quotient.
-/

open BenderSuzuki.External
open Stellmacher
open scoped Pointwise

universe u

@[expose] public section

private theorem hktPResidual_characteristic'
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    (hktPResidual p G).Characteristic := by
  refine ⟨?_⟩
  intro e
  ext x
  exact (hktPResidual_invariant e x).symm

theorem hktPResidual_map_of_surjective'
    {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] {p : ℕ} [Fact p.Prime]
    (f : G →* H) (hf : Function.Surjective f) :
    (hktPResidual p G).map f = hktPResidual p H := by
  classical
  apply le_antisymm
  · let R : Subgroup H := hktPResidual p H
    have hRnormal : R.Normal := hktPResidual_normal
    let _ : R.Normal := hRnormal
    let N : Subgroup G := R.comap f
    have hNnormal : N.Normal := hRnormal.comap f
    let _ : N.Normal := hNnormal
    have hmapN : N.map f = R :=
      Subgroup.map_comap_eq_self_of_surjective hf R
    let qmap : G ⧸ N →* H ⧸ R :=
      QuotientGroup.map N R f (fun _ hx => hx)
    have hqmap_bij : Function.Bijective qmap := by
      constructor
      · intro x y hxy
        obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective N x
        obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective N y
        apply QuotientGroup.eq_iff_div_mem.mpr
        change f (a / b) ∈ R
        simpa using (QuotientGroup.eq_iff_div_mem.mp hxy)
      · intro y
        obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective R y
        obtain ⟨a, rfl⟩ := hf b
        exact ⟨QuotientGroup.mk' N a, rfl⟩
    let e : (G ⧸ N) ≃* (H ⧸ R) := MulEquiv.ofBijective qmap hqmap_bij
    have hquot : IsPGroup p (G ⧸ N) :=
      (hktPResidual_quotient_isPGroup (Q := H) (q := p)).of_equiv e.symm
    exact (Subgroup.map_mono (hktPResidual_le N hNnormal hquot)).trans
      (le_of_eq hmapN)
  · have hmapNormal : ((hktPResidual p G).map f).Normal :=
      (hktPResidual_normal (Q := G) (q := p)).map f hf
    let _ : ((hktPResidual p G).map f).Normal := hmapNormal
    let R : Subgroup G := hktPResidual p G
    let _ : R.Normal := hktPResidual_normal
    let qmap : G ⧸ R →* H ⧸ R.map f :=
      QuotientGroup.map R (R.map f) f
        (fun _ hx => Subgroup.mem_map_of_mem f hx)
    have hqmap_surj : Function.Surjective qmap := by
      intro y
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (R.map f) y
      obtain ⟨a, rfl⟩ := hf b
      exact ⟨QuotientGroup.mk' R a, rfl⟩
    have hquot : IsPGroup p (H ⧸ R.map f) :=
      IsPGroup.of_surjective
        (hG := hktPResidual_quotient_isPGroup (Q := G) (q := p))
        qmap hqmap_surj
    exact hktPResidual_le (R.map f) hmapNormal hquot

private theorem twoResidualAmbient_eq_map_hktPResidual'
    {G : Type u} [Group G] [Finite G] (L : Subgroup G) :
    twoResidualAmbient L = (hktPResidual 2 L).map L.subtype := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRnormal : (hktPResidual 2 L).Normal := hktPResidual_normal
  let _ : (hktPResidual 2 L).Normal := hRnormal
  have hconvert : twoResidualSubgroup L = hktPResidual 2 L := by
    apply le_antisymm
    · rw [twoResidualSubgroup]
      apply sInf_le
      refine ⟨hktPResidual_normal, ?_⟩
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp
        (hktPResidual_quotient_isPGroup (Q := L) (q := 2))
      exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
    · intro x hx
      rw [twoResidualSubgroup, Subgroup.mem_sInf]
      intro N hN
      let _ : N.Normal := hN.1
      apply hktPResidual_le N hN.1 ?_ hx
      rw [IsPGroup.iff_card]
      obtain ⟨n, hn⟩ := hN.2
      exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  simp [twoResidualAmbient, hconvert]

theorem map_twoResidualAmbient_of_subgroup_image
    {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (L : Subgroup G) (f : G →* H) (J : Subgroup H)
    (hmap : L.map f = J) :
    (twoResidualAmbient L).map f = twoResidualAmbient J := by
  classical
  let fL : L →* J :=
    (f.comp L.subtype).codRestrict J (fun x => by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem f x.property)
  have hfL : Function.Surjective fL := by
    intro y
    have hy : (y : H) ∈ L.map f := by simp [hmap]
    rcases hy with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    exact Subtype.ext hxy
  have hres := hktPResidual_map_of_surjective' (p := 2) fL hfL
  rw [twoResidualAmbient_eq_map_hktPResidual' L,
    twoResidualAmbient_eq_map_hktPResidual' J]
  calc
    ((hktPResidual 2 L).map L.subtype).map f =
        (hktPResidual 2 L).map (f.comp L.subtype) :=
      Subgroup.map_map (K := hktPResidual 2 L) f L.subtype
    _ = ((hktPResidual 2 L).map fL).map J.subtype := by
      rw [Subgroup.map_map]
      rfl
    _ = (hktPResidual 2 J).map J.subtype := by rw [hres]

theorem map_conjBy
    {G H : Type*} [Group G] [Group H]
    (K : Subgroup G) (f : G →* H) (x : G) :
    (K.conjBy x).map f = (K.map f).conjBy (f x) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases Subgroup.mem_map.mp hz with ⟨k, hk, rfl⟩
    refine Subgroup.mem_map.mpr ⟨f k, Subgroup.mem_map_of_mem f hk, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · rintro hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, hzy⟩
    rcases Subgroup.mem_map.mp hz with ⟨k, hk, hkz⟩
    refine ⟨x * k * x⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨k, hk, by simp [MulAut.conj_apply, mul_assoc]⟩
    · rw [map_mul, map_mul, map_inv, hkz]
      exact hzy

private theorem hktPResidual_idempotent_top
    {G : Type u} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] :
    hktPResidual p (hktPResidual p G) = ⊤ := by
  classical
  let R : Subgroup G := hktPResidual p G
  let D : Subgroup R := hktPResidual p R
  have hRnormal : R.Normal := hktPResidual_normal
  let _ : R.Normal := hRnormal
  have hDchar : D.Characteristic := hktPResidual_characteristic' p
  let _ : D.Characteristic := hDchar
  let Damb : Subgroup G := D.map R.subtype
  have hDambNormal : Damb.Normal :=
    ConjAct.normal_of_characteristic_of_normal
  let _ : Damb.Normal := hDambNormal
  have hDambR : Damb ≤ R := Subgroup.map_subtype_le D
  let qD : G →* G ⧸ Damb := QuotientGroup.mk' Damb
  let Rbar : Subgroup (G ⧸ Damb) := R.map qD
  have hRbarNormal : Rbar.Normal :=
    hRnormal.map qD (QuotientGroup.mk'_surjective Damb)
  let _ : Rbar.Normal := hRbarNormal
  let fR : R →* G ⧸ Damb := qD.comp R.subtype
  have hfRker : fR.ker = D := by
    ext x
    change qD (x : G) = 1 ↔ x ∈ D
    constructor
    · intro hx
      have hxDamb : (x : G) ∈ Damb :=
        (QuotientGroup.eq_one_iff (N := Damb) (x : G)).1 hx
      rcases hxDamb with ⟨d, hd, hdx⟩
      have : d = x := R.subtype_injective hdx
      simpa [this] using hd
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := Damb) (x : G)).2
        (Subgroup.mem_map_of_mem R.subtype hx)
  have hfRrange : fR.range = Rbar := by
    ext y
    simp [fR, Rbar, qD, MonoidHom.mem_range, Subgroup.mem_map]
  have hRbarp : IsPGroup p Rbar := by
    have hquot : IsPGroup p (R ⧸ D) := by
      simpa [D] using
        (hktPResidual_quotient_isPGroup (Q := R) (q := p))
    have himage : IsPGroup p fR.range := by
      have hkerQuot : IsPGroup p (R ⧸ fR.ker) := by
        let e : R ⧸ D ≃* R ⧸ fR.ker :=
          QuotientGroup.quotientMulEquivOfEq hfRker.symm
        exact hquot.of_equiv e
      exact hkerQuot.of_equiv (QuotientGroup.quotientKerEquivRange fR)
    rwa [hfRrange] at himage
  have hquotRbarp : IsPGroup p ((G ⧸ Damb) ⧸ Rbar) := by
    have hquotR : IsPGroup p (G ⧸ R) :=
      hktPResidual_quotient_isPGroup
    let e : ((G ⧸ Damb) ⧸ Rbar) ≃* G ⧸ R := by
      exact (QuotientGroup.quotientQuotientEquivQuotient Damb R hDambR).trans
        (QuotientGroup.quotientMulEquivOfEq (by rfl))
    exact hquotR.of_equiv e.symm
  have hquotDambp : IsPGroup p (G ⧸ Damb) :=
    hkt_isPGroup_of_normal_quotient Rbar hRbarp hquotRbarp
  have hRleDamb : R ≤ Damb :=
    hktPResidual_le Damb hDambNormal hquotDambp
  apply top_unique
  intro x _
  have hxamb : (x : G) ∈ Damb := hRleDamb x.property
  rcases hxamb with ⟨d, hd, hdx⟩
  have : d = x := R.subtype_injective hdx
  simpa [this] using hd

theorem twoResidualAmbient_has_top_twoResidual
    {G : Type u} [Group G] [Finite G] (L : Subgroup G) :
    hktPResidual 2 (twoResidualAmbient L) = ⊤ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let R : Subgroup L := hktPResidual 2 L
  have hRnormal : R.Normal := hktPResidual_normal
  let _ : R.Normal := hRnormal
  let F : Subgroup G := twoResidualAmbient L
  have hF : F = R.map L.subtype := by
    simpa [F, R] using twoResidualAmbient_eq_map_hktPResidual' L
  let e₀ : R ≃* R.map L.subtype :=
    Subgroup.equivMapOfInjective R L.subtype L.subtype_injective
  let e : R ≃* F := e₀.trans (MulEquiv.subgroupCongr hF.symm)
  have hmap : (hktPResidual 2 R).map e.toMonoidHom = hktPResidual 2 F :=
    hktPResidual_map_of_surjective' (p := 2) e.toMonoidHom e.surjective
  have hidem : hktPResidual 2 R = ⊤ := hktPResidual_idempotent_top 2
  rw [hidem, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective] at hmap
  change hktPResidual 2 F = ⊤
  exact hmap.symm

theorem residualPerfect_le_commutator_of_quotient
    {G : Type u} [Group G] [Finite G]
    (O F T : Subgroup G) (hOnormal : O.Normal)
    (hOtwo : IsPGroup 2 O)
    (hFperfect : hktPResidual 2 F = ⊤)
    (hmap : F.map (QuotientGroup.mk' O) ≤
      (⁅F, T⁆).map (QuotientGroup.mk' O)) :
    F ≤ ⁅F, T⁆ := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : O.Normal := hOnormal
  let qO : G →* G ⧸ O := QuotientGroup.mk' O
  let D : Subgroup G := ⁅F, T⁆
  have hFleDO : F ≤ D ⊔ O := by
    have hcomap : F ≤ (D.map qO).comap qO := by
      rw [← Subgroup.map_le_iff_le_comap]
      simpa [D, qO] using hmap
    simpa [qO, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using hcomap
  let H : Subgroup G := F ⊔ D
  have hHleDO : H ≤ D ⊔ O := sup_le hFleDO le_sup_left
  let DH : Subgroup H := D.subgroupOf H
  have hDleH : D ≤ H := le_sup_right
  have hDnormalH : DH.Normal := by
    simpa [H, DH, sup_comm] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := F) (N := D) (Subgroup.normalizer_commutator_ge_left F T))
  let _ : DH.Normal := hDnormalH
  let OH : Subgroup H := O.comap H.subtype
  have hOHtwo : IsPGroup 2 OH := hOtwo.comap_subtype
  let qD : H →* H ⧸ DH := QuotientGroup.mk' DH
  have hOHmap : OH.map qD = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective DH y
    have hhDO : (h : G) ∈ D ⊔ O := hHleDO h.property
    have hcoe : (↑(D ⊔ O) : Set G) = (D : Set G) * (O : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right D O
        (Subgroup.le_normalizer_of_normal : D ≤ Subgroup.normalizer O)
    change (h : G) ∈ (↑(D ⊔ O) : Set G) at hhDO
    rw [hcoe] at hhDO
    obtain ⟨d, hd, o, ho, hdo⟩ := hhDO
    have hdH : d ∈ H := hDleH hd
    have hoH : o ∈ H := by
      have heq : o = d⁻¹ * (h : G) := by rw [← hdo]; simp
      rw [heq]
      exact H.mul_mem (H.inv_mem hdH) h.property
    let dH : H := ⟨d, hdH⟩
    let oH : H := ⟨o, hoH⟩
    have hdDH : dH ∈ DH := hd
    have hoOH : oH ∈ OH := ho
    refine ⟨oH, hoOH, ?_⟩
    have hhd : h = dH * oH := by
      apply Subtype.ext
      exact hdo.symm
    rw [hhd, map_mul]
    have hdone : qD dH = 1 :=
      (QuotientGroup.eq_one_iff (N := DH) dH).2 hdDH
    rw [hdone, one_mul]
  have hquotTwo : IsPGroup 2 (H ⧸ DH) := by
    have himage : IsPGroup 2 (OH.map qD) := IsPGroup.map hOHtwo qD
    rw [hOHmap] at himage
    exact himage.of_equiv Subgroup.topEquiv
  have hFleH : F ≤ H := le_sup_left
  let fF : F →* H ⧸ DH := qD.comp (Subgroup.inclusion hFleH)
  have hRangeTwo : IsPGroup 2 fF.range := hquotTwo.to_subgroup fF.range
  have hKerQuotTwo : IsPGroup 2 (F ⧸ fF.ker) :=
    hRangeTwo.of_equiv (QuotientGroup.quotientKerEquivRange fF).symm
  have hresKer : hktPResidual 2 F ≤ fF.ker :=
    hktPResidual_le fF.ker inferInstance hKerQuotTwo
  intro x hx
  have hxker : (⟨x, hx⟩ : F) ∈ fF.ker := by
    apply hresKer
    rw [hFperfect]
    trivial
  have hqone : qD ⟨x, hFleH hx⟩ = 1 := hxker
  have hxDH : (⟨x, hFleH hx⟩ : H) ∈ DH :=
    (QuotientGroup.eq_one_iff (N := DH) _).1 hqone
  exact hxDH

end
