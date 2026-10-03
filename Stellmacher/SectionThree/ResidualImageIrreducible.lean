module

public import Stellmacher.SectionThree.LemmaThreeThree
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift

/-!
# Irreducibility of an elementary residual image

This module packages the consequence of Stellmacher (3.3)(a--c) used in the
last applications of (1.7) in the proof of (3.9).  If the image of the
`2`-residual of a solvable member of `PSet` is a nontrivial elementary abelian
`3`-group, then it is irreducible under the image of the distinguished Sylow
subgroup.

The proof first factors the residual map modulo `O₂(P)`.  Part (3.3)(a) says
that the resulting residual is a group for some odd prime `p`; its nontrivial
elementary abelian `3`-image forces `p = 3`.  The target has trivial Frattini
subgroup, so (3.3)(c) shows that the normal-core layer of the source residual
lies in the map's kernel.  The map therefore descends through the normal-core
quotient from (3.3)(b).  Irreducibility there makes its kernel trivial, and
pulling back an invariant subgroup proves irreducibility of the target image.

Source: B. Stellmacher, *An Application of the Amalgam Method: The 2-Local
Structure of N-Groups of Characteristic 2 Type*, Journal of Algebra 190
(1997), Lemma (3.3), pp. 21--22, as used in Lemma (3.9), p. 24; see
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionThree

open BenderSuzuki.External

universe u v

private theorem twoResidualSubgroup_eq_hktPResidual_image
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) :
    twoResidualSubgroup P = hktPResidual 2 P := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnormal : (hktPResidual 2 P).Normal := hktPResidual_normal
  let _ : (hktPResidual 2 P).Normal := hnormal
  apply le_antisymm
  · rw [twoResidualSubgroup]
    apply sInf_le
    refine ⟨hktPResidual_normal, ?_⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp
      (hktPResidual_quotient_isPGroup (Q := P) (q := 2))
    exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  · intro x hx
    rw [twoResidualSubgroup, Subgroup.mem_sInf]
    intro N hN
    let _ : N.Normal := hN.1
    apply hktPResidual_le N hN.1 ?_ hx
    rw [IsPGroup.iff_card]
    obtain ⟨n, hn⟩ := hN.2
    exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩

/-- A nontrivial elementary abelian `3`-image of the residual in a solvable
member of `PSet ⊤ S` is irreducible under the image of `S`. -/
public theorem pSet_residual_image_irreducible
    {G : Type u} {X : Type v} [Group G] [Finite G] [Group X] [Finite X]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) (f : P →* X)
    (R : Subgroup X)
    (hR : (twoResidualSubgroup P).map f = R)
    (hRne : R ≠ ⊥) (hRelem : IsElementaryAbelian 3 R) :
    IsIrreducibleSection ((S.subgroupOf P).map f) ⊥ R := by
  classical
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let U : Subgroup P := twoResidualSubgroup P
  let fU0 : U →* X := f.comp U.subtype
  let fU : U →* R := fU0.codRestrict R (fun x => by
    rw [← hR]
    exact Subgroup.mem_map_of_mem f x.property)
  have hfU : Function.Surjective fU := by
    intro r
    have hr : (r : X) ∈ (twoResidualSubgroup P).map f := by
      rw [hR]
      exact r.property
    rcases hr with ⟨u, hu, hur⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    exact Subtype.ext hur
  have hRthree : IsPGroup 3 R := by
    let _ : IsElementaryAbelian 3 R := hRelem
    exact IsElementaryAbelian.isPGroup 3 R
  rcases hP.2 with ⟨B, hBmax, hSB, hBuniq⟩
  have hSP : S ≤ P := by
    obtain ⟨T, hT⟩ := hP.1.2.1
    rw [← hT]
    exact Subgroup.map_subtype_le (T : Subgroup P)
  have hSsubB : S.subgroupOf P ≤ B := by
    intro s hs
    have hsS : (s : G) ∈ S := hs
    obtain ⟨b, hb, hbs⟩ := hSB hsS
    have hbeq : b = s := P.subtype_injective hbs
    simpa [← hbeq] using hb
  let P₀ : Subgroup P := B.normalCore
  have hP₀ : P₀ ≤ B ∧ P₀.Normal ∧
      ∀ N : Subgroup P, N.Normal → N ≤ B → N ≤ P₀ := by
    refine ⟨B.normalCore_le, inferInstance, ?_⟩
    intro N hN hNB
    exact (@Subgroup.normal_le_normalCore P _ B N hN).2 hNB
  have hB : IsCoatom B ∧ S.subgroupOf P ≤ B ∧
      ∀ B' : Subgroup P, IsCoatom B' → S.subgroupOf P ≤ B' → B' = B := by
    refine ⟨hBmax, hSsubB, ?_⟩
    intro B' hB'max hSB'
    apply hBuniq B' hB'max
    intro s hs
    exact Subgroup.mem_map.mpr
      ⟨⟨s, hSP hs⟩, hSB' (show (⟨s, hSP hs⟩ : P) ∈
        S.subgroupOf P from hs), rfl⟩
  have h33 := lemma_three_three S h P hP B P₀ hB hP₀ hsolv
  let O : Subgroup P := pCore 2 P
  let _ : O.Normal := inferInstance
  let qO : P →* P ⧸ O := QuotientGroup.mk' O
  let Ubar : Subgroup (P ⧸ O) :=
    twoResidualAmbient (⊤ : Subgroup (P ⧸ O))
  have hUmapO : U.map qO = Ubar := by
    rw [show U = hktPResidual 2 P from
      twoResidualSubgroup_eq_hktPResidual_image P]
    rw [map_hktPResidual_quotient 2 O]
    exact twoResidualAmbient_top_eq_hktPResidual.symm
  let qU : U →* Ubar :=
    (qO.comp U.subtype).codRestrict Ubar (fun x => by
      rw [← hUmapO]
      exact Subgroup.mem_map_of_mem qO x.property)
  have hqU : Function.Surjective qU := by
    intro y
    have hy : (y : P ⧸ O) ∈ U.map qO := by
      rw [hUmapO]
      exact y.property
    rcases hy with ⟨u, hu, huy⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    exact Subtype.ext huy
  let OU : Subgroup U := O.comap U.subtype
  have hOUtwo : IsPGroup 2 OU :=
    (pCore_isPGroup (p := 2) (G := P)).comap_of_injective
      U.subtype U.subtype_injective
  have hOUmapTwo : IsPGroup 2 (OU.map fU) := IsPGroup.map hOUtwo fU
  have hOUmapThree : IsPGroup 3 (OU.map fU) :=
    hRthree.to_subgroup (OU.map fU)
  have hOUmapBot : OU.map fU = ⊥ := by
    exact disjoint_self.mp
      (IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ hOUmapTwo hOUmapThree)
  have hkerqU : qU.ker = OU := by
    ext x
    simp [qU, OU, qO, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hkerqUfU : qU.ker ≤ fU.ker := by
    rw [hkerqU]
    exact (Subgroup.map_eq_bot_iff OU).mp hOUmapBot
  let eO : Ubar →* R := qU.liftOfSurjective hqU ⟨fU, hkerqUfU⟩
  have heO_comp (x : U) : eO (qU x) = fU x := by
    exact qU.liftOfRightInverse_comp_apply
      (Function.surjInv hqU) (Function.rightInverse_surjInv hqU)
      ⟨fU, hkerqUfU⟩ x
  have heOsurj : Function.Surjective eO := by
    intro r
    obtain ⟨u, rfl⟩ := hfU r
    exact ⟨qU u, heO_comp u⟩
  obtain ⟨p, hp, hpodd, hUbarp⟩ := h33.part_a
  let _ : Fact p.Prime := ⟨hp⟩
  have hRp : IsPGroup p R := hUbarp.of_surjective eO heOsurj
  have hp3 : p = 3 := by
    by_contra hp3
    have hdisj : Disjoint R R :=
      IsPGroup.disjoint_of_ne p 3 hp3 R R hRp hRthree
    exact hRne (disjoint_self.mp hdisj)
  subst p
  have hPhiUbarKer : frattini Ubar ≤ eO.ker := by
    have hPhiMap : frattini Ubar ≤ (frattini R).comap eO :=
      frattini_le_comap_frattini_of_surjective heOsurj
    have hPhiR : frattini R = ⊥ := by
      let _ : Fact (IsPGroup 3 R) := ⟨hRthree⟩
      let _ : IsElementaryAbelian 3 R := hRelem
      exact frattini_eq_bot_of_isElementaryAbelian (R := R) (p := 3)
    simpa [hPhiR] using hPhiMap
  have hP₀capUKer : P₀.comap U.subtype ≤ fU.ker := by
    intro x hx
    have hqOx : qO (x : P) ∈ P₀.map qO :=
      Subgroup.mem_map_of_mem qO hx
    have hP₀bar : P₀.map qO = frattiniAmbient Ubar := by
      simpa [qO, Ubar, O] using h33.part_c
    rw [hP₀bar] at hqOx
    rcases hqOx with ⟨z, hz, hzx⟩
    have hqUeq : qU x = z := Subtype.ext hzx.symm
    rw [MonoidHom.mem_ker]
    rw [← heO_comp x, hqUeq]
    exact MonoidHom.mem_ker.mp (hPhiUbarKer hz)
  let _ : P₀.Normal := hP₀.2.1
  let q₀ : P →* P ⧸ P₀ := QuotientGroup.mk' P₀
  let K : Subgroup (P ⧸ P₀) :=
    twoResidualAmbient (⊤ : Subgroup (P ⧸ P₀))
  have hUmap₀ : U.map q₀ = K := by
    rw [show U = hktPResidual 2 P from
      twoResidualSubgroup_eq_hktPResidual_image P]
    rw [map_hktPResidual_quotient 2 P₀]
    exact twoResidualAmbient_top_eq_hktPResidual.symm
  let qU₀ : U →* K :=
    (q₀.comp U.subtype).codRestrict K (fun x => by
      rw [← hUmap₀]
      exact Subgroup.mem_map_of_mem q₀ x.property)
  have hqU₀ : Function.Surjective qU₀ := by
    intro y
    have hy : (y : P ⧸ P₀) ∈ U.map q₀ := by
      rw [hUmap₀]
      exact y.property
    rcases hy with ⟨u, hu, huy⟩
    refine ⟨⟨u, hu⟩, ?_⟩
    exact Subtype.ext huy
  have hkerqU₀ : qU₀.ker = P₀.comap U.subtype := by
    ext x
    simp [qU₀, q₀, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hkerqU₀fU : qU₀.ker ≤ fU.ker := by
    rw [hkerqU₀]
    exact hP₀capUKer
  let e : K →* R := qU₀.liftOfSurjective hqU₀ ⟨fU, hkerqU₀fU⟩
  have he_comp (x : U) : e (qU₀ x) = fU x := by
    exact qU₀.liftOfRightInverse_comp_apply
      (Function.surjInv hqU₀) (Function.rightInverse_surjInv hqU₀)
      ⟨fU, hkerqU₀fU⟩ x
  have hesurj : Function.Surjective e := by
    intro r
    obtain ⟨u, rfl⟩ := hfU r
    exact ⟨qU₀ u, he_comp u⟩
  let Tbar : Subgroup (P ⧸ P₀) := (S.subgroupOf P).map q₀
  have hirred : IsIrreducibleSection Tbar ⊥ K := by
    rcases h33.part_b with ⟨hP₀normal, hsec⟩
    simpa [Tbar, q₀, K] using hsec
  have hUnormal : U.Normal := by
    rw [show U = hktPResidual 2 P from
      twoResidualSubgroup_eq_hktPResidual_image P]
    exact hktPResidual_normal
  let kerbar : Subgroup (P ⧸ P₀) := e.ker.map K.subtype
  have hkerbarK : kerbar ≤ K := Subgroup.map_subtype_le e.ker
  have hkerbarInv : IsConjugateInvariantBy kerbar Tbar := by
    intro t a ha
    rcases t.property with ⟨s, hsS, hst⟩
    rcases ha with ⟨k, hk, hka⟩
    obtain ⟨u, huk⟩ := hqU₀ k
    let usu : U := ⟨(s : P) * (u : P) * (s : P)⁻¹,
      hUnormal.conj_mem u u.property s⟩
    have husuKer : qU₀ usu ∈ e.ker := by
      rw [MonoidHom.mem_ker, he_comp]
      apply Subtype.ext
      change f ((s : P) * (u : P) * (s : P)⁻¹) = 1
      rw [map_mul, map_mul, map_inv]
      have hfu : f (u : P) = 1 := by
        have hek : e k = 1 := MonoidHom.mem_ker.mp hk
        rw [← huk, he_comp] at hek
        exact congrArg Subtype.val hek
      simp [hfu]
    refine ⟨qU₀ usu, husuKer, ?_⟩
    change (q₀ (usu : U) : P ⧸ P₀) =
      (t : P ⧸ P₀) * a * (t : P ⧸ P₀)⁻¹
    rw [← hka, ← huk]
    change q₀ ((s : P) * (u : P) * (s : P)⁻¹) =
      (t : P ⧸ P₀) * q₀ (u : P) * (t : P ⧸ P₀)⁻¹
    rw [map_mul, map_mul, map_inv, hst]
  have hkerbarBot : kerbar = ⊥ := by
    rcases hirred with ⟨_, _, hirred'⟩
    rcases hirred' kerbar bot_le hkerbarK hkerbarInv with hbot | htop
    · exact hbot
    · exfalso
      apply hRne
      apply bot_unique
      intro r hr
      obtain ⟨k, hk⟩ := hesurj ⟨r, hr⟩
      have hkbar : (k : P ⧸ P₀) ∈ kerbar := by
        rw [htop]
        exact k.property
      rcases hkbar with ⟨z, hz, hzk⟩
      have hze : e z = 1 := MonoidHom.mem_ker.mp hz
      have : z = k := K.subtype_injective hzk
      rw [Subgroup.mem_bot]
      calc
        r = (e k : R) := (congrArg Subtype.val hk).symm
        _ = 1 := congrArg Subtype.val (by simpa [this] using hze)
  have heinj : Function.Injective e := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply (Subgroup.map_eq_bot_iff_of_injective e.ker K.subtype_injective).mp
    exact hkerbarBot
  refine ⟨bot_le, ?_, ?_⟩
  · intro hbotR
    exact hRne hbotR.symm
  · intro A _hbotA hAR hAinv
    let AR : Subgroup R := A.subgroupOf R
    let AK : Subgroup K := AR.comap e
    let Abar : Subgroup (P ⧸ P₀) := AK.map K.subtype
    have hAbarK : Abar ≤ K := Subgroup.map_subtype_le AK
    have hAbarInv : IsConjugateInvariantBy Abar Tbar := by
      intro t a ha
      rcases t.property with ⟨s, hsS, hst⟩
      rcases ha with ⟨k, hk, hka⟩
      obtain ⟨u, huk⟩ := hqU₀ k
      let usu : U := ⟨(s : P) * (u : P) * (s : P)⁻¹,
        hUnormal.conj_mem u u.property s⟩
      have hfuA : f (u : P) ∈ A := by
        change (e k : X) ∈ A at hk
        rw [← huk, he_comp] at hk
        exact hk
      have husuAK : qU₀ usu ∈ AK := by
        change (e (qU₀ usu) : X) ∈ A
        rw [he_comp]
        change f ((s : P) * (u : P) * (s : P)⁻¹) ∈ A
        rw [map_mul, map_mul, map_inv]
        exact hAinv
          ⟨f (s : P), Subgroup.mem_map_of_mem f hsS⟩
          (f (u : P)) hfuA
      refine ⟨qU₀ usu, husuAK, ?_⟩
      change (q₀ (usu : U) : P ⧸ P₀) =
        (t : P ⧸ P₀) * a * (t : P ⧸ P₀)⁻¹
      rw [← hka, ← huk]
      change q₀ ((s : P) * (u : P) * (s : P)⁻¹) =
        (t : P ⧸ P₀) * q₀ (u : P) * (t : P ⧸ P₀)⁻¹
      rw [map_mul, map_mul, map_inv, hst]
    rcases hirred with ⟨_, _, hirred'⟩
    rcases hirred' Abar bot_le hAbarK hAbarInv with hAbarBot | hAbarTop
    · have hAKbot : AK = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective AK K.subtype_injective).mp
          hAbarBot
      left
      apply bot_unique
      intro x hx
      have hxR : x ∈ R := hAR hx
      obtain ⟨k, hk⟩ := hesurj ⟨x, hxR⟩
      have hkAK : k ∈ AK := by
        change (e k : X) ∈ A
        rw [hk]
        exact hx
      rw [hAKbot] at hkAK
      have hkone : k = 1 := by simpa using hkAK
      rw [Subgroup.mem_bot]
      calc
        x = (e k : R) := (congrArg Subtype.val hk).symm
        _ = ((1 : R) : X) := congrArg Subtype.val (by simp [hkone])
        _ = 1 := rfl
    · have hAKtop : AK = ⊤ := by
        apply Subgroup.map_injective K.subtype_injective
        change Abar = (⊤ : Subgroup K).map K.subtype
        rw [hAbarTop]
        simpa [MonoidHom.range_eq_map] using
          (Subgroup.range_subtype (H := K)).symm
      right
      apply le_antisymm hAR
      intro x hxR
      obtain ⟨k, hk⟩ := hesurj ⟨x, hxR⟩
      have hkAK : k ∈ AK := by rw [hAKtop]; trivial
      change (e k : X) ∈ A at hkAK
      rwa [hk] at hkAK

end Stellmacher.SectionThree
