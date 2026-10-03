module

public import Stellmacher.SectionThree.LemmaThreeEightCore

/-!
# The barred 2-core intersection in Stellmacher (3.9)

Let `C ≤ N ≤ H` be normal in `H`, with `N` maximal subject to avoiding the
two local 2-residuals.  If `R/C = O₂(H/C)`, then `(N ⊔ R)/N` is a 2-group.
This is proved by comparing relative indices through `H → H/C`.  Residual
idempotence then shows that `N ⊔ R` still avoids both residuals, so maximality
forces `R ≤ N`.  Consequently an element of the image of `S` lying in
`O₂(H/C)` lifts to `S ⊓ N ≤ C` and is trivial.

This is the quotient-core assertion `\bar S ∩ O₂(\bar H)=1` used on
journal p. 24 in the proof of Stellmacher (3.9), as transcribed in
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionThree

open BenderSuzuki.External

universe u

private theorem core_preimage_extension_isPGroup_39
    {H : Type u} [Group H] [Finite H]
    (C N : Subgroup H) (hCN : C ≤ N)
    (hCnormal : C.Normal) (hNnormal : N.Normal) :
    letI : C.Normal := hCnormal
    let q : H →* H ⧸ C := QuotientGroup.mk' C
    let R : Subgroup H := (pCore 2 (H ⧸ C)).comap q
    let K : Subgroup H := N ⊔ R
    letI : (N.subgroupOf K).Normal := by
      dsimp [K]
      exact Subgroup.Normal.subgroupOf hNnormal (N ⊔ R)
    IsPGroup 2 (K ⧸ N.subgroupOf K) := by
  classical
  let _ : C.Normal := hCnormal
  let _ : N.Normal := hNnormal
  let q : H →* H ⧸ C := QuotientGroup.mk' C
  let O : Subgroup (H ⧸ C) := pCore 2 (H ⧸ C)
  let R : Subgroup H := O.comap q
  let K : Subgroup H := N ⊔ R
  have hCK : C ≤ K := hCN.trans le_sup_left
  have hNnormalK : (N.subgroupOf K).Normal :=
    Subgroup.Normal.subgroupOf hNnormal K
  let _ : (N.subgroupOf K).Normal := hNnormalK
  have hker : q.ker = C := QuotientGroup.ker_mk' C
  have hmapR : R.map q = O := by
    exact Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective C) O
  have hmapK : K.map q = N.map q ⊔ O := by
    simp [K, Subgroup.map_sup, hmapR]
  have hNbarNormal : (N.map q).Normal :=
    hNnormal.map q (QuotientGroup.mk'_surjective C)
  let _ : (N.map q).Normal := hNbarNormal
  let D : Subgroup O := (N.map q).subgroupOf O
  have hDnormal : D.Normal :=
    Subgroup.Normal.subgroupOf hNbarNormal O
  let _ : D.Normal := hDnormal
  have hOquot : IsPGroup 2 (O ⧸ D) :=
    (pCore_isPGroup (p := 2) (G := H ⧸ C)).to_quotient D
  rw [IsPGroup.iff_card] at hOquot ⊢
  obtain ⟨n, hn⟩ := hOquot
  refine ⟨n, ?_⟩
  rw [← Subgroup.index_eq_card] at hn
  rw [← Subgroup.index_eq_card]
  change N.relIndex K = _
  change (N.map q).relIndex O = _ at hn
  rw [← hn, ← Subgroup.relIndex_sup_left O (N.map q), ← hmapK]
  rw [Subgroup.relIndex_map_map, hker, sup_of_le_left hCN,
    sup_of_le_left hCK]

private theorem ambient_core_preimage_extension_isPGroup_39
    {G : Type u} [Group G] [Finite G]
    (H N : Subgroup G) (C : Subgroup H)
    (hNH : N ≤ H) (hCN : C.map H.subtype ≤ N)
    (hCnormal : C.Normal)
    (hNnormal : (N.subgroupOf H).Normal) :
    letI : C.Normal := hCnormal
    let q : H →* H ⧸ C := QuotientGroup.mk' C
    let R : Subgroup H := (pCore 2 (H ⧸ C)).comap q
    let Ramb : Subgroup G := R.map H.subtype
    let K : Subgroup G := N ⊔ Ramb
    letI : (N.subgroupOf K).Normal := by
      apply (Subgroup.normal_subgroupOf_iff_le_normalizer
        (le_sup_left : N ≤ N ⊔ Ramb)).mpr
      exact (sup_le hNH (Subgroup.map_subtype_le R)).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hNnormal)
    IsPGroup 2 (K ⧸ N.subgroupOf K) := by
  classical
  let CH : Subgroup H := C
  let NH : Subgroup H := N.subgroupOf H
  have hCHNH : CH ≤ NH := by
    intro c hc
    exact Subgroup.mem_subgroupOf.mpr
      (hCN ⟨c, hc, rfl⟩)
  have hCHnormal : CH.Normal := hCnormal
  have hNHnormal : NH.Normal := hNnormal
  let _ : CH.Normal := hCHnormal
  let _ : NH.Normal := hNHnormal
  let q : H →* H ⧸ CH := QuotientGroup.mk' CH
  let R : Subgroup H := (pCore 2 (H ⧸ CH)).comap q
  let Ramb : Subgroup G := R.map H.subtype
  let K : Subgroup G := N ⊔ Ramb
  have hRambH : Ramb ≤ H := Subgroup.map_subtype_le _
  have hKH : K ≤ H := sup_le hNH hRambH
  have hNnormalK : (N.subgroupOf K).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_sup_left : N ≤ K)).mpr
    exact hKH.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hNnormal)
  let _ : (N.subgroupOf K).Normal := hNnormalK
  have hNHnormalSup : (NH.subgroupOf (NH ⊔ R)).Normal :=
    Subgroup.Normal.subgroupOf hNHnormal (NH ⊔ R)
  let _ : (NH.subgroupOf (NH ⊔ R)).Normal := hNHnormalSup
  have hint : IsPGroup 2
      (↑(NH ⊔ R : Subgroup H) ⧸ NH.subgroupOf (NH ⊔ R)) :=
    core_preimage_extension_isPGroup_39 CH NH hCHNH hCHnormal hNHnormal
  rw [IsPGroup.iff_card] at hint ⊢
  obtain ⟨n, hn⟩ := hint
  refine ⟨n, ?_⟩
  rw [← Subgroup.index_eq_card] at hn
  rw [← Subgroup.index_eq_card]
  change N.relIndex K = _
  change NH.relIndex (NH ⊔ R) = _ at hn
  rw [← hn]
  have hKint : K.subgroupOf H = NH ⊔ R := by
    calc
      K.subgroupOf H = N.subgroupOf H ⊔ Ramb.subgroupOf H :=
        Subgroup.subgroupOf_sup hNH hRambH
      _ = NH ⊔ R := by simp [NH, Ramb, subgroupOf_map_subtype_eq]
  have hrel := Subgroup.relIndex_map_map_of_injective
    NH (K.subgroupOf H) H.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hNH,
    Subgroup.map_subgroupOf_eq_of_le hKH, hKint] at hrel
  exact hrel

private theorem twoResidualAmbient_eq_map_hktPResidual_39
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) :
    twoResidualAmbient P = (hktPResidual 2 P).map P.subtype := by
  have heq : twoResidualSubgroup P = hktPResidual 2 P := by
    apply le_antisymm
    · have hnormal : (hktPResidual 2 P).Normal := hktPResidual_normal
      let _ : (hktPResidual 2 P).Normal := hnormal
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp
        (hktPResidual_quotient_isPGroup (Q := P) (q := 2))
      apply sInf_le
      refine ⟨hnormal, n, ?_⟩
      simpa [Subgroup.index_eq_card] using hn
    · apply le_sInf
      intro M hM
      have hnormal : M.Normal := hM.1
      let _ : M.Normal := hnormal
      obtain ⟨n, hn⟩ := hM.2
      apply hktPResidual_le M hnormal
      rw [IsPGroup.iff_card]
      exact ⟨n, by simpa [Subgroup.index_eq_card] using hn⟩
  simp [twoResidualAmbient, heq]

private theorem twoResidualAmbient_le_of_quotient_isPGroup_39
    {G : Type u} [Group G] [Finite G]
    (D K P : Subgroup G) (hDnormal : (D.subgroupOf K).Normal)
    (hquot : IsPGroup 2 (↑K ⧸ D.subgroupOf K)) (hPK : P ≤ K) :
    twoResidualAmbient P ≤ D := by
  classical
  let _ : (D.subgroupOf K).Normal := hDnormal
  let q : K →* ↑K ⧸ D.subgroupOf K :=
    QuotientGroup.mk' (D.subgroupOf K)
  let i : P →* K := Subgroup.inclusion hPK
  let f := q.comp i
  have hRker : hktPResidual 2 P ≤ f.ker :=
    hktPResidual_le_ker_of_isPGroup f hquot
  rw [twoResidualAmbient_eq_map_hktPResidual_39]
  rintro _ ⟨x, hx, rfl⟩
  have hfx : f x = 1 := MonoidHom.mem_ker.mp (hRker hx)
  have hxi : i x ∈ D.subgroupOf K :=
    (QuotientGroup.eq_one_iff (N := D.subgroupOf K) (x := i x)).mp hfx
  exact hxi

private theorem twoResidualAmbient_idempotent_39
    {G : Type u} [Group G] [Finite G] (P : Subgroup G) :
    twoResidualAmbient (twoResidualAmbient P) = twoResidualAmbient P := by
  classical
  let R : Subgroup G := twoResidualAmbient P
  have htop : twoResidualAmbient (⊤ : Subgroup R) = ⊤ := by
    rw [twoResidualAmbient_top_eq_hktPResidual]
    exact twoResidualAmbient_has_top_twoResidual P
  have hmap := map_twoResidualAmbient_of_subgroup_image
    (⊤ : Subgroup R) R.subtype R (by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype])
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
  exact hmap.symm

/-- The image of `S` in the centralizer quotient has trivial intersection
with its 2-core under the maximal-normal hypotheses used in (3.9). -/
public theorem threeNine_barred_sylow_inf_twoCore_eq_bot
    {G : Type u} [Group G] [Finite G]
    (S H N P₁ P₂ : Subgroup G) (C : Subgroup H)
    (_hSH : S ≤ H) (hNH : N ≤ H) (hCN : C.map H.subtype ≤ N)
    (hCnormal : C.Normal)
    (hNnormal : (N.subgroupOf H).Normal)
    (hR₁notN : ¬ twoResidualAmbient P₁ ≤ N)
    (hR₂notN : ¬ twoResidualAmbient P₂ ≤ N)
    (hmax : ∀ N' : Subgroup G, N ≤ N' → N' ≤ H →
      (N'.subgroupOf H).Normal →
      (¬ twoResidualAmbient P₁ ≤ N' ∧
        ¬ twoResidualAmbient P₂ ≤ N') → N' = N)
    (hSN : S ⊓ N ≤ C.map H.subtype) :
    letI : C.Normal := hCnormal
    let q : H →* H ⧸ C := QuotientGroup.mk' C
    (S.subgroupOf H).map q ⊓ pCore 2 (H ⧸ C) = ⊥ := by
  classical
  let CH : Subgroup H := C
  have hCHnormal : CH.Normal := hCnormal
  let _ : CH.Normal := hCHnormal
  let q : H →* H ⧸ CH := QuotientGroup.mk' CH
  let O : Subgroup (H ⧸ CH) := pCore 2 (H ⧸ CH)
  let R : Subgroup H := O.comap q
  let Ramb : Subgroup G := R.map H.subtype
  let Camb : Subgroup G := C.map H.subtype
  let K : Subgroup G := N ⊔ Ramb
  have hRambH : Ramb ≤ H := Subgroup.map_subtype_le _
  have hKH : K ≤ H := sup_le hNH hRambH
  have hRnormal : R.Normal := pCore_normal.comap q
  have hRambNormal : (Ramb.subgroupOf H).Normal := by
    simpa [Ramb, subgroupOf_map_subtype_eq] using hRnormal
  have hKnormal : (K.subgroupOf H).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr
    exact (le_inf
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hNnormal)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hRambH).mp hRambNormal)).trans
        (Subgroup.normalizer_inf_normalizer_le_normalizer_sup N Ramb)
  have hNnormalK : (N.subgroupOf K).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_sup_left : N ≤ K)).mpr
    exact hKH.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mp hNnormal)
  let _ : (N.subgroupOf K).Normal := hNnormalK
  have hquot : IsPGroup 2 (↑K ⧸ N.subgroupOf K) :=
    ambient_core_preimage_extension_isPGroup_39 H N C hNH hCN
      hCnormal hNnormal
  have hRiN_of_le_K (P : Subgroup G)
      (hRiK : twoResidualAmbient P ≤ K) : twoResidualAmbient P ≤ N := by
    rw [← twoResidualAmbient_idempotent_39 P]
    exact twoResidualAmbient_le_of_quotient_isPGroup_39 N K
      (twoResidualAmbient P) hNnormalK hquot hRiK
  have hR₁notK : ¬ twoResidualAmbient P₁ ≤ K := fun hle =>
    hR₁notN (hRiN_of_le_K P₁ hle)
  have hR₂notK : ¬ twoResidualAmbient P₂ ≤ K := fun hle =>
    hR₂notN (hRiN_of_le_K P₂ hle)
  have hKN : K = N := hmax K le_sup_left hKH hKnormal ⟨hR₁notK, hR₂notK⟩
  have hRambN : Ramb ≤ N := by
    rw [← hKN]
    exact le_sup_right
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨s, hsS, rfl⟩ := hx.1
  have hsR : s ∈ R := hx.2
  have hsN : (s : G) ∈ N := hRambN ⟨s, hsR, rfl⟩
  have hsC : (s : G) ∈ Camb := hSN ⟨Subgroup.mem_subgroupOf.mp hsS, hsN⟩
  have hsCH : s ∈ CH := by
    simpa [Camb, CH, subgroupOf_map_subtype_eq] using hsC
  exact (QuotientGroup.eq_one_iff (N := CH) (x := s)).mpr
    hsCH

end Stellmacher.SectionThree
