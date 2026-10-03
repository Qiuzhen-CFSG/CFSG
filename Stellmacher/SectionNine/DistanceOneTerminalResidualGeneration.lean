module
public import Stellmacher.SectionNine.DistanceOneVstarResidualContainment
public import Theory.GroupTheory.CentralS3InvolutionComplement
public import Theory.GroupTheory.NormalCenterQuotient

/-!
# Generation of the terminal residual by Vstar and a cubic actor

In the original ambient distance-one context, any order-three element of the
terminal two-residual generates that residual together with the exact Vstar.
The only additional inputs are the explicit faithful and local conclusions.
This gives a criterion for residual invariance: invariance under Vstar and
under one actual order-three residual actor suffices.

Vstar is normal of order32 in the terminal stabilizer of order384, so its
quotient has order12. The normal terminal core has index6; its image in this
quotient therefore has order2 and is central. The small central-extension
Sylow theorem makes the Sylow three normal. The prescribed actor cannot lie
in Vstar, because its order is three, so its image generates that Sylow
subgroup. Its inverse image is normal of index4 and consequently contains
the terminal two-residual by the residual's defining intersection. Taking
inverse images identifies this subgroup with Vstar joined with the actor's
cyclic subgroup. The already proved containment Vstar in the residual and
actor membership give the reverse inclusion.

Source: Stellmacher (9.1), Journal of Algebra190 (1997), p.48, residual
normality of the selected elementary subgroup. All subgroups and quotient
maps are constructed from the original context; no residual generation or
quotient classification hypothesis is assumed.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven
universe u

/-- Every actual order-three residual actor supplements Vstar in the
terminal two-residual. -/
public theorem distance_one_terminal_residual_eq_vstar_sup_zpowers
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlength : ctx.criticalPath.length = 1)
    (hfaithful : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (actor : G) (hactor : actor ∈ EAt ctx.Γ ctx.criticalPath.a')
    (horder : orderOf actor = 3) :
    EAt ctx.Γ ctx.criticalPath.a' = conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a') ⊔ Subgroup.zpowers actor := by
  classical
  let V := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  have hVE : V ≤ E := distance_one_vstar_le_terminal_residual ctx hlength hfaithful hlocal
  have hEV : E ≤ terminal := by
    simpa only [E, terminal, EAt, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
      GAt, CosetGraphContext.stabilizer] using SevenSix.twoResidualIn_le terminal
  have hcontain := distance_one_vstar_containments ctx.toLocalContext hlength
  have hVT : V ≤ terminal := hcontain.1.1
  have hVQ : V ≤ Q := hcontain.2.1
  let Vn := V.subgroupOf terminal
  let Qn := Q.subgroupOf terminal
  let : Vn.Normal := hcontain.1.2
  have hVcard : Nat.card V = 32 := distance_one_vstar_card ctx.toLocalContext hlocal
  have hVncard : Nat.card Vn = 32 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVT).toEquiv).trans hVcard
  have hTcard : Nat.card terminal = 384 := distance_one_terminal_card ctx.toLocalContext hlength hlocal
  let W := terminal ⧸ Vn
  let q : terminal →* W := QuotientGroup.mk' Vn
  have hqsur : Function.Surjective q := QuotientGroup.mk'_surjective Vn
  have hWcard : Nat.card W = 12 := by
    have hc := Vn.card_mul_index
    rw [hVncard, hTcard, Subgroup.index_eq_card] at hc
    change 32 * Nat.card W = 384 at hc
    omega
  obtain ⟨projection, hsurj, hker⟩ := hlocal.2.1
  change terminal →* SL2Two at projection
  change Function.Surjective projection at hsurj
  change projection.ker = Qn at hker
  let : Qn.Normal := hker ▸ inferInstance
  have hQindex : Qn.index = 6 := by
    rw [← hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top]
    exact SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  let Z := Qn.map q
  let : Z.Normal := Subgroup.Normal.map (inferInstance : Qn.Normal) q hqsur
  have hZindex : Z.index = 6 := by
    rw [Subgroup.index_map_eq Qn hqsur]
    · exact hQindex
    · rw [QuotientGroup.ker_mk']
      exact Subgroup.subgroupOf_mono terminal hVQ
  have hZcard : Nat.card Z = 2 := by
    have hc := Z.card_mul_index
    rw [hZindex, hWcard] at hc
    omega
  have hZcentral : Z ≤ Subgroup.center W := Subgroup.central_of_normal_card_two Z hZcard
  let a : terminal := ⟨actor, hEV hactor⟩
  have haorder : orderOf a = 3 := by rw [← Subgroup.orderOf_coe]; exact horder
  have ha3 : a ^ 3 = 1 := by rw [← haorder]; exact pow_orderOf_eq_one a
  have haqne : q a ≠ 1 := by
    intro heq
    have haV : a ∈ Vn := (QuotientGroup.eq_one_iff a).mp heq
    have hd := orderOf_dvd_natCard (⟨actor, haV⟩ : V)
    rw [← Subgroup.orderOf_coe, horder, hVcard] at hd
    norm_num at hd
  let C := Subgroup.zpowers (q a)
  have hCcard : Nat.card C = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [← map_pow, ha3, map_one]) haqne
  have hCp : IsPGroup 3 C := IsPGroup.of_card (n := 1) hCcard
  obtain ⟨P, hCP⟩ := hCp.exists_le_sylow
  obtain ⟨hPcard, hPnormal⟩ := central_small_sylow_three_normal Z hZcentral
    (by omega) (by rw [hZcard, hWcard]) P
  have hPC : (P : Subgroup W) = C :=
    (Subgroup.eq_of_le_of_card_ge hCP (by rw [hCcard, hPcard])).symm
  let : C.Normal := hPC ▸ hPnormal
  let N := C.comap q
  have hNnormal : N.Normal := Subgroup.Normal.comap (inferInstance : C.Normal) q
  have hNindex : N.index = 2 ^ 2 := by
    rw [Subgroup.index_comap_of_surjective C hqsur]
    have hc := C.card_mul_index
    rw [hCcard, hWcard] at hc
    omega
  have hres : twoResidualSubgroup terminal ≤ N := sInf_le ⟨hNnormal, 2, hNindex⟩
  have hN : N = Subgroup.zpowers a ⊔ Vn := by
    change (Subgroup.zpowers (q a)).comap q = _
    rw [← MonoidHom.map_zpowers, Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hEmap : E = (twoResidualSubgroup terminal).map terminal.subtype := by
    simp only [E, terminal, CosetGraphContext.e, ctx.Γ.twoResidualAt_def,
      GAt, CosetGraphContext.stabilizer, twoResidualIn, twoResidualAmbient]
    rfl
  have hupper : E ≤ V ⊔ Subgroup.zpowers actor := by
    rw [hEmap]
    have hm := Subgroup.map_mono (f := terminal.subtype) hres
    rw [hN, Subgroup.map_sup, MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le hVT] at hm
    change (twoResidualSubgroup terminal).map terminal.subtype ≤
      Subgroup.zpowers actor ⊔ V at hm
    rwa [sup_comm] at hm
  exact le_antisymm hupper (sup_le hVE (Subgroup.zpowers_le.mpr hactor))

end Stellmacher.SectionNine
