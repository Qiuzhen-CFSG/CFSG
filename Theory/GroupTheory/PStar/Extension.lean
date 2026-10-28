module

public import Theory.GroupTheory.PStar.ExtensionKernels
public import Theory.GroupTheory.PStar.ExtensionCentralSylow
public import Theory.GroupTheory.PStar.ExtensionChief
public import Theory.GroupTheory.PStar.ExtensionReduction

/-!
# Two-star extensions and Sylow centralizers

The general two-star extension criterion combines the chief-kernel theorem
with induction on the normal kernel order and restriction to the ambient
two-residual. All hypotheses in that reduction are discharged here.

Prime-to-p kernels and Sylow-centralizer residuals already have proofs for
every prime in the imported modules. The prime-two applications below also
derive these conclusions from the completed general extension criterion,
using the literal normal subgroups and subtype embeddings.

Source: GLS II, Chapter B, Lemmas 5.3 and 5.4
(`refs/KGroup/GLS2/ChapterB.tex`, lines 600–628).
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- GLS II B.5.3 for p = 2, with all three source hypotheses and no
chief-kernel or induction premise. -/
theorem isPStar_pResidual_of_extension (N : Subgroup G) [N.Normal]
    (P : Sylow 2 N) (hquot : IsPStar 2 (G ⧸ N))
    (hres : IsPStar 2 (pResidual 2 N))
    (hgen : (pResidual 2 N).map N.subtype ⊔
      centralizer ((P : Subgroup N).map N.subtype : Set G) = ⊤) :
    IsPStar 2 (pResidual 2 G) :=
  isPStar_pResidual_of_extension_of_chief_case
    (fun _ _ _ K _ hK S hY hq hs =>
      isPStar_of_isChief_centralizer_supplement hY K hK S hq hs)
    N P hquot hres hgen

/-- The extension criterion in a two-perfect ambient group. -/
theorem isPStar_of_extension (N : Subgroup G) [N.Normal]
    (P : Sylow 2 N) (hG : IsPPerfect 2 G) (hquot : IsPStar 2 (G ⧸ N))
    (hres : IsPStar 2 (pResidual 2 N))
    (hgen : (pResidual 2 N).map N.subtype ⊔
      centralizer ((P : Subgroup N).map N.subtype : Set G) = ⊤) :
    IsPStar 2 G := by
  have h := isPStar_pResidual_of_extension N P hquot hres hgen
  exact h.of_equiv
    ((MulEquiv.subgroupCongr ((pResidual_eq_top_iff 2 G).mpr hG)).trans topEquiv)

/-- The first assertion of GLS II B.5.3, obtained by applying its general
prime-two extension criterion to the normal odd core. -/
theorem isPStar_of_quotient_pPrimeCore_two
    (hquot : IsPStar 2 (G ⧸ pPrimeCore 2 G)) : IsPStar 2 G := by
  let N := pPrimeCore 2 G
  have hcop : Nat.Coprime 2 (Nat.card N) := pPrimeCore_coprime_card
  have hN : IsPStar 2 N := isPStar_of_coprime_card hcop
  have hNR : N ≤ pResidual 2 G :=
    le_pResidual_of_isPPerfect N ((pResidual_eq_top_iff 2 N).mp hN.1)
  have hG : IsPPerfect 2 G := by
    apply (pResidual_eq_top_iff 2 G).mp
    have h := congrArg (comap (QuotientGroup.mk' N))
      ((map_pResidual_of_surjective 2 (QuotientGroup.mk' N)
        (QuotientGroup.mk'_surjective N)).trans hquot.1)
    simpa only [comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr hNR, comap_top] using h
  let P : Sylow 2 N := Sylow.nonempty.some
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  have hP : (P : Subgroup N) = ⊥ := (P : Subgroup N).eq_bot_of_card_eq
    (Nat.eq_one_of_dvd_coprimes (hcop.pow_left n) (by rw [hn])
      (P : Subgroup N).card_subgroup_dvd_card)
  have hres : IsPStar 2 (pResidual 2 N) := hN.of_equiv
    ((MulEquiv.subgroupCongr hN.1).trans topEquiv).symm
  apply isPStar_of_extension N P hG hquot hres
  have hc : centralizer ((P : Subgroup N).map N.subtype : Set G) = ⊤ :=
    centralizer_eq_top_iff_subset.mpr (show
      (P : Subgroup N).map N.subtype ≤ center G by
        rw [hP, Subgroup.map_bot]; exact bot_le)
  rw [hc, sup_top_eq]

/-- GLS II B.5.4 for p = 2, applying B.5.3 to N intersect C_G(P).
Its Sylow subgroup is central in C_G(P), and transfer supplies the odd
order of its residual. -/
theorem IsPStar.isPStar_pResidual_centralizer_two (hG : IsPStar 2 G)
    (N : Subgroup G) [N.Normal] (P : Sylow 2 N) :
    IsPStar 2 (pResidual 2 (centralizer ((P : Subgroup N).map N.subtype : Set G))) := by
  let S := (P : Subgroup N).map N.subtype
  let C := centralizer (S : Set G)
  let K := N.subgroupOf C
  let q := QuotientGroup.mk' N
  let f : C →* G ⧸ N := q.comp C.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    have h := congrArg (Subgroup.map q) (hG.2 N P)
    simpa only [f, q, MonoidHom.range_comp, range_subtype, Subgroup.map_sup,
      QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] using h
  have hk : f.ker = K := by
    ext x
    exact QuotientGroup.eq_one_iff (x : G)
  have hquot : IsPStar 2 (C ⧸ K) := (hG.quotient N).of_equiv
    ((QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hk))
  let T : Sylow 2 K := Sylow.nonempty.some
  let U := (T : Subgroup K).map K.subtype
  have hUN : U.map C.subtype ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    have hxK : x ∈ K := map_subtype_le (T : Subgroup K) hx
    exact hxK
  have hUP : U.map C.subtype ≤ S :=
    le_embedded_sylow_of_centralizes N (U.map C.subtype) P
      ((T.isPGroup'.map K.subtype).map C.subtype) hUN (map_subtype_le _)
  have hcentral : U ≤ center C := by
    intro x hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext ((y.property x (hUP (mem_map_of_mem C.subtype hx))).symm)
  have hcentralK : (T : Subgroup K) ≤ center K := by
    intro x hx
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.mp
      (hcentral (mem_map_of_mem K.subtype hx)) y)
  have hres : IsPStar 2 (pResidual 2 K) :=
    isPStar_of_coprime_card (coprime_card_pResidual_of_central_sylow T hcentralK)
  apply isPStar_pResidual_of_extension K T hquot hres
  rw [centralizer_eq_top_iff_subset.mpr hcentral, sup_top_eq]

end Theory.GroupTheory
