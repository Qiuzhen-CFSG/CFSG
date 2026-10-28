module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import Theory.GroupAction.OddInvolutionFrattini
public import Theory.GroupTheory.PCoreSurjective
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Endpoint

/-!
# Normal generation in the three-primary rank-one branches

An elementary two-actor moving the normal odd group P* also moves its
Frattini quotient. Irreducibility forces P* into the actor's normal closure:
the competing Frattini alternative contradicts movement, and the full
alternative lifts by Frattini nongeneration. Adjoining the base edge then
generates H. Pulling U_H back along the genuine critical-pair conjugator
and using the F.9.13 kernel identity proves generation at Gγ itself.

The parabolic-core faithfulness calculation extends the argument in
Five.Localization.SecondActor.Faithfulness to ReducedOdd. All kernels,
star images, edges, and stabilizers are the actual source constructions.
The Sylow containment also separates the residual's image from P*.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed p.951, with F.9.13 on printed p.322.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.RankOne
variable {G : Type*} [Group G]

private theorem commutator_not_le_frattini [Finite G] {p : ℕ}
    (P B : Subgroup G) [P.Normal] [IsElementaryAbelian 2 B]
    (hp : IsPGroup p P) (ho : Odd p) (hm : ⁅P, B⁆ ≠ ⊥) :
    ¬ ⁅P, B⁆ ≤ (frattini P).map P.subtype := by
  intro h
  have h' : ⁅B, P⁆ ≤ (frattini P).map P.subtype := by rwa [commutator_comm]
  apply hm
  rw [commutator_comm]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro b hb x hx
  let a := MulAut.conjNormal b (H := P)
  have ha2 : a ^ 2 = 1 := by
    have hb2 : b ^ 2 = 1 := congrArg Subtype.val
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 B) (⟨b, hb⟩ : B))
    change (MulAut.conjNormal : G →* MulAut P) b ^ 2 = 1
    rw [← map_pow, hb2, map_one]
  have hquot : quotientAut (frattini P) a = 1 := by
    ext q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (frattini P) q
    rw [quotientAut_apply_mk]
    change QuotientGroup.mk' (frattini P) (a r) = QuotientGroup.mk' (frattini P) r
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hh := h' (commutator_mem_commutator hb r.property)
    obtain ⟨s, hs, he⟩ := hh
    have he' : s = a r / r := by
      apply Subtype.ext
      simpa only [Subgroup.coe_div, div_eq_mul_inv, a, MulAut.conjNormal_apply,
        Subgroup.coe_mk, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def] using he
    exact he' ▸ hs
  have ha : a = 1 := OddInvolutionFrattini.involution_eq_one_of_quotient_eq_one
    hp (Nat.coprime_two_left.mpr ho) a ha2 hquot
  have he := congrArg Subtype.val (DFunLike.congr_fun ha (⟨x, hx⟩ : P))
  change b * x * b⁻¹ = x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

private theorem normal_contains_of_irreducible_frattini [Finite G]
    (P E B N : Subgroup G) [P.Normal] [N.Normal]
    (hirr : ∀ D : Subgroup G, (frattini P).map P.subtype ≤ D → D ≤ P →
      E ≤ normalizer (D : Set G) → D = (frattini P).map P.subtype ∨ D = P)
    (hBN : B ≤ N) (hm : ¬ ⁅P, B⁆ ≤ (frattini P).map P.subtype) : P ≤ N := by
  let Phi := (frattini P).map P.subtype
  let : Phi.Normal := ConjAct.normal_of_characteristic_of_normal
  let D := Phi ⊔ (P ⊓ N)
  have hc : ⁅P, B⁆ ≤ P ⊓ N := le_inf (commutator_le_left _ _)
    ((commutator_mono le_rfl hBN).trans (commutator_le_right _ _))
  have hDP : D ≤ P := sup_le (map_subtype_le _) inf_le_left
  have hfull : D = P := (hirr D le_sup_left hDP le_normalizer_of_normal).resolve_left
    (fun he => hm (hc.trans (he ▸ le_sup_right)))
  have htop : (P ⊓ N).subgroupOf P ⊔ frattini P = ⊤ := by
    apply (map_injective P.subtype_injective)
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le inf_le_left, ← MonoidHom.range_eq_map, range_subtype]
    exact (sup_comm _ _).trans hfull
  have hN : (P ⊓ N).subgroupOf P = ⊤ := frattini_nongenerating htop
  intro x hx
  have hm : (⟨x, hx⟩ : P) ∈ (P ⊓ N).subgroupOf P := hN ▸ mem_top _
  exact hm.2

/-- Star-image containment lifts after adjoining the actual two-core. -/
theorem le_sup_core_of_starImage_le {H P N : Subgroup G}
    (hPH : P ≤ H) (hNH : N ≤ H)
    (hPN : Source.starImage H P ≤ Source.starImage H N) : P ≤ N ⊔ Source.QH H := by
  intro p hp
  let pH : H := ⟨p, hPH hp⟩
  have hi := hPN (mem_map_of_mem (QuotientGroup.mk' (pCore 2 H))
    (show pH ∈ P.subgroupOf H from hp))
  have hc : pH ∈ (N.subgroupOf H) ⊔ pCore 2 H := by
    have hh : pH ∈ ((N.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).comap
      (QuotientGroup.mk' (pCore 2 H)) := hi
    simpa only [comap_map_eq, QuotientGroup.ker_mk'] using hh
  have hm := mem_map_of_mem H.subtype hc
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hNH] at hm
  exact hm

/-- The source Sylow condition puts O₂(H) in the base edge L₁T. -/
theorem core_le_base_of_sylow {H L₁ : Subgroup G} (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) : Source.QH H ≤ L₁ ⊔ T := by
  have h := pCoreIn_le_sylow H (T.subtype hTH)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at h
  exact h.trans le_sup_right

/-- In particular P* cannot be the image of a subgroup inside M. -/
theorem starImage_ne_of_outside {H P X M : Subgroup G}
    (hPH : P ≤ H) (hXH : X ≤ H) (hXM : X ≤ M)
    (hQM : Source.QH H ≤ M) (hout : ¬ P ≤ M) :
    Source.starImage H X ≠ Source.starImage H P := by
  intro he
  exact hout ((le_sup_core_of_starImage_le hPH hXH he.symm.le).trans
    (sup_le hXM hQM))

/-- The residual of 13.8.12 has a different star image from the outside P. -/
theorem residual_starImage_ne {p : ℕ} {H L₁ T M Vα : Subgroup G}
    (d : ReducedOdd p H L₁ T M Vα) (hQM : Source.QH H ≤ M) :
    Source.starImage H (residualInM H M) ≠ Source.starImage H d.P :=
  starImage_ne_of_outside d.P_le
    ((twoResidual_le _).trans (inf_le_left.trans (twoFitting_le H)))
    ((residualInM_le H M).trans inf_le_right) hQM d.outside

/-- Irreducibility on the Frattini quotient gives actual normal generation;
this includes the extraspecial alternative. -/
theorem base_generation_of_moves [Finite G] {p : ℕ}
    {H L₁ T M Vα B : Subgroup G} [IsElementaryAbelian 2 B]
    (d : ReducedOdd p H L₁ T M Vα) (hBH : B ≤ H)
    (hcore : Source.QH H ≤ L₁ ⊔ T)
    (hm : ⁅Source.starImage H d.P, Source.starImage H B⁆ ≠ ⊥) :
    H = conjugateSpanBy B H ⊔ (L₁ ⊔ T) := by
  let N := conjugateSpanBy B H
  have hNH : N ≤ H := conjugateSpanBy_le_self hBH
  have hHN : H ≤ normalizer (N : Set G) := le_normalizer_conjugateSpanBy B H
  let : (N.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHN
  let : (Source.starImage H N).Normal := Normal.map inferInstance
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)
  let := d.Pstar_normal
  let : IsElementaryAbelian 2 (Source.starImage H B) :=
    CriticalGeometry.starImage_isElementaryAbelian H B hBH
  have hnPhi := commutator_not_le_frattini _ _
    (starImage_isPGroup H d.P d.P_isPGroup) d.odd hm
  have hPN : Source.starImage H d.P ≤ Source.starImage H N :=
    normal_contains_of_irreducible_frattini _ _ _ _ d.irreducible
      (starImage_mono H (le_conjugateSpanBy B H)) hnPhi
  have hPL := le_sup_core_of_starImage_le d.P_le hNH hPN
  apply le_antisymm
  · exact d.generated.le.trans
      (sup_le (hPL.trans (sup_le_sup_left hcore N)) le_sup_right)
  · exact sup_le hNH (d.generated ▸ le_sup_right)

private theorem supplement_core_centralizer
    {K : Type*} [Group K] (P J Q : Subgroup K) [P.Normal]
    (hgen : P ⊔ J = ⊤) (hQ : IsPGroup 2 Q)
    (hnQ : J ≤ normalizer (Q : Set K)) :
    Q ⊓ centralizer (P : Set K) ≤ pCore 2 K := by
  let C := Q ⊓ centralizer (P : Set K)
  have hPC : P ≤ normalizer (C : Set K) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (P : Set K) from inf_le_right)).trans
      (centralizer_le_normalizer _)
  have hJC : J ≤ normalizer (C : Set K) :=
    (le_inf hnQ le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  have hC : C.Normal := normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hPC hJC))
  exact le_sSup ⟨hC, hQ.to_le inf_le_left⟩

private theorem hstar_core [Finite G] (H : Subgroup G) :
    pCore 2 (Source.Hstar H) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have he := congrArg (map q)
    (q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk)
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at he
  exact he.trans (QuotientGroup.map_mk'_self _)

/-- Faithfulness of the parabolic two-core on the odd normal star image. -/
theorem parabolic_core_star_centralizer [Finite G] {p : ℕ}
    {H L₁ T M Vα : Subgroup G} (d : ReducedOdd p H L₁ T M Vα) :
    Source.starImage H ((L₁ ⊔ T).pCoreIn 2) ⊓
      centralizer (Source.starImage H d.P : Set (Source.Hstar H)) = ⊥ := by
  let J := L₁ ⊔ T
  have hJ : J ≤ H := d.generated ▸ le_sup_right
  let := d.Pstar_normal
  have hgen : Source.starImage H d.P ⊔ Source.starImage H J = ⊤ := by
    unfold Source.starImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup d.P_le hJ, ← d.generated,
      subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hn := starImage_normalizes H (le_normalizer_pCoreIn 2 J)
  apply bot_unique
  exact (supplement_core_centralizer _ _ _ hgen
    (starImage_isPGroup H _ (isPGroup_pCoreIn 2 J)) hn).trans_eq (hstar_core H)

private theorem starImage_eq_bot_iff {H B : Subgroup G} (hBH : B ≤ H) :
    Source.starImage H B = ⊥ ↔ B ≤ Source.QH H := by
  have hc : (Source.QH H).subgroupOf H = pCore 2 H :=
    comap_map_eq_self_of_injective H.subtype_injective _
  rw [Source.starImage, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', ← hc]
  exact ⟨fun h b hb => h (show (⟨b, hBH hb⟩ : H) ∈ B.subgroupOf H from hb),
    fun h _ hb => h hb⟩

/-- A nontrivial star actor in the parabolic two-core moves P*. -/
theorem core_actor_moves [Finite G] {p : ℕ} {H L₁ T M Vα B : Subgroup G}
    (d : ReducedOdd p H L₁ T M Vα)
    (hB : B ≤ (L₁ ⊔ T).pCoreIn 2) (hnot : ¬ B ≤ Source.QH H) :
    ⁅Source.starImage H d.P, Source.starImage H B⁆ ≠ ⊥ := by
  have hBH : B ≤ H := hB.trans ((pCoreIn_le 2 _).trans (d.generated ▸ le_sup_right))
  intro hcomm
  rw [commutator_comm] at hcomm
  have hzero : Source.starImage H B = ⊥ := by
    apply le_bot_iff.mp
    rw [← parabolic_core_star_centralizer d]
    exact le_inf (starImage_mono H hB) (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  exact hnot ((starImage_eq_bot_iff hBH).mp hzero)

/-- Conjugating into the parabolic core also forces a nontrivial star actor to move P*. -/
theorem actor_moves_of_core_placement [Finite G] {p : ℕ}
    {H L₁ T M Vα B : Subgroup G} (d : ReducedOdd p H L₁ T M Vα)
    (h : H) (hB : B.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2)
    (hne : Source.starImage H B ≠ ⊥) :
    ⁅Source.starImage H d.P, Source.starImage H B⁆ ≠ ⊥ := by
  let := d.Pstar_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  intro hcomm
  have hcent := commutator_eq_bot_iff_le_centralizer.mp
    ((commutator_comm _ _).trans hcomm)
  apply hne
  apply bot_unique
  rintro x ⟨b, hb, rfl⟩
  have hc : q h * q b * (q h)⁻¹ ∈
      Source.starImage H ((L₁ ⊔ T).pCoreIn 2) := by
    refine ⟨h * b * h⁻¹, hB (mem_map_of_mem _ hb), ?_⟩
    change q (h * b * h⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hh := (inferInstance :
      (centralizer (Source.starImage H d.P : Set (Source.Hstar H))).Normal).conj_mem
      (q b) (hcent (mem_map_of_mem q hb)) (q h)
  have he : q h * q b * (q h)⁻¹ = 1 := by
    have hi := show q h * q b * (q h)⁻¹ ∈
      Source.starImage H ((L₁ ⊔ T).pCoreIn 2) ⊓
        centralizer (Source.starImage H d.P : Set (Source.Hstar H)) from ⟨hc, hh⟩
    rwa [parabolic_core_star_centralizer d, mem_bot] at hi
  exact mem_bot.mpr (mul_left_cancel ((mul_inv_eq_one.mp he).trans (mul_one (q h)).symm))

/-- Base generation for Uγ, using its actual 13.8.8(2) conjugate-core placement. -/
theorem base_generation_of_core_placement [Finite G] {p : ℕ}
    {H L₁ T M Vα B : Subgroup G} [IsElementaryAbelian 2 B]
    (d : ReducedOdd p H L₁ T M Vα) (hBH : B ≤ H)
    (hcore : Source.QH H ≤ L₁ ⊔ T) (h : H)
    (hB : B.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2)
    (hne : Source.starImage H B ≠ ⊥) :
    H = conjugateSpanBy B H ⊔ (L₁ ⊔ T) :=
  base_generation_of_moves d hBH hcore (actor_moves_of_core_placement d h hB hne)

/-- Generation at the actual endpoint, using the F.9.13 kernel and edge facts.
No generation premise or reversed critical-pair witness is assumed. -/
theorem endpoint_generation [Finite G] {p : ℕ}
    {L T H V V₃ V₁ L₁ M Vα : Subgroup G}
    (c : CriticalGeometry.CriticalPair L T H V)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (d : ReducedOdd p H L₁ T M Vα)
    (he : (L ⊔ T) ⊓ H = L₁ ⊔ T)
    (hedge : Source.UH H V₃ ≤
      (CriticalGeometry.edgeGroup L T H c.gamma c.previous).pCoreIn 2)
    (hcore : Source.QH H ≤ L₁ ⊔ T)
    (hkernel : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) =
      Source.UH H V₃ ⊓ c.Qgamma)
    (hproper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃) :
    CriticalGeometry.vertexGroup L T H c.gamma =
      conjugateSpanBy (Source.UH H V₃) (CriticalGeometry.vertexGroup L T H c.gamma) ⊔
        CriticalGeometry.edgeGroup L T H c.gamma c.previous := by
  let e := MulAut.conj (c.gb : G)
  let B := (Source.UH H V₃).map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hback : B.map e.toMonoidHom = Source.UH H V₃ :=
    (map_symm_eq_iff_map_eq _ (e := e)).mp rfl
  have hB : B ≤ (L₁ ⊔ T).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hback, map_pCoreIn_of_ker_isPGroup _ (IsPGroup.ker_isPGroup_of_injective e.injective), ← c.edgeGroup_eq L₁ he]
    exact hedge
  have hBH : B ≤ H := hB.trans ((pCoreIn_le 2 _).trans (d.generated ▸ le_sup_right))
  have hnot : ¬ B ≤ Source.QH H := by
    intro hn
    have hh : Source.UH H V₃ ≤ c.Qgamma := by
      have hm := map_mono (f := e.toMonoidHom) hn
      rwa [hback] at hm
    exact hproper.not_ge (hkernel ▸ le_inf le_rfl hh)
  have hgen := congrArg (Subgroup.map e.toMonoidHom)
    (base_generation_of_moves d hBH hcore (core_actor_moves d hB hnot))
  rw [Subgroup.map_sup, CriticalGeometry.map_conjugateSpan, hback,
    ← c.vertexGroup_gamma, ← c.edgeGroup_eq L₁ he] at hgen
  exact hgen

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.RankOne
end
