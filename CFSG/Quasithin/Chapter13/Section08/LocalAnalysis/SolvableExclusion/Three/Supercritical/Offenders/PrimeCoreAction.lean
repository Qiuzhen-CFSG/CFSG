module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Supercritical.Construction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Cosets

/-!
# The odd core moved by the critical endpoint

Write H* = P* J*, where J = L₁T. The intersection of C(P*) with the
image of O₂(J) is a normal two-subgroup: J* normalizes it and P*
centralizes it. It is therefore trivial. The actual conjugator from
13.8.8(2) transfers this faithful action to Vγ* and hence Uγ*.

In the smaller group P*Uγ*, Uγ* is a Sylow two-subgroup. Every nontrivial
two-subgroup is conjugate into it, so every such subgroup moves P*, and
thus also the local p-core. This supplies the movement hypothesis for a
minimal cubic offender selected in that smaller group. Neither movement
by the chosen offender nor its minimality is an input here.

The parabolic-core argument generalizes the five-primary proof in
`Five.Localization.SecondActor.Faithfulness` to the supplied OddConstruction.
The source endpoint remains the literal conjugate attached to CriticalPair;
the conjugator h belongs to H and sends Vγ to the supplied Vα.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.8(2)
and the first two paragraphs of 13.8.13, printed pp.949–951.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders
variable {G : Type*} [Group G]

/-- A two-group normalized by K cannot centralize the normal supplement P
when the whole group has trivial two-core. -/
theorem centralizer_inf_eq_bot_of_supplement
    (P K B : Subgroup G) [P.Normal]
    (hgen : P ⊔ K = ⊤) (hB : IsPGroup 2 B)
    (hKB : K ≤ normalizer (B : Set G)) (hcore : pCore 2 G = ⊥) :
    B ⊓ centralizer (P : Set G) = ⊥ := by
  let C := B ⊓ centralizer (P : Set G)
  have hPC : P ≤ centralizer (C : Set G) := le_centralizer_iff.mpr inf_le_right
  have hKN : K ≤ normalizer (C : Set G) :=
    (le_inf hKB le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hCN : C.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgen]
    exact sup_le (hPC.trans (Subgroup.centralizer_le_normalizer _)) hKN
  have hC2 : IsPGroup 2 C := by
    exact (hB.to_subgroup (C.subgroupOf B)).of_equiv
      (subgroupOfEquivOfLe inf_le_left)
  have hle : C ≤ pCore 2 G := le_sSup ⟨hCN, hC2⟩
  exact le_bot_iff.mp (hle.trans hcore.le)

variable [Finite G]

/-- The actual quotient by the two-core has trivial two-core. -/
theorem hstar_twoCore (H : Subgroup G) : pCore 2 (Source.Hstar H) = ⊥ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have he := congrArg (map q)
    (q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk)
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at he
  exact he.trans (QuotientGroup.map_mk'_self _)

/-- The source supplement core acts faithfully on the constructed odd image. -/
theorem parabolic_core_star_centralizer {p : ℕ}
    {H L₁ T M Vα : Subgroup G} (c : OddConstruction p H L₁ T M Vα) :
    Source.starImage H ((L₁ ⊔ T).pCoreIn 2) ⊓
      centralizer (Source.starImage H c.P : Set (Source.Hstar H)) = ⊥ := by
  let J := L₁ ⊔ T
  have hJ : J ≤ H := c.generated ▸ le_sup_right
  let _ := c.Pstar_normal
  have hgen : Source.starImage H c.P ⊔ Source.starImage H J = ⊤ := by
    unfold Source.starImage
    rw [← Subgroup.map_sup, ← subgroupOf_sup c.P_le hJ, ← c.generated,
      subgroupOf_self, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact centralizer_inf_eq_bot_of_supplement _ _ _ hgen
    (starImage_isPGroup H _ (isPGroup_pCoreIn 2 J))
    (starImage_normalizes H (le_normalizer_pCoreIn 2 J)) (hstar_twoCore H)

/-- Transport faithfulness using the actual element of H in 13.8.8(2). -/
theorem star_faithful_on_P_of_core_placement {p : ℕ}
    {H L₁ T M Vα Vγ : Subgroup G} (c : OddConstruction p H L₁ T M Vα)
    (h : H)
    (hplace : Vγ.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2) :
    Source.starImage H Vγ ⊓ centralizer (Source.starImage H c.P : Set _) = ⊥ := by
  let _ := c.Pstar_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  apply bot_unique
  rintro x ⟨hx, hc⟩
  obtain ⟨v, hv, rfl⟩ := hx
  have hconj : q h * q v * (q h)⁻¹ ∈
      Source.starImage H ((L₁ ⊔ T).pCoreIn 2) := by
    refine ⟨h * v * h⁻¹, hplace (mem_map_of_mem _ hv), ?_⟩
    change q (h * v * h⁻¹) = _
    rw [map_mul, map_mul, map_inv]
  have hcent : q h * q v * (q h)⁻¹ ∈
      centralizer (Source.starImage H c.P : Set _) :=
    (inferInstance : (centralizer (Source.starImage H c.P : Set (Source.Hstar H))).Normal).conj_mem (q v) hc (q h)
  have he : q h * q v * (q h)⁻¹ = 1 := by
    have hh := show q h * q v * (q h)⁻¹ ∈
        Source.starImage H ((L₁ ⊔ T).pCoreIn 2) ⊓ centralizer (Source.starImage H c.P : Set _)
      from ⟨hconj, hcent⟩
    rwa [parabolic_core_star_centralizer c, mem_bot] at hh
  exact mem_bot.mpr (mul_left_cancel ((mul_inv_eq_one.mp he).trans (mul_one (q h)).symm))


/-- Faithfulness for the actual endpoint, with the 13.8.8 conjugator retained. -/
theorem endpoint_faithful {p : ℕ} {L L₁ T H M V Vα V₃ : Subgroup G}
    (c : OddConstruction p H L₁ T M Vα)
    (e : CriticalGeometry.CriticalPair L T H V)
    (hUV : Source.UH H V₃ ≤ Source.VH H V) (h : H)
    (hα : e.Vgamma.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hplace : Vα ≤ (L₁ ⊔ T).pCoreIn 2) :
    Source.starImage H (e.Ugamma V₃) ⊓
      centralizer (Source.starImage H c.P : Set _) = ⊥ := by
  have hle : e.Ugamma V₃ ≤ e.Vgamma := map_mono hUV
  apply bot_unique
  exact (inf_le_inf_right _ (starImage_mono H hle)).trans_eq
    (star_faithful_on_P_of_core_placement c h (hα ▸ hplace))

/-- Every nontrivial two-subgroup of a split odd-by-two group moves its
normal odd subgroup, if the complement acts faithfully. -/
theorem two_subgroup_moves_of_faithful_complement {p : ℕ} [Fact p.Prime]
    (P A D : Subgroup G) [P.Normal] (hP : IsPGroup p P) (ho : Odd p)
    (hA : IsPGroup 2 A) (hgen : P ⊔ A = ⊤)
    (hfaith : A ⊓ centralizer (P : Set G) = ⊥)
    (hD : IsPGroup 2 D) (hne : D ≠ ⊥) : ⁅P, D⁆ ≠ ⊥ := by
  have hd : Disjoint P A := hP.disjoint_of_coprime hA (Nat.coprime_two_right.mpr ho)
  have hmul : (P : Set G) * (A : Set G) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨x, hx, y, hy, he⟩ := mem_sup_of_normal_left.mp (hgen.ge (mem_top g))
    exact ⟨x, hx, y, hy, he⟩
  have hcomp := isComplement'_of_disjoint_and_mul_eq_univ hd hmul
  have hodd : Odd A.index := by
    rw [hcomp.index_eq_card]
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn]
    exact ho.pow
  let S : Sylow 2 G := hA.toSylow hodd.not_two_dvd_nat
  obtain ⟨R, hDR⟩ := hD.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R S
  intro hc
  have hDC : D ≤ centralizer (P : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  apply hne
  apply bot_unique
  intro d hd
  have hm : g * d * g⁻¹ ∈ A := by
    have hm : g * d * g⁻¹ ∈ ((g • R : Sylow 2 G) : Subgroup G) :=
      mem_map_of_mem (MulAut.conj g).toMonoidHom (hDR hd)
    rw [hg] at hm
    exact hm
  have hc' : g * d * g⁻¹ ∈ centralizer (P : Set G) :=
    (inferInstance : (centralizer (P : Set G)).Normal).conj_mem d (hDC hd) g
  have he : g * d * g⁻¹ = 1 := by
    have hh : g * d * g⁻¹ ∈ A ⊓ centralizer (P : Set G) := ⟨hm, hc'⟩
    rwa [hfaith, mem_bot] at hh
  exact mem_bot.mpr (mul_left_cancel ((mul_inv_eq_one.mp he).trans (mul_one g).symm))

/-- The prime core in the localized acting group is moved by every
nonidentity two-subgroup, without assuming that a chosen offender moves it. -/
theorem two_subgroup_moves_primeCore_in_join {p : ℕ} [Fact p.Prime]
    (P A : Subgroup G) [P.Normal] (hP : IsPGroup p P) (ho : Odd p)
    (hA : IsPGroup 2 A) (hfaith : A ⊓ centralizer (P : Set G) = ⊥)
    (D : Subgroup (P ⊔ A : Subgroup G)) (hD : IsPGroup 2 D) (hne : D ≠ ⊥) :
    ⁅pCore p (P ⊔ A : Subgroup G), D⁆ ≠ ⊥ := by
  let J := P ⊔ A
  let P' := P.subgroupOf J
  let A' := A.subgroupOf J
  have hP' : IsPGroup p P' := hP.comap_subtype
  have hA' : IsPGroup 2 A' := hA.comap_subtype
  have hgen : P' ⊔ A' = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
  have hfaith' : A' ⊓ centralizer (P' : Set J) = ⊥ := by
    apply bot_unique
    rintro x ⟨hxA, hxC⟩
    have hc : (x : G) ∈ centralizer (P : Set G) := by
      intro y hy
      exact congrArg Subtype.val (hxC (⟨y, (le_sup_left : P ≤ P ⊔ A) hy⟩ : J) hy)
    have hx : (x : G) ∈ A ⊓ centralizer (P : Set G) := ⟨hxA, hc⟩
    rw [hfaith, mem_bot] at hx
    exact Subtype.ext hx
  have hm := two_subgroup_moves_of_faithful_complement P' A' D hP' ho hA' hgen hfaith' hD hne
  have hcore : P' ≤ pCore p J := le_sSup ⟨inferInstance, hP'⟩
  intro he
  exact hm (le_bot_iff.mp ((commutator_mono hcore le_rfl).trans he.le))

/-- This is the local prime-core action required after choosing a minimal
cubic offender in P*Uγ*. It applies to every nontrivial two-subgroup. -/
theorem endpoint_join_primeCore_moved {p : ℕ}
    {L L₁ T H M V Vα V₃ : Subgroup G}
    (c : OddConstruction p H L₁ T M Vα)
    (e : CriticalGeometry.CriticalPair L T H V)
    (hUV : Source.UH H V₃ ≤ Source.VH H V) (h : H)
    (hα : e.Vgamma.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hplace : Vα ≤ (L₁ ⊔ T).pCoreIn 2)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (D : Subgroup (Source.starImage H c.P ⊔ Source.starImage H (e.Ugamma V₃) : Subgroup (Source.Hstar H)))
    (hD : IsPGroup 2 D) (hne : D ≠ ⊥) :
    ⁅pCore p (Source.starImage H c.P ⊔ Source.starImage H (e.Ugamma V₃) : Subgroup (Source.Hstar H)), D⁆ ≠ ⊥ := by
  let _ : Fact p.Prime := ⟨c.prime⟩
  let _ := c.Pstar_normal
  let _ : IsElementaryAbelian 2 (e.Ugamma V₃) :=
    IsElementaryAbelian.map (MulAut.conj (e.gb : G)).toMonoidHom
  have hA := starImage_isPGroup H (e.Ugamma V₃)
    (IsElementaryAbelian.isPGroup 2 (e.Ugamma V₃))
  exact two_subgroup_moves_primeCore_in_join _ _
    (starImage_isPGroup H c.P c.P_isPGroup) c.odd hA
    (endpoint_faithful c e hUV h hα hplace) D hD hne

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Supercritical.Offenders

end
