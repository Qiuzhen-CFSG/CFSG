module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.NoThreeSupport
public import CFSG.Quasithin.ChapterD.Section03.SourceSetup
public import Theory.GroupTheory.PGroup.ExtraspecialThreeReducibleGenerators
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.Representation.ExtraspecialCubicDisplacement
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.MinimalDegree
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Sylow irreducibility in the original extraspecial degree-six branch

For a normal elementary binary subgroup U of the selected maximal local M,
use the literal faithful quotient M/C_M(U). Suppose its normal extraspecial
actor P has order 27 and exponent three, acts on the six-dimensional U, and
supplements the Sylow image. Then that Sylow image is irreducible on P/Phi(P).

A reducible coprime action gives two normalized noncentral cubic subgroups
generating P. Faithfulness in degree six makes the central fixed space zero;
the extraspecial displacement formula gives a nonzero fixed plane for each
cubic subgroup. Original partner uniqueness places both full preimages in Mc.
Together with T they generate M, contradicting M distinct from Mc. The final
wrapper proves the supplement when P is the actual two-residual.

Source: Aschbacher--Smith, 15.1.2, printed p.1086, case (4) of D.2.17.
The preceding identification of O^2(M/C_M(U)) with P belongs to the full-orbit
assembly; it is recorded explicitly in the residual specialization.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_fixed_ne_bot
    {P V : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) P V) (hf : Function.Injective ρ)
    (hc : Nat.card P = 27) (hd : Module.finrank (ZMod 2) V = 6)
    (X : Subgroup P) (hX : Nat.card X = 3) (hXZ : X ≠ center P) :
    fixedSpace ρ X ≠ ⊥ := by
  let : IsIrreducible ρ := RankTwo.ExtraspecialModel.irreducible_of_faithful_six ρ hf hc hd
  have hz : invariants (ρ.comp (center P).subtype) = ⊥ := by
    by_contra hn
    have h := ρ.le_ker_of_normal_invariants_ne_bot (center P) hn
    have hb : center P = ⊥ := bot_unique (by
      simpa only [(MonoidHom.ker_eq_bot_iff _).mpr hf] using h)
    have hcard := IsExtraspecial.center_order_p 3 P
    rw [hb, card_bot] at hcard
    omega
  have hcod := BinaryCoprimeDegree.extraspecial_twentySeven_fixedCodim_subgroup ρ hc hz X hX hXZ
  have hadd := fixedCodim_add_finrank ρ X
  intro he
  rw [he, Module.finrank_zero_of_subsingleton, hd] at hadd
  rw [hd] at hcod
  omega

public theorem source_extraspecial_component_frattini_irreducible
    (T : Sylow 2 G) {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (P : Subgroup (M ⧸ centralizer (U : Set M))) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (hdim : Module.finrank (ZMod 2) (Additive U) = 6)
    (hgen : P ⊔ ((T.subtype hM.1.2 : Subgroup M).map
      (QuotientGroup.mk' (centralizer (U : Set M)))) = ⊤) :
    ChapterD.Section03.FrattiniIrreducible
      ((T.subtype hM.1.2 : Subgroup M).map (QuotientGroup.mk' (centralizer (U : Set M)))) P
      (by rw [normalizer_eq_top]; exact le_top) := by
  let q := QuotientGroup.mk' (centralizer (U : Set M))
  let ρ := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  let S : Subgroup (M ⧸ centralizer (U : Set M)) := (T.subtype hM.1.2 : Subgroup M).map q
  have hSP : S ≤ normalizer (P : Set _) := by rw [normalizer_eq_top]; exact le_top
  let α := P.normalizerMonoidHom.comp (inclusion hSP)
  have hS : IsPGroup 2 S := (T.subtype hM.1.2).isPGroup'.map q
  have hcop : Nat.Coprime 3 (Nat.card S) := by
    obtain ⟨n, hn⟩ := hS.exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 from by decide).pow_right n
  intro L hstable
  by_cases hL0 : L = ⊥
  · exact Or.inl hL0
  by_cases hL1 : L = ⊤
  · exact Or.inr hL1
  exfalso
  obtain ⟨K,R,hK,hR,hKZ,hRZ,hKR,hKs,hRs⟩ :=
    ExtraspecialSylow.exists_normalized_cubic_generators α hcop hP hexp L hL0 hL1 hstable
  let X := K.map P.subtype
  let Y := R.map P.subtype
  have hn (A : Subgroup P) (hs : ∀ s : S, ∀ x ∈ A, α s x ∈ A) :
      S ≤ normalizer (A.map P.subtype : Set _) := by
    apply le_normalizer_iff.mpr
    rintro s hsm x ⟨a,ha,rfl⟩
    have he : ((α ⟨s,hsm⟩ a : P) : M ⧸ centralizer (U : Set M)) = s * (a : _) * s⁻¹ := by
      exact normalizerMonoidHom_apply_apply_coe P ⟨s,hSP hsm⟩ a
    change s * (a : M ⧸ centralizer (U : Set M)) * s⁻¹ ∈ A.map P.subtype
    rw [← he]
    exact mem_map_of_mem P.subtype (hs ⟨s,hsm⟩ a ha)
  have hf : Function.Injective ρ := NormalElementaryQuotient.representation_injective U q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
  have hXfix : fixedSpace ρ X ≠ ⊥ := by
    rw [← fixedSpace_comp_map ρ P.subtype K]
    exact cubic_fixed_ne_bot (ρ.comp P.subtype) (hf.comp P.subtype_injective) hP hdim K hK hKZ
  have hYfix : fixedSpace ρ Y ≠ ⊥ := by
    rw [← fixedSpace_comp_map ρ P.subtype R]
    exact cubic_fixed_ne_bot (ρ.comp P.subtype) (hf.comp P.subtype_injective) hP hdim R hR hRZ
  have hXM := normalized_actor_preimage_le_partner_of_fixed_ne_bot T hM.1.2 hu U X (hn K hKs) hXfix
  have hYM := normalized_actor_preimage_le_partner_of_fixed_ne_bot T hM.1.2 hu U Y (hn R hRs) hYfix
  let B := Mc.subgroupOf M
  have hXB : X.comap q ≤ B := by
    intro x hx
    exact hXM (mem_map_of_mem M.subtype hx)
  have hYB : Y.comap q ≤ B := by
    intro x hx
    exact hYM (mem_map_of_mem M.subtype hx)
  have hXmap : X ≤ B.map q := by
    apply (map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) X).ge.trans
    exact map_mono hXB
  have hYmap : Y ≤ B.map q := by
    apply (map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Y).ge.trans
    exact map_mono hYB
  have hXY : X ⊔ Y = P := by
    rw [← Subgroup.map_sup, hKR, ← MonoidHom.range_eq_map, range_subtype]
  have hPB : P ≤ B.map q := hXY ▸ sup_le hXmap hYmap
  have hMc := (show Mc ∈ maximalTwoLocalOvergroups
    (centralizer (centralInvolutions T : Set G)) from hu ▸ Set.mem_singleton Mc)
  have hTMc : (T : Subgroup G) ≤ Mc := by
    apply le_trans _ hMc.2
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm
  have hSB : S ≤ B.map q := by
    rintro s ⟨t,ht,rfl⟩
    exact mem_map_of_mem q (hTMc ht)
  have hBmap : B.map q = ⊤ := top_unique (hgen ▸ sup_le hPB hSB)
  have hker : q.ker ≤ B := by
    intro x hx
    apply hXB
    change q x ∈ X
    rw [show q x = 1 from hx]
    exact X.one_mem
  have hBtop : B = ⊤ := by
    have he := congrArg (Subgroup.comap q) hBmap
    simpa only [comap_map_eq_self hker, comap_top] using he
  have hMMc : M ≤ Mc := by
    intro m hm
    have hb : (⟨m,hm⟩ : M) ∈ B := hBtop ▸ mem_top _
    exact hb
  exact hne (hM.1.1.eq_of_le hMc.1.1 hMMc)

/-- The full-orbit source specialization after identifying the actual odd
residual. Its residual/Sylow supplement is proved by the literal quotient map. -/
public theorem source_extraspecial_residual_frattini_irreducible
    (T : Sylow 2 G) {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (U : Subgroup M) [U.Normal] [IsElementaryAbelian 2 U]
    (P : Subgroup (M ⧸ centralizer (U : Set M))) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (hdim : Module.finrank (ZMod 2) (Additive U) = 6)
    (hres : P = pResidual 2 (M ⧸ centralizer (U : Set M))) :
    ChapterD.Section03.FrattiniIrreducible
      ((T.subtype hM.1.2 : Subgroup M).map (QuotientGroup.mk' (centralizer (U : Set M)))) P
      (by rw [normalizer_eq_top]; exact le_top) := by
  apply source_extraspecial_component_frattini_irreducible T hM hu hne U P hP hexp hdim
  rw [hres]
  exact pResidual_sup_sylow_eq_top
    ((T.subtype hM.1.2).mapSurjective (QuotientGroup.mk'_surjective (centralizer (U : Set M))))

end CFSG.Quasithin.Chapter15.Section01
