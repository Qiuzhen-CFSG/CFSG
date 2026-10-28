module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceSelectionCores
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.ZeroIntersection
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.ActionTorus.Actor
/-!
# The zero-intersection FF clause on the original selected family

For each actual quotient in E.2.4, the image of V has binary dimension
at most the rank of A/C_A(V). The symplectic case uses the specified
Sylow-center placement, including field two. If V intersects its generating
conjugate trivially, the pair core is elementary abelian. Its fixed subgroup
then makes the literal actor an offender on V.

The actor is embedded directly in Aut_H(V) using the original Sylow and
conjugator. This proves E.2.13(5) in the action used by selection, without
an action-identification premise. The reduced selection interface retains
witness existence, symplectic exclusion, and the center marking. E.2.14's
rank and torus clauses and the field-four endgame remain separate obligations.

Source: Aschbacher–Smith, E.2.13(4–5), printed pp.224–225, and 8.2.2,
printed pp.714–715 (1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]
private theorem pair_proper_of_model {I M V : Subgroup G} {S : Sylow 2 I} {i : I}
    (hp : TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹)
    {X : Type*} [Group X] [Nontrivial X] (e : Star M I ≃* X) : V.subgroupOf I ≠ ⊤ := by
  intro he
  have hM : M.subgroupOf I = ⊤ := by
    apply top_unique
    simpa only [he,normalizer_eq_top] using hp.normalizer_le
  have hc : Nat.card (Star M I) = 1 := by
    change Nat.card (I ⧸ (M.subgroupOf I).normalCore) = 1
    rw [hM,normalCore_eq_self]
    simp
  let : Finite X := Finite.of_equiv (Star M I) e.toEquiv
  exact (ne_of_gt (Finite.one_lt_card (α := X))) ((Nat.card_congr e.toEquiv).symm.trans hc)

/-- Dimension comparison on the actual classified two-conjugate pair. -/
theorem family_actor_dimension {K : GroupClass} {H T M V I : Subgroup G} {k : ℕ}
    (h : HypothesisE28 K H T M V) (f : Family H T M V I k)
    (hfit : generalizedFitting H = pCore 2 H)
    (S : Sylow 2 I) (hS : (S : Subgroup I) = T.subgroupOf I)
    (i : I) (hgen : V ⊔ V.map (MulAut.conj i.val⁻¹).toMonoidHom = I) :
    V.subgroupOf I ≠ ⊤ ∧ ∃ d : ℕ,
      Nat.card (starImage M I V) ≤ 2^d ∧
      d ≤ Nat.log 2 ((TwoConjugate.Z (V.subgroupOf I) i⁻¹).relIndex
        (TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹)) := by
  have hp := Family.twoConjugate h f S hS i hgen
  have hfitI := family_characteristic_two h f hfit
  let := hp.elementary
  rcases f.classified with (⟨hk,e,_⟩ | ⟨m,hm,_,e,_⟩ | ⟨_,p,a,hpprime,ho,_,⟨e⟩⟩) | hs
  · have hproper := pair_proper_of_model hp e
    let ξ := e.trans (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm
    have hcard := GaloisField.card 2 k (by omega)
    exact ⟨hproper,k,hp.star_card_le_linear_two k hcard ξ,
      hp.actor_rank_ge_linear_two_star hproper hfitI k (by omega) hcard ξ⟩
  · let : Fact (0 < m) := ⟨hm⟩
    have hproper := pair_proper_of_model hp e
    refine ⟨hproper,2*m+1,hp.star_card_le_suzuki m hm e,?_⟩
    have hd := hp.actor_rank_ge_suzuki hfitI m (by omega) e
    omega
  · have hproper := pair_proper_of_model hp e
    let E := starImage M I V
    have hEp : IsPGroup 2 E := (IsElementaryAbelian.isPGroup 2 (V.subgroupOf I)).map _
    have hne : E ≠ ⊥ := by
      intro he
      have hv : V.subgroupOf I ≤ localCore M I := by
        simpa only [QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp he
      exact hp.V_not_le_twoCore hproper
        (hp.le_twoCore_of_le_J _ (IsElementaryAbelian.isPGroup 2 _) hv)
    have hd : Nat.card E ∣ 2*p^a := by
      have hh := E.card_subgroup_dvd_card
      rwa [Nat.card_congr e.toEquiv,DihedralGroup.nat_card] at hh
    obtain ⟨b,hb⟩ := hEp.exists_card_eq
    have hcop : Nat.Coprime (Nat.card E) (p^a) := by
      rw [hb]
      exact ho.coprime_two_left.pow b a
    have hc : Nat.card E = 2 := ((Nat.dvd_prime Nat.prime_two).mp
      (hcop.dvd_of_dvd_mul_right hd)).resolve_left (fun he => hne (Subgroup.card_eq_one.mp he))
    exact ⟨hproper,1,by simpa only [pow_one] using hc.le,hp.actor_rank_pos hproper hfitI⟩
  · obtain ⟨hk,_,e,_,hcenter,_⟩ := hs
    let : Nontrivial (Theory.SpecificGroups.SymplecticFour.Sp (BinaryGaloisField k)) :=
      (Theory.SpecificGroups.SymplecticFour.RootSubgroup.parameter_injective
        (F := BinaryGaloisField k) 0).nontrivial
    have hproper := pair_proper_of_model hp e
    let q := QuotientGroup.mk' (localCore M I)
    let R := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
    let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
    have hR : (R : Subgroup (Star M I)) = starImage M I T := by
      change (S : Subgroup I).map q = _
      rw [hS]
      rfl
    have hVS : (V.subgroupOf I).map (e.toMonoidHom.comp q) ≤
        (center R').map (R' : Subgroup _).subtype := by
      have hh := map_mono (f := e.toMonoidHom) hcenter
      rw [←hR,embeddedCenter,map_embeddedCenter _ e.toMonoidHom e.injective] at hh
      change (V.subgroupOf I).map (e.toMonoidHom.comp q) ≤
        (center ((R : Subgroup (Star M I)).map e.toMonoidHom)).map
          ((R : Subgroup (Star M I)).map e.toMonoidHom).subtype
      simpa only [starImage,map_map] using hh
    have hcard := GaloisField.card 2 k (by omega)
    exact ⟨hproper,2*k,TwoConjugate.Hypotheses.star_card_le_symplectic_center
      k hk hcard e R' hVS,hp.actor_rank_ge_symplectic_four hfitI k hk hcard e⟩

/-- The source E.2.13(5) bound in the actual ambient induced action. -/
theorem family_quadraticRatio_le_one_of_intersection_eq_bot
    {K : GroupClass} {H T M V I : Subgroup G} [IsElementaryAbelian 2 V] {k : ℕ}
    (h : HypothesisE28 K H T M V) (hfit : generalizedFitting H = pCore 2 H)
    (f : Family H T M V I k) (i : I)
    (hgen : V ⊔ V.map (MulAut.conj i.val⁻¹).toMonoidHom = I)
    (hz : V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom = ⊥) :
    quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V H).subtype) ≤ 1 := by
  obtain ⟨S,hS⟩ := f.sylow
  have hp := Family.twoConjugate h f S hS i hgen
  obtain ⟨hproper,d,hstar,hd⟩ := family_actor_dimension h f hfit S hS i hgen
  have hVI : V ≤ I := hgen ▸ le_sup_left
  have hz' : TwoConjugate.Z (V.subgroupOf I) i⁻¹ = ⊥ := by
    apply Subgroup.map_injective I.subtype_injective
    rw [selected_intersection_image I V hVI i,hz,Subgroup.map_bot]
  have hST : (S : Subgroup I).map I.subtype ≤ T := by
    rw [hS]
    exact map_comap_le _ _
  have hTN : T ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.le_sylow).mp h.normal_in_sylow
  let a := DihedralCubic.actorIn hp (hST.trans hTN)
  let ψ : TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹ →*
      inducedAutomizer V H :=
    (V.normalizerMonoidHom.rangeRestrict.comp a).codRestrict (inducedAutomizer V H)
      (fun x => mem_map_of_mem _ (h.le_ambient (hST
        (mem_map_of_mem I.subtype (DihedralCubic.A_le_sylow hp x.property)))))
  let ρ := (automizerRepresentation V).comp (inducedAutomizer V H).subtype
  let e := subgroupOfEquivOfLe hVI
  have hρ : Function.Injective ρ := (automizerRepresentation_injective V).comp
    (inducedAutomizer V H).subtype_injective
  have ha : ∀ (x : TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹)
      (v : V.subgroupOf I),
      (e.symm (ρ (ψ x) (Additive.ofMul (e v))).toMul : I) =
        (x : I) * v * (x : I)⁻¹ := by
    intro x v
    apply Subtype.ext
    rfl
  exact (hp.offender_of_P_elementary_and_star_dimension hproper
    (family_characteristic_two h f hfit) (hp.P_elementary_of_Z_eq_bot hz')
    e ρ hρ ψ ha d hstar hd).2

/-- The non-FF hypothesis forces the actual two-conjugate intersection to
be nontrivial, without a separate E.2.13(5) premise. -/
theorem family_intersection_ne_bot_of_quadraticRatio_gt_one
    {K : GroupClass} {H T M V I : Subgroup G} [IsElementaryAbelian 2 V] {k : ℕ}
    (h : HypothesisE28 K H T M V) (hfit : generalizedFitting H = pCore 2 H)
    (f : Family H T M V I k) (i : I)
    (hgen : V ⊔ V.map (MulAut.conj i.val⁻¹).toMonoidHom = I)
    (hq : 1 < quadraticRatio
      ((automizerRepresentation V).comp (inducedAutomizer V H).subtype)) :
    V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom ≠ ⊥ := by
  intro hz
  exact (not_le_of_gt hq)
    (family_quadraticRatio_le_one_of_intersection_eq_bot h hfit f i hgen hz)

end CFSG.Quasithin.Chapter8.Section02.HermitianSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

/-- The three remaining selection clauses after deriving the
zero-intersection FF bound on every actual family pair. -/
structure SelectionStructuralSources (K : GroupClass) : Prop where
  e29 : ∀ H T M V : Subgroup G, HypothesisE28 K H T M V →
    ∃ I k, Family H T M V I k
  e2136 : ∀ {H T M V I : Subgroup G} {k : ℕ}, HypothesisE28 K H T M V →
    generalizedFitting H = pCore 2 H → Family H T M V I k →
    (∀ i : I, (V.subgroupOf I).map (MulAut.conj i⁻¹).toMonoidHom ≤ T.subgroupOf I →
      (V.subgroupOf I).map (MulAut.conj i⁻¹).toMonoidHom ≤ centralizer (V.subgroupOf I : Set I)) →
    ∀ n : ℕ, 0 < n → ¬ Nonempty (Star M I ≃* Sp (BinaryGaloisField n))
  e2142_center : ∀ {H T M V I : Subgroup G} {k : ℕ}, HypothesisE28 K H T M V →
    generalizedFitting H = pCore 2 H → Family H T M V I k →
    (∀ x ∈ H ⊓ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V) → ∀ i : I,
    V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I →
    V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ≠ ⊥ →
    starImage M I V = embeddedCenter (starImage M I T)

/-- The proved E.2.13(5) supplies the omitted clause on the same action. -/
theorem SelectionStructuralSources.remaining {K : GroupClass}
    (earlier : SelectionStructuralSources (G := G) K) :
    SelectionRemainingSources (G := G) K :=
  ⟨earlier.e29, family_quadraticRatio_le_one_of_intersection_eq_bot,
    earlier.e2136, earlier.e2142_center⟩

/-- Selection now requires only the three remaining structural clauses;
its zero-intersection FF bound is proved on the actual pair. -/
theorem exists_selected_of_structural_sources {K : GroupClass}
    (earlier : SelectionStructuralSources (G := G) K)
    {H T M V : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE28 K H T M V) (hchar : generalizedFitting H = pCore 2 H)
    (hw : 0 < globalW V T)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ∃ (I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I), Selected H T M V I k i S :=
  exists_selected_of_remaining_sources earlier.remaining h hchar hw hq hTI hNV

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
