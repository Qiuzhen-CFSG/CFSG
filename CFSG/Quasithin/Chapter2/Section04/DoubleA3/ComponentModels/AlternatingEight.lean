module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentActionNormalizer
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.MarkedCentralizers
public import Theory.Alternating.Aut
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.SpecificGroups.Alternating.EightTwoCentral
public import Theory.SpecificGroups.Alternating.EightFourNormalizer
public import Theory.SpecificGroups.Alternating.EightFourCentralizer

/-!
# Excluding the alternating-eight component in the paired cubic source

The original first cubic block acts faithfully on the component. Its
involution acts as the original marked product z₁z₂, so it centralizes a full
Sylow subgroup of the component. For A₈, the corresponding permutation has
no fixed letters. The commuting permutation group of this A₄ action therefore
has order at most two, forcing its normalizer to have relative index at least
four on every inner Sylow subgroup.

The source supplies the opposite bound of two. We transport that bound through
the actual component-normalizer action and restrict its Sylow image to an
order-64 inner subgroup. No component absorption or additional model marking
is assumed. The final wrapper constructs the original 1.1.5 premise from the
same ambient T and the same product z₁z₂.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, the
alternating-eight exclusion preceding (2.4.32), printed p.547.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
local notation "A8" => alternatingGroup (Fin 8)
local notation "S8" => Equiv.Perm (Fin 8)
local notation "A4" => alternatingGroup (Fin 4)

private def eightAutEquiv : MulAut A8 ≃* S8 :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := A8))
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by decide) (by decide))).symm

private theorem twoPerfect_eight_action_even {L : Type*} [Group L]
    (hL : IsPPerfect 2 L) (f : L →* S8) (l : L) : f l ∈ A8 := by
  have hp : IsPGroup 2 (S8 ⧸ A8) :=
    IsPGroup.of_card (n:=1) (by rw [←index_eq_card,alternatingGroup.index_eq_two]; decide)
  have hh := pResidual_le_ker_of_isPGroup 2 ((QuotientGroup.mk' A8).comp f) hp
  have htop := (pResidual_eq_top_iff 2 L).mpr hL
  exact (QuotientGroup.eq_one_iff (f l)).mp (hh (htop.symm ▸ mem_top l))

private theorem card_eight_sylow {J : Type*} [Group J] [Finite J]
    (e : J ≃* A8) (P : Sylow 2 J) : Nat.card P = 64 := by
  rw [P.card_eq_multiplicity,Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
  norm_num [Nat.factorial]
  rw [show 20160 = 2^6 * 315 by decide,Nat.factorization_mul (by decide) (by decide),Finsupp.add_apply,
    Nat.prime_two.factorization_pow,Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 315)]
  decide

/-- Restrict the original actor Sylow to the inner component. -/
private theorem inner_sylow_image
    {H : Type*} [Group H] [Finite H] (K : Subgroup H)
    (eK : K ≃* A8) (P : Sylow 2 (normalizer (K : Set H))) :
    let a := eightAutEquiv.toMonoidHom.comp
      ((MulAut.congr eK).toMonoidHom.comp K.normalizerMonoidHom)
    ∃ Q : Subgroup S8, Q ≤ (P : Subgroup _).map a ∧ Nat.card Q = 64 := by
  let N := normalizer (K : Set H)
  let K₀ := K.subgroupOf N
  let a := eightAutEquiv.toMonoidHom.comp
    ((MulAut.congr eK).toMonoidHom.comp K.normalizerMonoidHom)
  let e₀ : K₀ ≃* K := subgroupOfEquivOfLe K.le_normalizer
  let : K₀.Normal := Subgroup.normal_in_normalizer
  obtain ⟨R,hR⟩ := P.exists_subgroupOf_eq_of_normal K₀
  have hak (k : K₀) : a (k : N) = (eK (e₀ k) : S8) := by
    change eightAutEquiv ((MulAut.congr eK) (K.normalizerMonoidHom (k:N))) = _
    apply eightAutEquiv.symm.injective
    rw [eightAutEquiv.symm_apply_apply]
    apply MulEquiv.ext
    intro x
    change eK (e₀ k * eK.symm x * (e₀ k)⁻¹) = eK (e₀ k) * x * (eK (e₀ k))⁻¹
    simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
  have hai : Function.Injective (a.comp K₀.subtype) := by
    intro x y hh
    apply e₀.injective
    apply eK.injective
    apply Subtype.ext
    exact (hak x).symm.trans (hh.trans (hak y))
  let Q := ((R : Subgroup K₀).map K₀.subtype).map a
  refine ⟨Q,?_,?_⟩
  · apply map_mono
    rw [hR]
    rintro _ ⟨r,hr,rfl⟩
    exact hr
  · change Nat.card (((R : Subgroup K₀).map K₀.subtype).map a) = 64
    rw [map_map,←Nat.card_congr ((R : Subgroup K₀).equivMapOfInjective
      (a.comp K₀.subtype) hai).toEquiv]
    exact card_eight_sylow (e₀.trans eK) R


variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

private theorem canonical_actor_image
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (f : (d.block.map d.H.subtype) →* MulAut K)
    (hact : ∀ (l : d.block.map d.H.subtype) (k : K),
      ((f l k : involutionCentralizer g.z₂) : G) = (l:G)*(k:G)*(l:G)⁻¹) :
    (((d.block.map d.H.subtype).subgroupOf (involutionCentralizer g.z₂)).subgroupOf
      (normalizer (K : Set (involutionCentralizer g.z₂)))).map K.normalizerMonoidHom = f.range := by
  let H := involutionCentralizer g.z₂
  let L := d.block.map d.H.subtype
  let N := normalizer (K : Set H)
  have hLH : L ≤ H := g.first_block_le_second_centralizer
  have hLN : L.subgroupOf H ≤ N := g.first_block_normalizes_component hG K hK
  ext b
  constructor
  · rintro ⟨n,hn,rfl⟩
    refine ⟨⟨n.val.val,hn⟩,?_⟩
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    apply Subtype.ext
    exact hact _ _
  · rintro ⟨l,rfl⟩
    let n : N := ⟨⟨l,hLH l.property⟩,hLN l.property⟩
    refine ⟨n,l.property,?_⟩
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    apply Subtype.ext
    exact (hact _ _).symm

/-- The original Sylow normalizer bound remains valid on a literal order-64
inner action subgroup after transport to the symmetric-eight model. -/
private theorem source_action_index
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) (eK : K ≃* A8)
    (f : (d.block.map d.H.subtype) →* MulAut K)
    (hact : ∀ (l : d.block.map d.H.subtype) (k : K),
      ((f l k : involutionCentralizer g.z₂) : G) = (l:G)*(k:G)*(l:G)⁻¹) :
    let E := (MulAut.congr eK).trans eightAutEquiv
    ∃ Q : Subgroup S8, Nat.card Q = 64 ∧
      (normalizer (((E.toMonoidHom.comp f).range) : Set S8)).relIndex Q ≤ 2 := by
  let H := involutionCentralizer g.z₂
  let N := normalizer (K : Set H)
  let L := (d.block.map d.H.subtype).subgroupOf H
  let B := (L.subgroupOf N).map K.normalizerMonoidHom
  let E := (MulAut.congr eK).trans eightAutEquiv
  obtain ⟨P,hP,hindex⟩ := g.component_action_normalizer_bound hG K hK
  obtain ⟨Q,hQP,hQcard⟩ := inner_sylow_image K eK P
  have hB : B = f.range := canonical_actor_image g hG K hK f hact
  have hi : (normalizer (((E.toMonoidHom.comp f).range) : Set S8)).relIndex
      (((P : Subgroup N).map K.normalizerMonoidHom).map E.toMonoidHom) ≤ 2 := by
    have hm : B.map E.toMonoidHom = (E.toMonoidHom.comp f).range := by
      rw [hB,MonoidHom.range_comp]
    rw [←hm,←map_equiv_normalizer_eq B E,relIndex_map_map_of_injective _ _ E.injective]
    exact hindex
  refine ⟨Q,hQcard,?_⟩
  apply le_trans (relIndex_le_of_le_right ?_ (show
    (normalizer (((E.toMonoidHom.comp f).range) : Set S8)).relIndex
      (((P : Subgroup N).map K.normalizerMonoidHom).map E.toMonoidHom) ≠ 0 from
    index_ne_zero_of_finite)) hi
  rw [map_map]
  have he : E.toMonoidHom.comp K.normalizerMonoidHom =
      eightAutEquiv.toMonoidHom.comp ((MulAut.congr eK).toMonoidHom.comp K.normalizerMonoidHom) := by
    apply MonoidHom.ext
    intro n
    rfl
  rw [he]
  exact hQP


private theorem first_action_fixedPointFree
    (g : SourceCentralizerGeometry c) (_hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) (eK : K ≃* A8)
    (f : (d.block.map d.H.subtype) →* MulAut K)
    (hact : ∀ (l : d.block.map d.H.subtype) (k : K),
      ((f l k : involutionCentralizer g.z₂) : G) = (l:G)*(k:G)*(l:G)⁻¹)
    (u : d.block.map d.H.subtype) (hu : (u:G) = g.z₁) :
    ∀ i : Fin 8, eightAutEquiv (MulAut.congr eK (f u)) i ≠ i := by
  let H := involutionCentralizer g.z₂
  let E := (MulAut.congr eK).trans eightAutEquiv
  let f8 := E.toMonoidHom.comp f
  have hv : f8 u ∈ A8 := twoPerfect_eight_action_even c.first.short.twoPerfect f8 u
  let v : A8 := ⟨f8 u,hv⟩
  obtain ⟨_,α,P,hα,mark,_⟩ := h.component_inputs K hK
  have hf : f u = α := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    apply Subtype.ext
    have hkc : g.z₂*(k:G)*g.z₂⁻¹ = (k:G) := by
      rw [←mem_centralizer_singleton_iff.mp (k : H).property,mul_inv_cancel_right]
    calc
      ((f u k : H) : G) = g.z₁*(k:G)*g.z₁⁻¹ := by rw [hact,hu]
      _ = g.z₁*(g.z₂*(k:G)*g.z₂⁻¹)*g.z₁⁻¹ := by rw [hkc]
      _ = ((α k : H) : G) := by rw [hα]; group
  have hvo : orderOf v = 2 := by
    rw [←Subgroup.orderOf_coe v]
    change orderOf (E (f u)) = 2
    rw [E.orderOf_eq,hf]
    exact mark.order_two
  let P8 : Sylow 2 A8 := P.mapSurjective (f := eK.toMonoidHom) eK.surjective
  have hconj : MulAut.conj v = MulAut.congr eK α := by
    have hh := eightAutEquiv.symm_apply_apply (MulAut.congr eK (f u))
    change MulAut.conj v = MulAut.congr eK (f u) at hh
    exact hh.trans (congrArg (MulAut.congr eK) hf)
  apply AlternatingEight.twoCentral_fixedPointFree P8 v hvo
  intro p
  obtain ⟨k,hk,he⟩ := p.property
  have hfix : MulAut.conj v (eK k) = eK k := by
    rw [hconj]
    change eK (α (eK.symm (eK k))) = eK k
    rw [eK.symm_apply_apply,mark.fixes k hk]
  have hc : v * eK k = eK k * v := by
    exact mul_inv_eq_iff_eq_mul.mp hfix
  exact congrArg Subtype.val (he ▸ hc)


/-- The original paired-cubic action excludes an alternating-eight component.
The same marked involution and actor Sylow are used throughout. -/
theorem SourceCentralizerGeometry.alternating_eight_model_false
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) (eK : K ≃* A8) : False := by
  obtain ⟨f,hfi,hact⟩ := g.faithful_first_block_action hG h K hK
  obtain ⟨eL⟩ := c.cubic_first.equiv_alternatingFour
  let E := (MulAut.congr eK).trans eightAutEquiv
  let f8 := E.toMonoidHom.comp f
  let F : A4 →* S8 := f8.comp eL.symm.toMonoidHom
  have hFi : Function.Injective F := E.injective.comp (hfi.comp eL.symm.injective)
  let u : d.block.map d.H.subtype := ⟨g.z₁,(map_subtype_le _) g.first_mem⟩
  have hu : orderOf (eL u) = 2 := by
    rw [eL.orderOf_eq,←Subgroup.orderOf_coe u]
    exact g.order_first
  have hfree : ∀ i : Fin 8, F (eL u) i ≠ i := by
    change ∀ i : Fin 8, E (f (eL.symm (eL u))) i ≠ i
    rw [eL.symm_apply_apply]
    exact first_action_fixedPointFree g hG h K hK eK f hact u rfl
  have hc := AlternatingEight.four_centralizer_card_le_two F hFi (eL u) hu hfree
  have hrange : F.range = f8.range := by
    ext σ
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨eL.symm a,rfl⟩
    · rintro ⟨l,rfl⟩
      exact ⟨eL l,congrArg f8 (eL.symm_apply_apply l)⟩
  obtain ⟨Q,hQ,hindex⟩ := source_action_index g hG K hK eK f hact
  have hindex' : (normalizer (F.range : Set S8)).relIndex Q ≤ 2 := by
    rw [hrange]
    exact hindex
  exact AlternatingEight.four_normalizer_index_false F.range Q
    (MonoidHom.ofInjective hFi).symm hc hQ hindex'

/-- Discharge the marked-involution premise from the original ambient data. -/
theorem SourceCentralizerGeometry.alternating_eight_false_from_original
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) (eK : K ≃* A8) : False :=
  g.alternating_eight_model_false hG (g.lemma115 hG hM hTM hu).2 K hK eK

end CFSG.Quasithin.Chapter2.DoubleA3
end
