module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.LocalOvergroups.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.M24.SylowNormalizer
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.Alternatives
public import Theory.Mathieu.M24.LocalGeometry.LinearFourCore

/-!
# The octad branch of the M₂₄ pair-placement alternative

An octad stabilizer has order 322,560, whose three-part is nine. Thus a
source odd complement in it is elementary abelian of order nine. Restriction
to the octad is the proved surjection onto A₈ with a kernel of order sixteen,
and is injective on this complement. The Sylow subgroup restricts and maps
to a Sylow subgroup of A₈; the two image subgroups still permute.

Every extending pair automorphism of M₂₄ is inner. The proved self-normalizing
Sylow theorem puts its conjugator inside the Sylow subgroup, hence inside
the octad stabilizer. An invariant line for the common inner normalizer in
A₈ therefore pulls back to a line in the complement's Frattini quotient.
Octad conjugacy makes the reduction uniform over all actual octads.

Only the eight-point line calculation is assumed in the final theorem of
this module. Its explicit `EightPointPairLine` premise remains unproved here.
It must be discharged before claiming the M₂₄ source exclusion.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), and GLS3, Table 5.3e, the E₁₆.A₈ octad stabilizer.
-/

@[expose] public section

open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.Placement
open scoped Pointwise

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction

/-- An odd complement lying in an octad stabilizer has order nine;
the extraspecial order 27 is excluded by the actual stabilizer order. -/
theorem elementary_of_le_octad {R : Subgroup M24} (hR : XiOddQuotient 3 R)
    (O : Octad) (hRO : R ≤ octadStabilizer O) :
    IsElementaryAbelian 3 R ∧ Nat.card R = 9 := by
  rcases hR with h | ⟨_, hc, _⟩
  · exact h
  · have hd := card_dvd_of_le hRO
    rw [hc, octadStabilizer_card] at hd
    norm_num at hd

/-- The intransitive branch cannot contain an extraspecial complement of order
27: its Sylow overgroup fixes an octad, whose stabilizer has three-part nine. -/
theorem elementary_of_intransitive_pair {S : Sylow 2 M24} {R : Subgroup M24}
    (h : PairInput S R)
    (hnt : ¬ MulAction.IsPretransitive (R ⊔ S.toSubgroup : Subgroup M24) (Fin 24)) :
    IsElementaryAbelian 3 R ∧ Nat.card R = 9 := by
  obtain ⟨O, hO⟩ :=
    LinearFourPlacement.intransitive_sylow_overgroup_le_octadStabilizer
      S (R ⊔ S.toSubgroup) le_sup_right hnt
  exact elementary_of_le_octad h.oddComplement O (le_sup_left.trans hO)

/-- Every extending pair automorphism is conjugation by an element of
the Sylow subgroup that also normalizes the complement. -/
theorem pairAutomizer_inner_mem_sylow (S : Sylow 2 M24) (R : Subgroup M24)
    {a : MulAut R} (ha : a ∈ pairAutomizer S.toSubgroup R) :
    ∃ g ∈ S.toSubgroup ⊓ normalizer (R : Set M24),
      ∀ r : R, (a r : M24) = g * r * g⁻¹ := by
  obtain ⟨g, hg, he⟩ := pairAutomizer_inner S.toSubgroup R ha
  refine ⟨g, ⟨sylowNormalizerControl S hg, ?_⟩, he⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change g * x * g⁻¹ ∈ R
    rw [← he ⟨x, hx⟩]
    exact (a ⟨x, hx⟩).property
  · intro hy
    obtain ⟨x, hx⟩ := a.surjective ⟨y, hy⟩
    exact ⟨x, x.property, (he x).symm.trans (congrArg Subtype.val hx)⟩

private theorem seed_pairReducible (hline : EightPointPairLine)
    (S : Sylow 2 M24) (R : Subgroup M24) (h : PairInput S R)
    (hle : R ⊔ S.toSubgroup ≤ octadStabilizer LinearFourCore.seedOctad) :
    PairReducible S.toSubgroup R := by
  classical
  let H := octadStabilizer LinearFourCore.seedOctad
  have hRH : R ≤ H := le_sup_left.trans hle
  have hSH : S.toSubgroup ≤ H := le_sup_right.trans hle
  have hR := elementary_of_le_octad h.oddComplement LinearFourCore.seedOctad hRH
  let _ := hR.1
  let _ : Fact (IsPGroup 3 R) := ⟨h.oddComplement.isPGroup⟩
  let e := (Finset.equivFinOfCardEq
    (m24Blocks_card _ LinearFourCore.seedOctad.property)).altCongrHom
  let octadAction : H →* alternatingGroup LinearFourCore.seedOctad.val :=
    (LinearFourCore.action LinearFourCore.seedOctad).codRestrict _
      (fun g => LinearFourCore.action_range ▸ ⟨g, rfl⟩)
  let f : H →* alternatingGroup (Fin 8) :=
    e.toMonoidHom.comp octadAction
  have hf : Function.Surjective f := by
    intro z
    obtain ⟨b, rfl⟩ := e.surjective z
    have hb : b.val ∈ (LinearFourCore.action LinearFourCore.seedOctad).range :=
      LinearFourCore.action_range.symm ▸ b.property
    obtain ⟨g, hg⟩ := hb
    exact ⟨g, congrArg e (Subtype.ext hg)⟩
  have hker : f.ker = (LinearFourCore.action LinearFourCore.seedOctad).ker := by
    ext x
    change e (octadAction x) = 1 ↔ _
    rw [← map_one e, e.injective.eq_iff]
    exact Subtype.ext_iff
  have htwo : IsPGroup 2 f.ker := by
    rw [hker]
    exact IsPGroup.of_card (n := 4) LinearFourCore.kernel_card
  let fR : R →* alternatingGroup (Fin 8) := f.comp (inclusion hRH)
  have hfR : Function.Injective fR := by
    apply (MonoidHom.ker_eq_bot_iff fR).mp
    apply bot_unique
    intro x hx
    have hd : Disjoint (R.subgroupOf H) f.ker :=
      (h.oddComplement.isPGroup.comap_of_injective H.subtype H.subtype_injective).disjoint_of_coprime htwo (by decide)
    have heq : inclusion hRH x = 1 := hd.le_bot ⟨x.property, hx⟩
    exact Subtype.ext (congrArg (fun z : H => (z : M24)) heq)
  let P := (S.subtype hSH).mapSurjective hf
  let D := fR.range
  have hD : D = (R.subgroupOf H).map f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨inclusion hRH x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hDc : Nat.card D = 9 :=
    (Nat.card_congr (MonoidHom.ofInjective hfR).toEquiv).symm.trans hR.2
  have hDe : IsElementaryAbelian 3 D :=
    IsElementaryAbelian.of_surjective fR.rangeRestrict fR.rangeRestrict_surjective
  have hpermH : (R.subgroupOf H : Set H) * (S.toSubgroup.subgroupOf H : Set H) =
      (S.toSubgroup.subgroupOf H : Set H) * (R.subgroupOf H : Set H) := by
    apply H.subtype_injective.image_injective
    simpa only [Set.image_mul, ← coe_map, map_subgroupOf_eq_of_le hRH,
      map_subgroupOf_eq_of_le hSH, Sylow.coe_coe] using h.permutes
  have hperm : (D : Set (alternatingGroup (Fin 8))) * (P : Set (alternatingGroup (Fin 8))) =
      (P : Set (alternatingGroup (Fin 8))) * (D : Set (alternatingGroup (Fin 8))) := by
    rw [hD]
    change ((R.subgroupOf H).map f : Set (alternatingGroup (Fin 8))) *
      ((S.toSubgroup.subgroupOf H).map f : Set (alternatingGroup (Fin 8))) =
      ((S.toSubgroup.subgroupOf H).map f : Set (alternatingGroup (Fin 8))) *
      ((R.subgroupOf H).map f : Set (alternatingGroup (Fin 8)))
    simpa only [coe_map, Set.image_mul] using congrArg (Set.image f) hpermH
  obtain ⟨C, hCD, hCc, hCi⟩ := hline P D hDe hDc hperm
  let A := C.comap fR
  have hAcard : Nat.card A = 3 := by
    rw [← card_map_of_injective (K := A) hfR, map_comap_eq_self hCD, hCc]
  have hAb : A ≠ ⊥ := by
    intro hh
    rw [hh, card_bot] at hAcard
    omega
  have hAt : A ≠ ⊤ := by
    intro hh
    rw [hh, card_top, hR.2] at hAcard
    omega
  have hAinv : ∀ a ∈ pairAutomizer S.toSubgroup R, ∀ r ∈ A, a r ∈ A := by
    intro a ha r hr
    obtain ⟨g, hg, he⟩ := pairAutomizer_inner_mem_sylow S R ha
    let gH : H := ⟨g, hSH hg.1⟩
    have hgP : f gH ∈ (P : Subgroup _) := mem_map_of_mem f hg.1
    have hgN : gH ∈ normalizer (R.subgroupOf H : Set H) :=
      le_normalizer_comap H.subtype hg.2
    have hgD : f gH ∈ normalizer (D : Set (alternatingGroup (Fin 8))) := by
      rw [hD]
      exact le_normalizer_map f (mem_map_of_mem f hgN)
    have hcj : inclusion hRH (a r) = gH * inclusion hRH r * gH⁻¹ :=
      Subtype.ext (he r)
    change f (inclusion hRH (a r)) ∈ C
    rw [hcj, map_mul, map_mul, map_inv]
    exact hCi (f gH) ⟨hgP, hgD⟩ (fR r) hr
  let q := QuotientGroup.mk' (frattini R)
  have hq : Function.Injective q := by
    apply (MonoidHom.ker_eq_bot_iff q).mp
    rw [QuotientGroup.ker_mk', frattini_eq_bot_of_isElementaryAbelian (p := 3)]
  apply pairReducible_of_invariant
  refine ⟨A.map q, ?_, ?_, ?_⟩
  · exact fun hb => hAb ((A.map_eq_bot_iff_of_injective hq).mp hb)
  · intro ht
    apply hAt
    apply map_injective hq
    rw [ht, map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  · rintro a ha x ⟨r, hr, rfl⟩
    rw [quotientAut_apply_mk]
    exact mem_map_of_mem q (hAinv a ha r hr)

/-- The eight-point line calculation suffices for every native octad branch.
The invariant line is pulled back through the actual restriction action,
then transported through the Frattini quotient and octad conjugacy. -/
theorem pairReducible_of_eightPointPairLine (hline : EightPointPairLine)
    (S : Sylow 2 M24) (R : Subgroup M24) (h : PairInput S R)
    (O : Octad) (hle : R ⊔ S.toSubgroup ≤ octadStabilizer O) :
    PairReducible S.toSubgroup R := by
  obtain ⟨g, hg⟩ := exists_smul_octad_eq O LinearFourCore.seedOctad
  let e : MulAut M24 := MulAut.conj g
  have hgeom : (octadStabilizer O).map e.toMonoidHom =
      octadStabilizer LinearFourCore.seedOctad := by
    change _ = MulAction.stabilizer M24 LinearFourCore.seedOctad.val
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    rfl
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let R' := R.map e.toMonoidHom
  have hle' : R' ⊔ S'.toSubgroup ≤ octadStabilizer LinearFourCore.seedOctad := by
    rw [← hgeom]
    change R.map e.toMonoidHom ⊔ S.toSubgroup.map e.toMonoidHom ≤ _
    rw [← Subgroup.map_sup]
    exact map_mono hle
  exact pairReducible_of_map e S.toSubgroup R
    (seed_pairReducible hline S' R' (pairInput_map e h) hle')

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.M24PairAction

end
