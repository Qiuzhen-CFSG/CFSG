module
public import CFSG.Quasithin.Chapter13.Section01.RadicalNormality.OrbitSource.Overgroups
/-!
# The original canonical radical is unchanged along a local chain

The odd radical of L₀ is normal in each containing local K by the actual
whole-orbit exclusion. Its quotient embeds as a normal p-subgroup of K/O₂(K)
and lies in the exponent-p omega layer. Two-perfectness then places it in
Ξₚ(K). Both groups are original irreducible members of Ξ(G,T), so relative
normality forces equality. Thus the original Ξₚ(L₀) is characteristic in K.

The earlier whole-orbit bound and universal A clauses retain their existing
producers. No radical identification or characteristicity is an input.
Source: Aschbacher--Smith, 13.1.4, p.867, and the radical comparison in1.3.8.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.XiEmbedding Chapter12.Section02
open Chapter1.Section02 Chapter1.Section02.Adequate
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem normal_Xi_le_XiP {T X K : Subgroup G}
    (hX : XiMember T X) (hXK : X ≤ K) (hn : (X.subgroupOf K).Normal)
    {p : ℕ} [Fact p.Prime] (hq : XiOddQuotient p (XiQuotient X)) : X ≤ XiP p K := by
  let f := normalRadicalMap hXK
  have hp : IsPGroup p f.range := hq.isPGroup.of_equiv (normalRadicalEquiv hXK hn)
  have hfn : f.range.Normal := by
    change (normalRadicalMap hXK).range.Normal
    rw [normalRadicalMap, MonoidHom.range_comp, inclusion_range]
    exact hn.map _ (QuotientGroup.mk'_surjective _)
  have hcore : f.range ≤ pCore p (XiQuotient K) := le_sSup ⟨hfn, hp⟩
  have hshape := hq.of_mulEquiv (normalRadicalEquiv hXK hn)
  have hpow (x : f.range) : x ^ p = 1 := by
    rcases hshape with ⟨hE, _⟩ | ⟨_, _, hexp⟩
    · let := hE
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hE.exponent_dvd_p x
    · rw [← hexp]
      exact Monoid.pow_exponent_eq_one x
  have homega : f.range ≤ xiOmegaCore p K := by
    intro x hx
    refine ⟨⟨x, hcore hx⟩, subset_closure ?_, rfl⟩
    change (⟨x, hcore hx⟩ : pCore p (XiQuotient K)) ^ (p ^ 1) = 1
    apply Subtype.ext
    simpa only [coe_pow, coe_one, pow_one] using congrArg Subtype.val (hpow ⟨x, hx⟩)
  have hpre : X ≤ (xiPPreimage p K).map K.subtype := by
    intro x hx
    refine ⟨inclusion hXK ⟨x, hx⟩, ?_, rfl⟩
    exact homega ⟨⟨x, hx⟩, rfl⟩
  have hr := embedded_pResidual_mono 2 hpre
  rw [(pResidual_eq_top_iff 2 X).mpr hX.perfect,
    ← MonoidHom.range_eq_map, range_subtype, ← map_embedded_pResidual] at hr
  exact hr

variable {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → A36Conclusion C)
    (hA38 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK KnownSimple.IsKnownSimple D → pCore 2 D = ⊥ →
      ∀ C : Subgroup D, C.IsCComponent → C.Normal ∨ IsQuasisimple C)
    (hA410 : A410EarlierResult G)
    (hbound : ∀ (K W : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T K →
      ∀ D : ChosenModule T K W, cubicRatio D.orbitRepresentation ≤ 2)
include h hA36 hA38 hA410 hbound

theorem Hypothesis1311.radical_eq_of_overgroup_of_orbit_bound
    {L₀ K : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    (hK : K ∈ L G T) (hLK : L₀ ≤ K)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    XiP p L₀ = XiP p K := by
  have hKL := h.nonquasisimpleFaithful_overgroup_of_orbit_bound hA36 hA38 hA410 hbound hL hK hLK
  have hn := h.radical_normal_in_overgroup_of_orbit_bound hA36 hA38 hA410 hbound hL hK hLK ho hd
  have hl := ((mem_faithfulLocalComponents_iff T L₀).mp hL.1).1
  have hQ : ∀ D ∈ L G (T : Subgroup G),
      IsSQTK KnownSimple.IsKnownSimple ((D ⊔ T : Subgroup G) ⧸ pCore 2 (D ⊔ T : Subgroup G)) :=
    fun D hD => uniqueness_local_quotient_sqtk h.simpleQTKE hD.2.2
  have hshape := (XiP_oddQuotient_of_A36 hA36 hl (hQ L₀ hl) hL.2 ho hd).2
  have hXK : XiP p L₀ ≤ K := (XiP_le p L₀).trans hLK
  have hdk := prime_dvd_fitting_of_normal_radical hXK hn hshape
  have hX : XiMember (T : Subgroup G) (XiP p L₀) :=
    lemma_1_3_3 hA36 hA38 hQ ⟨L₀, hl, hL.2, p, Fact.out, ho, hd, rfl⟩
  have hY : XiMember (T : Subgroup G) (XiP p K) :=
    lemma_1_3_3 hA36 hA38 hQ ⟨K, hK, hKL.2, p, Fact.out, ho, hdk, rfl⟩
  have hXY := normal_Xi_le_XiP hX hXK hn hshape
  have hNY : ((XiP p L₀).subgroupOf (XiP p K)).Normal :=
    normal_subgroupOf_of_le_normalizer ((XiP_le p K).trans
      ((normal_subgroupOf_iff_le_normalizer hXK).mp hn))
  exact RadicalIdentification.eq_of_normal_le hX hY hXY hNY

theorem Hypothesis1311.radical_characteristic_in_overgroup_of_orbit_bound
    {L₀ K : Subgroup G} (hL : L₀ ∈ nonquasisimpleFaithful T)
    (hK : K ∈ L G T) (hLK : L₀ ≤ K)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀))) :
    ((XiP p L₀).subgroupOf K).Characteristic := by
  rw [h.radical_eq_of_overgroup_of_orbit_bound hA36 hA38 hA410 hbound hL hK hLK ho hd]
  infer_instance
end CFSG.Quasithin.Chapter13.Section01
