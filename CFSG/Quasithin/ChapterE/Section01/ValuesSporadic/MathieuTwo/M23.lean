module

public import CFSG.Quasithin.ChapterE.Section01.ValuesSporadic.MathieuTwo.M22
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.Maximal
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalCore
public import Theory.Mathieu.M23.Properties.Automorphisms

/-!
# Rank-two E-generation for M23

A Sylow two-subgroup of the heptad stabilizer is Sylow in M23, since that
stabilizer has odd index 253. It fixes a point in the action of degree 23.
The resulting point stabilizer is genuinely isomorphic to M22. It and the
heptad stabilizer generate M23: the latter is maximal and has strictly
smaller order. Its actual action onto A7 has a two-group kernel, so both
local groups have the required bound.

All automorphisms of the concrete M23 are inner. Hence a faithful normal
copy of M23 is the whole ambient group, covering the extension clause of
E.1.14. The source generalized-Fitting hypothesis supplies faithfulness.

Source: Aschbacher--Smith E.1.14(5), printed p.214, citing Asc82a Lemma 4.9;
the heptad geometry is developed in the project's concrete Witt design.
-/

public section
namespace CFSG.Quasithin.ChapterE.MathieuTwo
open Subgroup Theory.GroupTheory Sporadic.Mathieu Sporadic.Mathieu.M23Geometry

/-- Generation lifts through the kernel of the literal heptad action. -/
theorem heptadStabilizer_isEGenerated : IsEGenerated 2 heptadStabilizer := by
  obtain ⟨f, hf, hk⟩ := heptadStabilizer_alternating_quotient
  exact isEGenerated_of_two_kernel f hf hk alternatingSeven_isEGenerated

/-- The heptad stabilizer and a point stabilizer prove the concrete M23 bound. -/
theorem m23_isEGenerated : IsEGenerated 2 M23 := by
  let U : Sylow 2 heptadStabilizer := default
  have hi : ¬ 2 ∣ ((U : Subgroup heptadStabilizer).map heptadStabilizer.subtype).index := by
    rw [index_map_subtype, heptadStabilizer_index]
    exact Nat.prime_two.not_dvd_mul U.not_dvd_index (by decide)
  let T : Sylow 2 M23 := (U.isPGroup'.map heptadStabilizer.subtype).toSylow hi
  have hTH : (T : Subgroup M23) ≤ heptadStabilizer := map_subtype_le _
  obtain ⟨a, ha⟩ := T.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card
    (Fin 23) (by norm_num)
  have hTP : (T : Subgroup M23) ≤ MulAction.stabilizer M23 a := by
    intro t ht
    exact ha ⟨t, ht⟩
  let := m23_isPretransitive
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M23 (9 : Fin 23) a
  let e : M22 ≃* MulAction.stabilizer M23 a :=
    m23EquivM22PointStabilizer.trans (MulAction.stabilizerEquivStabilizer hg.symm)
  have hc : Nat.card (MulAction.stabilizer M23 a) = 443520 :=
    (Nat.card_congr e.toEquiv).symm.trans m22_order
  have hHP : heptadStabilizer ⊔ MulAction.stabilizer M23 a = ⊤ := by
    apply heptadStabilizer_isCoatom.2
    apply lt_of_le_of_ne le_sup_left
    intro he
    have hPH : MulAction.stabilizer M23 a ≤ heptadStabilizer := he ▸ le_sup_right
    have hcard := card_le_of_le hPH
    rw [heptadStabilizer_card, hc] at hcard
    omega
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget 2 T Ω
  rw [← hHP]
  exact sup_le
    (ChiefOrbit.overgroup_le_generationTarget T _ hTH hΩ heptadStabilizer_isEGenerated)
    (ChiefOrbit.overgroup_le_generationTarget T _ hTP hΩ (m22_isEGenerated.map_equiv e))

variable {G : Type*} [Group G]

/-- There is no proper faithful extension of M23, by its actual automorphism theorem. -/
theorem m23_extension_eq_top (L : Subgroup G) [L.Normal]
    (hC : centralizer (L : Set G) = ⊥) (e : L ≃* M23) : L = ⊤ := by
  have hs : Function.Surjective (MulAut.conj : L →* MulAut L) := by
    intro a
    obtain ⟨x, hx⟩ := m23_conj_surjective ((MulAut.congr e) a)
    refine ⟨e.symm x, (MulAut.congr e).injective ?_⟩
    rw [MulAut.congr_conj, e.apply_symm_apply, hx]
  have hinner : MulAut.innerSubgroup L = ⊤ := MonoidHom.range_eq_top.mpr hs
  have h := MulAut.conjNormal_comap_innerSubgroup L
  rw [hinner, comap_top, hC, sup_bot_eq] at h
  exact h.symm

variable [Finite G]

/-- The M23 case with the literal generalized-Fitting hypothesis of E.1.14. -/
theorem m23_generalizedFitting_isEGenerated (L : Subgroup G)
    (hL : L = generalizedFitting G) [IsSimpleGroup L]
    (e : L ≃* M23) : IsEGenerated 2 G := by
  subst L
  have ha : ¬ IsMulCommutative (generalizedFitting G) := by
    intro hc
    let := hc
    have hp : (Nat.card (generalizedFitting G)).Prime :=
      Group.is_simple_iff_prime_card.mp inferInstance
    rw [Nat.card_congr e.toEquiv, m23_order] at hp
    norm_num at hp
  have htop := m23_extension_eq_top _ (SimpleSocle.centralizer_eq_bot ha) e
  let f : G ≃* M23 := Subgroup.topEquiv.symm.trans
    ((MulEquiv.subgroupCongr htop.symm).trans e)
  exact m23_isEGenerated.map_equiv f.symm

end CFSG.Quasithin.ChapterE.MathieuTwo
