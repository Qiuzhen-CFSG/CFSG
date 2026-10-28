module
public import CFSG.Quasithin.ChapterG.Section06.SourceClassification.TwoFactorReconstruction.AmbientNormalizer
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.ComponentPairSylowUnique
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.LinearThree
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
/-!
# Minimal parabolicity excludes the paired binary-three row of G.6.4

The actual factor stabilizer is the commuting product of the two factors.
The original Sylow exchanges them and generates the group with either factor.
Minimal parabolicity therefore descends to the intrinsic Sylow subgroup of
that factor. The point and line parabolics of GL₃(2) contradict unique maximality.
All factor normality, generation and model conditions are derived from the
literal G.6.4 output and faithful action.

Source: Aschbacher--Smith G.6.4(3) and the application in 10.2.1,
printed pp.346 and743, using B.6.8(3), pp.114--115.
-/
public section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterG.Section06
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]

private theorem sl3_not_unique (S : Sylow 2 SL(3,ZMod 2)) :
    ¬ Order.HasUniqueMaximalOver (S : Subgroup SL(3,ZMod 2)) ⊤ := by
  let ρ := linearNatural BinaryField.two 3
  have hm : IsRepeatedLinearNatural (ρ.comp (⊤ : Subgroup SL(3,ZMod 2)).subtype)
      BinaryField.two 3 1 := by
    refine ⟨⟨Subgroup.topEquiv, (LinearEquiv.funUnique (Fin 1) (ZMod 2) (Fin 3 → ZMod 2)).symm, ?_⟩⟩
    intro g v
    funext i
    rfl
  obtain ⟨P,Q,hPQ,hP,hQ,_,_,hiP,hiQ⟩ :=
    ChapterB.exists_sylow_invariant_linear_three_parabolics S ⊤ ρ BinaryField.two 1 (by decide) hm
  intro hu
  obtain ⟨M,hM,_⟩ := hu.2
  have hPM := hu.le_maximal hM (by simpa using hiP) (lt_top_iff_ne_top.mpr hP)
  have hQM := hu.le_maximal hM (by simpa using hiQ) (lt_top_iff_ne_top.mpr hQ)
  exact hM.2.ne (top_unique (hPQ ▸ sup_le hPM hQM))

omit [Finite G] in
private theorem factor_normalizer {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {a : G} (d : TwoFactors ρ a)
    (hf : Function.Injective ρ) : normalizer (d.first : Set G) = d.first ⊔ d.second := by
  have hne : d.first ≠ d.second := by
    intro he
    apply d.second_nontrivial
    simpa only [he,inf_idem] using d.disjoint
  apply le_antisymm
  · intro g hg
    have hga : d.first.map (MulAut.conj g).toMonoidHom = d.first :=
      mem_normalizer_iff_map_conj_eq.mp hg
    have hgb : d.second.map (MulAut.conj g).toMonoidHom = d.second :=
      (d.permutation g).resolve_right (fun h => hne (hga.symm.trans h.1)) |>.2
    rw [d.join_eq]
    exact TwoFactorReconstruction.mem_closure_of_preserves_factors d.toTwoFactorModules hf g hga hgb
  · exact sup_le d.first.le_normalizer ((commutator_eq_bot_iff_le_centralizer.mp
      (by rw [commutator_comm]; exact d.commute)).trans (Subgroup.centralizer_le_normalizer _))

private theorem factor_generation {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {a : G} (d : TwoFactors ρ a)
    (hf : Function.Injective ρ) (T : Sylow 2 G) : d.first ⊔ (T : Subgroup G) = ⊤ := by
  have hne : d.first ≠ d.second := by
    intro he
    apply d.second_nontrivial
    simpa only [he,inf_idem] using d.disjoint
  have hsub : (Set.range fun g : G => d.first.map (MulAut.conj g).toMonoidHom) ⊆
      {d.first, d.second} := by
    rintro _ ⟨g,rfl⟩
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using (d.permutation g).imp And.left And.left
  have hi : (normalizer (d.first : Set G)).index ≤ 2 := by
    rw [← ncard_conjugates_eq_index_normalizer]
    exact (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hne)
  have hin : (normalizer (d.first : Set G)).index ≠ 1 := by
    intro he
    obtain ⟨t,_,_,_,ht⟩ := d.extension
    have hn := mem_normalizer_iff_map_conj_eq.mp (show t ∈ normalizer (d.first : Set G) from index_eq_one.mp he ▸ mem_top t)
    exact hne (hn.symm.trans ht)
  have hi2 : (normalizer (d.first : Set G)).index = 2 := by
    have := (normalizer (d.first : Set G)).index_ne_zero_of_finite
    omega
  have hTn : ¬ (T : Subgroup G) ≤ normalizer (d.first : Set G) := by
    intro he
    have hdiv := index_dvd_of_le he
    rw [hi2] at hdiv
    exact T.not_dvd_index hdiv
  obtain ⟨s,hs,hsn⟩ := Set.not_subset.mp hTn
  have hswap : d.first.map (MulAut.conj s).toMonoidHom = d.second :=
    ((d.permutation s).resolve_left (fun h => hsn (mem_normalizer_iff_map_conj_eq.mpr h.1))).1
  let J := d.first ⊔ (T : Subgroup G)
  have hBJ : d.second ≤ J := by
    rw [← hswap]
    rintro x ⟨y,hy,rfl⟩
    exact J.mul_mem (J.mul_mem (mem_sup_right hs) (mem_sup_left hy)) (J.inv_mem (mem_sup_right hs))
  have hNJ : normalizer (d.first : Set G) ≤ J := by
    rw [factor_normalizer d hf]
    exact sup_le le_sup_left hBJ
  have hiJ : J.index ∣ 2 := hi2 ▸ index_dvd_of_le hNJ
  rcases (Nat.dvd_prime Nat.prime_two).mp hiJ with h1 | h2
  · exact index_eq_one.mp h1
  · have hh := index_dvd_of_le (show (T : Subgroup G) ≤ J from le_sup_right)
    rw [h2] at hh
    exact (T.not_dvd_index hh).elim
/-- The pure exchanged pair in G.6.4 has no binary three-dimensional factor
when the ambient group is minimal parabolic. -/
theorem TwoFactors.not_binary_three_first
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} {a : G} (d : TwoFactors ρ a)
    (hf : Function.Injective ρ) (T : Sylow 2 G)
    (hmin : ChapterB.IsMinimalParabolicOver T ⊤) :
    ¬ HasModelOn ρ d.first (Representation.BinaryOffender.subspaceCommutator ρ ⊤ d.first)
      (binaryLinearAction 3) := by
  rintro ⟨e,_,_,_⟩
  let eSL := e.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
  let : IsSimpleGroup SL(3,ZMod 2) := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup d.first := eSL.isSimpleGroup
  let : Group.IsPerfect (BinaryLinear.OuterCyclic.LinearGroup 3) :=
    BinaryLinear.linearGroup_isPerfect 3 (by decide)
  let : Group.IsPerfect d.first := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hz : center d.first = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center d.first) inferInstance with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative d.first (center_eq_top_iff.mp ht)).elim
  have hq : IsQuasisimple d.first := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  have hns : d.first.IsSubnormal := by
    apply Subgroup.IsSubnormal.step d.first (normalClosure ({a} : Set G))
      (d.join_eq ▸ le_sup_left) (inferInstance : (normalClosure ({a} : Set G)).Normal).isSubnormal
    apply (normal_subgroupOf_iff_le_normalizer (d.join_eq ▸ le_sup_left)).mpr
    rw [←d.join_eq,←factor_normalizer d hf]
  have hA : IsComponent G d.first := ⟨hns,hq⟩
  have heven : 2 ∣ Nat.card d.first := by
    rw [Nat.card_congr eSL.toEquiv,Atlas.Comparisons.Exceptional.sl3Two_card]
    decide
  have hu := ChapterB.component_sylow_unique_of_pair_normalizer T hmin d.first d.second hA
    heven (factor_generation d hf T) (commutator_eq_bot_iff_le_centralizer.mp d.commute)
    (disjoint_iff.mpr d.disjoint) (factor_normalizer d hf)
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_subnormal d.first hns
  let S := P.mapSurjective (f := eSL.toMonoidHom) eSL.surjective
  apply sl3_not_unique S
  have hh := hu.map eSL.mapSubgroup
  rw [OrderIso.map_top] at hh
  change Order.HasUniqueMaximalOver (((T : Subgroup G).subgroupOf d.first).map eSL.toMonoidHom) ⊤ at hh
  change Order.HasUniqueMaximalOver ((P : Subgroup d.first).map eSL.toMonoidHom) ⊤
  rwa [hP]
end CFSG.Quasithin.ChapterG.Section06
