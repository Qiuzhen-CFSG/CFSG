module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryReeRoots
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryCartan
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.Source
public import Theory.SpecificGroups.ReeF4.LocalPrimeRank
public import Theory.SpecificGroups.ReeF4.LinearLocalFixer
public import Theory.GroupAction.InnerSylowNormalizer
public import Theory.GroupTheory.PerfectCentralCoverCentralQuotient
public import Theory.GroupTheory.GeneralizedFitting.ComponentRankNormality

/-!
# Ree centralization, original Sylow placement and the Cartan obstruction

The root calculation puts each member of the canonical inner image in the
full center of its prescribed Ree Sylow. The actual perfect central cover
has odd center, including at field eight. A rank-two split torus and strong
quasithinness make the component relatively normal.

A genuine end-node torus scales the long-root center faithfully, giving
centralizer index at least seven in the original Sylow normalizer. All
two-power automorphisms of the Ree model are inner. Once that Sylow lies in
the original core Q, its normalizer therefore normalizes the same Q.
The chosen-module application in NonFFSourceDoubledBinaryReeExclusion
combines these results with the literal paired-plane S₃ bound to exclude
the final ordinary-component row.

Source: Aschbacher–Smith 7.7.6, printed p.706, refs/quasithin.pdf. The inner
action gives a direct normalizer argument in this row, retaining the actual
Ree carrier, field parameter, central quotient and original Sylow subgroup.
-/

public noncomputable section
open Subgroup Theory.GroupTheory ReeF4 ReeF4.Parabolics
open CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter7.NormalizedSource
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryReePlacement

private theorem centralizer_comap_equiv {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (x : X) :
    (centralizer ({e x} : Set Y)).comap e.toMonoidHom = centralizer ({x} : Set X) := by
  ext y
  simp only [mem_comap, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    ← map_mul, e.injective.eq_iff]

/-- The original inner image lies in the full center of its original Ree Sylow. -/
theorem ree_centralizes {G : Type*} [Group G] [Finite G]
    {m : ℕ} (hm : 1 ≤ m) (hmodel : LocalModels.IsReeF4At G m)
    (S : Sylow 2 G) (A : Subgroup G) (hAS : A ≤ (S : Subgroup G))
    (hi : ((centralizer (A : Set G)).subgroupOf (S : Subgroup G)).index ≤ 2) :
    A ≤ (center S).map (S : Subgroup G).subtype := by
  obtain ⟨d,⟨e₀⟩⟩ := hmodel
  let e := e₀.trans d.modelEquiv
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨S₀,hS₀⟩ := ReeF4.ConverseParabolics.exists_sylow_eq_unipotent m
  rw [ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.unipotent_eq_rootUnipotent] at hS₀
  let c : S ≃* unipotent m :=
    (e.subgroupMap (S : Subgroup G)).trans ((R.equiv S₀).trans (MulEquiv.subgroupCongr hS₀))
  intro a ha
  let x : S := ⟨a,hAS ha⟩
  have hC : (centralizer ({x} : Set S)) = (centralizer ({a} : Set G)).subgroupOf
      (S : Subgroup G) := by
    ext y
    simp only [mem_centralizer_singleton_iff,mem_subgroupOf,x]
    exact Subtype.ext_iff
  have hidx : (centralizer ({x} : Set S)).index ≤ 2 := by
    rw [hC]
    apply le_trans _ hi
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero index_ne_zero_of_finite)
      (index_dvd_of_le (comap_mono (centralizer_le (Set.singleton_subset_iff.mpr ha))))
  have hcidx : (centralizer ({c x} : Set (unipotent m))).index ≤ 2 := by
    rw [←(centralizer ({c x} : Set _)).index_comap_of_surjective
      (f := c.toMonoidHom) c.surjective,centralizer_comap_equiv]
    exact hidx
  refine ⟨x,mem_center_iff.mpr ?_,rfl⟩
  intro y
  apply c.injective
  simpa only [map_mul] using mem_center_iff.mp
    (DoubledBinaryReeRoots.ree_coordinate_central m hm (c x) hcidx) (c y)

/-- The ordinary component cover has odd center, including field eight. -/
theorem ree_center_odd {K : Type*} [Group K] [Finite K] [IsQuasisimple K]
    {m : ℕ} (hm : 1 ≤ m) (hmodel : LocalModels.IsReeF4At (K ⧸ center K) m) :
    Odd (Nat.card (center K)) := by
  obtain ⟨d,⟨e⟩⟩ := hmodel
  have hh := ReeF4.CentralCovers.TwoPrimary.not_two_dvd_kernel m hm
    (PerfectCentralCovering.centralQuotientCover (e.trans d.modelEquiv))
  rw [PerfectCentralCovering.centralQuotientCover_ker] at hh
  exact Nat.not_even_iff_odd.mp (fun he => hh (even_iff_two_dvd.mp he))

/-- A split-torus prime of rank two makes the component relatively normal. -/
theorem ree_component_normal {G : Type*} [Group G] [Finite G]
    (H K : Subgroup G) (hK : IsComponentIn K H) (hH : IsStronglyQuasithin H)
    (hz : center K = ⊥) {m : ℕ} (hm : 1 ≤ m)
    (hmodel : LocalModels.IsReeF4At (K ⧸ center K) m) : (K.subgroupOf H).Normal := by
  let := hK.quasisimple
  obtain ⟨d,⟨e⟩⟩ := hmodel
  let eK : K ≃* Model m := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans (e.trans d.modelEquiv))
  let e₀ := (subgroupOfEquivOfLe hK.1).trans eK
  have hz₀ : center (K.subgroupOf H) = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr (subgroupOfEquivOfLe hK.1)).toEquiv,hz,card_bot]
  obtain ⟨p,hp,ho,_,hr⟩ := ReeF4.LocalPrimeRank.local_quotient_shared_prime hm .linear
  let : Fact p.Prime := ⟨hp⟩
  apply hK.2.normal_of_centerless_primeRank (p := p) hz₀
  · rw [primeRank_equiv p e₀]
    exact hr
  · exact hH p hp ho

open ReeF4.LargeLocalSeeds ReeF4.LargeLocalSeeds.LinearCommutators
open ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open ReeF4.EvenInvolutionGeometry
open Theory.AlgebraicGroup.StandardRootSystem

private def scalar (m : ℕ) (u : (CoefficientField m)ˣ) : Model m :=
  (canonicalLocalBlockInput m).modelEquiv (endTorusElement (canonicalLocalBlockInput m) u).val

private theorem scalar_split (m : ℕ) (u : (CoefficientField m)ˣ) :
    toSplitGroup m (scalar m u) = endTorusWord m u := by
  rw [toSplitGroup_apply,scalar,LocalBlockInput.modelEquiv_coe]
  rfl

private theorem scalar_normalizes (m : ℕ) (u : (CoefficientField m)ˣ) :
    scalar m u ∈ normalizer (unipotent m : Set (Model m)) := by
  apply (borel_le_unipotent_normalizer_of_splitTorus m (splitTorus_le_unipotent_normalizer m))
  apply fixedTorus_le_borel
  change toSplitGroup m (scalar m u) ∈ splitTorus m
  rw [scalar_split,endTorusWord]
  exact mul_mem (subset_closure ⟨_,_,rfl⟩) (subset_closure ⟨_,_,rfl⟩)

private theorem scalar_root (m : ℕ) (u : (CoefficientField m)ˣ) (a : CoefficientField m) :
    scalar m u * longRootElement m a * (scalar m u)⁻¹ = longRootElement m (u*a) := by
  apply toSplitGroup_injective m
  simpa only [map_mul,map_inv,scalar_split,longRootElement_coe] using
    ReeF4.LinearLocalFixer.endTorus_longRoot m u a

private theorem standard_normalizer_index (m : ℕ) (hm : 1 ≤ m)
    (A : Subgroup (Model m)) (hne : A ≠ ⊥)
    (hAZ : A ≤ (center (unipotent m)).map (unipotent m).subtype) :
    7 ≤ ((centralizer (A : Set (Model m))).subgroupOf
      (normalizer (unipotent m : Set (Model m)))).index := by
  let N := normalizer (unipotent m : Set (Model m))
  let C := (centralizer (A : Set (Model m))).subgroupOf N
  obtain ⟨a,ha,hane⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hroot := hAZ ha
  rw [unipotent_center_eq_longRootGroup m hm] at hroot
  obtain ⟨r,hr⟩ := (mem_longRootGroup m a).mp hroot
  have hr0 : r ≠ 0 := by intro hh; exact hane (hr.symm.trans (by rw [hh,longRootElement_zero]))
  let b (u : (CoefficientField m)ˣ) : N := ⟨scalar m u,scalar_normalizes m u⟩
  let f : (CoefficientField m)ˣ → N ⧸ C := fun u => QuotientGroup.mk (b u)
  have hf : Function.Injective f := by
    intro u v huv
    have hc : (b u)⁻¹ * b v ∈ C := QuotientGroup.eq.mp huv
    have he := mem_centralizer_iff.mp hc a ha
    change a * ((scalar m u)⁻¹ * scalar m v) = ((scalar m u)⁻¹ * scalar m v) * a at he
    have hconj : scalar m v * a * (scalar m v)⁻¹ = scalar m u * a * (scalar m u)⁻¹ := by
      calc
        _ = scalar m u * (((scalar m u)⁻¹ * scalar m v) * a) * (scalar m v)⁻¹ := by group
        _ = scalar m u * (a * ((scalar m u)⁻¹ * scalar m v)) * (scalar m v)⁻¹ := by rw [he]
        _ = _ := by group
    rw [←hr,scalar_root,scalar_root] at hconj
    apply Units.ext
    exact (mul_right_cancel₀ hr0 (longRootElement_injective m hconj)).symm
  have hc := Nat.card_le_card_of_injective f hf
  change Nat.card (CoefficientField m)ˣ ≤ C.index at hc
  rw [Nat.card_units,field_card] at hc
  have hq : 8 ≤ 2^(2*m+1) := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (show 3 ≤ 2*m+1 by omega)
  exact (by omega : 7 ≤ 2^(2*m+1)-1).trans hc

private theorem centralizer_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (A : Subgroup G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image (A : Set G) e.toMonoidHom)
  intro x hx
  obtain ⟨y,rfl⟩ := e.surjective x
  refine ⟨y,?_,rfl⟩
  intro a ha
  apply e.injective
  simpa only [map_mul] using hx (e a) (mem_map_of_mem e.toMonoidHom ha)

/-- The original Ree Sylow normalizer has centralizer index at least seven. -/
theorem ree_normalizer_index {G : Type*} [Group G] [Finite G]
    {m : ℕ} (hm : 1 ≤ m) (hmodel : LocalModels.IsReeF4At G m)
    (P : Sylow 2 G) (A : Subgroup G) (hne : A ≠ ⊥)
    (hAP : A ≤ (P : Subgroup G))
    (hi : ((centralizer (A : Set G)).subgroupOf (P : Subgroup G)).index ≤ 2) :
    7 ≤ ((centralizer (A : Set G)).subgroupOf (normalizer (P : Set G))).index := by
  have hAZ := ree_centralizes hm hmodel P A hAP hi
  obtain ⟨d,⟨e₀⟩⟩ := hmodel
  let e := e₀.trans d.modelEquiv
  obtain ⟨S₀,hS₀⟩ := ReeF4.ConverseParabolics.exists_sylow_eq_unipotent m
  rw [ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.unipotent_eq_rootUnipotent] at hS₀
  let P₀ := S₀.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P₀ P
  let f := e.symm.trans (MulAut.conj g)
  have hP : (unipotent m).map f.toMonoidHom = (P : Subgroup G) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((S₀ : Subgroup (Model m)).map e.symm.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = (P : Subgroup G) at hh
    change (unipotent m).map ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
    rw [←map_map,←hS₀]
    exact hh
  have hZ : ((center (unipotent m)).map (unipotent m).subtype).map f.toMonoidHom =
      (center P).map (P : Subgroup G).subtype := by
    rw [map_embeddedCenter _ _ f.injective,hP]
  let A₀ := A.map f.symm.toMonoidHom
  have hA₀ : A₀.map f.toMonoidHom = A := by
    change (A.map f.symm.toMonoidHom).map f.toMonoidHom = A
    rw [map_map]
    rw [show f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id _ by
      ext x; exact f.apply_symm_apply x,map_id]
  have hAZ₀ : A₀ ≤ (center (unipotent m)).map (unipotent m).subtype := by
    apply (map_le_map_iff_of_injective (f := f.toMonoidHom) f.injective).mp
    rw [hA₀,hZ]
    exact hAZ
  have hne₀ : A₀ ≠ ⊥ := by intro hh; apply hne; rw [←hA₀,hh,Subgroup.map_bot]
  have hb := standard_normalizer_index m hm A₀ hne₀ hAZ₀
  have hN : (normalizer (unipotent m : Set (Model m))).map f.toMonoidHom =
      normalizer (P : Set G) := by
    rw [map_equiv_normalizer_eq,hP]
    rfl
  have hC : (centralizer (A₀ : Set (Model m))).map f.toMonoidHom = centralizer (A : Set G) := by
    rw [centralizer_map_equiv,hA₀]
  change 7 ≤ (centralizer (A : Set G)).relIndex (normalizer (P : Set G))
  rw [←hC,←hN,relIndex_map_map_of_injective _ _ f.injective]
  exact hb

/-- The original core action is inner, so the actual component Sylow normalizer
normalizes that same core. -/
theorem ree_normalizer_le_core_normalizer {G : Type*} [Group G] [Finite G]
    (K Q : Subgroup G) [IsQuasisimple K] (hQ : IsPGroup 2 Q)
    (hQN : Q ≤ normalizer (K : Set G)) (P : Sylow 2 K)
    (hPQ : (P : Subgroup K).map K.subtype ≤ Q)
    {m : ℕ} (hm : 1 ≤ m) (hmodel : LocalModels.IsReeF4At (K ⧸ center K) m) :
    (normalizer (P : Set K)).map K.subtype ≤ normalizer (Q : Set G) := by
  obtain ⟨d,⟨e₀⟩⟩ := hmodel
  let e := e₀.trans d.modelEquiv
  apply sylowNormalizer_le_normalizer_of_inner_action K Q hQ hQN P hPQ
  intro s
  let f : Q →* MulAut (Model m) := (MulAut.centralQuotientAction e).comp
    (K.normalizerMonoidHom.comp (inclusion hQN))
  obtain ⟨n,hn⟩ := hQ s
  have hp : f s ^ (2^n) = 1 := by rw [←map_pow,hn,map_one]
  obtain ⟨g,hg⟩ := ReeF4.Parabolics.OuterLocal.LargeAutomorphisms.inner_of_twoPower hm (f s) n hp
  exact (MulAut.centralQuotientAction_inner_iff e _).mp ⟨g,hg.symm⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryReePlacement
