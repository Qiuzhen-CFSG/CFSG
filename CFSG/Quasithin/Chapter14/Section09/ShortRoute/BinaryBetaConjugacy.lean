module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.BinaryRootConjugacy
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryInteriorStars
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairFixedSpaces

/-!
# Central-translate separation for the binary elementary beta root

In the elementary commuting distance-one branch, the binary beta quotient
has Sylow subgroups of order two. Its neighboring seed has index two in
Z_alpha. The established two-seed fixed-space calculation shows that an
individual seed element outside Q_beta has no new centralizers in Q_beta
modulo Z_beta. In the whole beta local group, a centralizing quotient image
normalizes the same Sylow subgroup. The original edge factorization then
reduces to this two-core calculation.

Every element of the full local center consequently lies in the elementary
neighboring seed, identifying that center with Z_beta. Interior-star
fixation places the literal four-path radical in this seed, and the odd
five-path fixer makes every nonidentity root survive the endpoint action.
This proves the actual conjugacy-class intersection with the full central
coset. The final application constructs the original full-Cartan four-path
root and its local conjugate reflection and applies that intersection theorem.
The universal-to-reduced map is retained throughout.

This is the binary beta specialization of DGS (14.8). The two-root central
correction, reflection membership, alpha exchange, and full profile assembly
are subsequent obligations. No strict (14.9)(c) actor premise is used.

Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.3), (11.6)--(11.7), pp.168--175; (14.1)--(14.2), pp.210--211;
and (14.8), pp.214--215.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute
open CommutingOneProfile CommutingTrivial CommutingNontrivial
variable {G : Type*} [Group G]
section Local
variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {k : Type*} [Field k] [Finite k] [CharP k 2]

private theorem binary_rankOne {H : Type*} [Group H] (e : H ≃* SL(2,ZMod 2)) :
    IsRankOneModel H := by
  let f : SL(2,ZMod 2) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (ZMod 2))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  exact .linear 1 (by decide) ⟨ZMod 2,inferInstance,inferInstance,by simp,⟨e.trans f⟩⟩

/-- For a binary beta seed element outside the beta core, the centralizer
preimage in that core is exactly its intersection with the alpha seed. -/
theorem binary_beta_core_centralizer_preimage
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (x : G) (hx : x ∈ Z (family P) a) (hxQ : x ∉ Q (family P) b)
    (q : G) (hq : q ∈ Q (family P) b) :
    ⁅q,x⁆ ∈ Z (family P) b ↔ q ∈ Z (family P) a := by
  let F := family P
  let := finite_endpoints h
  let := source_center_elementary h a
  have Mb := binary_rankOne eb
  have hcore := source_linear_binary_beta_core_structure h hB d hc hb hcomm hbc hac
    Ma ea eb g hga hgb
  have hcent := (source_linear_rankOne_center_intersections h hB d hc hb hcomm
    hbc hac Ma Mb ea).2.2.1
  have hfixed := (source_rankOne_pair_fixed_preimages h hB d hc hb hbc hac Ma Mb
    q (hcore.1 ▸ hq)).1
  rw [hcent] at hfixed
  constructor
  · intro hqx
    apply ((hfixed.mp ?_).1)
    intro t ht
    by_cases htQ : t ∈ Q F b
    · exact hcore.2.2.2.2.1 (commutator_mem_commutator hq htQ)
    have htx : t*x ∈ Q F b := by
      have hi := source_binary_seed_index h d hc hb eb
      have hnotx : (⟨x,hx⟩ : Z F a) ∉ (Z F a ⊓ Q F b).subgroupOf (Z F a) :=
        fun hh => hxQ hh.2
      have hnott : (⟨t,ht⟩ : Z F a) ∉ (Z F a ⊓ Q F b).subgroupOf (Z F a) :=
        fun hh => htQ hh.2
      exact ((mul_mem_iff_of_index_two hi (a := (⟨t,ht⟩ : Z F a))
        (b := (⟨x,hx⟩ : Z F a))).mpr (iff_of_false hnott hnotx)).2
    have hqtx : ⁅q,t*x⁆ ∈ Z F b := hcore.2.2.2.2.1
      (commutator_mem_commutator hq htx)
    have hn : t ∈ normalizer (Z F b : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F b)).mp (Z_normal F b)
        ((((source_Z_Q_U h a).1.trans (map_subtype_le _)).trans
          (source_Z_Q_U h a).2).trans
            ((ballKernel_one_le_edge F (source_critical_one_adjacent hc hb)).trans inf_le_right) ht)
    have hcj : t*⁅q,x⁆*t⁻¹ ∈ Z F b := (mem_normalizer_iff.mp hn _).mp hqx
    rw [commutatorElement_mul_right_eq_mul_conj,
      show ⁅q,t⁆*t*⁅q,x⁆*t⁻¹=⁅q,t⁆*(t*⁅q,x⁆*t⁻¹) by group] at hqtx
    exact (Z F b).mul_mem_cancel_right hcj |>.mp hqtx
  · intro hqa
    have he : q*x=x*q := congrArg Subtype.val
      (mul_comm (⟨q,hqa⟩ : Z F a) ⟨x,hx⟩)
    rw [commutatorElement_eq_one_iff_mul_comm.mpr he]
    exact one_mem _


private theorem centralizes_two_subgroup {H : Type*} [Group H]
    (R : Subgroup H) (hR : Nat.card R=2) {x y : H}
    (hx : x∈R) (hx1 : x≠1) (hyx : Commute y x) : y∈centralizer (R : Set H) := by
  intro z hz
  have hxR : (⟨x,hx⟩ : R)≠1 := fun he => hx1 (congrArg Subtype.val he)
  obtain ⟨n,hn⟩ := mem_zpowers_iff.mp
    (mem_zpowers_of_prime_card hR hxR (g' := (⟨z,hz⟩ : R)))
  have he : x^n=z := congrArg Subtype.val hn
  rw [←he]
  exact (hyx.zpow_right n).symm

/-- The full beta local group has the same centralizer preimage. The
binary quotient first forces the conjugator into the actual edge subgroup. -/
theorem binary_beta_local_centralizer_preimage
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hcomm : ⁅Z (family P) a,Z (family P) b⁆ = ⊥)
    (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (ea : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* SL(2,k))
    (eb : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* SL(2,ZMod 2))
    (g : G) (hga : g ∈ stabilizer (family P) a) (hgb : g • b ≠ b)
    (x : G) (hx : x ∈ Z (family P) a) (hxQ : x ∉ Q (family P) b)
    (y : G) (hy : y ∈ d.localGroup b) :
    ⁅y,x⁆ ∈ Z (family P) b ↔ y ∈ Z (family P) a := by
  let F := family P
  let := finite_endpoints h
  let := source_center_elementary h a
  let D := d.localGroup b
  let : Finite D := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  have hab := source_critical_one_adjacent hc hb
  have Mb := binary_rankOne eb
  have hQa := source_linear_binary_core_eq_center h hB d hc hb hcomm hbc hac Ma ea eb g hga hgb
  have hE := (source_linear_rankOne_core_identities h hB d hc hb hbc hac Ma Mb ea).1
  rw [hQa] at hE
  have hZQ : Z F b ≤ Q F b := (source_Z_Q_U h b).1.trans (map_subtype_le _)
  have hZaE : Z F a ≤ (stabilizer F b ⊓ stabilizer F a).pCoreIn 2 := by
    rw [inf_comm,hE]
    exact le_sup_left
  obtain ⟨T,hT⟩ := source_edge_core_local_sylow h hB d hab.symm
  have hZaD : Z F a ≤ D := by
    have hh : (T : Subgroup (d.localGroup b)).map (d.localGroup b).subtype ≤ D :=
      map_subtype_le (T : Subgroup (d.localGroup b))
    rw [hT] at hh
    exact hZaE.trans hh
  let f := eb.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hf : Function.Surjective f := eb.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfk : f.ker=pCore 2 D := by
    rw [MonoidHom.ker_comp_of_injective _ _ eb.injective,QuotientGroup.ker_mk']
  let R := T.mapSurjective hf
  have hR : Nat.card R=2 := (Nat.card_congr
    (Matrix.SpecialLinearGroup.sylowEquivAdditive (ZMod 2) 2 R).symm.toEquiv).trans (by simp)
  have hRT : (R : Subgroup SL(2,ZMod 2)).comap f=T := by
    change ((T : Subgroup D).map f).comap f=_
    rw [Subgroup.comap_map_eq,hfk,sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal T)]
  let xD : D := ⟨x,hZaD hx⟩
  let yD : D := ⟨y,hy⟩
  have hxT : xD∈T := by
    have hm := hZaE hx
    rw [←hT] at hm
    obtain ⟨z,hz,hzx⟩ := hm
    exact (show z=xD from Subtype.ext hzx) ▸ hz
  have hxR : f xD∈R := mem_map_of_mem f hxT
  have hx1 : f xD≠1 := by
    intro he
    have hh : xD∈pCore 2 D := hfk ▸ MonoidHom.mem_ker.mpr he
    exact hxQ ((localGroup_core_eq F d b).le (mem_map_of_mem D.subtype hh))
  constructor
  · intro hyx
    have hxy0 : ⁅f yD,f xD⁆=1 := by
      rw [←map_commutatorElement]
      apply MonoidHom.mem_ker.mp
      rw [hfk]
      have hh := (localGroup_core_eq F d b).ge (hZQ hyx)
      obtain ⟨u,hu,he⟩ := hh
      exact (show u=⁅yD,xD⁆ from Subtype.ext he) ▸ hu
    have hNR : f yD∈normalizer (R : Set SL(2,ZMod 2)) :=
      Subgroup.centralizer_le_normalizer _ (centralizes_two_subgroup R hR hxR hx1
        (commutatorElement_eq_one_iff_commute.mp hxy0))
    have hNT : yD∈normalizer (T : Set D) := by
      have hn : (normalizer (R : Set SL(2,ZMod 2))).comap f=normalizer (T : Set D) := by
        change (normalizer ((R : Subgroup SL(2,ZMod 2)) : Set SL(2,ZMod 2))).comap f=_
        rw [comap_normalizer_eq_of_surjective _ hf,hRT]
        rfl
      exact hn ▸ hNR
    have hya : y∈stabilizer F a := by
      have hh : yD∈(stabilizer F a).subgroupOf D := by
        rw [(source_edge_local_normalizer h d hab.symm Mb T hT).2]
        exact hNT
      exact hh
    have hyE := (source_binary_local_edge_eq_core h hB d hab eb).le ⟨hy,hya⟩
    rw [hE] at hyE
    have hnQ : Z F a ≤ normalizer (Q F b : Set G) := hZaD.trans
      ((d.local_le b).trans (CommutingNontrivial.stabilizer_normalizes_Q F b))
    change y∈((Z F a ⊔ Q F b : Subgroup G) : Set G) at hyE
    rw [coe_mul_of_left_le_normalizer_right (Z F a) (Q F b) hnQ] at hyE
    obtain ⟨u,hu,v,hv,rfl⟩ := hyE
    have hux : ⁅u,x⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (congrArg Subtype.val (mul_comm (⟨u,hu⟩ : Z F a) ⟨x,hx⟩))
    rw [commutatorElement_mul_left_eq_conj_mul,hux,mul_one] at hyx
    have hnZ : u∈normalizer (Z F b : Set G) :=
      (normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F b)).mp (Z_normal F b)
        (d.local_le b (hZaD hu))
    have hvx : ⁅v,x⁆∈Z F b := (mem_normalizer_iff.mp hnZ _).mpr hyx
    have hvZ := (binary_beta_core_centralizer_preimage h hB d hc hb hcomm hbc hac
      Ma ea eb g hga hgb x hx hxQ v hv).mp hvx
    exact (Z F a).mul_mem hu hvZ
  · intro hyZ
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (congrArg Subtype.val (mul_comm (⟨y,hyZ⟩ : Z F a) ⟨x,hx⟩))]
    exact one_mem _


private theorem binary_linear_coordinates {H : Type*} [Group H]
    (mb : ClassicalGroup.IsPSL H 2 2) : Nonempty (H ≃* SL(2,ZMod 2)) := by
  obtain ⟨k,fk,fink,hk,⟨eb⟩⟩ := mb
  let _ := fk
  let _ := fink
  let _ : Fintype k := Fintype.ofFinite k
  let _ : CharP k 2 := charP_of_card_eq_prime_pow
    (show Fintype.card k=2^1 by simpa only [Nat.card_eq_fintype_card,pow_one] using hk)
  let eSL : H ≃* SL(2,k) :=
    eb.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  let ek := ZMod.ringEquivOfPrime k Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hk)
  let f := Matrix.SpecialLinearGroup.map (n := Fin 2) ek.symm.toRingHom
  have hf : Function.Injective f := by
    intro a b hab
    ext i j
    exact ek.symm.injective (congrArg (fun z : SL(2,ZMod 2) => z.val i j) hab)
  have hcard : Nat.card SL(2,k)=Nat.card SL(2,ZMod 2) := by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup,
      BenderSuzuki.External.huppert614_card_specialLinearGroup,hk]
    simp
  exact ⟨eSL.trans (MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩))⟩


end Local

section Original
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))

include h hc hb hcomm helem

variable (hbinary : ClassicalGroup.IsPSL
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype ⧸
        pCore 2 ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype)) 2 2)
include hbinary
/-- The binary elementary source supplies the exact centralizer preimage
at its original beta endpoint, retaining the literal seed and beta core. -/
theorem elementary_binary_beta_local_centralizer_preimage
    (x : G₀) (hx : x∈Z F (base F false)) (hxQ : x∉Q F (base F true))
    (y : G₀) (hy : y∈graphLocalGroup F (base F true)) :
    ⁅y,x⁆∈Z F (base F true) ↔ y∈Z F (base F false) := by
  let d := reducedFullEarlierLocalTheorems h
  obtain ⟨m,hm,_,ma,_⟩ := original_borel_elementary_orders_and_paths_of_source
    h hc hb hcomm helem
  let j := (graphLocalGroup F (base F false)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let e := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  have ma' := ma.of_mulEquiv e
  have Ma : IsRankOneModel (d.localGroup (base F false) ⧸
      pCore 2 (d.localGroup (base F false))) := .linear (2*m) (by omega) ma'
  obtain ⟨k,fk,finK,hK,⟨ea⟩⟩ := ma'
  let _ := fk
  let _ := finK
  let _ : Fintype k := Fintype.ofFinite k
  let _ : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hK)
  let eSL := ea.trans (MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
    ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩).symm
  let jb := (graphLocalGroup F (base F true)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ jb (pCore_map_iso 2 jb)
  obtain ⟨eb⟩ := binary_linear_coordinates (hbinary.of_mulEquiv eqb)
  have hval (v : Vertex F) : 3≤Nat.card ((graph F).neighborSet v) := by
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) v.type
  obtain ⟨c,hbc,hca⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet (base F true))
    (by rw [←Nat.card_coe_set_eq]; have hh := hval (base F true); omega) (base F false)
  obtain ⟨b',hab',hb'b⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (graph F).neighborSet (base F false))
    (by rw [←Nat.card_coe_set_eq]; have hh := hval (base F false); omega) (base F true)
  obtain ⟨g,hga,hgb⟩ := locally_transitive F (source_critical_one_adjacent hc hb) hab'
  exact binary_beta_local_centralizer_preimage (reduced_triple h)
    (reduced_borel_core_sylow h) d hc hb hcomm hbc hca.symm Ma eSL eb
    g hga (by rw [hgb]; exact hb'b) x hx hxQ y hy

/-- The full center of the binary beta local group is exactly Z_beta.
The exact centralizer preimage puts each central element in the elementary
neighboring seed, so the full center equals its omega subgroup. -/
theorem elementary_binary_beta_full_center :
    centerIn (graphLocalGroup F (base F true))=Z F (base F true) := by
  let ht := reduced_triple h
  let J := graphLocalGroup F (base F true)
  let _ : IsElementaryAbelian 2 (Z F (base F false)) := source_center_elementary ht _
  have hZ := (source_commuting_one_center_identities ht (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) hc hb hcomm).1
  change Z F (base F true)=omegaCenterIn J at hZ
  have hZa : Z F (base F false)≤J := by
    apply pGroup_le_sylowGenerated _ _ _ (IsElementaryAbelian.isPGroup 2 _)
    exact (((source_Z_Q_U ht _).1.trans (map_subtype_le _)).trans
      (source_Z_Q_U ht _).2).trans
      ((ballKernel_one_le_edge F (source_critical_one_adjacent hc hb)).trans inf_le_right)
  have hnot : ¬Z F (base F false)≤Q F (base F true) :=
    fun hh => hc.2 (hh.trans (source_Z_Q_U ht _).2)
  obtain ⟨x,hx,hxQ⟩ := SetLike.not_le_iff_exists.mp hnot
  apply le_antisymm
  · intro z hz
    have hzx : ⁅z,x⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_iff.mp hz.2 x (hZa hx)).symm
    have hzZa := (elementary_binary_beta_local_centralizer_preimage h hc hb hcomm
      helem hbinary x hx hxQ z hz.1).mp (hzx.symm ▸ one_mem _)
    rw [hZ]
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨hz.1,hz.2,elemPow_eq_one_of_isElementaryAbelian z hzZa⟩
  · intro z hz
    rw [hZ] at hz
    obtain ⟨hzJ,hzc,_⟩ := (mem_omegaCenterIn_iff _ _).mp hz
    exact ⟨hzJ,hzc⟩

/-- Binary beta specialization of DGS (14.8): no nonidentity central
translate of the original seed involution is conjugate to it locally. -/
theorem elementary_binary_beta_central_translate
    (x : G₀) (hx : x∈Z F (base F false)) (hxQ : x∉Q F (base F true))
    (y : G₀) (hy : y∈graphLocalGroup F (base F true))
    (z : G₀) (hz : z∈Z F (base F true)) (he : y*x*y⁻¹=x*z) : z=1 := by
  let _ : IsElementaryAbelian 2 (Z F (base F false)) :=
    source_center_elementary (reduced_triple h) (base F false)
  have hzZa : z∈Z F (base F false) := source_commuting_one_center_le_neighbor
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    hc hb hcomm (source_critical_one_adjacent hc hb).symm hz
  have hxz : x*z=z*x := congrArg Subtype.val
    (mul_comm (⟨x,hx⟩ : Z F (base F false)) ⟨z,hzZa⟩)
  have hecomm : ⁅y,x⁆=z := by rw [commutatorElement_def,he,hxz,mul_inv_cancel_right]
  have hyZ := (elementary_binary_beta_local_centralizer_preimage h hc hb hcomm
    helem hbinary x hx hxQ y hy).mp (hecomm.symm ▸ hz)
  have hyx : y*x=x*y := congrArg Subtype.val
    (mul_comm (⟨y,hyZ⟩ : Z F (base F false)) ⟨x,hx⟩)
  exact hecomm.symm.trans (commutatorElement_eq_one_iff_mul_comm.mpr hyx)

open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan

omit hbinary in
/-- The original four-path radical lies in the preceding alpha seed, and
its surviving endpoint action stays outside the actual beta two-core. -/
theorem elementary_four_path_root_image
    {a : SourceVertex A} (p : (sourceGraph A).Walk a (base T true))
    (hp : p.IsPath) (hl : p.length=4) (hprev : p.penultimate=base T false) :
    (pathRoot (X := (A).Universal) p).map (bOne_tree_map h) ≤ Z F (base F false) ∧
      ∀ x∈pathRoot (X := (A).Universal) p,
        x∉ballKernel T (base T true) 1 → (bOne_tree_map h) x∉Q F (base F true) := by
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let cov := bOne_tree_cover h
  let φ := bOne_tree_map h
  let R := pathRoot (X := (A).Universal) p
  have h3 : p.getVert 3=base T false := by
    simpa only [penultimate,hl] using hprev
  have hR : R ≤ ballKernel T (base T false) 1 := by
    intro x hx z hz
    rcases (mem_ball_one T (base T false) z).mp hz with hz | rfl
    · exact original_elementary_pathRoot_fixes_interior_stars h hc hb helem p hp x hx
        3 (by decide) (by omega) z (h3.symm ▸ hz)
    · rw [←h3]
      exact (pCoreIn_le 2 _ hx) 3 (by omega)
  have hRU : R.map φ ≤ U F (base F false) := by
    have hh := (map_mono hR).trans (cov.ballKernel_map_le (base T false) 1)
    rw [cov.vertex_base] at hh
    exact hh
  have hRQ : R.map φ ≤ Q F (base F false) :=
    CommutingTrivial.two_subgroup_le_Q F _ (reduced_kernel_sylow h _)
      ((pathRoot_isTwo p).map φ) hRU
  obtain ⟨_,_,_,_,hQa,_⟩ := original_borel_elementary_orders_and_paths_of_source
    h hc hb hcomm helem
  have hQZ : Q F (base F false)=Z F (base F false) :=
    (map_injective (G₀).subtype_injective) hQa
  refine ⟨hRQ.trans_eq hQZ,?_⟩
  intro x hx hxU hxQ
  apply hxU
  have hxfix : x • base T true=base T true := by
    simpa only [getVert_length] using (pCoreIn_le 2 _ hx) p.length le_rfl
  apply cov.ballKernel_lift (base T true) 1 x hxfix
  rw [cov.vertex_base]
  exact (source_Z_Q_U (reduced_triple h) _).2 hxQ

omit hbinary in
/-- Nonidentity elements of the actual four-path radical survive the full
endpoint permutation action: an extra fixed exit would put them in the odd
five-path fixer. -/
theorem elementary_four_path_root_survives
    {a : SourceVertex A} (p : (sourceGraph A).Walk a (base T true))
    (hp : p.IsPath) (hl : p.length=4)
    (x : (A).Universal) (hx : x∈pathRoot (X := (A).Universal) p) (hx1 : x≠1) :
    x∉ballKernel T (base T true) 1 := by
  let cov := bOne_tree_cover h
  have hval : 3≤Nat.card ((sourceGraph A).neighborSet (base T true)) := by
    rw [Nat.card_congr (Equiv.ofBijective _ (cov.neighbor_bijective (base T true)))]
    change 3≤Nat.card ((graph F).neighborSet (cov.vertex (base T true)))
    rw [cov.vertex_base]
    rw [card_neighbors_of_indices F (fun i => ((F (!i)).subgroupOf (F i)).index)
      (fun _ => rfl)]
    exact source_valence_ge_three (reduced_triple h) (reduced_vertex_sylow h) _
  obtain ⟨z,hz,hzprev⟩ := Set.exists_ne_of_one_lt_ncard
    (s := (sourceGraph A).neighborSet (base T true))
    (by rw [←Nat.card_coe_set_eq]; omega) p.penultimate
  have htree := (Universal.cosetGraph_isTree A
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).isAcyclic
  have hnew : z∉p.support := fun hzmem =>
    hzprev (htree.eq_penultimate_of_adj_end hp hz hzmem)
  have hodd := (original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem).2
    (p.concat hz) (hp.concat hnew hz) (by rw [length_concat,hl])
  intro hxU
  apply hx1
  exact (pathRoot_inf_stabilizer_eq_bot p hz hodd).le
    ⟨hx,hxU z ((mem_ball_one T _ _).mpr (Or.inl hz))⟩

/-- DGS (14.8) for the literal binary four-path radical and the original
universal-to-reduced map. Interior-star geometry supplies its seed placement. -/
theorem elementary_binary_four_path_central_translate
    {a : SourceVertex A} (p : (sourceGraph A).Walk a (base T true))
    (hp : p.IsPath) (hl : p.length=4) (hprev : p.penultimate=base T false)
    (x : (A).Universal) (hx : x∈pathRoot (X := (A).Universal) p)
    (hx1 : x≠1)
    (y : G₀) (hy : y∈graphLocalGroup F (base F true))
    (z : G₀) (hz : z∈centerIn (graphLocalGroup F (base F true)))
    (he : y*(bOne_tree_map h) x*y⁻¹=(bOne_tree_map h) x*z) : z=1 := by
  have hxU := elementary_four_path_root_survives h hc hb hcomm helem p hp hl x hx hx1
  obtain ⟨hR,hxQ⟩ := elementary_four_path_root_image h hc hb hcomm helem p hp hl hprev
  exact elementary_binary_beta_central_translate h hc hb hcomm helem hbinary
    ((bOne_tree_map h) x) (hR (mem_map_of_mem _ hx)) (hxQ x hx hxU) y hy z
      ((elementary_binary_beta_full_center h hc hb hcomm helem hbinary).le hz) he

/-- The literal conjugacy-class intersection in DGS (14.8), at the binary
beta endpoint, with the full local center and the actual root image. -/
theorem elementary_binary_four_path_conjugacy_intersection
    {a : SourceVertex A} (p : (sourceGraph A).Walk a (base T true))
    (hp : p.IsPath) (hl : p.length=4) (hprev : p.penultimate=base T false)
    (x : (A).Universal) (hx : x∈pathRoot (X := (A).Universal) p) (hx1 : x≠1) :
    {w : G₀ | ∃ y∈graphLocalGroup F (base F true),
      y*(bOne_tree_map h) x*y⁻¹=w} ∩
      ({(bOne_tree_map h) x} * (centerIn (graphLocalGroup F (base F true)) : Set G₀)) =
        {(bOne_tree_map h) x} := by
  ext w
  constructor
  · rintro ⟨⟨y,hy,hyx⟩,hw⟩
    obtain ⟨u,hu,z,hz,huz⟩ := hw
    have hu' : u=(bOne_tree_map h) x := hu
    subst u
    have hz1 := elementary_binary_four_path_central_translate h hc hb hcomm helem
      hbinary p hp hl hprev x hx hx1 y hy z hz (hyx.trans huz.symm)
    simpa only [hz1,mul_one,Set.mem_singleton_iff] using huz.symm
  · rintro rfl
    exact ⟨⟨1,one_mem _,by simp⟩,(bOne_tree_map h) x,rfl,1,one_mem _,mul_one _⟩

/-- The source constructs its full-Cartan four-path root and reflection.
The same root satisfies central-translate separation under the literal beta
local group; no root, reflection or centralizer identity is assumed. -/
theorem elementary_binary_separated_four_path_reflection
    (c : CompatibleCartans L (reducedSylow L S)) :
    ∃ a, ∃ p : (sourceGraph A).Walk a (base T true),
      p.IsPath ∧ p.length=4 ∧ p.penultimate=base T false ∧
      cartan c≤pathFixer (X := (A).Universal) p ∧
      ∃ x∈pathRoot (X := (A).Universal) p, orderOf x=2 ∧
        x∉ballKernel T (base T true) 1 ∧
      ∃ t : (A).Universal, t • base T true=base T true ∧
        t • base T false≠base T false ∧ t*t=1 ∧
        t∈centralizer (cartan c : Set (A).Universal) ∧
        (∃ g∈T true, (bOne_tree_map h) g∈graphLocalGroup F (base F true) ∧ g*x*g⁻¹=t) ∧
        {w : G₀ | ∃ y∈graphLocalGroup F (base F true),
          y*(bOne_tree_map h) x*y⁻¹=w} ∩
          ({(bOne_tree_map h) x} * (centerIn (graphLocalGroup F (base F true)) : Set G₀)) =
            {(bOne_tree_map h) x} := by
  obtain ⟨a,p,hp,hl,hprev,hCp,_⟩ :=
    original_elementary_binary_beta_four_path_reflection h hc hb hcomm helem hbinary c
  obtain ⟨x,hx,hxo,hxU⟩ := original_elementary_binary_prescribed_path_involution
    h hc hb hcomm helem hbinary c true p hp hl hprev hCp
  obtain ⟨t,ht,htmove,htsq,htC,hconj⟩ :=
    original_elementary_binary_beta_prescribed_root_reflection
      h hc hb hcomm helem hbinary c p hp hl hprev hCp x hx hxo
  refine ⟨a,p,hp,hl,hprev,hCp,x,hx,hxo,hxU,t,ht,htmove,htsq,htC,hconj,?_⟩
  exact elementary_binary_four_path_conjugacy_intersection h hc hb hcomm helem hbinary
    p hp hl hprev x hx (by intro hh; simp [hh] at hxo)

end Original
end CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute
