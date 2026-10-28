module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.IntrinsicPairAction

/-!
# Intrinsic coprime splitting in the elementary beta branch

The previously constructed pair action replaces the alpha catalogue in the
odd-actor argument. In a linear beta quotient, the actual two Sylow fixed
spaces are complementary, so a cubic matrix fixes only zero. For D10 the
product of the two involutions supplies the odd actor. Lifting this actor
and applying coprime decomposition gives Q_beta = V C_Q_beta(y), with
intersection exactly the common center. The literal elementary edge quotient
selects these two beta possibilities, with neither local catalogue assumed.

ElementaryAlphaCatalogue applies this splitting to the actual alpha Sylow
and excludes the order-144 enlargement. No action or splitting is an input
to the elementary-branch theorem. The auxiliary two-rank-one theorem retains
the independently meaningful full adjacent-core product premise.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(5.11), p.112, (11.3)(h), pp.170--171, and (11.7), pp.174--175.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryConjugationSection
open Representation.BinaryOffender Representation.RankOne.QuadraticRecognition
open scoped Pointwise IsMulCommutative MatrixGroups commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
open Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => family (fun i => Subgroup.subgroupOf (P₀ L S i) (Reduction.G₀ L S))
local notation "G₀" => Reduction.G₀ L S
private theorem small_elementary_generator {D : Type*} [Group D] [Finite D]
    (hr : primeRank 2 D ≤ 1) (A : Subgroup D) [IsElementaryAbelian 2 A] (hne : A ≠ ⊥) :
    ∃ t : D, IsInvolution t ∧ zpowers t = A := by
  have hu : Nat.card A ≤ 2 := by
    simpa using (primeRank_le_iff_elementary_card_le D).mp hr A inferInstance
  have hcard : Nat.card A = 2 := by
    have hp := Nat.card_pos (α := A)
    have hn : Nat.card A ≠ 1 := fun he => hne (A.eq_bot_iff_card.mpr he)
    omega
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (by rw [hcard])
  have ho : orderOf (t : D) = 2 := (Subgroup.orderOf_coe t).trans ht
  refine ⟨t,⟨fun he => by simp only [he,orderOf_one] at ho; omega,
    by simpa only [ho] using pow_orderOf_eq_one (t : D)⟩,?_⟩
  exact eq_of_le_of_card_ge (zpowers_le.mpr t.property) (by rw [Nat.card_zpowers,ho,hcard])

/-- The full core product supplies the pair splitting when the actual beta
quotient has two-rank one, without an alpha catalogue premise. -/
theorem reduced_pair_coprime_splitting_of_two_rank_one
    (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b)
    (hb : DGS85.b F = 1) (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (hprod : (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = Q F a ⊔ Q F b)
    (Mb : IsRankOneModel (graphLocalGroup F b ⧸ pCore 2 (graphLocalGroup F b)))
    (hr : primeRank 2 (graphLocalGroup F b ⧸ pCore 2 (graphLocalGroup F b)) ≤ 1) :
    let V := pairSpan (Z F a) (Z F c) (Q F b)
    let J := Z F a ⊓ Z F c
    ∃ y ∈ Z F a ⊔ Z F c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q F b = V ⊔ (Q F b ⊓ centralizer (zpowers y : Set G₀)) ∧
      V ⊓ centralizer (zpowers y : Set G₀) = J := by
  let ht := reduced_triple h
  let hB := reduced_borel_core_sylow h
  let d := reducedFullEarlierLocalTheorems h
  let := finite_endpoints ht
  let := source_center_elementary ht a
  let := source_center_elementary ht c
  let H := (Z F a ⊔ Z F c) ⊔ Q F b
  let V := pairSpan (Z F a) (Z F c) (Q F b)
  let J := Z F a ⊓ Z F c
  let L := graphLocalGroup F b
  let : Finite L := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let : Finite (L ⧸ pCore 2 L) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hJ,hE,hQ,σ,s,_,hcompl,_,_⟩ := reduced_source_pair_section_of_core_product h hc hb hbc hac hprod
  let := hJ
  let := hE
  let := hQ
  let K := H ⧸ (Q F b).subgroupOf H
  let π := QuotientGroup.mk' ((Q F b).subgroupOf H)
  obtain ⟨R,T,_,hHK,e,_⟩ := source_pair_actor_equiv ht hB d hc hb hbc hac Mb
  change Sylow 2 (L ⧸ pCore 2 L) at R T
  change H ≤ L at hHK
  let : Finite H := Finite.of_injective (inclusion hHK) (inclusion_injective _)
  let : Finite K := Finite.of_surjective π (QuotientGroup.mk'_surjective _)
  have hKrank : primeRank 2 K ≤ 1 :=
    (primeRank_le_of_injective 2
      ((omegaCenterIn (R : Subgroup (L ⧸ pCore 2 L)) ⊔
        omegaCenterIn (T : Subgroup (L ⧸ pCore 2 L))).subtype.comp e.toMonoidHom)
      (Subtype.val_injective.comp e.injective)).trans hr
  let A := ((Z F a).subgroupOf H).map π
  let C := ((Z F c).subgroupOf H).map π
  have hZaH : Z F a ≤ H := le_sup_left.trans le_sup_left
  have hZcH : Z F c ≤ H := le_sup_right.trans le_sup_left
  obtain ⟨g,hg,hga⟩ := source_rankOne_center_pair_moves ht hB d hc hb hbc Mb
  have hgb : g • b = b := d.local_le b (hHK (mem_sup_left hg))
  have hcc : IsCriticalPair F c b := by
    simpa only [hga,hgb] using criticalPair_translate F hc g
  have hne (z : Vertex F) (hzH : Z F z ≤ H)
      (hz : IsCriticalPair F z b) : ((Z F z).subgroupOf H).map π ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    rw [QuotientGroup.ker_mk'] at hk
    apply hz.2
    exact (show Z F z ≤ Q F b from fun x hx =>
      hk (show (⟨x,hzH hx⟩ : H) ∈ (Z F z).subgroupOf H from hx)).trans
        (source_Z_Q_U ht b).2
  let : IsElementaryAbelian 2 ((Z F a).subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hZaH
  let : IsElementaryAbelian 2 ((Z F c).subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hZcH
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map π
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map π
  obtain ⟨t,htInv,htA⟩ := small_elementary_generator hKrank A (hne a hZaH hc)
  obtain ⟨r,hrt,hrC⟩ := small_elementary_generator hKrank C (hne c hZcH hcc)
  have hf := source_rankOne_pair_fixed_spaces ht hB d hc hb hbc Mb π
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) σ s
  have hd : Disjoint (fixedSpace σ (zpowers t)) (fixedSpace σ (zpowers r)) := by
    rw [htA,hrC,hf.2.1,hf.2.2]
    exact hcompl.disjoint
  have hfixed := involution_product_fixed_eq_bot σ t r
    (by simpa only [pow_two] using htInv.2) (by simpa only [pow_two] using hrt.2) hd
  have ho := odd_product_of_two_rank_one hKrank htInv hrt
  have htr : t*r ≠ 1 := by
    intro he
    obtain ⟨x,hx,hxQ⟩ := SetLike.not_le_iff_exists.mp
      (source_rankOne_seed_escape ht hB d hc hb hbc hac Mb).1
    let v : V := ⟨x,(show Z F a ⊓ Q F b ≤ V from le_sup_left) hx⟩
    have hv : (s.coordinates v).toAdd ∈ fixedSpace σ (zpowers (t*r)) := by
      rw [he]
      apply (mem_fixedSpace_zpowers_iff _ _ _).mpr
      simp only [map_one]
      rfl
    rw [hfixed,Submodule.mem_bot] at hv
    have hxJ := (s.coordinates_eq_one_iff v).mp (Multiplicative.toAdd.injective hv)
    exact hxQ (((source_Z_Q_U ht c).1.trans (map_subtype_le _)) hxJ.2)
  apply source_pair_coprime_splitting_of_odd_actor ht d hc hb hbc hHK π
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) s.kernel_le (t*r) ho htr
  intro y hy x hx
  rw [←s.fixed_coordinate_iff_commutator_mem y ⟨x,hx⟩]
  change σ (π y) (s.coordinates ⟨x,hx⟩).toAdd = (s.coordinates ⟨x,hx⟩).toAdd ↔ _
  rw [hy,←mem_fixedSpace_zpowers_iff,hfixed,Submodule.mem_bot]
  exact s.coordinates_eq_one_iff ⟨x,hx⟩
private theorem pair_splitting_of_linear_actor_intrinsic
    {k : Type*} [Field k] [Finite k] [CharP k 2]
    (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b)
    (hb : DGS85.b F = 1) (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (hprod : (stabilizer F a ⊓ stabilizer F b).pCoreIn 2 = Q F a ⊔ Q F b)
    (Mb : IsRankOneModel (graphLocalGroup F b ⧸ pCore 2 (graphLocalGroup F b)))
    (hHK : (Z F a ⊔ Z F c) ⊔ Q F b ≤ graphLocalGroup F b)
    (f : ((Z F a ⊔ Z F c) ⊔ Q F b : Subgroup G₀) →* SL(2,k))
    (hf : Function.Surjective f)
    (hk : f.ker = (Q F b).subgroupOf ((Z F a ⊔ Z F c) ⊔ Q F b))
    (R T : Sylow 2 SL(2,k))
    (ha : ((Z F a).subgroupOf ((Z F a ⊔ Z F c) ⊔ Q F b)).map f = R)
    (hc' : ((Z F c).subgroupOf ((Z F a ⊔ Z F c) ⊔ Q F b)).map f = T) :
    let V := pairSpan (Z F a) (Z F c) (Q F b)
    let J := Z F a ⊓ Z F c
    ∃ y ∈ Z F a ⊔ Z F c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q F b = V ⊔ (Q F b ⊓ centralizer (zpowers y : Set G₀)) ∧
      V ⊓ centralizer (zpowers y : Set G₀) = J := by
  let ht := reduced_triple h
  let hB := reduced_borel_core_sylow h
  let d := reducedFullEarlierLocalTheorems h
  let := finite_endpoints ht
  let H := (Z F a ⊔ Z F c) ⊔ Q F b
  let V := pairSpan (Z F a) (Z F c) (Q F b)
  let J := Z F a ⊓ Z F c
  let D₀ := Q F a ⊓ Q F c
  obtain ⟨hJ,hE,hQ,σ₀,s₀,_⟩ := reduced_source_pair_section_of_core_product h hc hb hbc hac hprod
  let := hJ
  let := hE
  have hinter : D₀ ⊓ V = J := source_rankOne_pair_core_intersection ht hB d hc hb hbc hac Mb
  have hn := source_pair_core_normalizers ht (source_critical_one_adjacent hc hb) hbc
  have hHJ : H ≤ normalizer (J : Set G₀) := by
    rw [←hinter]
    exact (le_inf hn.2.1 hn.2.2.1).trans inf_normalizer_le_normalizer_inf
  have hdisp : ⁅Q F b,V⁆ ≤ J := by
    rw [←hinter]
    exact le_inf (((reduced_source_pair_core_action_of_core_product h hc hb hbc hac hprod).trans
      (inf_le_inf ((source_Z_Q_U ht a).1.trans (map_subtype_le _))
        ((source_Z_Q_U ht c).1.trans (map_subtype_le _)))))
      (le_normalizer_iff_commutator_le_right.mp (le_sup_right.trans hn.2.2.1))
  obtain ⟨σ,s,_⟩ := exists_descended_actor H V J s₀.section_le s₀.kernel_le
    hn.2.2.1 hHJ f hf (by
      intro y hy x hx
      have hyker : y ∈ f.ker := hy
      rw [hk] at hyker
      exact hdisp (commutator_mem_commutator hyker hx))
  have hfixed := source_rankOne_pair_fixed_spaces ht hB d hc hb hbc Mb f hf hk σ s
  have hJQ : J ≤ Q F b := s.kernel_le.trans (pairSpan_le_core _ _ _)
  have he : J = (Z F a ⊓ Q F b) ⊓ (Z F c ⊓ Q F b) :=
    le_antisymm (le_inf (le_inf inf_le_left hJQ) (le_inf inf_le_right hJQ))
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
  have hcompl := s.isCompl_imageSpace (Z F a ⊓ Q F b)
    (Z F c ⊓ Q F b) rfl he
  rw [←hfixed.2.1,←hfixed.2.2,ha,hc'] at hcompl
  let : Finite V := Finite.of_injective (inclusion ((pairSpan_le_core _ _ _).trans (Q_le_stabilizer _ b))) (inclusion_injective _)
  let : Finite (V ⧸ J.subgroupOf V) := Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  let y₀ := Representation.QuadraticFourGroup.TensorClassification.cubicMatrix k
  have hy₀ : orderOf y₀ = 3 := Representation.QuadraticFourGroup.TensorClassification.cubicMatrix_order k
  apply source_pair_coprime_splitting_of_odd_actor ht d hc hb hbc hHK f hf hk s.kernel_le y₀
    (hy₀ ▸ (by decide : Odd (3:ℕ))) (fun he => by simp only [he,orderOf_one] at hy₀; omega)
  intro y hy x hx
  have hz := sl2_odd_fixed_eq_bot_of_complement σ R T hcompl y₀
    (hy₀ ▸ (by decide : Odd (3:ℕ))) (pow_orderOf_eq_one y₀)
    (fun he => by simp only [he,orderOf_one] at hy₀; omega)
  rw [←s.fixed_coordinate_iff_commutator_mem y ⟨x,hx⟩]
  change σ (f y) (s.coordinates ⟨x,hx⟩).toAdd = (s.coordinates ⟨x,hx⟩).toAdd ↔ _
  rw [hy,←mem_fixedSpace_zpowers_iff,hz,Submodule.mem_bot]
  exact s.coordinates_eq_one_iff ⟨x,hx⟩


section Marking
variable {P : Fin 2 → Subgroup G} {B : Subgroup G}
private theorem linear_omega_pair {k : Type*} [Field k] [Finite k] [CharP k 2]
    (R T : Sylow 2 SL(2,k)) (hne : R ≠ T) :
    omegaCenterIn (R : Subgroup SL(2,k)) ⊔ omegaCenterIn (T : Subgroup SL(2,k)) = ⊤ := by
  rw [omegaCenterIn_eq_omegaOneAmbient,omegaCenterIn_eq_omegaOneAmbient,
    sl2_omega_center_eq,sl2_omega_center_eq]
  exact Matrix.SpecialLinearGroup.sylow_sup_eq_top 2 R T hne
private theorem full_pair_actor {D : Type*} [Group D]
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (e : (d.localGroup b ⧸ pCore 2 (d.localGroup b)) ≃* D)
    (hgen : ∀ R T : Sylow 2 D, R ≠ T →
      omegaCenterIn (R : Subgroup D) ⊔ omegaCenterIn (T : Subgroup D) = ⊤) :
    let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
    ∃ hHK : H ≤ d.localGroup b,
      let f := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 (d.localGroup b))).comp (inclusion hHK))
      Function.Surjective f ∧ f.ker = (Q (family P) b).subgroupOf H ∧
      ∃ R T : Sylow 2 D, R ≠ T ∧
        ((Z (family P) a).subgroupOf H).map f = omegaCenterIn (R : Subgroup D) ∧
        ((Z (family P) c).subgroupOf H).map f = omegaCenterIn (T : Subgroup D) := by
  let := finite_endpoints h
  let : Finite (d.localGroup b) := Finite.of_injective (inclusion (d.local_le b)) (inclusion_injective _)
  let : Finite (d.localGroup b ⧸ pCore 2 (d.localGroup b)) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hHK,R,T,hRT,hk,ha,hc',hr⟩ := source_pair_actor_map h hB d hc hb hbc hac Mb
  let H := (Z (family P) a ⊔ Z (family P) c) ⊔ Q (family P) b
  let K := d.localGroup b
  let q := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hHK)
  let f := e.toMonoidHom.comp q
  let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let T' := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hRT' : R' ≠ T' := by
    intro he
    exact hRT (Sylow.ext (map_injective e.injective (congrArg Sylow.toSubgroup he)))
  have hker : f.ker = (Q (family P) b).subgroupOf H := by
    rw [←hk]
    ext x
    change e (q x) = 1 ↔ q x = 1
    rw [←e.map_one,e.injective.eq_iff]
  have hmap (A : Subgroup H) (S : Sylow 2 (K ⧸ pCore 2 K))
      (hAS : A.map q = omegaCenterIn (S : Subgroup (K ⧸ pCore 2 K))) :
      A.map f = omegaCenterIn (S.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup D) := by
    rw [show f = e.toMonoidHom.comp q from rfl,←map_map,hAS,
      NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective]
    rfl
  have hfa := hmap _ R ha
  have hfc := hmap _ T hc'
  have hsurj : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,hr,Subgroup.map_sup,
      NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective,
      NilesRankOneKernel.omegaCenterIn_map_injective e.toMonoidHom e.injective]
    exact hgen R' T' hRT'
  exact ⟨hHK,hsurj,hker,R',T',hRT',hfa,hfc⟩


end Marking

/-- The literal elementary beta branch supplies an odd splitting actor,
without either endpoint catalogue premise. -/
theorem reduced_elementary_pair_coprime_splitting (h : HypothesisF11 L S)
    {a b c : Vertex F} (hc : IsCriticalPair F a b) (hb : DGS85.b F = 1)
    (hbc : (graph F).Adj b c) (hac : a ≠ c)
    (helem : ∃ hN : ((Q F b).subgroupOf
        ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F a ⊓ stabilizer F b).pCoreIn 2) ⧸
        (Q F b).subgroupOf ((stabilizer F a ⊓ stabilizer F b).pCoreIn 2))) :
    let V := pairSpan (Z F a) (Z F c) (Q F b)
    let J := Z F a ⊓ Z F c
    ∃ y ∈ Z F a ⊔ Z F c, Odd (orderOf y) ∧ y ≠ 1 ∧
      Q F b = V ⊔ (Q F b ⊓ centralizer (zpowers y : Set G₀)) ∧
      V ⊓ centralizer (zpowers y : Set G₀) = J := by
  let ht := reduced_triple h
  let hB := reduced_borel_core_sylow h
  let d := reducedFullEarlierLocalTheorems h
  have hab := source_critical_one_adjacent hc hb
  have helem' : ∃ hN : ((Q F b).subgroupOf
        ((stabilizer F b ⊓ stabilizer F a).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F b ⊓ stabilizer F a).pCoreIn 2) ⧸
        (Q F b).subgroupOf ((stabilizer F b ⊓ stabilizer F a).pCoreIn 2)) := by
    rw [inf_comm (stabilizer F b) (stabilizer F a)]
    exact helem
  have Mb := reduced_actor_model_of_elementary_edge h hab.symm helem'
  have hprod := (reduced_elementary_center_and_core_products h hc hb helem).2
  rcases source_linear_or_dihedral_of_elementary_edge ht hB d hab.symm Mb helem' with
    ⟨n,hn,mark⟩ | mark
  · obtain ⟨k,_,_,hcard,⟨eb⟩⟩ := mark
    let : Fintype k := Fintype.ofFinite k
    let : CharP k 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    let ep : SL(2,k) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
      MulEquiv.ofBijective (BenderSuzuki.Converse.pi k)
        ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
    obtain ⟨hHK,hf,hk,R,T,_,ha,hc'⟩ := full_pair_actor ht hB d hc hb hbc hac Mb
      (eb.trans ep.symm) linear_omega_pair
    rw [omegaCenterIn_eq_omegaOneAmbient,sl2_omega_center_eq] at ha hc'
    exact pair_splitting_of_linear_actor_intrinsic h hc hb hbc hac hprod Mb hHK _ hf hk R T ha hc'
  · let := finite_endpoints ht
    let M := graphLocalGroup F b
    let : Finite M := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
    exact reduced_pair_coprime_splitting_of_two_rank_one h hc hb hbc hac hprod Mb
      (small_beta_models_two_rank (.inl mark))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
