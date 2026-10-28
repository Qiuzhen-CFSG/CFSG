module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenPartition
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.SevenPartition.Quotient
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.Source
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.LieParabolics.Linear.Inner
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.NormalSylowQuotientAction.MarkedLift
public import Theory.GroupTheory.NormalSymmetricThreeExtension

/-!
# The original ordinary A₇ source alternative

Extend the prescribed quotient marking to the actual normalizer and choose
a three-pair partition over its two-group image. The resulting full preimage
is normalized by N_S(L), has characteristic two and S₃ two-core quotient.
Its two-residual is strictly larger than the order-twelve quotient residual:
otherwise it would centralize the ambient two-core and hence lie in it.
Since the preimage order has only one factor of three, this rules out a
product of A₃ blocks and establishes every source-family clause.

Original same-pair placement puts this escaping preimage in M ∩ L. Its
proved generation with M_L completes ConstrainedA7Alternative and the A₇
constructor of ConstrainedAlternatives. Both original source primes and
the actual quotient marking are retained. The later exchanged application
receives the same source-family construction and generation. Original
15.1.14 remains explicit in the actual-marker application. The other small
blocks, general local-family Borel placement and catalogue exhaustion
remain with this catalogue owner.

Source: Aschbacher--Smith 15.1.20(2b), 15.1.22(*), (1), pp.1094--1099.
-/

public section
open Subgroup Equiv Theory.GroupTheory
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open AlternatingSeven.ThreeResidualLocals

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
variable {G : Type*} [Group G] [Finite G]

private theorem residual_card_lt_of_characteristic_core
    {D : Type*} [Group D] [Finite D]
    (P : Subgroup G) (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hQ : pCore 2 G ≤ P) (f : P →* D) (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 G).subgroupOf P)
    (hne : pResidual 2 D ≠ ⊥) :
    Nat.card (pResidual 2 D) < Nat.card (pResidual 2 P) := by
  let R := pResidual 2 P
  let Q := (pCore 2 G).subgroupOf P
  let g := f.subgroupMap R
  have him : R.map f = pResidual 2 D := map_pResidual_of_surjective 2 f hf
  by_contra hn
  have hinj : Function.Injective g :=
    (f.subgroupMap_surjective R).bijective_of_nat_card_le (by
      rw [him]
      exact Nat.le_of_not_gt hn) |>.1
  have hdis : Disjoint R Q := by
    rw [disjoint_iff_inf_le]
    intro x hx
    have hx0 : f x = 1 := by change x ∈ f.ker; rw [hk]; exact hx.2
    have he : g ⟨x,hx.1⟩ = g 1 := by apply Subtype.ext; exact hx0.trans (map_one f).symm
    exact congrArg Subtype.val (hinj he)
  have hcomm : ⁅R,Q⁆ = ⊥ := bot_unique ((commutator_le_inf R Q).trans hdis.le_bot)
  have hRQ : R ≤ Q := by
    intro x hx
    apply hc
    intro y hy
    have hyP := hQ hy
    exact congrArg Subtype.val ((commutator_eq_bot_iff_le_centralizer.mp hcomm) hx ⟨y,hyP⟩ hy)
  have hz : R.map f = ⊥ := (Subgroup.map_eq_bot_iff R).mpr (hk.symm ▸ hRQ)
  exact hne (him.symm.trans hz)

/-- Every literal three-pair preimage in a characteristic-two group has
characteristic two and a residual too large to be a product of A₃ blocks. -/
theorem sevenPartitionPreimage_intrinsic (K : Subgroup G)
    (hf : generalizedFitting K = pCore 2 K)
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    (p : Partition 7 4 ![2,2,2,1]) :
    generalizedFitting (sevenPartitionPreimage K e p) = pCore 2 (sevenPartitionPreimage K e p) ∧
      Nonempty (((sevenPartitionPreimage K e p) ⧸ pCore 2 (sevenPartitionPreimage K e p)) ≃* Perm (Fin 3)) ∧
      ¬ IsAThreeProduct (sevenPartitionPreimage K e p) := by
  let q := (alternatingGroup (Fin 7)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K)))
  let P := p.stabilizer.comap q
  let E := alternatingGroup (Fin 7) ⊓ p.stabilizer
  let f : P →* E := (q.comp P.subtype).codRestrict E (fun x =>
    ⟨(e (QuotientGroup.mk' (pCore 2 K) x)).property,x.property⟩)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨k,hk⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) ⟨x,x.property.1⟩
    have hq : q k = x := congrArg Subtype.val hk
    refine ⟨⟨k,?_⟩,Subtype.ext hq⟩
    change q k ∈ p.stabilizer
    rw [hq]
    exact x.property.2
  have hker : q.ker = pCore 2 K := by
    ext k
    change (e (QuotientGroup.mk' (pCore 2 K) k)).val = 1 ↔ k ∈ pCore 2 K
    rw [←QuotientGroup.eq_one_iff]
    exact Subtype.ext_iff.symm.trans (e.map_eq_one_iff)
  have hk : f.ker = (pCore 2 K).subgroupOf P := by
    ext x
    change (⟨q x,_⟩ : E) = 1 ↔ (x : K) ∈ pCore 2 K
    exact Subtype.ext_iff.trans (show q x = 1 ↔ (x : K) ∈ pCore 2 K from
      Iff.of_eq (congrArg (fun H : Subgroup K => (x : K) ∈ H) hker))
  have hQ : pCore 2 K ≤ P := by
    intro x hx
    change q x ∈ p.stabilizer
    have hz : x ∈ q.ker := hker.symm ▸ hx
    rw [show q x = 1 from hz]
    exact one_mem _
  have hself : centralizer (pCore 2 K : Set K) ≤ pCore 2 K :=
    hf ▸ centralizer_generalizedFitting_le K
  have hfit : generalizedFitting P = pCore 2 P :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_le_of_pCore_le P hself hQ)
  let t : P ≃* sevenPartitionPreimage K e p := P.equivMapOfInjective K.subtype K.subtype_injective
  have h24 : Nat.card E = 24 := SevenPartition.even_stabilizer_card p
  have h12 : Nat.card (pResidual 2 E) = 12 := SevenPartition.even_stabilizer_residual_card p
  have hne : pResidual 2 E ≠ ⊥ := by intro hz; rw [hz,card_bot] at h12; omega
  have hlt := residual_card_lt_of_characteristic_core P hself hQ f hsurj hk hne
  have hcard : Nat.card (pResidual 2 P) = Nat.card (pResidual 2 (sevenPartitionPreimage K e p)) := by
    have hh := congrArg (fun X : Subgroup (sevenPartitionPreimage K e p) => Nat.card X)
      (map_pResidual_of_surjective 2 t.toMonoidHom t.surjective)
    rw [card_map_of_injective t.injective] at hh
    exact hh
  have h9 : ¬9 ∣ Nat.card (sevenPartitionPreimage K e p) := by
    rw [←Nat.card_congr t.toEquiv,←f.ker.card_mul_index,index_ker,
      f.range_eq_top_of_surjective hsurj,card_top,h24]
    obtain ⟨n,hn⟩ := (show IsPGroup 2 f.ker from hk ▸ pCore_isPGroup.comap_subtype).exists_card_eq
    rw [hn]
    intro hd
    exact (by decide : ¬9 ∣ 24)
      (((by decide : Nat.Coprime 9 2).pow_right n).dvd_of_dvd_mul_left hd)
  refine ⟨?_,?_,?_⟩
  · rw [←map_generalizedFitting_equiv t,←pCore_map_iso 2 t,hfit]
  · obtain ⟨v⟩ := SevenPartition.even_stabilizer_quotient p
    let u := (QuotientGroup.congr _ _ t (pCore_map_iso 2 t)).symm
    exact ⟨u.trans ((f.pCoreQuotientEquiv hsurj
      (hk ▸ pCore_isPGroup.comap_subtype)).trans v)⟩
  · intro hA
    have hb := aThreeProduct_residual_card_le _ h9 hA
    rw [hcard,h12] at hlt
    omega
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Subgroup.NormalSylowQuotientAction
open BinaryPermutation.SevenNormalizer
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The prescribed A₇ quotient extends to the actual normalizer; selecting a
partition over its two-group image makes the literal preimage invariant. -/
theorem sevenPartitionPreimage_normalized (K A : Subgroup G)
    (hA : IsPGroup 2 A) (hn : A ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) :
    ∃ p : Partition 7 4 ![2,2,2,1],
      A ⊓ K ≤ sevenPartitionPreimage K e p ∧
      A ≤ normalizer (sevenPartitionPreimage K e p : Set G) := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let f := permutationOfAut.toMonoidHom.comp
    ((markedCoreAction 2 K e).comp (inclusion hn))
  obtain ⟨p,hp⟩ := SevenPartition.exists_partition f.range
    (hA.of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hinner (k : K) (hk : (k : G) ∈ A) : f ⟨k,hk⟩ = (q k).val := by
    have he : markedCoreAction 2 K e ⟨k,hn hk⟩ = MulAut.conj (q k) := by
      apply MulEquiv.ext
      intro y
      obtain ⟨x,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) y
      change markedCoreAction 2 K e ⟨k,hn hk⟩ (e (QuotientGroup.mk' (pCore 2 K) x)) = _
      rw [markedCoreAction_mk]
      change q (k * x * k⁻¹) = q k * q x * (q k)⁻¹
      simp only [map_mul,map_inv]
    change permutationOfAut (markedCoreAction 2 K e ⟨k,hn hk⟩) = _
    rw [he,permutationOfAut_conj]
  have hact (a : A) (k : K) :
      (q (K.normalizerMonoidHom ⟨a,hn a.property⟩ k)).val =
        f a * (q k).val * (f a)⁻¹ := by
    have he := congrArg (fun b : MulAut (alternatingGroup (Fin 7)) => (b (q k)).val)
      (conjugation_permutationOfAut (markedCoreAction 2 K e ⟨a,hn a.property⟩))
    exact (congrArg Subtype.val (markedCoreAction_mk 2 K e ⟨a,hn a.property⟩ k)).symm.trans he.symm
  let P0 := p.stabilizer.comap ((alternatingGroup (Fin 7)).subtype.comp q)
  let P := P0.map K.subtype
  have hnP (a : A) : a.val ∈ normalizer (P : Set G) := by
    apply mem_normalizer_iff.mpr
    intro x
    have forward (b : A) (y : G) (hy : y ∈ P) : b.val * y * b.val⁻¹ ∈ P := by
      obtain ⟨k,hk,rfl⟩ := hy
      refine ⟨K.normalizerMonoidHom ⟨b,hn b.property⟩ k,?_,rfl⟩
      change (q (K.normalizerMonoidHom ⟨b,hn b.property⟩ k)).val ∈ p.stabilizer
      rw [hact]
      exact p.stabilizer.mul_mem (p.stabilizer.mul_mem (hp ⟨b,rfl⟩) hk)
        (p.stabilizer.inv_mem (hp ⟨b,rfl⟩))
    constructor
    · exact forward a x
    · intro hx
      have hh := forward a⁻¹ _ hx
      simpa only [Subgroup.coe_inv,inv_mul_cancel_left,inv_inv,mul_assoc,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hh
  refine ⟨p,?_,fun a ha => hnP ⟨a,ha⟩⟩
  intro k hk
  refine ⟨⟨k,hk.2⟩,?_,rfl⟩
  change (q ⟨k,hk.2⟩).val ∈ p.stabilizer
  rw [←hinner ⟨k,hk.2⟩ hk.1]
  exact hp ⟨⟨k,hk.1⟩,rfl⟩
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData


namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Representation Representation.BinaryOffender Stellmacher ChapterC ChapterC.C27Source
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The selected preimage satisfies every clause of the original source family,
with the actual N_S(L) action and the original two-core quotient marking. -/
theorem constrained_seven_source_parabolic (d : CaseIComponentData T M Mc V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7)) :
    ∃ π : Partition 7 4 ![2,2,2,1],
      d.IsSourceParabolic (sevenPartitionPreimage d.L e π) ∧
      d.SL ≤ sevenPartitionPreimage d.L e π := by
  obtain ⟨π,hSL,hn⟩ := sevenPartitionPreimage_normalized d.L d.sylowNormalizer
    (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T)) inf_le_right e
  obtain ⟨hfit,⟨t⟩,hnot⟩ := sevenPartitionPreimage_intrinsic d.L hf e π
  refine ⟨π,⟨map_subtype_le _,hn,hfit,Or.inl ?_,hnot⟩,?_⟩
  · exact NormalSymmetricThreeExtension.normalized_join _ _ hn t
      (T.isPGroup'.to_le (inf_le_left.trans d.S_le_T))
  · exact (le_inf (le_inf inf_le_left (inf_le_right.trans d.L.le_normalizer)) inf_le_right).trans hSL

private theorem seven_partition_marking (d : CaseIComponentData T M Mc V)
    (e : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7))
    (π : Partition 7 4 ![2,2,2,1])
    (hSL : d.SL ≤ sevenPartitionPreimage d.L e π)
    (hM : sevenPartitionPreimage d.L e π ≤ M ⊓ d.L) :
    let f := (alternatingGroup (Fin 7)).subtype.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L)))
    (d.SL.subgroupOf d.L).map f ≤ π.stabilizer ∧
      alternatingGroup (Fin 7) ⊓ π.stabilizer ≤ ((M ⊓ d.L).subgroupOf d.L).map f := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 d.L))
  let f := (alternatingGroup (Fin 7)).subtype.comp q
  constructor
  · rintro g ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hyx⟩ := hSL hx
    have he : y = x := Subtype.ext hyx
    subst y
    exact hy
  · intro g hg
    obtain ⟨k,hk⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) ⟨g,hg.1⟩
    have he : f k = g := congrArg Subtype.val hk
    refine ⟨k,?_,he⟩
    apply hM
    refine ⟨k,?_,rfl⟩
    change f k ∈ π.stabilizer
    rw [he]
    exact hg.2

/-- Original 15.1.22(1): the ordinary A₇ partition is placed in M ∩ L,
and the two original intersections generate L. Both source primes retain
their actual quotient marking. -/
theorem PreExclusionSource.constrained_seven
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7)) :
    ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
      (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
      ∃ π : Partition 7 4 ![2,2,2,1],
        d.IsSourceParabolic (sevenPartitionPreimage d.L t π) ∧
        d.SL ≤ sevenPartitionPreimage d.L t π ∧
        sevenPartitionPreimage d.L t π ≤ M ⊓ d.L ∧
        M ⊓ d.L < d.L ∧ d.ConstrainedA7Alternative ∧ d.ConstrainedAlternatives := by
  obtain ⟨hn,hi,_⟩ := s.constrained_small_alternating_input (h := h)
    hG hempty hM hJ hu hf (Or.inr rfl) e
  obtain ⟨hb,t,ht⟩ := s.constrained_seven_block (h := h) hG hempty hM hJ hu hf e
  obtain ⟨π,hP,hSL⟩ := d.constrained_seven_source_parabolic hf t
  obtain ⟨_,hout,hgen⟩ := d.localFamily_seven_partition_generates h hM.1.2 hu
    ⟨d.L_component.1,s.local_component⟩ hi hb t π
  have hplace := (s.parabolic_placement_of_sylow_normalizes hG hM hJ hu h hn _ hP).resolve_right hout
  have hj : (M ⊓ d.L) ⊔ d.ML = d.L := le_antisymm
    (sup_le inf_le_right inf_le_right) (hgen.symm.le.trans (sup_le_sup_right hplace _))
  have ha : d.ConstrainedA7Alternative :=
    ⟨hb,⟨t,π,seven_partition_marking d t π hSL hplace⟩,hj⟩
  exact ⟨t,ht,π,hP,hSL,hplace,
    lt_of_le_not_ge inf_le_right (fun hh => s.outside_M (hh.trans inf_le_left)),
    ha,ConstrainedAlternatives.alternatingSeven ha⟩

/-- The later exchanged selection receives the same fully verified source
parabolic and its generation with M_L, with no new selection or marking. -/
theorem ExchangedSource.constrained_seven_source_parabolic
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7)) :
    IsAlternatingBlock d.L 7 ∧
      ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
        (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
        ∃ π : Partition 7 4 ![2,2,2,1],
          d.IsSourceParabolic (sevenPartitionPreimage d.L t π) ∧
          d.SL ≤ sevenPartitionPreimage d.L t π ∧
          sevenPartitionPreimage d.L t π < d.L ∧
          ¬ sevenPartitionPreimage d.L t π ≤ d.ML ∧
          sevenPartitionPreimage d.L t π ⊔ d.ML = d.L := by
  obtain ⟨_,hi,_⟩ := s.constrained_small_alternating_input hG hempty hM hJ hu h hf (Or.inr rfl) e
  obtain ⟨hb,t,ht⟩ := s.constrained_seven_block hG hempty hM hJ hu h hf e
  obtain ⟨π,hP,hSL⟩ := d.constrained_seven_source_parabolic hf t
  exact ⟨hb,t,ht,π,hP,hSL,d.localFamily_seven_partition_generates h hM.1.2 hu
    ⟨d.L_component.1,s.local_component⟩ hi hb t π⟩
end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher ChapterC
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual original marker supplies the completed A₇ row, preserving
both original primes and the original 15.1.14 premise. -/
theorem PreparedChosenModule.source_preExclusion_constrained_seven
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        ∀ e : d.normalizerImage d.L ≃* alternatingGroup (Fin 7),
          ∃ t : (d.L ⧸ pCore 2 d.L) ≃* alternatingGroup (Fin 7),
            (∀ k : d.L, t (QuotientGroup.mk' (pCore 2 d.L) k) = e (d.toNormalizerImage d.L k)) ∧
            d.ConstrainedA7Alternative ∧ d.ConstrainedAlternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro hf e
  obtain ⟨t,ht,π,hP,hSL,hplace,hproper,ha,hcat⟩ :=
    s.constrained_seven (h := h) hG hempty hM hJ hu hf e
  exact ⟨t,ht,ha,hcat⟩
end CFSG.Quasithin.Chapter15.Section01
