module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Swapped.Containment.Noncentral
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Factors.Complement
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import Theory.GroupAction.IrreducibleElementaryContainment
public import Theory.GroupTheory.CComponent.SimplePairProduct

/-!
# Lifting the exchanged-orbit containment and constructing its plane

Containment of the odd complement in the image of the relatively normal
orbit lifts through the actual centralizer two-core by coprimality.
Two-perfectness then places the whole canonical radical in that orbit.
The two genuine conjugate C-components construct a product marking of the
orbit quotient; it embeds the complement into two equal factors. The ambient
odd-rank bound makes it abelian, so its source elementary/extraspecial
alternative identifies it with the actual plane.

The conditional consumer supplies these deductions and the literal product
P T_u = T_u P to SwappedData. Descendant modules prove its quotient-containment,
complement-factor and model-row inputs, completing the sieve in Containment.Rows.

Source: Aschbacher--Smith, 13.1.12(3), printed p.874.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.Section02 Chapter1.XiEmbedding Chapter1.RadicalActions
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K : Subgroup G} {p : ℕ} [Fact p.Prime] {u : G}

/-- Quotient containment is sufficient on the literal maps; it is not
necessary to identify X with its image modulo O₂(C_G(u)). -/
theorem Context.swapped_containment_of_quotient (h : Context T L p)
    (s : Selected T L u) (e : Escape T L p u K) (P : Sylow p (XiP p L))
    (hquot : quotientImage (centralizer ({u} : Set G))
        ((P : Subgroup (XiP p L)).map (XiP p L).subtype) ≤
      quotientImage (centralizer ({u} : Set G))
        (componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)))) :
    XiP p L ≤ componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) := by
  let H := centralizer ({u} : Set G)
  let D := componentOrbit K ((T : Subgroup G) ⊓ H)
  let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  have hDH : D ≤ H := (componentOrbit_le_sup _ _).trans (sup_le e.component.1 inf_le_right)
  have hPH : P₀ ≤ H := (map_subtype_le _).trans
    ((SourceNonquasisimple.XiP_le_moved_centralizer h.hypothesis h.many h.maximal.1
      h.nonquasisimple p s.mem).trans inf_le_right)
  have hH := h.hypothesis.simpleQTKE.involution_centralizer_sqtk
    (h.involution s.mem s.ne_one)
  let : (D.subgroupOf H).Normal := e.orbit_normal hH
  have hsup : P₀.subgroupOf H ≤ D.subgroupOf H ⊔ pCore 2 H := by
    have hh := map_le_iff_le_comap.mp hquot
    change P₀.subgroupOf H ≤ ((D.subgroupOf H).map
      (QuotientGroup.mk' (pCore 2 H))).comap (QuotientGroup.mk' (pCore 2 H)) at hh
    simpa only [comap_map_eq,QuotientGroup.ker_mk'] using hh
  have hsub : P₀.subgroupOf H ≤ D.subgroupOf H :=
    le_normal_of_le_sup_coprime_pGroup _ _ _
      (h.swapped_complement_shape P).isPGroup.comap_subtype pCore_isPGroup
      (Nat.coprime_two_right.mpr h.odd) hsup
  have hPD : P₀ ≤ D := by
    have hm := map_mono (f := H.subtype) hsub
    simpa only [map_subgroupOf_eq_of_le hPH,map_subgroupOf_eq_of_le hDH] using hm
  exact h.radical_le_of_complement_le s P D hDH inferInstance hPD

private theorem simple_of_linear_model {Q : Type*} [Group Q]
    (hq : IsQuasisimple Q) {q : ℕ} (hm : ClassicalGroup.IsPSL Q 2 q) :
    IsSimpleGroup Q := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hm
  let _ := hq
  let _ : Group.IsPerfect PSL(2, F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hs : IsSimpleGroup PSL(2, F) :=
    MulAction.IwasawaStructure.isSimpleGroup Group.IsPerfect.commutator_eq_top
      PSL2.Iwasawa inferInstance
  exact e.isSimpleGroup_congr.mpr hs

/-- The broad source model list already makes the intrinsic quotient simple. -/
theorem Context.swapped_component_simple (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) :
    IsSimpleGroup (XiQuotient K) := by
  have hH := h.hypothesis.simpleQTKE.involution_centralizer_sqtk
    (h.involution s.mem s.ne_one)
  cases h.reducible_component_model o s e hH hr with
  | linear_even n hn iso => exact simple_of_linear_model e.quotient iso
  | linear_prime q hq ho iso => exact simple_of_linear_model e.quotient iso
  | suzuki m hm iso =>
    exact iso.some.isSimpleGroup_congr.mpr
      (BenderSuzuki.External.huppert_blackburn_XI_3_6 m (by omega)).1
  | janko iso => exact iso.some.isSimpleGroup

/-- The actual two conjugate components give a repeated-factor marking of
D/O₂(D). This uses neither containment of X nor an irreducible Sylow action. -/
theorem Context.swapped_quotient_product (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) :
    Nonempty (XiQuotient (componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G))) ≃*
      XiQuotient K × XiQuotient K) := by
  let H := centralizer ({u} : Set G)
  let S := (T : Subgroup G) ⊓ H
  let D := componentOrbit K S
  have hDH : D ≤ H := (componentOrbit_le_sup _ _).trans (sup_le e.component.1 inf_le_right)
  have hH := h.hypothesis.simpleQTKE.involution_centralizer_sqtk
    (h.involution s.mem s.ne_one)
  obtain ⟨t,ht,_,hne,he,_⟩ := h.exists_component_exchange o s e hH hr
  have hKD : K ≤ D := le_componentOrbit K S
  have hCD : K.conjBy t ≤ D := le_iSup (fun a : S => K.conjBy (a : G)) ⟨t,ht⟩
  let A := K.subgroupOf D
  let B := (K.conjBy t).subgroupOf D
  have hA : A.IsCComponent := e.component.2.subgroupOf_of_le hKD hDH
  have hB : B.IsCComponent :=
    (SwappedFactorsProof.conjugate_component e.component ht.2).2.subgroupOf_of_le hCD hDH
  have hab : A ≠ B := by
    intro hh
    have hh' := congrArg (map D.subtype) hh
    rw [map_subgroupOf_eq_of_le hKD,map_subgroupOf_eq_of_le hCD] at hh'
    exact hne hh'.symm
  have hgen : A ⊔ B = ⊤ := by
    change K.subgroupOf D ⊔ (K.conjBy t).subgroupOf D = ⊤
    rw [← subgroupOf_sup hKD hCD,← he]
    exact subgroupOf_self D
  let a : A ≃* K := subgroupOfEquivOfLe hKD
  let c : K ≃* K.conjBy t := equivMapOfInjective K (MulAut.conj t).toMonoidHom
    (MulAut.conj t).injective
  let b : B ≃* K := (subgroupOfEquivOfLe hCD).trans c.symm
  let aq : XiQuotient A ≃* XiQuotient K := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let bq : XiQuotient B ≃* XiQuotient K := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let : IsSimpleGroup (XiQuotient K) := h.swapped_component_simple o s e hr
  obtain ⟨q,hq,hker,_,_⟩ := exists_twoCore_product_of_simple_pair A B hA hB hab hgen aq bq
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)⟩

/-- A genuine repeated-factor quotient marking makes the actual complement
an elementary plane, without irreducibility of T_u. -/
theorem Context.swapped_plane_of_product (h : Context T L p)
    (s : Selected T L u) (e : Escape T L p u K) (P : Sylow p (XiP p L))
    (hcontained : XiP p L ≤ componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)))
    (product : XiQuotient (componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G))) ≃*
      XiQuotient K × XiQuotient K) :
    Nonempty (((P : Subgroup (XiP p L)).map (XiP p L).subtype) ≃* Plane p) := by
  let H := centralizer ({u} : Set G)
  let D := componentOrbit K ((T : Subgroup G) ⊓ H)
  let P₀ := (P : Subgroup (XiP p L)).map (XiP p L).subtype
  have hPD : P₀ ≤ D := (map_subtype_le _).trans hcontained
  have hDH : D ≤ H := (componentOrbit_le_sup _ _).trans (sup_le e.component.1 inf_le_right)
  have hH := h.hypothesis.simpleQTKE.involution_centralizer_sqtk
    (h.involution s.mem s.ne_one)
  have hD : IsSQTK KnownSimple.IsKnownSimple D :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hDH)).mp (hH.subgroup (D.subgroupOf H))
  have hr : primeRank p (XiQuotient K × XiQuotient K) ≤ 2 := by
    rw [← primeRank_congr p product]
    exact quotient_stronglyQuasithin hD.stronglyQuasithin p (Fact.out : p.Prime) h.odd
  let f : P₀ →* XiQuotient D := (QuotientGroup.mk' (pCore 2 D)).comp (inclusion hPD)
  have hshape := h.swapped_complement_shape P
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    have hc : inclusion hPD a ∈ pCore 2 D := (QuotientGroup.eq_one_iff _).mp ha
    have hcG : (a : G) ∈ D.pCoreIn 2 := mem_map_of_mem D.subtype hc
    exact Subtype.ext ((hshape.isPGroup.disjoint_of_coprime (isPGroup_pCoreIn 2 D)
      (Nat.coprime_two_right.mpr h.odd)).le_bot ⟨a.property,hcG⟩)
  have hc : IsMulCommutative P₀ := SwappedFactorsProof.commutative_pGroup_of_product_rank
    h.odd hr hshape.isPGroup (product.toMonoidHom.comp f) (product.injective.comp hf)
  let := hc
  rcases hshape with ⟨he,hcard⟩ | ⟨he,_,_⟩
  · let := he
    exact InvariantThree.plane_of_elementary_card hcard
  · exact ((QuotientGroup.nontrivial_iff.mp he.quotient_nontrivial)
      (center_eq_top (G := P₀))).elim

/-- The remaining quotient and factor geometry feeds the exact SwappedData
consumer. Constructing its two remaining premises stays with the containment
assembly; this conditional theorem does not complete the source sieve. -/
theorem Context.swapped_data_of_quotient_geometry (h : Context T L p)
    (o : OrbitFacts T L p) (s : Selected T L u) (e : Escape T L p u K)
    (hr : ¬ ComponentNormalizerIrreducible L K p u) (P : Sylow p (XiP p L))
    (hquot : quotientImage (centralizer ({u} : Set G))
        ((P : Subgroup (XiP p L)).map (XiP p L).subtype) ≤
      quotientImage (centralizer ({u} : Set G))
        (componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G))))
    (geometry : XiP p L ≤ componentOrbit K ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) →
      SwappedFactors ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        ((P : Subgroup (XiP p L)).map (XiP p L).subtype) K ∧
      SwappedRow p (XiQuotient K)) :
    SwappedData T L p u K ((P : Subgroup (XiP p L)).map (XiP p L).subtype) := by
  have hcontained := h.swapped_containment_of_quotient s e P hquot
  obtain ⟨hf,hrow⟩ := geometry hcontained
  obtain ⟨product⟩ := h.swapped_quotient_product o s e hr
  exact ⟨hcontained,h.swapped_plane_of_product s e P hcontained product,hf,
    h.complement_point_sylow_permutable s P,hrow⟩

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
