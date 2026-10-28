module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2SourceDuality
public import Theory.GroupTheory.SubgroupPartitionCounting
public import Theory.Representation.BinaryConjugationSection.CentralDuality

/-!
# The original point noncontainment in the G₂ critical pair

Construct the 14.5.21 duality from the actual central binary commutator
pairing, before any alternating Data. The faithful star action puts C_G(U)
in O₂(H) and puts the reciprocal point Zα in O₂(H) ∩ Uα.

If V₁ lies in Uα, the equal intersection and actor indices from 14.7.61
force O₂(H) ∩ Uα = U ∩ Uα. The centralizer of Zα has index at most two
in O₂(H), and its commutators with Uα lie in C_{O₂(H)}(U). This contradicts
the lower bound four on that same dual-section index from G2SourceDuality.

The last theorem constructs the duality and proves the first clause of
14.7.62(1) from the preceding literal intersection index. G2SourceMarkedActors
discharges that index from the full pencil-actor marking and applies this
to the common commutator family. Establishing that critical marking, the
reciprocal noncontainment, and the final four-cycle remain with this branch.
The exact earlier identity [U,O₂(H)] = V₁ is still explicit; its final source
discharge is retained by qt-d-14775-source.

Source: Aschbacher–Smith, 14.5.21(1)–(2), pp.1019–1020, and 14.7.61–62,
pp.1067–1068. The duality construction adapts CriticalIntersections/Construction
without its later Data argument, retaining both literal centralizers.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
open Chapter12.Section08 CriticalFusion.Source CriticalFusion.Source.CriticalIntersections
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (HStar F.H) W}
  (c : BinaryConjugationSection F.H F.U (F.Vi 1) (σ.comp (starMap F)))

omit [Finite G] in
private theorem original_point_centralizer : centralizer (F.Vi 1 : Set G) = F.H :=
  le_antisymm (Subgroup.centralizer_le_normalizer _)
    (normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)))

include c in
/-- Construct the original 14.5.21(1) duality before the later Data record. -/
theorem exists_source_duality
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U) :
    ∃ (X : Type u) (_ : AddCommGroup X) (_ : Module (ZMod 2) X),
      Nonempty (SourceDuality F X (Module.Dual (ZMod 2) X)) := by
  let := h.chosen.elementary
  let := hab
  let := elementary_U F
  have hUQ : F.U ≤ F.H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 F.U)
      c.section_le c.normalized
  have hNQ : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype]
      using (le_normalizer_map (H := pCore 2 F.H) F.H.subtype)
  have hcentral : F.Vi 1 ≤ centralizer (F.H : Set G) := by
    apply le_centralizer_iff.mp
    exact normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  obtain ⟨ρ,sU,sQ,hpair,_⟩ := BinaryConjugationSection.exists_central_duality
    F.H (F.H.pCoreIn 2) F.U (F.Vi 1) (pCoreIn_le 2 F.H)
    c.section_le hNQ c.normalized (c.kernel_le.trans hUQ) hcentral
    (core_commutator c) (by simpa using F.card 1 (by decide))
  exact ⟨_,inferInstance,inferInstance,⟨{
    uAction := ρ
    qAction := ρ.dual
    uSection := sU
    qSection := sQ
    duality := Representation.Equiv.refl ρ.dual
    functional_kernel := hpair }⟩⟩


include c

omit [Finite G] in
/-- Faithfulness of the original star action bounds the ambient centralizer of U. -/
theorem source_centralizer_U_le_core (hf : Function.Injective σ) :
    centralizer (F.U : Set G) ≤ F.H.pCoreIn 2 := by
  intro x hx
  have hxH : x ∈ F.H := by
    rw [← original_point_centralizer (F := F)]
    exact centralizer_le c.kernel_le hx
  let a : F.H := ⟨x,hxH⟩
  have hk : a ∈ (σ.comp (starMap F)).ker := by
    apply (c.action_mem_ker_iff a).mpr
    intro v hv
    have he : ⁅x,v⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hx v hv).symm
    exact he ▸ (F.Vi 1).one_mem
  have he : starMap F a = 1 := hf (hk.trans σ.map_one.symm)
  exact mem_map_of_mem F.H.subtype ((QuotientGroup.eq_one_iff a).mp he)

/-- The reciprocal point lies in the original two-core and the actual partner. -/
theorem source_partner_point_le_core (hf : Function.Injective σ)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (path : CriticalPath (L := L) F) : path.Zα ≤ F.H.pCoreIn 2 ⊓ path.Uα := by
  have hUZ : F.U ≤ centralizer (path.Zα : Set G) := by
    rw [partner_centralizer path]
    exact reciprocal_placement h path
  exact le_inf ((le_centralizer_iff.mp hUZ).trans (source_centralizer_U_le_core c hf))
    (map_mono c.kernel_le)

/-- Equal literal indices identify the reverse core intersection in the containment branch. -/
theorem source_reverse_core_intersection_of_point_le (hf : Function.Injective σ)
    (hab : IsMulCommutative F.U) (path : CriticalPath (L := L) F)
    (hAH : path.Uα ≤ F.H)
    (hindex : ((F.U ⊓ path.Uα) ⊔ F.Vi 1).relIndex F.U = Nat.card (star F path.Uα))
    (hpoint : F.Vi 1 ≤ path.Uα) : F.H.pCoreIn 2 ⊓ path.Uα = F.U ⊓ path.Uα := by
  let := hab
  have hUQ : F.U ≤ F.H.pCoreIn 2 := (le_centralizer _).trans (source_centralizer_U_le_core c hf)
  rw [sup_eq_left.mpr (le_inf c.kernel_le hpoint)] at hindex
  have hi : (F.H.pCoreIn 2 ⊓ path.Uα).relIndex path.Uα = Nat.card (star F path.Uα) :=
    CriticalIntersections.core_intersection_index_eq_star_card path.Uα hAH
  have hI := relIndex_mul_card_of_le (inf_le_left : F.U ⊓ path.Uα ≤ F.U)
  have hQ := relIndex_mul_card_of_le (inf_le_right : F.H.pCoreIn 2 ⊓ path.Uα ≤ path.Uα)
  have hcard : Nat.card path.Uα = Nat.card F.U :=
    card_map_of_injective (MulAut.conj path.conjugator⁻¹).injective
  rw [hindex] at hI
  rw [hi,hcard] at hQ
  have he : Nat.card (F.H.pCoreIn 2 ⊓ path.Uα : Subgroup G) =
      Nat.card (F.U ⊓ path.Uα : Subgroup G) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hQ.trans hI.symm)
  symm
  exact eq_of_le_of_card_ge (inf_le_inf_right _ hUQ) he.le

/-- The central order-two commutator bounds the actual point-centralizer index. -/
theorem source_partner_point_centralizer_index_le_two
    (path : CriticalPath (L := L) F) (hZU : path.Zα ≤ F.U) :
    (centralizer (path.Zα : Set G)).relIndex (F.H.pCoreIn 2) ≤ 2 := by
  obtain ⟨z,_,hz⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  let a := (MulAut.conj path.conjugator⁻¹) z
  have hZa : path.Zα = zpowers a := by
    rw [CriticalPath.Zα,hz,conjugate,MonoidHom.map_zpowers]
    rfl
  have haU : a ∈ F.U := hZU (hZa ▸ mem_zpowers a)
  have hvalue (q : F.H.pCoreIn 2) : ⁅a,(q : G)⁆ ∈ F.Vi 1 := by
    have hh := core_commutator c
    rw [commutator_comm] at hh
    exact hh (commutator_mem_commutator haU q.property)
  let f : F.H.pCoreIn 2 →* F.Vi 1 := {
    toFun q := ⟨⁅a,(q : G)⁆,hvalue q⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro q r
      apply Subtype.ext
      change ⁅a,(q : G) * (r : G)⁆ = ⁅a,(q : G)⁆ * ⁅a,(r : G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have he := (normalizer_le_centralizer_of_card_two (F.Vi 1)
        (by simpa using F.card 1 (by decide)) (pCoreIn_le 2 F.H q.property)) _ (hvalue r)
      calc
        _ = ⁅a,(q : G)⁆ * ((q : G) * ⁅a,(r : G)⁆) * (q : G)⁻¹ := by group
        _ = _ := by rw [← he]; group }
  have hk : f.ker = (centralizer (path.Zα : Set G)).subgroupOf (F.H.pCoreIn 2) := by
    ext q
    change (⟨⁅a,(q : G)⁆,hvalue q⟩ : F.Vi 1) = 1 ↔ _
    rw [Subtype.ext_iff]
    change ⁅a,(q : G)⁆ = 1 ↔ (q : G) ∈ centralizer (path.Zα : Set G)
    rw [commutatorElement_eq_one_iff_mul_comm,hZa]
    constructor
    · intro he x hx
      obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp hx
      exact (Commute.zpow_left he n).eq
    · intro hq
      exact hq a (mem_zpowers a)
  change ((centralizer (path.Zα : Set G)).subgroupOf (F.H.pCoreIn 2)).index ≤ 2
  rw [← hk,index_ker]
  have hle := Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  simpa only [hcard] using hle

/-- The containment branch forces index at most two in the literal dual section. -/
theorem source_dual_fixed_index_le_two_of_point_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hf : Function.Injective σ) (hab : IsMulCommutative F.U)
    (path : CriticalPath (L := L) F) (hAH : path.Uα ≤ F.H)
    (hindex : ((F.U ⊓ path.Uα) ⊔ F.Vi 1).relIndex F.U = Nat.card (star F path.Uα))
    (hpoint : F.Vi 1 ≤ path.Uα) :
    (commutatorPreimage (F.H.pCoreIn 2) path.Uα
      (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))).relIndex (F.H.pCoreIn 2) ≤ 2 := by
  let := hab
  have hI := source_reverse_core_intersection_of_point_le c hf hab path hAH hindex hpoint
  have hZU : path.Zα ≤ F.U :=
    (source_partner_point_le_core c hf h path).trans (hI.le.trans inf_le_left)
  have hQn : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype]
      using (le_normalizer_map (H := pCore 2 F.H) F.H.subtype)
  have hD : ⁅F.H.pCoreIn 2 ⊓ centralizer (path.Zα : Set G),path.Uα⁆ ≤
      F.H.pCoreIn 2 ⊓ path.Uα := by
    refine le_inf ?_ (le_normalizer_iff_commutator_le_right.mp
      (inf_le_right.trans (partner_centralizer_normalizes path)))
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hAH.trans hQn))
  have hbound : ⁅F.H.pCoreIn 2 ⊓ centralizer (path.Zα : Set G),path.Uα⁆ ≤
      F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) :=
    le_inf (hD.trans inf_le_left) ((hD.trans (hI.le.trans inf_le_left)).trans (le_centralizer _))
  have hle := le_commutatorPreimage inf_le_left hbound
  have hi := relIndex_le_of_le_left (L := F.H.pCoreIn 2) hle index_ne_zero_of_finite
  rw [inf_relIndex_left] at hi
  exact hi.trans (source_partner_point_centralizer_index_le_two c path hZU)

variable {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- The first noncontainment of 14.7.62 follows from the actual selected actor
and the intersection-index identity supplied by 14.7.61(2),(4). -/
theorem source_point_noncontainment_of_duality
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective σ)
    (s : SourceDuality F X Y) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection)
    (hindex : ((F.U ⊓ path.Uα) ⊔ F.Vi 1).relIndex F.U = Nat.card (star F path.Uα)) :
    ¬ F.Vi 1 ≤ path.Uα := by
  have hAH : path.Uα ≤ F.H := hplace.trans
    ((pCoreIn_le 2 (F.Li L 1 ⊔ (T : Subgroup G))).trans
      (sup_le ((F.Li_le L 1).trans inf_le_right) (F.invariant 1)))
  have hA := critical_elementary h hab path hplace selection
  let := hA.2
  obtain ⟨a,ha,hne⟩ : ∃ a ∈ star F path.Uα, a ≠ 1 := by
    by_contra! hh
    exact hA.1 (eq_bot_iff.mpr hh)
  have hpow : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a ha
  obtain ⟨a,ha,rfl⟩ := ha
  have hlo := source_dual_fixed_index_ge_four c h hcomponent hfit eK s hcomm
    path.Uα hAH a ha hne hpow
  intro hpoint
  have hhi := source_dual_fixed_index_le_two_of_point_le c h hf hab path hAH hindex hpoint
  omega

/-- Construct the original duality and exclude containment of the flag point.
The only later input is the literal intersection index supplied by 14.7.61. -/
theorem source_point_noncontainment
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hcomponent : ((K F).subgroupOf F.H).IsCComponent)
    (hfit : generalizedFitting (HStar F.H) = star F (K F))
    (eK : ((K F) ⧸ pCore 2 (K F)) ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective σ) (hcomm : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (path : CriticalPath (L := L) F) (hplace : path.Uα ≤ F.Ri L 1)
    (selection : path.RankSelection)
    (hindex : ((F.U ⊓ path.Uα) ⊔ F.Vi 1).relIndex F.U = Nat.card (star F path.Uα)) :
    ¬ F.Vi 1 ≤ path.Uα := by
  obtain ⟨X,aX,mX,hs⟩ := exists_source_duality c h hab
  let := aX
  let := mX
  obtain ⟨s⟩ := hs
  exact source_point_noncontainment_of_duality c h hab hcomponent hfit eK hf s hcomm
    path hplace selection hindex

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.G2Source
