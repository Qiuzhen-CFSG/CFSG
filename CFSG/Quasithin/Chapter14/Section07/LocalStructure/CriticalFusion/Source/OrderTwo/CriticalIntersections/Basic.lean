module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.ModuleTransport
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.Selection
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Critical intersections before the duality contradiction

This proves 14.7.69(b)–(e) from the actual source setup, the earlier reciprocal
geodesic placement U ≤ Gα, the full earlier identity [U,O₂(H)]=V₁, and the
original-section calculations in (a). The ambient subgroup identities are
proved by lifting through exactly V₁. The displacement bound excludes all
points of U outside U₀V from Qα. Actual cardinalities then give both critical
ranks, without postulating reciprocal symmetry or a swapping group element.

In the temporary branch V₁ ≤ Uα, equal quotient orders identify O₂(H)∩Uα.
The point centralizer has index at most two in O₂(H) and centralizes Uα modulo
C_{O₂(H)}(U). Thus this branch yields a fixed subspace of codimension at most
one in precisely the section from 14.5.21(1), expressed as a literal relative
index. `SourceDuality` specifies that earlier theorem's two genuine sections,
equivariant linear isomorphism and functional kernels.

The module calculations remain with qt-14-07-order-two-marked-partitions.
The geodesic placement and earlier critical selection remain with qt-14-07;
14.5.21(1)–(2) remain with qt-14-05-terminal-duality. We use the actual (2),
not an unjustified enlargement of [V₂,O₂(H)]=V₁ in 14.7.4(1).
The transport of rank two to the dual section, point noncontainment, reciprocal
source setup, (f), and the order-two U₀ exclusion are still required. No theorem
below asserts the completion of 14.7.69 or assumes those conclusions.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.5.21, printed pp.1019–1020; 14.7.39, p.1060; 14.7.69, pp.1072–1073.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace CriticalIntersections

private theorem imageSpace_mem_iff (d : Data T L V F W) (B : Subgroup G)
    (hZB : F.Vi 1 ≤ B) (x : F.U) :
    (d.conjugationSection.coordinates x).toAdd ∈ d.conjugationSection.imageSpace B ↔
      (x : G) ∈ B := by
  constructor
  · intro hx
    obtain ⟨b, hb, he⟩ := (d.conjugationSection.mem_imageSpace_iff B _).mp hx
    have hk : (x / b : F.U).val ∈ F.Vi 1 := by
      apply (d.conjugationSection.coordinates_eq_one_iff _).mp
      rw [map_div, Multiplicative.toAdd.injective he]
      exact div_self' _
    have hm := B.mul_mem (hZB hk) hb
    simpa using hm
  · intro hx
    exact (d.conjugationSection.mem_imageSpace_iff B _).mpr ⟨x, hx, rfl⟩

/-- The two identities in 14.7.69(a) are identities on the original U/V₁.
The last field is the displacement bound immediately following (c).
These are the outputs required from the independent marked-module calculation;
no ambient intersection or point noncontainment is included. -/
structure ModuleCalculations (d : Data T L V F W)
    (c : CriticalPath (L := L) F) (hAH : c.Uα ≤ F.H) : Prop where
  moved : d.conjugationSection.imageSpace ⁅F.U, c.Uα⁆ =
    d.conjugationSection.imageSpace (d.U₀ ⊔ V)
  fixed : Representation.invariants (d.action.comp (Subgroup.inclusion hAH)) =
    d.conjugationSection.imageSpace (d.U₀ ⊔ V)
  displacement : ∀ x ∈ F.U, x ∉ d.U₀ ⊔ V →
    4 ≤ Nat.card (⁅zpowers x, c.Uα⁆ : Subgroup G)

/-- The genuine 14.5.21(1) duality on its two original sections. The
functional clause keeps the source identification of each functional kernel.
Producing this datum remains with qt-14-05-terminal-duality. -/
structure SourceDuality (F : InvariantFlag T V 3)
    (X Y : Type u) [AddCommGroup X] [Module (ZMod 2) X]
    [AddCommGroup Y] [Module (ZMod 2) Y] where
  uAction : Representation (ZMod 2) F.H X
  qAction : Representation (ZMod 2) F.H Y
  uSection : BinaryConjugationSection F.H F.U
    (F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G)) uAction
  qSection : BinaryConjugationSection F.H (F.H.pCoreIn 2)
    (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) qAction
  duality : qAction.Equiv uAction.dual
  functional_kernel : ∀ q : F.H.pCoreIn 2, ∀ v : F.U,
    duality (qSection.coordinates q).toAdd (uSection.coordinates v).toAdd = 0 ↔
      ⁅(q : G), (v : G)⁆ = 1

omit [Finite G] in
private theorem centralizer_conjugate (A : Subgroup G) (g : G) :
    conjugate (centralizer (A : Set G)) g = centralizer (conjugate A g : Set G) := by
  change (centralizer (A : Set G)).map (MulAut.conj g⁻¹).toMonoidHom = _
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨(MulAut.conj g) x, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    intro a ha
    apply (MulAut.conj g⁻¹).injective
    simpa [map_mul, MulAut.conj_apply, mul_assoc] using
      hx ((MulAut.conj g⁻¹) a) (mem_map_of_mem _ ha)

omit [Finite G] in
private theorem core_conjugate (A : Subgroup G) (g : G) :
    conjugate (A.pCoreIn 2) g = (conjugate A g).pCoreIn 2 :=
  map_pCoreIn_of_injective 2 A _ (MulAut.conj g⁻¹).injective

/-- The actual section kernel gives C_G(U) ≤ O₂(H). It does not identify
O₂(H) with O₂(K). -/
theorem centralizer_U_le_core (d : Data T L V F W) (hc : d.SectionCentralizer) :
    centralizer (F.U : Set G) ≤ F.H.pCoreIn 2 := by
  intro x hx
  have hxH : x ∈ F.H := by
    rw [d.centralizer_eq]
    intro y hy
    have hyz : y = d.z := Set.mem_singleton_iff.mp hy
    subst y
    exact hx d.z (d.U₀_le_U d.z_mem_U₀)
  have hk : (⟨x, hxH⟩ : F.H) ∈ d.action.ker := by
    change d.action ⟨x, hxH⟩ = 1
    ext w
    obtain ⟨a, ha⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w)
    have ha' : (d.conjugationSection.coordinates a).toAdd = w :=
      congrArg Multiplicative.toAdd ha
    change d.action ⟨x, hxH⟩ w = w
    rw [← ha', ← d.conjugationSection.equivariant]
    congr 2
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul).mpr (hx a a.property).symm
  rw [hc] at hk
  exact hk

/-- The same centralizer containment transported by the actual right conjugator. -/
theorem centralizer_Uα_le_Qα (d : Data T L V F W) (hc : d.SectionCentralizer)
    (c : CriticalPath (L := L) F) : centralizer (c.Uα : Set G) ≤ c.Qα := by
  rw [CriticalPath.Uα, ← centralizer_conjugate]
  exact (map_mono (centralizer_U_le_core d hc)).trans_eq (core_conjugate _ _)

/-- 14.7.69(b). The reciprocal placement is the earlier geodesic placement
U ≤ Gα; it is not an intersection equality. -/
theorem commutator_sandwich (d : Data T L V F W) (c : CriticalPath (L := L) F)
    (hAH : c.Uα ≤ F.H) (hUH : F.U ≤ conjugate F.H c.conjugator) :
    ⁅F.U, c.Uα⁆ ≤ F.U ⊓ c.Uα ∧
      F.U ⊓ c.Uα ≤ F.U ⊓ centralizer (c.Uα : Set G) := by
  let : IsMulCommutative F.U := d.abelian
  let : IsMulCommutative c.Uα :=
    inferInstanceAs (IsMulCommutative (F.U.map (MulAut.conj c.conjugator⁻¹).toMonoidHom))
  have hAn : c.Uα ≤ normalizer (F.U : Set G) := hAH.trans d.conjugationSection.normalized
  have hUn : F.U ≤ normalizer (c.Uα : Set G) :=
    hUH.trans ((map_mono d.conjugationSection.normalized).trans (le_normalizer_map _))
  exact ⟨le_inf (le_normalizer_iff_commutator_le_left.mp hAn)
    (le_normalizer_iff_commutator_le_right.mp hUn),
    le_inf inf_le_left (inf_le_right.trans (le_centralizer _))⟩

private theorem point_centralizes (d : Data T L V F W) (A : Subgroup G)
    (hAH : A ≤ F.H) : F.Vi 1 ≤ centralizer (A : Set G) := by
  rw [d.point]
  apply zpowers_le.mpr
  intro a ha
  exact (show d.z * a = a * d.z from
    (show a ∈ centralizer ({d.z} : Set G) from d.centralizer_eq ▸ hAH ha)
      d.z (Set.mem_singleton d.z)).symm

/-- 14.7.69(c): the module equality lifts through precisely V₁. -/
theorem centralizer_and_products (d : Data T L V F W)
    (c : CriticalPath (L := L) F) (hAH : c.Uα ≤ F.H)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hm : ModuleCalculations d c hAH) :
    ⁅F.U, c.Uα⁆ ⊔ F.Vi 1 = d.U₀ ⊔ V ∧
      (F.U ⊓ c.Uα) ⊔ F.Vi 1 = d.U₀ ⊔ V ∧
      F.U ⊓ centralizer (c.Uα : Set G) = d.U₀ ⊔ V := by
  let P := d.U₀ ⊔ V
  have hPU : P ≤ F.U := sup_le d.U₀_le_U (Data.V_le_U F)
  have hZP : F.Vi 1 ≤ P := d.point_le_U₀.trans le_sup_left
  have hZU : F.Vi 1 ≤ F.U := d.conjugationSection.kernel_le
  obtain ⟨hDE, hEC⟩ := commutator_sandwich d c hAH hUH
  have hDU : ⁅F.U, c.Uα⁆ ≤ F.U := hDE.trans inf_le_left
  have hCP : F.U ⊓ centralizer (c.Uα : Set G) ≤ P := by
    intro x hx
    apply (imageSpace_mem_iff d P hZP ⟨x, hx.1⟩).mp
    rw [← hm.fixed]
    intro a
    change d.action (Subgroup.inclusion hAH a)
      (d.conjugationSection.coordinates ⟨x, hx.1⟩).toAdd = _
    rw [← d.conjugationSection.equivariant]
    congr 2
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul).mpr (hx.2 a a.property)
  have hgen : ⁅F.U, c.Uα⁆ ⊔ F.Vi 1 = P := by
    apply le_antisymm (sup_le ((hDE.trans hEC).trans hCP) hZP)
    intro x hx
    let B := ⁅F.U, c.Uα⁆ ⊔ F.Vi 1
    apply (imageSpace_mem_iff d B le_sup_right ⟨x, hPU hx⟩).mp
    apply d.conjugationSection.imageSpace_mono (le_sup_left : ⁅F.U, c.Uα⁆ ≤ B)
    rw [hm.moved]
    exact (imageSpace_mem_iff d P hZP ⟨x, hPU hx⟩).mpr hx
  have hZC : F.Vi 1 ≤ F.U ⊓ centralizer (c.Uα : Set G) :=
    le_inf hZU (point_centralizes d _ hAH)
  have hPC : P ≤ F.U ⊓ centralizer (c.Uα : Set G) :=
    hgen.ge.trans (sup_le (hDE.trans hEC) hZC)
  exact ⟨hgen, le_antisymm (sup_le (hEC.trans hCP) hZP)
    (hgen.ge.trans (sup_le_sup_right hDE _)), le_antisymm hCP hPC⟩

omit [Finite G] in
/-- The whole earlier 14.5.21(2) commutator identity transports to the
actual Qα. In particular the weaker 14.7.4(1) restriction is not enlarged
silently to a statement about U. -/
theorem reciprocal_core_commutator
    (c : CriticalPath (L := L) F)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ⁅c.Uα, c.Qα⁆ = c.Zα := by
  change ⁅conjugate F.U c.conjugator, (conjugate F.H c.conjugator).pCoreIn 2⁆ = _
  rw [← core_conjugate]
  change ⁅F.U.map _, (F.H.pCoreIn 2).map _⁆ = (F.Vi 1).map _
  rw [← map_commutator, hcomm]

/-- 14.7.69(d), from the source displacement bound and the earlier
central commutator identity. -/
theorem core_intersection (d : Data T L V F W) (hc : d.SectionCentralizer)
    (c : CriticalPath (L := L) F) (hAH : c.Uα ≤ F.H)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hm : ModuleCalculations d c hAH)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    F.U ⊓ c.Qα = d.U₀ ⊔ V := by
  have hC := (centralizer_and_products d c hAH hUH hm).2.2
  apply le_antisymm
  · intro x hx
    by_contra hn
    have hfour := hm.displacement x hx.1 hn
    have hle : ⁅zpowers x, c.Uα⁆ ≤ c.Zα := by
      rw [← reciprocal_core_commutator c hcomm, commutator_comm c.Uα]
      exact commutator_mono (zpowers_le.mpr hx.2) le_rfl
    have hcard := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
    have hz : Nat.card c.Zα = 2 := by
      rw [CriticalPath.Zα, conjugate, card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective]
      simpa using F.card 1 (by decide)
    omega
  · rw [← hC]
    exact inf_le_inf_left _ (centralizer_Uα_le_Qα d hc c)

/-- 14.7.69(e), with the same original Zα and the genuine O₂(H). -/
theorem point_le_core_intersection (d : Data T L V F W) (hc : d.SectionCentralizer)
    (c : CriticalPath (L := L) F)
    (hUH : F.U ≤ conjugate F.H c.conjugator) :
    c.Zα ≤ F.H.pCoreIn 2 ⊓ c.Uα := by
  have hHZ : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    le_centralizer_iff.mp (point_centralizes d F.H le_rfl)
  have hUZ : F.U ≤ centralizer (c.Zα : Set G) := by
    apply hUH.trans
    rw [CriticalPath.Zα, ← centralizer_conjugate]
    exact map_mono hHZ
  exact le_inf ((le_centralizer_iff.mp hUZ).trans (centralizer_U_le_core d hc))
    (map_mono d.conjugationSection.kernel_le)

/-- Orders of the original natural quotient, before making any critical choice. -/
theorem card_U_eq_sixteen_mul_card_U₀ (d : Data T L V F W) :
    Nat.card F.U = 16 * Nat.card d.U₀ := by
  let q : F.U →* Multiplicative Representation.SL2FourNatural.V :=
    d.projection.toLinearMap.toAddMonoidHom.toMultiplicative.comp
      d.conjugationSection.coordinates
  have hq : Function.Surjective q := by
    intro w
    obtain ⟨v, hv⟩ := d.projection_onto w.toAdd
    obtain ⟨x, hx⟩ := d.conjugationSection.onto (Multiplicative.ofAdd v)
    refine ⟨x, ?_⟩
    change Multiplicative.ofAdd (d.projection (d.conjugationSection.coordinates x).toAdd) = w
    rw [hx]
    exact Multiplicative.toAdd.injective hv
  have hk : q.ker = d.U₀.subgroupOf F.U := by
    ext x
    exact (d.mem_U₀ x).symm
  rw [card_eq_card_quotient_mul_card_subgroup q.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv, hk,
    Nat.card_congr (subgroupOfEquivOfLe d.U₀_le_U).toEquiv]
  congr 1
  change Nat.card Representation.SL2FourNatural.V = 16
  rw [Nat.card_eq_fintype_card, Representation.SL2FourNatural.card_vector]

/-- The product U₀V has order four times the order of U₀. -/
theorem card_fixed_product (d : Data T L V F W) (hs : d.ModuleSeparation) :
    Nat.card (d.U₀ ⊔ V : Subgroup G) = 4 * Nat.card d.U₀ := by
  let : IsMulCommutative F.U := d.abelian
  have hn : V ≤ normalizer (d.U₀ : Set G) :=
    (Data.V_le_U F).trans (d.conjugationSection.section_le.trans d.H_normalizes_U₀)
  have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes d.U₀ V hn
  rw [inf_comm d.U₀ V, d.seed_inf_U₀ hs] at h
  have hV : Nat.card V = 8 := by
    rw [← F.last]
    simpa using F.card 3 (by decide)
  have hZ : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  rw [hV, hZ] at h
  omega

/-- The source critical quotient has rank two, measured by its literal index. -/
theorem fixed_product_index (d : Data T L V F W) (hs : d.ModuleSeparation) :
    (d.U₀ ⊔ V).relIndex F.U = 4 := by
  have hPU : d.U₀ ⊔ V ≤ F.U := sup_le d.U₀_le_U (Data.V_le_U F)
  have h := ((d.U₀ ⊔ V).subgroupOf F.U).index_mul_card
  change (d.U₀ ⊔ V).relIndex F.U * Nat.card ((d.U₀ ⊔ V).subgroupOf F.U) = _ at h
  rw [Nat.card_congr (subgroupOfEquivOfLe hPU).toEquiv,
    card_fixed_product d hs, card_U_eq_sixteen_mul_card_U₀ d, ← mul_assoc] at h
  have hp : 0 < Nat.card d.U₀ := Nat.card_pos
  have hm := Nat.eq_of_mul_eq_mul_right hp h
  omega

/-- Equal positive ranks in Remark 14.7.39, obtained from (d) and the actual
star map. This equality alone does not supply a group element swapping vertices. -/
theorem equal_critical_ranks (d : Data T L V F W) (hc : d.SectionCentralizer)
    (hs : d.ModuleSeparation) (c : CriticalPath (L := L) F)
    (earlier : c.EarlierImages) (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hm : ModuleCalculations d c (c.Uα_le_H earlier))
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hfull : star F c.Uα = star F (Q T L)) :
    Nat.log 2 ((F.U ⊓ c.Qα).relIndex F.U) = 2 ∧
      Nat.log 2 (Nat.card (star F c.Uα)) = 2 := by
  rw [core_intersection d hc c (c.Uα_le_H earlier) hUH hm hcomm,
    fixed_product_index d hs, hfull, c.star_Q_card d earlier]
  decide

omit [Finite G] in
/-- The order of an image under star is the index of the literal intersection
with O₂(H), using containment in H rather than an ambient quotient map. -/
theorem core_intersection_index_eq_star_card
    (A : Subgroup G) (hAH : A ≤ F.H) :
    (F.H.pCoreIn 2 ⊓ A).relIndex A = Nat.card (star F A) := by
  have hk : (starMap F).ker = (F.H.pCoreIn 2).subgroupOf F.H := by
    rw [starMap, QuotientGroup.ker_mk']
    change pCore 2 F.H = ((pCore 2 F.H).map F.H.subtype).comap F.H.subtype
    exact (comap_map_eq_self_of_injective F.H.subtype_injective _).symm
  rw [inf_relIndex_right, ← relIndex_subgroupOf hAH, ← hk, relIndex_ker]
  rfl

/-- In the temporary branch V₁ ≤ Uα, equal actual quotient orders force
O₂(H) ∩ Uα = U ∩ Uα. This is the input to the duality contradiction,
not an assumed ambient intersection. -/
theorem reverse_core_intersection_of_point_le (d : Data T L V F W)
    (hc : d.SectionCentralizer) (hs : d.ModuleSeparation)
    (c : CriticalPath (L := L) F) (earlier : c.EarlierImages)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hm : ModuleCalculations d c (c.Uα_le_H earlier))
    (hfull : star F c.Uα = star F (Q T L)) (hpoint : F.Vi 1 ≤ c.Uα) :
    F.H.pCoreIn 2 ⊓ c.Uα = F.U ⊓ c.Uα := by
  let : IsMulCommutative F.U := d.abelian
  have hUQ : F.U ≤ F.H.pCoreIn 2 := (le_centralizer _).trans (centralizer_U_le_core d hc)
  have hEP : F.U ⊓ c.Uα = d.U₀ ⊔ V := by
    have h := (centralizer_and_products d c (c.Uα_le_H earlier) hUH hm).2.1
    rwa [sup_eq_left.mpr (le_inf d.conjugationSection.kernel_le hpoint)] at h
  have hi : (F.H.pCoreIn 2 ⊓ c.Uα).relIndex c.Uα = 4 := by
    rw [core_intersection_index_eq_star_card _ (c.Uα_le_H earlier), hfull,
      c.star_Q_card d earlier]
  have hcA : Nat.card c.Uα = Nat.card F.U :=
    card_map_of_injective (MulAut.conj c.conjugator⁻¹).injective
  have hcI := ((F.H.pCoreIn 2 ⊓ c.Uα).subgroupOf c.Uα).index_mul_card
  change (F.H.pCoreIn 2 ⊓ c.Uα).relIndex c.Uα *
    Nat.card ((F.H.pCoreIn 2 ⊓ c.Uα).subgroupOf c.Uα) = Nat.card c.Uα at hcI
  rw [hi, Nat.card_congr (subgroupOfEquivOfLe (inf_le_right :
    F.H.pCoreIn 2 ⊓ c.Uα ≤ c.Uα)).toEquiv, hcA,
    card_U_eq_sixteen_mul_card_U₀ d] at hcI
  symm
  apply eq_of_le_of_card_ge (inf_le_inf_right _ hUQ)
  rw [hEP, card_fixed_product d hs]
  omega

private theorem point_centralizer_eq (d : Data T L V F W) :
    centralizer (F.Vi 1 : Set G) = F.H := by
  apply le_antisymm
  · rw [d.centralizer_eq]
    apply centralizer_le
    intro x hx
    have he : x = d.z := Set.mem_singleton_iff.mp hx
    rw [he, d.point]
    exact mem_zpowers d.z
  · exact le_centralizer_iff.mp (point_centralizes d F.H le_rfl)

/-- The critical point centralizer is the conjugate of the original H,
with the original right conjugator. -/
theorem critical_point_centralizer_eq (d : Data T L V F W)
    (c : CriticalPath (L := L) F) :
    centralizer (c.Zα : Set G) = conjugate F.H c.conjugator := by
  rw [CriticalPath.Zα, ← centralizer_conjugate, point_centralizer_eq d]

/-- When Zα lies in U, its centralizer has index at most two in O₂(H).
This proves the group-side hyperplane bound used by the source duality step. -/
theorem critical_point_centralizer_index_le_two (d : Data T L V F W)
    (c : CriticalPath (L := L) F)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) (hZU : c.Zα ≤ F.U) :
    (centralizer (c.Zα : Set G)).relIndex (F.H.pCoreIn 2) ≤ 2 := by
  let a := (MulAut.conj c.conjugator⁻¹) d.z
  have hZa : c.Zα = zpowers a := by
    rw [CriticalPath.Zα, d.point, conjugate, MonoidHom.map_zpowers]
    rfl
  have haU : a ∈ F.U := hZU (hZa ▸ mem_zpowers a)
  have hvalue (q : F.H.pCoreIn 2) : ⁅a, (q : G)⁆ ∈ F.Vi 1 := by
    rw [← hcomm]
    exact commutator_mem_commutator haU q.property
  let f : F.H.pCoreIn 2 →* F.Vi 1 := {
    toFun q := ⟨⁅a, (q : G)⁆, hvalue q⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro q r
      apply Subtype.ext
      change ⁅a, (q : G) * (r : G)⁆ = ⁅a, (q : G)⁆ * ⁅a, (r : G)⁆
      rw [commutatorElement_mul_right_eq_mul_conj]
      have he := point_centralizes d (F.H.pCoreIn 2) (pCoreIn_le 2 F.H)
        (hvalue r) q q.property
      calc
        _ = ⁅a, (q : G)⁆ * ((q : G) * ⁅a, (r : G)⁆) * (q : G)⁻¹ := by group
        _ = _ := by rw [he]; group }
  have hk : f.ker = (centralizer (c.Zα : Set G)).subgroupOf (F.H.pCoreIn 2) := by
    ext q
    change (⟨⁅a, (q : G)⁆, hvalue q⟩ : F.Vi 1) = 1 ↔ _
    rw [Subtype.ext_iff]
    change ⁅a, (q : G)⁆ = 1 ↔ (q : G) ∈ centralizer (c.Zα : Set G)
    rw [commutatorElement_eq_one_iff_mul_comm, hZa]
    constructor
    · intro he x hx
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
      exact (Commute.zpow_left he n).eq
    · intro hq
      exact hq a (mem_zpowers a)
  change ((centralizer (c.Zα : Set G)).subgroupOf (F.H.pCoreIn 2)).index ≤ 2
  rw [← hk, index_ker]
  have hle := Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  simpa only [hcard] using hle

/-- In the temporary containment branch, the point centralizer centralizes
Uα modulo C_{O₂(H)}(U), exactly the section occurring in 14.5.21(1). -/
theorem dual_section_commutator_bound_of_point_le (d : Data T L V F W)
    (hc : d.SectionCentralizer) (hs : d.ModuleSeparation)
    (c : CriticalPath (L := L) F) (earlier : c.EarlierImages)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hm : ModuleCalculations d c (c.Uα_le_H earlier))
    (hfull : star F c.Uα = star F (Q T L)) (hpoint : F.Vi 1 ≤ c.Uα) :
    ⁅F.H.pCoreIn 2 ⊓ centralizer (c.Zα : Set G), c.Uα⁆ ≤
      F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G) := by
  let : IsMulCommutative F.U := d.abelian
  have hQn : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (le_normalizer_map (H := pCore 2 F.H) F.H.subtype)
  have hAn : centralizer (c.Zα : Set G) ≤ normalizer (c.Uα : Set G) := by
    rw [critical_point_centralizer_eq d c]
    exact (map_mono d.conjugationSection.normalized).trans (le_normalizer_map _)
  have hD : ⁅F.H.pCoreIn 2 ⊓ centralizer (c.Zα : Set G), c.Uα⁆ ≤
      F.H.pCoreIn 2 ⊓ c.Uα := by
    refine le_inf ?_ (le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hAn))
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp ((c.Uα_le_H earlier).trans hQn))
  have hDU : ⁅F.H.pCoreIn 2 ⊓ centralizer (c.Zα : Set G), c.Uα⁆ ≤ F.U :=
    hD.trans ((reverse_core_intersection_of_point_le d hc hs c earlier hUH hm hfull hpoint).le.trans
      inf_le_left)
  exact le_inf (hD.trans inf_le_left) (hDU.trans (le_centralizer _))

/-- The temporary point-containment branch fixes a subspace of codimension
at most one in the exact dual section. Expressing this with a literal relative
index makes the later duality application independent of quotient coordinates. -/
theorem dual_section_fixed_index_le_two_of_point_le (d : Data T L V F W)
    (hc : d.SectionCentralizer) (hs : d.ModuleSeparation)
    (c : CriticalPath (L := L) F) (earlier : c.EarlierImages)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hm : ModuleCalculations d c (c.Uα_le_H earlier))
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hfull : star F c.Uα = star F (Q T L)) (hpoint : F.Vi 1 ≤ c.Uα) :
    (commutatorPreimage (F.H.pCoreIn 2) c.Uα
      (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G))).relIndex (F.H.pCoreIn 2) ≤ 2 := by
  have hZU : c.Zα ≤ F.U :=
    (point_le_core_intersection d hc c hUH).trans
      ((reverse_core_intersection_of_point_le d hc hs c earlier hUH hm hfull hpoint).le.trans
        inf_le_left)
  have hle : F.H.pCoreIn 2 ⊓ centralizer (c.Zα : Set G) ≤
      commutatorPreimage (F.H.pCoreIn 2) c.Uα
        (F.H.pCoreIn 2 ⊓ centralizer (F.U : Set G)) :=
    le_commutatorPreimage inf_le_left
      (dual_section_commutator_bound_of_point_le d hc hs c earlier hUH hm hfull hpoint)
  have hi := relIndex_le_of_le_left (L := F.H.pCoreIn 2) hle index_ne_zero_of_finite
  rw [inf_relIndex_left] at hi
  exact hi.trans (critical_point_centralizer_index_le_two d c hcomm hZU)

end CriticalIntersections
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
