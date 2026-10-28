module
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.QuotientMaps
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections
public import Theory.GroupTheory.CommutatorPreimage
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.QuotientImage.ActionData

/-!
# The centralizer and index obstruction in J.2.4

For h in C_Q(B) outside U, its R₁-centralizer has B-invariant image in
R₁/S. Cubic irreducibility makes this image either zero or the whole
quotient. In the latter case h centralizes R₁ modulo V because h lies in
S and S/V is abelian; J.2.3(8) would then put h in U. Thus C_R₁(h) ≤ S.

If the commutator image in H/Z were trivial, the actual commutator row
would be a homomorphism Q → Z, with kernel of index at most two. That
kernel lies in Q ∩ S, whose index is four, a contradiction. Finally,
changing h by an element of U leaves the quotient row unchanged.

CubicQuotientData is an explicit premise at this helper boundary; its
construction in `QuotientImage.CubicAction` is supplied by the image assembly.
The fixed-subgroup premise is the literal J.2.3(8) conclusion, with
membership in V expressing triviality in the original S/V quotient.

Source: Aschbacher–Smith, Lemma J.2.4(1), printed p.434 (PDF p.445).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.ChapterJ.Fusion
variable {G : Type*} [Group G] [Finite G]

/-- J.2.3(8) and the cubic action put the full R₁-centralizer in S. -/
theorem centralizer_R₁_le_S_of_cubic (d : LocalSetup G)
    (B : Sylow 3 d.toTypeRuSetup.L₁) (cubic : CubicQuotientData d B)
    (hR : d.toTypeRuSetup.R₁ = d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S)
    (hfixed : ∀ s ∈ d.toTypeRuSetup.S,
      (∀ r ∈ d.toTypeRuSetup.R₁, ⁅r,s⁆ ∈ d.V) → s ∈ d.toTypeRuSetup.U)
    (h : G) (hh : h ∈ HB d.toTypeRuSetup B)
    (hhC : h ∈ d.toTypeRuSetup.HC) (hnot : h ∉ d.toTypeRuSetup.U) :
    d.toTypeRuSetup.R₁ ⊓ centralizer ({h} : Set G) ≤ d.toTypeRuSetup.S := by
  let D := d.toTypeRuSetup
  let C := D.R₁ ⊓ centralizer ({h} : Set G)
  have hhS : h ∈ D.S := by
    change h ∈ d.L.pCoreIn 2
    rw [← d.ru1.centralizer_V]
    exact centralizer_le (le_conjugateSpan D.H d.V) hhC.2
  have hLnorm : D.L₁ ≤ normalizer (D.R₁ : Set G) := by
    change D.L₁ ≤ normalizer (((pCore 2 D.L₁).map D.L₁.subtype) : Set G)
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 D.L₁).le_normalizer_map D.L₁.subtype
  have hBR : BSubgroup D B ≤ normalizer (D.R₁ : Set G) := (map_subtype_le _).trans hLnorm
  have hBC : BSubgroup D B ≤ normalizer (C : Set G) := by
    apply le_trans (le_inf hBR ?_) inf_normalizer_le_normalizer_inf
    apply le_trans _ (centralizer ({h} : Set G)).le_normalizer
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (hh.2 b hb)
  rcases cubic.invariant C inf_le_left hBC with hCS | hgen
  · exact hCS
  exfalso
  apply hnot
  apply hfixed h hhS
  have hSR : D.S ≤ D.R₁ := by rw [hR]; exact le_sup_right
  have hRV : D.R₁ ≤ normalizer d.V :=
    (pCoreIn_le 2 D.L₁).trans ((map_subtype_le _).trans (inf_le_left.trans d.ru1.natural.normalized))
  have hSS : ⁅D.S,D.S⁆ = d.V := by
    rw [← d.ru1.derived_eq]
    change ⁅D.S,D.S⁆ = (⁅(⊤ : Subgroup D.S),⊤⁆ : Subgroup D.S).map D.S.subtype
    rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  have hCZ : ⁅C,zpowers h⁆ ≤ d.V := by
    have hcent : zpowers h ≤ centralizer (C : Set G) := by
      apply zpowers_le.mpr
      intro c hc
      exact mem_centralizer_singleton_iff.mp hc.2
    rw [commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcent)]
    exact bot_le
  have hSZ : ⁅D.S,zpowers h⁆ ≤ d.V :=
    (commutator_mono le_rfl (zpowers_le.mpr hhS)).trans hSS.le
  have hpre : D.R₁ ≤ commutatorPreimage D.R₁ (zpowers h) d.V := by
    calc
      D.R₁ = C ⊔ D.S := hgen.symm
      _ ≤ commutatorPreimage D.R₁ (zpowers h) d.V :=
        sup_le (le_commutatorPreimage inf_le_left hCZ) (le_commutatorPreimage hSR hSZ)
  intro r hr
  exact ((commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le D.R₁ (zpowers h) d.V hRV))
    (commutator_mem_commutator hr (mem_zpowers h))

/-- If [h,Q] lies in central Z, its row is an actual homomorphism Q → Z. -/
private def centralRow (d : TypeRuSetup G) (h : G)
    (hbound : ∀ q ∈ d.Q, ⁅h,q⁆ ∈ d.Z) : d.Q →* d.Z where
  toFun q := ⟨⁅h,(q : G)⁆,hbound q q.property⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' q r := by
    apply Subtype.ext
    change ⁅h,(q : G)*(r : G)⁆ = ⁅h,(q : G)⁆ * ⁅h,(r : G)⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hc : ⁅h,(r : G)⁆ * (q : G) = (q : G) * ⁅h,(r : G)⁆ :=
      pCoreIn_le 2 d.H q.property _ (hbound r r.property)
    calc
      _ = ⁅h,(q : G)⁆ * ((q : G) * ⁅h,(r : G)⁆) * (q : G)⁻¹ := by group
      _ = _ := by rw [← hc]; group

/-- The index-four obstruction in J.2.4: central commutators would give
an index at most two, while C_Q(h) lies in Q ∩ S of index four. -/
theorem modZ_commutator_ne_bot_of_index (d : TypeRuSetup G)
    (hZ : Nat.card d.Z = 2) (hQS : d.S.relIndex d.Q = 4)
    (h : d.HC) (hcentralizer : d.Q ⊓ centralizer ({(h : G)} : Set G) ≤ d.S) :
    ⁅zpowers (centerQuotientMap d ⟨h,h.property.1⟩),modZ d d.Q⁆ ≠ ⊥ := by
  intro hbot
  have hbound (q : G) (hq : q ∈ d.Q) : ⁅(h : G),q⁆ ∈ d.Z := by
    have hz : ⁅centerQuotientMap d ⟨h,h.property.1⟩,
        centerQuotientMap d ⟨q,pCoreIn_le 2 d.H hq⟩⁆ = 1 := by
      apply (show ⁅centerQuotientMap d ⟨h,h.property.1⟩,
          centerQuotientMap d ⟨q,pCoreIn_le 2 d.H hq⟩⁆ ∈ (⊥ : Subgroup _) from ?_)
      rw [← hbot]
      exact commutator_mem_commutator (mem_zpowers _)
        (mem_map.mpr ⟨⟨q,pCoreIn_le 2 d.H hq⟩,hq,rfl⟩)
    rw [← map_commutatorElement] at hz
    have hzmem : ⁅(⟨h,h.property.1⟩ : d.H),⟨q,pCoreIn_le 2 d.H hq⟩⁆ ∈
        d.Z.subgroupOf d.H := (QuotientGroup.eq_one_iff _).mp hz
    exact hzmem
  let f := centralRow d h hbound
  have hker : f.ker ≤ d.S.subgroupOf d.Q := by
    intro q hq
    apply hcentralizer
    refine ⟨q.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have hz := congrArg Subtype.val (MonoidHom.mem_ker.mp hq)
    exact (commutatorElement_eq_one_iff_mul_comm.mp hz).symm
  have hindex : 4 ≤ f.ker.index := by
    have hi := index_antitone hker
    change d.S.relIndex d.Q ≤ f.ker.index at hi
    rwa [hQS] at hi
  have hsmall : f.ker.index ≤ 2 := by
    rw [index_ker]
    exact (Nat.card_le_card_of_injective f.range.subtype f.range.subtype_injective).trans_eq hZ
  omega

/-- Changing h by an element of U leaves its literal quotient commutator row unchanged. -/
theorem commutatorRow_mul_U (d : TypeRuSetup G) [IsElementaryAbelian 2 d.U]
    (hUHC : d.U ≤ d.HC) (hCQ : ⁅d.HC,d.Q⁆ ≤ d.U) (hUQ : ⁅d.U,d.Q⁆ ≤ d.Z)
    (h : d.HC) (u : d.U) :
    commutatorRow d hUHC hCQ hUQ
      ⟨(h : G) * u,d.HC.mul_mem h.property (hUHC u.property)⟩ =
      commutatorRow d hUHC hCQ hUQ h := by
  apply MonoidHom.ext
  intro q
  rw [commutatorRow_apply, commutatorRow_apply]
  let hH : d.H := ⟨h,h.property.1⟩
  let uH : d.H := ⟨u,d.ru2.natural.section_le u.property⟩
  let qH : d.H := ⟨q,pCoreIn_le 2 d.H q.property⟩
  change centerQuotientMap d ⁅hH * uH,qH⁆ = centerQuotientMap d ⁅hH,qH⁆
  rw [map_commutatorElement, map_commutatorElement, map_mul,
    commutatorElement_mul_left_eq_conj_mul]
  have hc : ⁅centerQuotientMap d uH,centerQuotientMap d qH⁆ = 1 := by
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact hUQ (commutator_mem_commutator u.property q.property)
  rw [hc, mul_one, mul_inv_cancel, one_mul]

end CFSG.Quasithin.ChapterJ.Fusion
