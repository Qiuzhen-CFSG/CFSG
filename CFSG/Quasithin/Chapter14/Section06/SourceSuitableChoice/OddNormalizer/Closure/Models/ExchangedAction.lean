module
public import Theory.GroupTheory.GeneralizedFitting.SquareWreath
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.Contracts
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.Alternating.FivePairOuterTwo
public import Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder

/-!
# Marked wreath actions for the exchanged closure rows

The actual product of a relative C-component and its inverse conjugate gives
coordinates on the image of K in Mc/O₂(Mc). When that image is F*, conjugation
is faithful. The component outer group is a two-group in each surviving row,
so K and the original Sylow subgroup generate Mc.

The three actions use the concrete A₅, PSL₂(16), and PSL₃(2) carriers; the first
also embeds in the literal S₅ wreath group. Inner-conjugation and coordinate
formulas preserve both original factors and the original exchanger. Full outer
image recognition remains an obligation, not a field of these definitions.
`SourceWreathAction` applies every row to the actual original outside H.

Source: Aschbacher--Smith 14.6.14 and 14.6.16, printed pp.1033,1035.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open AutomorphismSquare WreathTwoElementaryRank Chapter1
variable {G : Type*} [Group G]

/-- A faithful action on the actual closure image, with the original component
and its inverse conjugate marking the two coordinates. This does not assert
that the wreath image is the whole target. -/
def MarkedExchangedWreath (Mc K L : Subgroup G) (s : Mc) (D : Type*) [Group D] : Prop :=
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let A := (L.subgroupOf Mc).map q
  let B := (K.subgroupOf Mc).map q
  ∃ e : A ≃* D, ∃ k : B ≃* D × D,
    (∀ x : A, (k.symm (e x,1) : Mc ⧸ pCore 2 Mc) = x) ∧
    (∀ x : A, (k.symm (1,e x) : Mc ⧸ pCore 2 Mc) = q s⁻¹ * x * (q s⁻¹)⁻¹) ∧
    ∃ ρ : (Mc ⧸ pCore 2 Mc) →*
        RegularWreathProduct (MulAut D) (Multiplicative (ZMod 2)),
      Function.Injective ρ ∧
      (∀ x : B, ρ x = baseHom (MulAut.conj (k x).1, MulAut.conj (k x).2)) ∧
      ∀ g (x : B), (k.symm (wreathHom (ρ g) (k x)) : Mc ⧸ pCore 2 Mc) =
        g * x * g⁻¹

variable [Finite G]

/-- The original product and its full layer give the marked faithful action,
and the two-group outer action proves Mc = K T. -/
theorem exchanged_closure_wreath_action
    {T Mc K L : Subgroup G} (hTMc : T ≤ Mc) (hLMc : L ≤ Mc)
    (hL : (L.subgroupOf Mc).IsCComponent) (hSyl : IsSylowIn 2 T Mc)
    (hex : ∃ s ∈ T, s ∉ normalizer (L : Set G) ∧
      (K : Set G) = (L : Set G) * (L.map (MulAut.conj s⁻¹).toMonoidHom : Set G))
    (hlayer : StrictClosureLayer Mc K)
    {D : Type*} [Group D] [Finite D] [IsQuasisimple D]
    (e : (L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) ≃* D)
    (hz : center D = ⊥) (ho : IsPGroup 2 (MulAut.Outer D)) :
    Mc = K ⊔ T ∧ ∃ s : Mc, (s : G) ∈ T ∧ (s : G) ∉ normalizer (L : Set G) ∧
      (K : Set G) = (L : Set G) *
        (L.map (MulAut.conj (s : G)⁻¹).toMonoidHom : Set G) ∧
      MarkedExchangedWreath Mc K L s D := by
  obtain ⟨s,hs,hsn,hprod⟩ := hex
  let t : Mc := ⟨s,hTMc hs⟩
  have ht : t⁻¹ ∉ normalizer (L.subgroupOf Mc : Set Mc) := by
    rw [←subgroupOf_normalizer_eq hLMc]
    exact fun hh => hsn (by simpa [t] using (normalizer (L : Set G)).inv_mem hh)
  have hc : ((L.subgroupOf Mc).conjBy t⁻¹).map Mc.subtype =
      L.map (MulAut.conj s⁻¹).toMonoidHom := by
    change ((L.subgroupOf Mc).map (MulAut.conj t⁻¹).toMonoidHom).map Mc.subtype = _
    rw [map_map]
    have he : Mc.subtype.comp (MulAut.conj t⁻¹).toMonoidHom =
        (MulAut.conj s⁻¹).toMonoidHom.comp Mc.subtype := by ext; rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hLMc]
  have hjoin : K = L ⊔ L.map (MulAut.conj s⁻¹).toMonoidHom := by
    apply le_antisymm
    · intro x hx
      change x ∈ (K : Set G) at hx
      rw [hprod] at hx
      obtain ⟨a,ha,b,hb,rfl⟩ := hx
      exact mul_mem_sup ha hb
    · apply sup_le
      · intro x hx
        rw [show x ∈ K ↔ x ∈ (K : Set G) from Iff.rfl,hprod]
        exact ⟨x,hx,1,one_mem _,mul_one x⟩
      · intro x hx
        rw [show x ∈ K ↔ x ∈ (K : Set G) from Iff.rfl,hprod]
        exact ⟨1,one_mem _,x,hx,one_mul x⟩
  have hm : (L.subgroupOf Mc ⊔ (L.subgroupOf Mc).conjBy t⁻¹).map Mc.subtype = K := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hLMc,hc,←hjoin]
  have hKMc : K ≤ Mc := hm ▸ map_subtype_le _
  have hpair : K.subgroupOf Mc = L.subgroupOf Mc ⊔ (L.subgroupOf Mc).conjBy t⁻¹ := by
    apply map_injective Mc.subtype_injective
    rw [map_subgroupOf_eq_of_le hKMc,hm]
  obtain ⟨P,hP⟩ := hSyl
  obtain ⟨hgen,ha⟩ := exchanged_cComponent_layer_action (L.subgroupOf Mc) hL t⁻¹ ht e hz ho
    (by rw [←hpair]; exact hlayer.image_eq_generalizedFitting) P
  have hgen' : K.subgroupOf Mc ⊔ (P : Subgroup Mc) = ⊤ := by rwa [←hpair] at hgen
  have hgenG := congrArg (map Mc.subtype) hgen'
  refine ⟨?_,t,hs,hsn,hprod,e,?_⟩
  · simpa only [Subgroup.map_sup,map_subgroupOf_eq_of_le hKMc,hP,
      ←MonoidHom.range_eq_map,range_subtype] using hgenG.symm
  · rw [hpair]
    exact ha

/-- Normalize the binary component field to the canonical Galois-field carrier. -/
theorem binary_component_equiv {A : Type*} [Group A] {m : ℕ}
    (h : ClassicalGroup.IsPSL A 2 (2 ^ m)) :
    Nonempty (A ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let := ZMod.algebra F 2
  exact ⟨e.trans (Atlas.fieldEquivPSL 2 (GaloisField.algEquivGaloisField 2 m hF).toRingEquiv)⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer

namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Subgroup Theory.GroupTheory
open Chapter1 Chapter1.XiEmbedding
open AutomorphismSquare WreathTwoElementaryRank
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]
local notation "A5" => alternatingGroup (Fin 5)
local notation "L16" => Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 4)
local notation "L3" => Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)

/-- The three surviving component rows, with a faithful marked action on the
same Mc/O₂(Mc). The outer image still has to be determined. -/
def ExchangedWreathRows (T Mc K L : Subgroup G) (p : ℕ) : Prop :=
  ∃ s : Mc, (s : G) ∈ T ∧ (s : G) ∉ normalizer (L : Set G) ∧
    (K : Set G) = (L : Set G) *
      (L.map (MulAut.conj (s : G)⁻¹).toMonoidHom : Set G) ∧
    ((p = 3 ∧ MarkedExchangedWreath Mc K L s A5) ∨
      (p = 5 ∧ MarkedExchangedWreath Mc K L s L16) ∨
      (p = 3 ∧ MarkedExchangedWreath Mc K L s L3))

/-- All three source rows give the marked faithful action and Mc = K T.
The component equivalences and outer two-group facts are proved here. -/
theorem exchanged_closure_wreath_rows
    {T Mc K L : Subgroup G} {p : ℕ} (hTMc : T ≤ Mc) (hLMc : L ≤ Mc)
    (hL : (L.subgroupOf Mc).IsCComponent) (hq : IsQuasisimple (XiQuotient L))
    (hSyl : IsSylowIn 2 T Mc)
    (hex : ∃ s ∈ T, s ∉ normalizer (L : Set G) ∧
      (K : Set G) = (L : Set G) * (L.map (MulAut.conj s⁻¹).toMonoidHom : Set G))
    (hlayer : StrictClosureLayer Mc K)
    (hmodels : (p = 3 ∧ ClassicalGroup.IsPSL
        ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 4) ∨
      (p = 5 ∧ ClassicalGroup.IsPSL
        ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 2 16) ∨
      (p = 3 ∧ ClassicalGroup.IsPSL
        ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 3 2)) :
    Mc = K ⊔ T ∧ ExchangedWreathRows T Mc K L p := by
  let A := (L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))
  let ec : XiQuotient L ≃* A :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLMc)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hLMc))).symm.trans
        (cComponentTwoCoreQuotientEquiv hL)
  let := hq
  rcases hmodels with ⟨hp,hm⟩ | ⟨hp,hm⟩ | ⟨hp,hm⟩
  · obtain ⟨eb⟩ := binary_component_equiv (m := 2) hm
    let e : A ≃* A5 := eb.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5
    let : IsQuasisimple A5 := IsQuasisimple.of_mulEquiv (ec.trans e)
    obtain ⟨hgen,s,hs,hsn,hprod,ha⟩ := exchanged_closure_wreath_action
      hTMc hLMc hL hSyl hex hlayer e (alternatingGroup.center_eq_bot (by simp))
      Theory.AlternatingFive.outer_isPGroup_two
    exact ⟨hgen,s,hs,hsn,hprod,Or.inl ⟨hp,ha⟩⟩
  · obtain ⟨e⟩ := binary_component_equiv (m := 4) hm
    let : IsQuasisimple L16 := IsQuasisimple.of_mulEquiv (ec.trans e)
    have ho : IsPGroup 2 (MulAut.Outer L16) := by
      apply IsPGroup.of_card (n := 2)
      exact Theory.PSL2.outer_card_eq_field_degree (GaloisField 2 4)
        (GaloisField.card 2 4 (by decide))
    obtain ⟨hgen,s,hs,hsn,hprod,ha⟩ := exchanged_closure_wreath_action
      hTMc hLMc hL hSyl hex hlayer e (GorensteinWalter.psl2_center_eq_bot _) ho
    exact ⟨hgen,s,hs,hsn,hprod,Or.inr (Or.inl ⟨hp,ha⟩)⟩
  · obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
    let : Fintype F := Fintype.ofFinite F
    let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
    let e : A ≃* L3 := eF.trans (Atlas.fieldEquivPSL 3 ef)
    let : IsQuasisimple L3 := IsQuasisimple.of_mulEquiv (ec.trans e)
    have ho : IsPGroup 2 (MulAut.Outer L3) :=
      Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv
        (MulAut.outerCongr Matrix.PSL3Two.equiv)
    obtain ⟨hgen,s,hs,hsn,hprod,ha⟩ := exchanged_closure_wreath_action
      hTMc hLMc hL hSyl hex hlayer e Matrix.PSL3Two.Automorphisms.center_psl_eq_bot ho
    exact ⟨hgen,s,hs,hsn,hprod,Or.inr (Or.inr ⟨hp,ha⟩)⟩

omit [Finite G] in
/-- In the PSL₂(4) row the faithful action lands in the literal S₅ wreath
carrier appearing in 14.6.14. Surjectivity is still a separate obligation. -/
theorem marked_four_wreath_embedding {Mc K L : Subgroup G} {s : Mc}
    (h : MarkedExchangedWreath Mc K L s A5) :
    ∃ ρ : (Mc ⧸ pCore 2 Mc) →*
        RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)),
      Function.Injective ρ := by
  obtain ⟨_,_,_,_,ρ,hi,_,_⟩ := h
  let e := RegularWreathProduct.congr
    Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.factorEquiv.symm
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  exact ⟨e.toMonoidHom.comp ρ,e.injective.comp hi⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
