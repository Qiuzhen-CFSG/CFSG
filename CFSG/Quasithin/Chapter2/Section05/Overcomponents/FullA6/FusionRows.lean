module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.BinaryCoverAnalysis
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Five.InvolutionFusion
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms.FieldDescent
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CentralCoreInvolutionSource
/-!
# Fusion eliminates the PSL₅(2) and Sp₄(4) full-A₆ overcomponent rows

In the binary degree-five case, symmetric Gram factorization makes every
outer-involution cocycle a coboundary. In the symplectic field-four case,
finite-field descent gives the same conclusion. Triviality of the two
multipliers transports these identities through the original central
quotient maps to the actual overcomponents.

The source applications retain the original inclusion into C_G(i), its
t-conjugation action, and the central marks t and z_K. Since z_K is a fixed
involution, the intrinsic coboundary supplies ambient fusion t ~ tz_K.
The original crossing equality z = tz_K then contradicts the independently
proved source nonfusion t ≁ z.

Source: Aschbacher–Smith 2.5.19(4), printed pp.561–562, and the source
2.5.11(2) Sylow-centralizer comparison on printed p.557. This implements
the two stated fusion rows without assuming an ambient fusion theorem.
-/

public section
open Subgroup Theory.GroupTheory
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.FusionRows
open CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification
open BinaryLinear.SixSylowActors.Five

private theorem ambient_fusion_of_coboundary {E G : Type*} [Group E] [Group G]
    (a : MulAut E) (f : E →* G) (t : G)
    (hact : ∀ y : E, f (a y) = t * f y * t⁻¹)
    (x w : E) (hx : a x = x) (hw : x = w * (a w)⁻¹) :
    IsConj t (t * f x) := by
  have hcomm : f x * t = t * f x := by
    have he := hact x
    rw [hx] at he
    exact (mul_inv_eq_iff_eq_mul.mp he.symm).symm
  apply isConj_iff.mpr
  refine ⟨f w, ?_⟩
  rw [← hcomm, hw, map_mul, map_inv, hact]
  group

private noncomputable def binaryEquiv {E : Type*} [Group E]
    (hm : ClassicalGroup.IsPSL E 5 2) : E ≃* LinearGroup 5 := Classical.choice <| by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  have hc : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  exact ⟨(e.trans (Atlas.fieldEquivPSL 5 (FiniteField.ringEquivOfCardEq hc))).trans
    (projectiveEquivLinear (by decide))⟩

/-- The actual degree-five central quotient has trivial cocycles for the
involution fixing its specified A₆. The multiplier removes the whole center. -/
theorem binary_quotient_cocycle_coboundary
    {E : Type*} [Group E] [Finite E] [IsQuasisimple E]
    (hm : ClassicalGroup.IsPSL (E ⧸ center E) 5 2)
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup E) (hB : B ≤ a.fixedSubgroup)
    (eB : B ≃* alternatingGroup (Fin 6))
    (x : E) (hx : x * a x = 1) : ∃ w : E, x = w * (a w)⁻¹ := by
  have hz : center E = ⊥ := center_eq_bot_five_of_trivial_multiplier
    Theory.SpecificGroups.PSL5Two.UniversalCover.universalProjection_ker_eq_bot hm
  have hout : a ∉ MulAut.innerSubgroup E := by
    rintro ⟨y, hy⟩
    have hyC : y ∈ centralizer (B : Set E) := by
      intro b hb
      have he : MulAut.conj y b = b := hy.symm ▸ (MulAut.mem_fixedSubgroup a b).mp (hB hb)
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    rw [six_centralizer_eq_center_of_binary_quotient (Or.inr hm) B ⟨eB⟩,
      hz, mem_bot] at hyC
    have ha1 : a = 1 := by simpa only [hyC, map_one] using hy.symm
    simp only [ha1, orderOf_one] at ha
    omega
  let q : E ≃* E ⧸ center E :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm
  let e := q.trans (binaryEquiv hm)
  let b := MulAut.congr e a
  have hb : b ^ 2 = 1 := by
    rw [← map_pow, show a ^ 2 = 1 from ha ▸ pow_orderOf_eq_one a, map_one]
  have hbo : b ∉ MulAut.innerSubgroup (LinearGroup 5) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, hk⟩ := (MulAut.congr_inner_iff e a).mp ⟨y, hy.symm⟩
    exact hout ⟨k, hk.symm⟩
  have he (y : E) : b (e y) = e (a y) := by
    change e (a (e.symm (e y))) = _
    rw [e.symm_apply_apply]
  obtain ⟨w, hw⟩ := binary_cocycle_coboundary b hb hbo (e x) (by
    rw [he, ← map_mul, hx, map_one])
  refine ⟨e.symm w, e.injective ?_⟩
  rw [map_mul, map_inv, ← he, e.apply_symm_apply]
  exact hw

open Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms FieldFixedResidual

/-- Finite-field descent supplies a coboundary in the actual component,
through its specified symplectic quotient and field involution. -/
theorem symplectic_quotient_cocycle_coboundary
    {E F : Type*} [Group E] [Group.IsPerfect E]
    [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (a : MulAut E) (e : (E ⧸ center E) ≃* Sp F)
    (hmark : MulAut.congr e (quotientAut (center E) a) = representative 1)
    (x : E) (hx : x * a x = 1) : ∃ w : E, x = w * (a w)⁻¹ := by
  obtain ⟨f, hf⟩ := CentralCovers.Even.exists_whole_model (n := 2) (by simpa using hF)
    (by decide) e
  have hcompat (y : E) : f (a y) = (representative 1) (f y) := by
    rw [hf, hf]
    have hh := congrArg (fun b : MulAut (Sp F) => b (e (QuotientGroup.mk' (center E) y))) hmark
    change e (quotientAut (center E) a (e.symm (e (QuotientGroup.mk' (center E) y)))) = _ at hh
    rw [e.symm_apply_apply, quotientAut_apply_mk] at hh
    exact hh
  obtain ⟨w, hw⟩ := InvolutionNormalForms.half_frobenius_cocycle_coboundary
    (n := 2) (by simpa using hF) (by decide) (by decide) (f x) (by
      change f x * representative 1 (f x) = 1
      rw [← hcompat, ← map_mul, hx, map_one])
  refine ⟨f.symm w, f.injective ?_⟩
  rw [map_mul, map_inv, hcompat, f.apply_symm_apply]
  exact hw

/-- PSL₅(2) fuses the original actor with its product by any fixed involution. -/
theorem binary_quotient_ambient_fusion
    {E G : Type*} [Group E] [Finite E] [IsQuasisimple E] [Group G]
    (hm : ClassicalGroup.IsPSL (E ⧸ center E) 5 2)
    (a : MulAut E) (ha : orderOf a = 2)
    (B : Subgroup E) (hB : B ≤ a.fixedSubgroup) (eB : B ≃* alternatingGroup (Fin 6))
    (f : E →* G) (t : G) (hact : ∀ y : E, f (a y) = t * f y * t⁻¹)
    (x : E) (hx : a x = x) (hx2 : x ^ 2 = 1) : IsConj t (t * f x) := by
  obtain ⟨w, hw⟩ := binary_quotient_cocycle_coboundary hm a ha B hB eB x
    (by simpa only [hx, ← pow_two] using hx2)
  exact ambient_fusion_of_coboundary a f t hact x w hx hw

/-- The Sp₄(4) field row fuses the original actor with its product by a
fixed involution, in the original ambient group. -/
theorem symplectic_quotient_ambient_fusion
    {E F G : Type*} [Group E] [Group.IsPerfect E] [Group G]
    [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4)
    (a : MulAut E) (e : (E ⧸ center E) ≃* Sp F)
    (hmark : MulAut.congr e (quotientAut (center E) a) = representative 1)
    (f : E →* G) (t : G) (hact : ∀ y : E, f (a y) = t * f y * t⁻¹)
    (x : E) (hx : a x = x) (hx2 : x ^ 2 = 1) : IsConj t (t * f x) := by
  obtain ⟨w, hw⟩ := symplectic_quotient_cocycle_coboundary hF a e hmark x
    (by simpa only [hx, ← pow_two] using hx2)
  exact ambient_fusion_of_coboundary a f t hact x w hx hw


open ComponentRefinement ComponentSelection

private theorem source_mark_in_overcomponent
    {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (t zK : G) (ht : orderOf t = 2) (hzK : orderOf zK = 2)
    (htC : t ∈ twoCore H) (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hzKK : zK ∈ K) (i : G) (X : Subgroup (centralizer ({i} : Set G)))
    (a : MulAut X) (hact : ∀ y : X, ((a y : centralizer ({i} : Set G)) : G) =
      t * (y : G) * t⁻¹)
    (hKX : K ≤ X.map (centralizer ({i} : Set G)).subtype) :
    ∃ x : X, (x : G) = zK ∧ a x = x ∧ x ^ 2 = 1 := by
  obtain ⟨x, hx, he⟩ := hKX hzKK
  let v : X := ⟨x, hx⟩
  have hv : (v : G) = zK := he
  have hCt := (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).1
  have hzt : zK * t = t * zK := mem_centralizer_singleton_iff.mp (hCt (c.component_le hzKK))
  refine ⟨v, hv, ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    rw [hact, hv, ← hzt, mul_inv_cancel_right]
  · apply Subtype.ext
    apply Subtype.ext
    change (v : G) ^ 2 = 1
    rw [hv, ← hzK]
    exact pow_orderOf_eq_one zK

/-- The PSL₅(2) row contradicts the original crossing marks. Ambient
nonfusion comes from source 2.5.11(2), with its own original Sylow subgroup. -/
theorem source_binary_row_false
    {G : Type*} [Group G] [Finite G]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (t zK : G) (ht : orderOf t = 2) (hzK : orderOf zK = 2)
    (htC : t ∈ twoCore H) (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hzKK : zK ∈ K) (hz : z = t * zK)
    (i : G) (X : Subgroup (centralizer ({i} : Set G)))
    (hX : IsComponent (centralizer ({i} : Set G)) X)
    (a : MulAut X) (ha : orderOf a = 2)
    (hact : ∀ y : X, ((a y : centralizer ({i} : Set G)) : G) = t * (y : G) * t⁻¹)
    (B : Subgroup X) (hB : B ≤ a.fixedSubgroup) (eB : B ≃* alternatingGroup (Fin 6))
    (hKX : K ≤ X.map (centralizer ({i} : Set G)).subtype)
    (hm : ClassicalGroup.IsPSL (X ⧸ center X) 5 2) : False := by
  let : IsQuasisimple X := hX.2
  obtain ⟨x, hx, hfix, hx2⟩ := source_mark_in_overcomponent c hgen t zK ht hzK htC htZ
    hzKK i X a hact hKX
  have hf := binary_quotient_ambient_fusion hm a ha B hB eB
    ((centralizer ({i} : Set G)).subtype.comp X.subtype) t hact x hfix hx2
  have hn := (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).2.2.2.2
  apply hn
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, hx, ← hz] using hf

/-- The Sp₄(4) field row contradicts the same original crossing marks. The
actual quotient marking is sufficient; no fusion or fixed-group premise is added. -/
theorem source_symplectic_row_false
    {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (t zK : G) (ht : orderOf t = 2) (hzK : orderOf zK = 2)
    (htC : t ∈ twoCore H) (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hzKK : zK ∈ K) (hz : z = t * zK)
    (i : G) (X : Subgroup (centralizer ({i} : Set G)))
    (hX : IsComponent (centralizer ({i} : Set G)) X)
    (a : MulAut X)
    (hact : ∀ y : X, ((a y : centralizer ({i} : Set G)) : G) = t * (y : G) * t⁻¹)
    (hKX : K ≤ X.map (centralizer ({i} : Set G)).subtype)
    (hF : Nat.card F = 4) (e : (X ⧸ center X) ≃* Sp F)
    (hmark : MulAut.congr e (quotientAut (center X) a) = representative 1) : False := by
  let : IsQuasisimple X := hX.2
  obtain ⟨x, hx, hfix, hx2⟩ := source_mark_in_overcomponent c hgen t zK ht hzK htC htZ
    hzKK i X a hact hKX
  have hf := symplectic_quotient_ambient_fusion hF a e hmark
    ((centralizer ({i} : Set G)).subtype.comp X.subtype) t hact x hfix hx2
  have hn := (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).2.2.2.2
  apply hn
  simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, hx, ← hz] using hf

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.FusionRows
