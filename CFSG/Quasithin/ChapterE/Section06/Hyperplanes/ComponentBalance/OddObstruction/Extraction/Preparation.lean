module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Detection
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Basic
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Canonical residual lifts for the E.6.19 obstruction

The earlier characteristic-two centralizer facts make every nonidentity
z in C_V(T) fixed-point-free on O(C_G(A)). The involution theorem therefore
makes this odd core abelian and proves that z inverts it. Consequently the
actual kernel O(C_G(A)) A is solvable. A quotient component has a unique
C-component lift, explicitly the solvable residual of its full preimage;
the normalizer correspondence retains the actual quotient map.

The final lemma proves the required specialization of Aschbacher 31.14(1)
directly: U centralizes a Sylow two-subgroup of the quotient, hence its
two-core. That core and the odd core of C(U) are normal subgroups of C(U)
of coprime orders, so they commute.

These results do not assert that the residual lift is an ordinary component.
Quotient component extraction, quasisimplicity of the lift, and the odd core
in the induced action centralizer are the remaining E.6.19 obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.19,
printed p.252 (PDF p.263); E.6.6(3), pp.246–247; and the inversion argument
in 1.1.5(2), p.502. The C-component correspondence is A.3.3(4), pp.42–43.
Aschbacher, Finite Group Theory, second edition, 31.14(1), printed p.159.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V A : Subgroup G}

private theorem oddCore_fixedPointFree
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V) (hne : z ≠ 1) :
    let zH : centralizer (A : Set G) := ⟨z, by
      let _ := h.elementary
      exact subspace_le_centralizer hA.1 le_rfl hz.1⟩
    MonoidHom.FixedPointFree
      (MulAut.conjNormal zH : MulAut (pPrimeCore 2 (centralizer (A : Set G)))) := by
  let _ := h.elementary
  let H := centralizer (A : Set G)
  let C := H ⊓ centralizer ({z} : Set G)
  let f : C →* H := inclusion inf_le_left
  let R := (pPrimeCore 2 H).comap f
  have hcop : Nat.Coprime 2 (Nat.card R) :=
    Nat.Coprime.of_dvd_right
      (card_comap_dvd_of_injective (pPrimeCore 2 H) f (inclusion_injective inf_le_left))
      pPrimeCore_coprime_card
  have hR : R ≤ pPrimeCore 2 C := le_sSup ⟨inferInstance, hcop⟩
  have hAC : A ≤ centralizer ({z} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr ((V.le_centralizer hz.1) a (hA.1 ha))
  have hC : HasCharacteristicTwo C := by
    have hc := earlier.centralizers A (centralizer ({z} : Set G))
      (h.centralizer_fixedPoint_characteristicTwo earlier hz hne) hAC
      ((IsElementaryAbelian.isPGroup 2 V).to_le hA.1)
    exact (Theory.Quasithin.centralizer_pCore_le_iff 2
      (MulEquiv.subgroupCongr (inf_comm (centralizer ({z} : Set G)) H))).mp hc
  have hbot : pPrimeCore 2 C = ⊥ := pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hC
  dsimp only
  intro r hr
  apply Subtype.ext
  apply Subtype.ext
  have he : z * ((r : H) : G) * z⁻¹ = ((r : H) : G) :=
    congrArg (fun x : pPrimeCore 2 H => ((x : H) : G)) hr
  have hrC : ((r : H) : G) ∈ C :=
    ⟨(r : H).property, mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp he).symm⟩
  have hrR : (⟨((r : H) : G), hrC⟩ : C) ∈ R := r.property
  exact congrArg (fun x : C => (x : G)) (mem_bot.mp (hbot ▸ hR hrR))

/-- The source odd core is abelian, using the earlier local characteristic-two facts. -/
theorem oddCore_abelian
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V) :
    IsMulCommutative (pPrimeCore 2 (centralizer (A : Set G))) := by
  let _ := h.elementary
  obtain ⟨z, hz, hne⟩ := Components.exists_sylow_fixed h
  let H := centralizer (A : Set G)
  let zH : H := ⟨z, subspace_le_centralizer hA.1 le_rfl hz.1⟩
  let φ : H →* MulAut (pPrimeCore 2 H) := MulAut.conjNormal
  have hfree : MonoidHom.FixedPointFree (φ zH) := oddCore_fixedPointFree h earlier hA hz hne
  have hz2 : zH ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz.1)
  have hi : Function.Involutive (φ zH) := by
    intro r
    change (φ zH * φ zH) r = r
    rw [← map_mul, ← pow_two, hz2, map_one]
    rfl
  exact ⟨⟨fun a b => (hfree.commute_all_of_involutive hi a b).eq⟩⟩

/-- Each nonidentity source fixed involution inverts the actual embedded odd core. -/
theorem oddCore_inverted
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V) (hne : z ≠ 1) :
    ∀ x ∈ oddCentralizer A, z * x * z⁻¹ = x⁻¹ := by
  let _ := h.elementary
  let H := centralizer (A : Set G)
  let zH : H := ⟨z, subspace_le_centralizer hA.1 le_rfl hz.1⟩
  let φ : H →* MulAut (pPrimeCore 2 H) := MulAut.conjNormal
  have hfree : MonoidHom.FixedPointFree (φ zH) := oddCore_fixedPointFree h earlier hA hz hne
  have hz2 : zH ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz.1)
  have hi : Function.Involutive (φ zH) := by
    intro r
    change (φ zH * φ zH) r = r
    rw [← map_mul, ← pow_two, hz2, map_one]
    rfl
  rintro x ⟨r, hr, rfl⟩
  exact congrArg (fun a : pPrimeCore 2 H => ((a : H) : G))
    (congrFun (hfree.coe_eq_inv_of_involutive hi) ⟨r, hr⟩)

/-- Solvability of the genuine quotient kernel, without invoking the odd-order theorem. -/
theorem quotientKernel_solvable
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V) : Group.IsSolvable (quotientKernel A) := by
  let H := centralizer (A : Set G)
  let _ := oddCore_abelian h earlier hA
  let _ : Group.IsSolvable (pPrimeCore 2 H) := Group.isSolvable_of_comm
    (fun a b => mul_comm a b)
  let _ : Group.IsSolvable (A.subgroupOf H) := Group.isSolvable_of_comm (by
    intro a b
    exact Subtype.ext (mem_center_iff.mp (subspace_le_center A a.property) b).symm)
  exact Group.isSolvable_sup_of_normal_left (pPrimeCore 2 H) (A.subgroupOf H)

/-- The full preimage in C_G(A) under its specified quotient map. -/
def componentPreimage (A : Subgroup G) (D : Subgroup (CentralizerQuotient A)) :
     Subgroup (centralizer (A : Set G)) := D.comap (quotientMap A)

/-- The canonical residual lift inside C_G(A), before proving quasisimplicity. -/
def componentLift (A : Subgroup G) (D : Subgroup (CentralizerQuotient A)) :
     Subgroup (centralizer (A : Set G)) :=
  (solvableResidual (componentPreimage A D)).map (componentPreimage A D).subtype

/-- A perfect quotient subgroup is the image of its canonical residual lift. -/
theorem componentLift_image (D : Subgroup (CentralizerQuotient A))
     [Group.IsPerfect D] : (componentLift A D).map (quotientMap A) = D := by
  change ((solvableResidual (D.comap (quotientMap A))).map
     (D.comap (quotientMap A)).subtype).map (quotientMap A) = D
  rw [map_solvableResidual_comap (quotientMap A) (quotientMap_surjective A) D,
     solvableResidual_eq_top, ← MonoidHom.range_eq_map, range_subtype]

/-- A quotient component lifts to a C-component; ordinary component status is separate. -/
theorem componentLift_isCComponent
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V)
    {D : Subgroup (CentralizerQuotient A)} (hD : IsComponent (CentralizerQuotient A) D) :
    (componentLift A D).IsCComponent := by
  let _ := quotientKernel_solvable h earlier hA
  exact hD.isCComponent.solvableResidual_preimage (quotientKernel A)

/-- The exact normalizer correspondence for the canonical lift and quotient map. -/
theorem componentLift_normalizer
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V)
    {D : Subgroup (CentralizerQuotient A)} (hD : IsComponent (CentralizerQuotient A) D) :
    (normalizer (D : Set (CentralizerQuotient A))).comap (quotientMap A) =
      normalizer (componentLift A D : Set (centralizer (A : Set G))) := by
  let _ := quotientKernel_solvable h earlier hA
  let _ := hD.2
  have hl := componentLift_isCComponent h earlier hA hD
  have hn := normalizer_cComponent_quotient hl (quotientKernel A)
  change (normalizer ((componentLift A D).map (quotientMap A) :
     Set (CentralizerQuotient A))).comap (quotientMap A) = _ at hn
  rwa [componentLift_image] at hn

/-- Any C-component with the specified quotient image is the canonical lift. -/
theorem componentLift_unique
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V)
    {D : Subgroup (CentralizerQuotient A)} (hD : IsComponent (CentralizerQuotient A) D)
    {L : Subgroup (centralizer (A : Set G))} (hL : L.IsCComponent)
    (he : L.map (quotientMap A) = D) : L = componentLift A D := by
  let _ := quotientKernel_solvable h earlier hA
  let _ := hD.2
  exact hL.eq_of_map_quotient_eq (componentLift_isCComponent h earlier hA hD)
    (quotientKernel A) (he.trans (componentLift_image D).symm)

/-- Normalization by the actual image of V lifts to normalization inside C_G(A). -/
theorem componentLift_normalized
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hA : A ∈ obstructionFamily M V)
    {D : Subgroup (CentralizerQuotient A)} (hD : IsComponent (CentralizerQuotient A) D)
    (hn : quotientImage A V ≤ normalizer (D : Set (CentralizerQuotient A))) :
    V.subgroupOf (centralizer (A : Set G)) ≤
      normalizer (componentLift A D : Set (centralizer (A : Set G))) := by
  rw [← componentLift_normalizer h earlier hA hD]
  exact map_le_iff_le_comap.mp hn

private theorem oddCentralizer_centralizes_normal_two
    (B P : Subgroup G) [P.Normal] (hp : IsPGroup 2 P)
    (hPB : P ≤ centralizer (B : Set G)) :
    oddCentralizer B ≤ centralizer (P : Set G) := by
  let C := centralizer (B : Set G)
  let P' := P.subgroupOf C
  have hcop : Nat.Coprime (Nat.card P') (Nat.card (pPrimeCore 2 C)) := by
    have hp' : IsPGroup 2 P' := hp.comap_subtype
    obtain ⟨n, hn⟩ := hp'.exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := C)).pow_left n
  have hi : P' ⊓ pPrimeCore 2 C = ⊥ := (disjoint_of_coprime_natCard hcop).eq_bot
  rintro r ⟨r, hr, rfl⟩ p hpP
  have hp' : (⟨p, hPB hpP⟩ : C) ∈ P' := hpP
  have hc := commutator_le_inf (H₁ := P') (H₂ := pPrimeCore 2 C)
    (commutator_mem_commutator hp' hr)
  have hc' := mem_bot.mp (hi ▸ hc)
  exact congrArg Subtype.val (commutatorElement_eq_one_iff_mul_comm.mp hc')

/-- The central-Sylow specialization of Aschbacher 31.14(1) in the E.6.19 quotient. -/
theorem quotient_oddCentralizer_centralizes_twoCore
    (h : HypothesisE61 K T M V) (hA : A ∈ obstructionFamily M V)
    {U : Subgroup G} (hUV : U ≤ V) :
    oddCentralizer (quotientImage A U) ≤
      centralizer (pCore 2 (CentralizerQuotient A) : Set (CentralizerQuotient A)) := by
  obtain ⟨S, _, _, hVS⟩ := quotient_sylow_geometry h hA
  apply oddCentralizer_centralizes_normal_two _ _ pCore_isPGroup
  have hPS : pCore 2 (CentralizerQuotient A) ≤ S := pCore_isPGroup.le_sylow_of_normal S
  apply le_centralizer_iff.mp
  exact ((map_mono (comap_mono hUV)).trans hVS).trans (Subgroup.centralizer_le hPS)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction
