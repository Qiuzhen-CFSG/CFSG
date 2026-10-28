module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.CommonBorelConstruction
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.SpecifiedEndpointMarking
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.WholeIntersection
public import Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive.PrescribedCubic
public import Theory.GroupTheory.PrimeOrderLift

/-!
# Actual natural endpoints containing the same whole Borel

The first marked natural embedding contains the literal opposite radical
image and its canonical cubic. The reverse radical pair gives the second
quotient geometry. A natural embedding containing that same actual cubic
then constructs the second endpoint. Their common order192 subgroup is
proved to be the whole intersection in the original group.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
open Theory.SpecificGroups.SymplecticFour
open Representation.SL2FourNatural.BorelFactors
local notation "SL" => Representation.SL2FourNatural.SL
local notation "FVec" => Representation.SL2FourNatural.V
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem reverse_conjugate (A : Subgroup G) (p : G) :
    (A.map (MulAut.conj p).toMonoidHom).map (MulAut.conj p⁻¹).toMonoidHom = A := by
  rw [Subgroup.map_map]
  have he : (MulAut.conj p⁻¹).toMonoidHom.comp (MulAut.conj p).toMonoidHom = MonoidHom.id G := by
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv, MonoidHom.id_apply]
    group
  rw [he, Subgroup.map_id]

/-- Concrete subgroup, complement, quotient, and action data for one
natural endpoint inside the unchanged ambient group. -/
structure NaturalEndpointData (A : Subgroup G) [IsElementaryAbelian 2 A] where
  carrier : Subgroup G
  complement : Subgroup G
  kernel_le : A ≤ carrier
  normalizes : carrier ≤ normalizer (A : Set G)
  complement_le : complement ≤ carrier
  carrier_card : Nat.card carrier = 960
  complement_card : Nat.card complement = 60
  inf_complement : A ⊓ complement = ⊥
  sup_complement : A ⊔ complement = carrier
  quotient : carrier →* SL
  quotient_surjective : Function.Surjective quotient
  quotient_kernel : quotient.ker = A.subgroupOf carrier
  coordinates : A ≃* Multiplicative FVec
  action : ∀ (g : carrier) (a : A),
    coordinates (A.normalizerMonoidHom (inclusion normalizes g) a) =
      Multiplicative.ofAdd (Representation.SL2FourNatural.action (quotient g) (coordinates a).toAdd)
  is_complement : (A.subgroupOf carrier).IsComplement' (complement.subgroupOf carrier)
  complement_equiv : complement ≃* SL
  complement_marking : ∀ g : complement, complement_equiv g = quotient (inclusion complement_le g)
  binary_coordinates : Additive A ≃ₗ[ZMod 2] Matrix.PSp4Three.Vector 2 (ZMod 2)
  symplectic_quotient : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
    Matrix.PSp4Three.Sp 2 (ZMod 2)
  symplectic_action : ∀ (g : normalizer (A : Set G)) (x : A),
    (symplectic_quotient (QuotientGroup.mk g)).val *ᵥ binary_coordinates (Additive.ofMul x) =
      binary_coordinates (Additive.ofMul (A.normalizerMonoidHom g x))
  field_coordinates : FVec ≃ₗ[ZMod 2] Matrix.PSp4Three.Vector 2 (ZMod 2)
  embedding : SL →* Matrix.PSp4Three.Sp 2 (ZMod 2)
  embedding_injective : Function.Injective embedding
  embedding_action : ∀ g w, (embedding g).val *ᵥ field_coordinates w =
    field_coordinates (Representation.SL2FourNatural.action g w)
  preimage : carrier = (embedding.range.comap (symplectic_quotient.toMonoidHom.comp
    (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G)))))).map (normalizer (A : Set G)).subtype
  quotient_marking : ∀ g : carrier, embedding (quotient g) =
    symplectic_quotient (QuotientGroup.mk (inclusion normalizes g))
  coordinate_marking : ∀ a : A, (coordinates a).toAdd =
    field_coordinates.symm (binary_coordinates (Additive.ofMul a))

omit [Finite G] in
private theorem opposite_image_normalized
    (A B : Subgroup G) (hAB : A ≤ normalizer (B : Set G))
    (q : normalizer (B : Set G) →* Matrix.PSp4Three.Sp 2 (ZMod 2))
    (t : G) (htA : t ∈ normalizer (A : Set G)) (htB : t ∈ normalizer (B : Set G)) :
    q ⟨t, htB⟩ ∈ normalizer ((q.comp (inclusion hAB)).range : Set (Matrix.PSp4Three.Sp 2 (ZMod 2))) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro r ⟨y, ⟨a, rfl⟩, rfl⟩
    have ha : t * (a : G) * t⁻¹ ∈ A := (mem_normalizer_iff.mp htA a).mp a.property
    refine ⟨⟨t * (a : G) * t⁻¹, ha⟩, ?_⟩
    change q (inclusion hAB ⟨t * (a : G) * t⁻¹, ha⟩) = q ⟨t, htB⟩ * q (inclusion hAB a) * (q ⟨t, htB⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
  · exact (card_map_of_injective (MulAut.conj (q ⟨t, htB⟩)).injective).ge

private theorem endpoint_containing
    (A B : Subgroup G) [IsElementaryAbelian 2 A] (hA16 : Nat.card A = 16)
    (hBA : B ≤ normalizer (A : Set G))
    (e : Additive A ≃ₗ[ZMod 2] Matrix.PSp4Three.Vector 2 (ZMod 2))
    (φ : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
      Matrix.PSp4Three.Sp 2 (ZMod 2))
    (hφ : ∀ (g : normalizer (A : Set G)) (x : A),
      (φ (QuotientGroup.mk g)).val *ᵥ e (Additive.ofMul x) =
        e (Additive.ofMul (A.normalizerMonoidHom g x)))
    (v : FVec ≃ₗ[ZMod 2] Matrix.PSp4Three.Vector 2 (ZMod 2))
    (ι : SL →* Matrix.PSp4Three.Sp 2 (ZMod 2)) (hι : Function.Injective ι)
    (hv : ∀ g w, (ι g).val *ᵥ v w = v (Representation.SL2FourNatural.action g w))
    (hR : U0.map ι = ((φ.toMonoidHom.comp (QuotientGroup.mk'
      (A.subgroupOf (normalizer (A : Set G))))).comp (inclusion hBA)).range)
    (t : normalizer (A : Set G)) (ht : φ (QuotientGroup.mk t) ∈ ι.range) :
    ∃ d : NaturalEndpointData A, B ≤ d.carrier ∧ (t : G) ∈ d.carrier ∧
      d.binary_coordinates = e ∧ d.symplectic_quotient = φ ∧
      d.field_coordinates = v ∧ d.embedding = ι := by
  obtain ⟨P,K,hAP,hPN,hKP,hPe,hP960,hK60,hAK,hjoin,q,hq,hk,c,hqm,hcm,hc,hcomp,k,hkm⟩ :=
    exists_exactly_marked_natural_endpoint A hA16 e φ hφ v ι hι hv
  let d : NaturalEndpointData A := {
    carrier := P
    complement := K
    kernel_le := hAP
    normalizes := hPN
    complement_le := hKP
    carrier_card := hP960
    complement_card := hK60
    inf_complement := hAK
    sup_complement := hjoin
    quotient := q
    quotient_surjective := hq
    quotient_kernel := hk
    coordinates := c
    action := hc
    is_complement := hcomp
    complement_equiv := k
    complement_marking := hkm
    binary_coordinates := e
    symplectic_quotient := φ
    symplectic_action := hφ
    field_coordinates := v
    embedding := ι
    embedding_injective := hι
    embedding_action := hv
    preimage := hPe
    quotient_marking := hqm
    coordinate_marking := hcm }
  have hBP : B ≤ P := by
    intro b hb
    rw [hPe]
    refine ⟨⟨b,hBA hb⟩, ?_, rfl⟩
    change φ (QuotientGroup.mk (⟨b,hBA hb⟩ : normalizer (A : Set G))) ∈ ι.range
    have hr : φ (QuotientGroup.mk (⟨b,hBA hb⟩ : normalizer (A : Set G))) ∈ U0.map ι := by
      rw [hR]
      exact ⟨⟨b,hb⟩,rfl⟩
    exact (map_le_range _ _) hr
  have htP : (t : G) ∈ P := by
    rw [hPe]
    exact ⟨t,ht,rfl⟩
  exact ⟨d,hBP,htP,rfl,rfl,rfl,rfl⟩

/-- Original HS data construct two literal split natural endpoints whose
whole intersection is the same actual order192 Borel. Both quotient actions,
complements and symplectic embeddings remain marked in the original group. -/
theorem TypeAt.exists_paired_natural_endpoints (h : TypeAt z V) :
    ∃ (W A B : Subgroup G) (p t : G) (hAE : IsElementaryAbelian 2 A)
      (hBE : IsElementaryAbelian 2 B)
      (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G)),
      letI := hAE
      letI := hBE
      W ≤ V ∧ Nat.card W = 4 ∧ Nat.card A = 16 ∧ Nat.card B = 16 ∧
      p ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ p ^ 2 ∉ W ∧
      B = A.map (MulAut.conj p).toMonoidHom ∧
      A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      B ⊓ (normalizer (V : Set G)).pCoreIn 2 = W ∧
      centralizer (A : Set G) = A ∧ centralizer (B : Set G) = B ∧
      A ⊓ B = W ∧ ⁅A, B⁆ ≤ W ∧ Nat.card (A ⊔ B : Subgroup G) = 64 ∧
      A ⊔ B ≤ centralizer (W : Set G) ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧ (∀ x ∈ B, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ A, x ≠ 1 → Nat.card (A ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      (∀ x ∈ B, x ≠ 1 → Nat.card (B ⊓ (involutionCentralizer x).pCoreIn 2 : Subgroup G) = 8) ∧
      orderOf t = 3 ∧ t ∈ normalizer (W : Set G) ∧
      Disjoint (A ⊔ B) (zpowers t) ∧
      Nat.card ((A ⊔ B) ⊔ zpowers t : Subgroup G) = 192 ∧
      ∃ (dA : NaturalEndpointData A) (dB : NaturalEndpointData B),
        B ≤ dA.carrier ∧ A ≤ dB.carrier ∧ t ∈ dA.carrier ⊓ dB.carrier ∧
        dA.carrier ⊓ dB.carrier = (A ⊔ B) ⊔ zpowers t ∧
        U0.map dA.embedding = ((dA.symplectic_quotient.toMonoidHom.comp
          (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))).comp (inclusion hBA)).range ∧
        U0.map dB.embedding = ((dB.symplectic_quotient.toMonoidHom.comp
          (QuotientGroup.mk' (B.subgroupOf (normalizer (B : Set G))))).comp (inclusion hAB)).range := by
  obtain ⟨W,A,B,p,hAE,hBE,hAB,hBA,hWV,hW4,hA16,hB16,hp,hpW,hB,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,_,e,φ,hφ,v,ι,hι,hv,hR,_,
    t,ht3,htφ,htB,htW,hdis,_,h192⟩ := h.exists_marked_common_borel
  let := hAE
  let := hBE
  have hWA : W ≤ A := hi ▸ (show A ⊓ B ≤ A from inf_le_left)
  have hWB : W ≤ B := hi ▸ (show A ⊓ B ≤ B from inf_le_right)
  have hAC : A ≤ centralizer (W : Set G) := le_sup_left.trans hC
  have hBC : B ≤ centralizer (W : Set G) := le_sup_right.trans hC
  have htι : φ (QuotientGroup.mk t) ∈ ι.range := by rw [htφ]; exact ⟨_,rfl⟩
  obtain ⟨dA,hBdA,htdA,_,hφA,_,hιA⟩ := endpoint_containing A B hA16 hBA e φ hφ v ι hι hv hR t htι
  have hpInv : p⁻¹ ∈ (normalizer (V : Set G)).pCoreIn 2 := inv_mem hp
  have hpInvW : (p⁻¹) ^ 2 ∉ W := by rwa [inv_pow, W.inv_mem_iff]
  have hrev : A = B.map (MulAut.conj p⁻¹).toMonoidHom := by
    rw [hB, reverse_conjugate]
  have hfixedB : ∀ a ∈ A, a ∉ W → B ⊓ involutionCentralizer a = W := by
    intro a ha haW
    exact h.paired_plane_radical_centralizer W B hWV hW4 hWB hBC hBP p⁻¹ hpInv hpInvW a
      (hrev ▸ ha) haW
  obtain ⟨β₂,_,_,_,e₂,φ₂,hφ₂,himage₂⟩ := h.paired_radical_symplectic_image B A W
    hB16 hCB hpureB hpointsB hA16 hW4 hWB hAB ((inf_comm B A).trans hi) (by rwa [commutator_comm]) hfixedB
  let q₂ := φ₂.toMonoidHom.comp (QuotientGroup.mk' (B.subgroupOf (normalizer (B : Set G))))
  let R₂ := (q₂.comp (inclusion hAB)).range
  let W₂ := (((W.subgroupOf B).toAddSubgroup.toZModSubmodule 2).map e₂.toLinearMap)
  change Nat.card R₂ = 4 ∧ Module.finrank (ZMod 2) W₂ = 2 ∧
    (∀ x ∈ W₂, ∀ y ∈ W₂, form (ZMod 2) x y = 0) ∧
    (∀ r ∈ R₂, r ≠ 1 → ∀ w : Vector (ZMod 2), r • w = w ↔ w ∈ W₂) at himage₂
  let t₂ : normalizer (B : Set G) := ⟨t,htB⟩
  have ht₂3 : orderOf t₂ = 3 := (orderOf_coe t₂).symm.trans ht3
  have hq₂ker : q₂.ker = B.subgroupOf (normalizer (B : Set G)) := by
    ext g
    change φ₂ (QuotientGroup.mk g) = 1 ↔ (g : G) ∈ B
    rw [φ₂.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff g
  have hq₂p : IsPGroup 2 q₂.ker := by
    rw [hq₂ker]
    exact (IsElementaryAbelian.isPGroup (p := 2) (G := B)).of_surjective
      (subgroupOfEquivOfLe B.le_normalizer).symm.toMonoidHom
      (subgroupOfEquivOfLe B.le_normalizer).symm.surjective
  have hτ₂3 : orderOf (q₂ t₂) = 3 :=
    (q₂.orderOf_map_eq_of_coprime_of_isPGroup_ker hq₂p t₂ (by rw [ht₂3]; decide)).trans ht₂3
  have hτ₂R : q₂ t₂ ∈ normalizer (R₂ : Set (Matrix.PSp4Three.Sp 2 (ZMod 2))) :=
    opposite_image_normalized A B hAB q₂ t t.property htB
  obtain ⟨v₂,ι₂,hι₂,hv₂,hR₂,_,htι₂⟩ :=
    Theory.SpecificGroups.SymplecticFour.Binary.MarkedAlternatingFive.exists_marked_embedding_containing_cubic
      R₂ W₂ himage₂.1 himage₂.2.1 himage₂.2.2.1 himage₂.2.2.2 (q₂ t₂) hτ₂3 hτ₂R
  obtain ⟨dB,hAdB,htdB,_,hφB,_,hιB⟩ := endpoint_containing B A hB16 hAB
    e₂.toLinearEquiv φ₂ hφ₂ v₂ ι₂ hι₂ hv₂ hR₂ t₂ htι₂
  have hJle : (A ⊔ B) ⊔ zpowers (t : G) ≤ dA.carrier ⊓ dB.carrier :=
    sup_le (sup_le (le_inf dA.kernel_le hAdB) (le_inf hBdA dB.kernel_le))
      (zpowers_le.mpr ⟨htdA,htdB⟩)
  have hinter := h.paired_endpoint_whole_intersection W A hWV hW4 hA16 hWA hAC hAP p hp hpW
    dA.carrier dB.carrier ((A ⊔ B) ⊔ zpowers (t : G)) dA.normalizes
    (hB ▸ dB.normalizes) dA.carrier_card hJle h192
  refine ⟨W,A,B,p,t,hAE,hBE,hAB,hBA,hWV,hW4,hA16,hB16,hp,hpW,hB,hAP,hBP,hCA,hCB,
    hi,hcomm,h64,hC,hpureA,hpureB,hpointsA,hpointsB,ht3,htW,hdis,h192,dA,dB,
    hBdA,hAdB,⟨htdA,htdB⟩,hinter,?_,?_⟩
  · simpa only [hφA,hιA] using hR
  · simpa only [hφB,hιB] using hR₂

end CFSG.Quasithin.HigmanSims
