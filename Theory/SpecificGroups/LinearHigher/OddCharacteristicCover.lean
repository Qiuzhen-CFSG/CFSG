module

public import Theory.SpecificGroups.LinearHigher.OddCharacteristicCover.RootLifts
public import Theory.SpecificGroups.LinearHigher.PresentationFaithfulness
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws

/-!
# Odd central covers of PSL₄ over a field of prime order

The coherent root lifts satisfy the actual degree-four Steinberg presentation.
Its established matrix faithfulness gives an SL₄ homomorphism into the cover;
perfectness makes this homomorphism surjective. Field transport retains the
literal quotient projection, including when the defining prime divides the
central kernel. No coprimality to the defining characteristic is assumed.

This is the scalar-cover input for the odd linear Case II of
Aschbacher–Smith, §A.2, after the source reduction to degree four and prime fields.
Presentation source: Steinberg, *Lectures on Chevalley Groups*, §6, Theorems 8–9.
-/

open scoped MatrixGroups
namespace Theory.SpecificGroups.LinearHigher.OddCharacteristicCover
open Subgroup
variable {E : Type*} [Group E] [Group.IsPerfect E]

public theorem exists_covering_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (f : E →* PSL(4,ZMod p)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hcop : (Nat.card f.ker).Coprime 2) :
    ∃ s : SL(4,ZMod p) →* E, Function.Surjective s ∧
      f.comp s=QuotientGroup.mk' (center SL(4,ZMod p)) ∧ s.ker ≤ center SL(4,ZMod p) := by
  let e : SteinbergGroup 4 (ZMod p) ≃* SL(4,ZMod p) :=
    MulEquiv.ofBijective matrixMap ⟨matrixMap_four_injective,matrixMap_surjective (by decide)⟩
  let s := (lift (rootLift_relations f hf hc hcop hp2)).comp e.symm.toMonoidHom
  have hlift : f.comp (lift (rootLift_relations f hf hc hcop hp2))=projectiveMap := by
    apply PresentedGroup.ext
    rintro ⟨r,a⟩
    change f (lift _ (generator r a))=projectiveMap (generator r a)
    rw [lift_generator,rootLift_map,projectiveMap_generator]
  have hfac : f.comp s=QuotientGroup.mk' (center SL(4,ZMod p)) := by
    ext g
    change f (lift (rootLift_relations f hf hc hcop hp2) (e.symm g))=QuotientGroup.mk g
    rw [← MonoidHom.comp_apply,hlift,projectiveMap_eq]
    change QuotientGroup.mk (e (e.symm g))=QuotientGroup.mk g
    rw [e.apply_symm_apply]
  have hs : Function.Surjective s :=
    PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      f s (by rw [hfac]; exact QuotientGroup.mk'_surjective _) hc
  refine ⟨s,hs,hfac,?_⟩
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  have hh := DFunLike.congr_fun hfac x
  rw [MonoidHom.comp_apply,show s x=1 from hx,map_one] at hh
  exact hh.symm

public theorem exists_covering_of_card_prime {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F=p)
    (f : E →* PSL(4,F)) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (ho : Odd (Nat.card f.ker)) :
    ∃ s : SL(4,F) →* E, Function.Surjective s ∧
      f.comp s=QuotientGroup.mk' (center SL(4,F)) ∧ s.ker ≤ center SL(4,F) := by
  let : Fact p.Prime := ⟨hp⟩
  let := Fintype.ofFinite F
  let e : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let L := Atlas.fieldEquivSL 4 e
  let Q := Atlas.fieldEquivPSL 4 e
  let f₀ := Q.toMonoidHom.comp f
  have hker : f₀.ker=f.ker := MonoidHom.ker_comp_of_injective _ _ Q.injective
  obtain ⟨s₀,hs₀,he₀,_⟩ := exists_covering_prime hp2 f₀ (Q.surjective.comp hf)
    (hker ▸ hc) (by rw [hker]; exact Nat.coprime_two_right.mpr ho)
  let s : SL(4,F) →* E := s₀.comp L.toMonoidHom
  have he : f.comp s=QuotientGroup.mk' (center SL(4,F)) := by
    ext g
    apply Q.injective
    change f₀ (s₀ (L g))=Q (QuotientGroup.mk' _ g)
    rw [show f₀ (s₀ (L g))=QuotientGroup.mk' _ (L g) from DFunLike.congr_fun he₀ (L g)]
    exact (Atlas.fieldEquivPSL_mk 4 e g).symm
  refine ⟨s,hs₀.comp L.surjective,he,?_⟩
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  have hh := DFunLike.congr_fun he x
  rw [MonoidHom.comp_apply,show s x=1 from hx,map_one] at hh
  exact hh.symm

end Theory.SpecificGroups.LinearHigher.OddCharacteristicCover