module
public import Theory.GroupTheory.CentralTwoQuotientOddCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Odd-core exclusion in central quotient centralizers

Suppose every odd subgroup normalized by E is trivial. Through a central
two-kernel, a quotient centralizer containing the image of E has trivial
odd core. The proof first kills the odd core of the inverse image, then
uses central two-quotient odd-core descent and the literal quotient map.

Source application: Parrott (1972), printed p.683. This is the inverse-image
odd-complement argument and makes no solvability assumption on the ambient
group or the involution centralizer.
-/

open Subgroup
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G]

public theorem quotient_centralizer_oddCore_eq_bot
    (f : G →* H) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (hkp : IsPGroup 2 f.ker)
    (E : Subgroup G)
    (hodd : ∀ O : Subgroup G, Odd (Nat.card O) → E ≤ normalizer (O : Set G) → O = ⊥)
    (k : H) (hEc : E.map f ≤ centralizer ({k} : Set H)) :
    pPrimeCore 2 (centralizer ({k} : Set H)) = ⊥ := by
  let C := centralizer ({k} : Set H)
  let D := C.comap f
  let O := (pPrimeCore 2 D).map D.subtype
  have hED : E ≤ D := fun x hx => hEc (mem_map_of_mem f hx)
  have hEO : E ≤ normalizer (O : Set G) :=
    hED.trans ((le_normalizer : D ≤ normalizer (D : Set G)).trans
      (normalizer_le_normalizer_characteristic_image D (pPrimeCore 2 D)))
  have hOb : O = ⊥ := hodd O
    (by rw [card_map_of_injective D.subtype_injective]; exact Nat.coprime_two_left.mp pPrimeCore_coprime_card) hEO
  have hcore : pPrimeCore 2 D = ⊥ := map_injective D.subtype_injective (by simpa using hOb)
  let q : D →* C := (f.comp D.subtype).codRestrict C (fun x => x.property)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨g, hg⟩ := hf x
    exact ⟨⟨g, show f g ∈ C from hg ▸ x.property⟩, Subtype.ext hg⟩
  have hqk : q.ker ≤ center D := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hxk : (x : G) ∈ f.ker := congrArg C.subtype (show q x = 1 from hx)
    exact mem_center_iff.mp (hk hxk) y
  have hqp : IsPGroup 2 q.ker := by
    let j : q.ker →* f.ker := (D.subtype.comp q.ker.subtype).codRestrict f.ker
      (fun x => congrArg C.subtype (show q x.val = 1 from x.property))
    apply hkp.of_injective j
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg f.ker.subtype he
  have hb := pPrimeCore_quotient_eq_bot_of_central_two_subgroup q.ker hqk hqp hcore
  let e := QuotientGroup.quotientKerEquivOfSurjective q hq
  rw [← pPrimeCore_map_iso 2 e, hb, Subgroup.map_bot]
end MonoidHom
