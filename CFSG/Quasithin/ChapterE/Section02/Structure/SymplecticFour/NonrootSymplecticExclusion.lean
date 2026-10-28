module
public import Theory.SpecificGroups.SymplecticFour.NotTwoCentralizers
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import CFSG.Quasithin.ClassicalModels

/-!
# Removing the symplectic carrier from the root-free source catalogue

Transport the actual characteristic-two projective symplectic model through
its trivial center. The explicit commuting order-two/order-three pair then
contradicts the all-involution centralizer condition supplied by the root-free
source geometry. No classification of the embedding is needed.
Source: Aschbacher--Smith E.2.7, printed p.220.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Structure.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
variable {H : Type*} [Group H]
theorem not_symplectic_model_of_all_two_centralizers
    (hc : ∀ t : H, orderOf t=2 → IsPGroup 2 (centralizer ({t} : Set H)))
    {f : ℕ} (hm : ClassicalGroup.IsPSp H 2 (2^f)) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : CharP F 2 := EvenProjective.charTwo_of_card hF
  let j : Sp F →* H := e.symm.toMonoidHom.comp EvenProjective.equiv.toMonoidHom
  have hj : Function.Injective j := e.symm.injective.comp EvenProjective.equiv.injective
  apply not_all_involution_centralizers_two (F := F)
  intro t ht
  have hp := hc (j t) ((orderOf_injective j hj t).trans ht)
  have he : centralizer ({t} : Set (Sp F)) =
      (centralizer ({j t} : Set H)).comap j := by
    ext x
    rw [mem_centralizer_singleton_iff,mem_comap,mem_centralizer_singleton_iff,
      ←map_mul,←map_mul,hj.eq_iff]
  rw [he]
  exact hp.comap_of_injective j hj
end CFSG.Quasithin.ChapterE.Structure.SymplecticFour
