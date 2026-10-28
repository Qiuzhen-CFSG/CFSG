module
public import Theory.Representation.BinaryAlternatingFiveExtension.CentralProduct
public import Theory.Representation.BinaryAlternatingFiveExtension.OddExtension
public import Theory.Representation.BinaryAlternatingFiveExtension.SylowModel

/-!
# The marked Sylow model in the single alternating-five case

The natural binary module, the alternating residual subgroup, its centralizer,
and an actual odd involution determine the symmetric-five extension with a
central direct factor. We first construct that marked direct product and then
transport an arbitrary Sylow subgroup to `(D₈ wr C₂) × D`. The first projection
kernel is exactly the original centralizer pulled back to the Sylow subgroup.

These are the group and Sylow identifications used in the original single-`A₅`
case of Aschbacher--Smith, *The Classification of Quasithin Groups*, (2.4.29).
The odd involution assumption retains the source's offender information; a
symmetric quotient alone does not imply this splitting.
-/

public noncomputable section
namespace BinaryPermutation.AlternatingFiveExtension
open Subgroup
variable {H : Type*} [Group H] [Finite H]
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

/-- The original marked odd involution gives the full symmetric extension,
with the original centralizer as a literal direct factor. -/
theorem marked_product_equiv
    (q : H →* S5) (U L D : Subgroup H) [L.Normal]
    (hUL : U ≤ L) (hLq : L.map q = A5) (hkerL : q.ker ⊓ L = U)
    (hDc : D = centralizer (L : Set H)) (hD : D ≤ center H)
    (hker : q.ker = U ⊔ D) (hdis : Disjoint U D)
    (e : U ≃* V)
    (he : ∀ (h : H) (u : U),
      (e.symm (coreAction (q h) (e u)) : H) = h * (u : H) * h⁻¹)
    (t : H) (ht : t^2=1) (hodd : (q t).IsSwap) :
    ∃ E : H ≃* (Model × D),
      (∀ d : D, E (d : H) = (1,d)) ∧
      ((MonoidHom.fst Model D).comp E.toMonoidHom).ker = D := by
  obtain ⟨s,hs⟩ := exists_section_of_odd_involution q U L D hUL hLq hkerL hDc hdis e he t ht hodd
  exact product_equiv_of_marked_section q U D hD hker hdis e he s hs

/-- A marked central product gives the required Sylow model without changing
the subgroup represented by the central factor. -/
theorem sylow_equiv_of_marked_product
    (D : Subgroup H) (hDp : IsPGroup 2 D)
    (E : H ≃* (Model × D))
    (hEk : ((MonoidHom.fst Model D).comp E.toMonoidHom).ker = D)
    (S : Sylow 2 H) :
    ∃ eS : S ≃* SymmetricFourWreath.P × D,
      ((MonoidHom.fst SymmetricFourWreath.P D).comp eS.toMonoidHom).ker =
        D.subgroupOf (S : Subgroup H) := by
  let T : Sylow 2 (Model × D) := S.mapSurjective (f := E.toMonoidHom) E.surjective
  let eST : S ≃* T := (S : Subgroup H).equivMapOfInjective E.toMonoidHom E.injective
  let eT := SylowModel.sylowProdEquiv hDp T
  refine ⟨eST.trans eT,?_⟩
  ext x
  change (eT (eST x)).1 = 1 ↔ x.val ∈ D
  have hmem : (eT (eST x)).1 = 1 ↔ (E x.val).1 = 1 := by
    have hh := Subgroup.ext_iff.mp (SylowModel.sylowProdEquiv_ker_fst hDp T) (eST x)
    change (eT (eST x)).1 = 1 ↔ (E x.val).1 = 1 ∧ True at hh
    simpa only [and_true] using hh
  rw [hmem]
  exact Subgroup.ext_iff.mp hEk x.val

/-- The actual single-alternating source assumptions yield the wreath-product
Sylow model, with the given centralizer as the first projection kernel. -/
theorem marked_sylow_equiv
    (q : H →* S5) (U L D : Subgroup H) [L.Normal]
    (hUL : U ≤ L) (hLq : L.map q = A5) (hkerL : q.ker ⊓ L = U)
    (hDc : D = centralizer (L : Set H)) (hD : D ≤ center H)
    (hker : q.ker = U ⊔ D) (hdis : Disjoint U D)
    (e : U ≃* V)
    (he : ∀ (h : H) (u : U),
      (e.symm (coreAction (q h) (e u)) : H) = h * (u : H) * h⁻¹)
    (t : H) (ht : t^2=1) (hodd : (q t).IsSwap)
    (hDp : IsPGroup 2 D) (S : Sylow 2 H) :
    ∃ eS : S ≃* SymmetricFourWreath.P × D,
      ((MonoidHom.fst SymmetricFourWreath.P D).comp eS.toMonoidHom).ker =
        D.subgroupOf (S : Subgroup H) := by
  obtain ⟨E,_,hEk⟩ := marked_product_equiv q U L D hUL hLq hkerL hDc hD hker hdis e he t ht hodd
  exact sylow_equiv_of_marked_product D hDp E hEk S

end BinaryPermutation.AlternatingFiveExtension
end
