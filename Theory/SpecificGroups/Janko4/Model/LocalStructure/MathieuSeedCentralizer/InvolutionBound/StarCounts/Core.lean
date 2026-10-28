module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarDefs
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Moving centralizer lower bounds into the concrete star subgroup

A subgroup of the permutation centralizer contained in `StarGroup` injects
into the centralizer computed internally in `StarGroup`. This connects the
word and transversal certificates to the actual carrier used by `StarClass`.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
open Janko4.Cardinality.QuotientCount.Image
open Janko4.Cardinality.QuotientCount.Image.StarOrderCertificate

theorem card_generated_le_centralizer {n : ℕ} (b : Bool)
    (gen : Fin n → Equiv.Perm (Fin 24)) (hG : generated gen ≤ StarGroup)
    (hC : generated gen ≤ Subgroup.centralizer ({(starBase b).val} : Set (Equiv.Perm (Fin 24)))) :
    Nat.card (generated gen) ≤ Nat.card (Subgroup.centralizer ({starBase b} : Set StarGroup)) := by
  let f : generated gen → Subgroup.centralizer ({starBase b} : Set StarGroup) :=
    fun g => ⟨⟨g.val, hG g.property⟩, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hC g.property)))⟩
  exact Nat.card_le_card_of_injective f (fun _ _ h =>
    Subtype.ext (congrArg (fun x => x.val.val) h))

end Janko4.LocalStructure.MathieuSeedCentralizer.InvolutionBound.StarCountsCertificate
