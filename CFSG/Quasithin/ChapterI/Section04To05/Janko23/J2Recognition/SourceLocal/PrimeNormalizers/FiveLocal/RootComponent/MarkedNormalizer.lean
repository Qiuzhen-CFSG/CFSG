module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.Recognition
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.Completion
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.Transport
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer.LocalProduct

/-!
# Assembly of the marked root-five normalizers

The quotient recognition gives the intrinsic A₅ component. A marked product
for one five-subgroup in the selected root involution centralizer transports
to every member of the root-five family. The generation and internal-complement
arguments then complete every field of `RootFiveWitness`.

The selected geometry constructs the local marked product. Thus the final
theorem retains only the quotient-recognition premise, whose discharge belongs
to the parent root-component assembly. Ambient simplicity and order are not
needed for this post-recognition argument.
Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer
variable {G : Type*} [Group G] [Finite G]

/-- Reduce the whole family to the geometric product construction inside the
selected centralizer. All seed-orbit and involution markings survive transport. -/
theorem rootFiveFamily_of_local_products {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D)
    (Q : ∀ E : Subgroup G, FiveCentralizing S.t E →
      Nonempty (Quotient E ≃* alternatingGroup (Fin 5)))
    (P : ∀ E : Subgroup G, Nat.card E = 5 → E ≤ involutionCentralizer S.t →
      (Quotient E ≃* alternatingGroup (Fin 5)) → Nonempty (ProductData D E)) :
    RootFiveFamily D S.t := by
  have ht : 5 ^ (Nat.card (involutionCentralizer S.t)).factorization 5 = 5 := by
    rw [S.model.centralizer_card]
    decide +kernel
  obtain ⟨F, hF, hFt⟩ := exists_fiveCentralizing S.t ht
  obtain ⟨e⟩ := Q F ⟨hF, S.t, IsConj.refl _, hFt⟩
  obtain ⟨W⟩ := P F hF hFt e
  apply rootFiveFamily_of_products S Q
  intro E hE
  obtain ⟨g, rfl⟩ := (fiveCentralizing_iff_mem_orbit S.t ht F hF hFt E).mp hE
  exact ⟨W.conjugate (ConjAct.ofConjAct g)⟩

/-- Recognized centralizer quotients complete every marked root-five witness.
The selected product supplies the two literal normalizer factors and the
seed-conjugate inverter; transport, generation and the actual core complement
then give the whole family. The parent source assembly discharges `Q` using
the quotient involution geometry. -/
theorem rootFiveFamily_of_quotient_models {D : Seed G}
    (S : InvolutionGeometry.SelectedGeometry D)
    (Q : ∀ E : Subgroup G, FiveCentralizing S.t E →
      Nonempty (Quotient E ≃* alternatingGroup (Fin 5))) :
    RootFiveFamily D S.t := by
  exact rootFiveFamily_of_local_products S Q (LocalProduct.selected_product S)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent.MarkedNormalizer
