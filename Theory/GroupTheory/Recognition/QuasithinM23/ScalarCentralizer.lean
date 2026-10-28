module
public import Theory.GroupTheory.Recognition.QuasithinM23.ScalarCubicNormalizer
public import Theory.GroupTheory.CentralizerSmallKernelTransport
/-!
# The marked scalar centralizer has a factor of order 180

The scalar units and SL₂(4) embed together in the centralizer of any scalar
in ΓL₂(4). Transport through an injective local marking retains their full
product in the actual ambient centralizer. This supplies the five-divisibility
needed to exclude the normal-Sylow case in the source cubic recognition.

Source: Aschbacher–Smith 5.2.15, printed pp.654–655 (`refs/quasithin.pdf`).
-/
public noncomputable section
open Subgroup
open Representation.SL2FourNatural Representation.SL2FourNatural.SemilinearNormalizer
namespace Theory.GroupTheory.QuasithinM23
/-- Scalar units and SL₂(4) embed together in a scalar centralizer. -/
theorem scalar_centralizer_card_multiple (a : Fˣ) :
    180 ∣ Nat.card (centralizer ({scalar a} : Set Gamma)) := by
  let g : Fˣ × SL →* Gamma := SemidirectProduct.inl.comp scalarSpecial
  have hcent (x : Fˣ × SL) : g x ∈ centralizer ({scalar a} : Set Gamma) := by
    apply mem_centralizer_singleton_iff.mpr
    change SemidirectProduct.inl (scalarSpecial x) * SemidirectProduct.inl (Matrix.GeneralLinearGroup.scalar (Fin 2) a) =
      SemidirectProduct.inl (Matrix.GeneralLinearGroup.scalar (Fin 2) a) * SemidirectProduct.inl (scalarSpecial x)
    rw [←map_mul,←map_mul,Matrix.GeneralLinearGroup.scalar_commute]
  let f := g.codRestrict _ hcent
  have hf : Function.Injective f := by
    intro x y h
    exact scalarSpecial_injective (SemidirectProduct.inl_injective (congrArg Subtype.val h))
  have hcard : Nat.card (Fˣ × SL) = 180 := by
    rw [Nat.card_prod,Nat.card_congr alternatingFiveEquiv.toEquiv,nat_card_alternatingGroup,
      Nat.card_eq_fintype_card,card_labels]
    norm_num [Nat.factorial]
  exact hcard ▸ card_dvd_of_injective f hf

/-- An injective marked semilinear local supplies the same divisor in the
literal ambient cubic centralizer. -/
theorem marked_scalar_centralizer_card_multiple
    {X G : Type*} [Group X] [Finite X] [Group G] [Finite G]
    (f : X →* G) (hf : Function.Injective f) (e : X ≃* Gamma)
    (c : X) (hc : e c ∈ scalar.range) :
    180 ∣ Nat.card (centralizer ({f c} : Set G)) := by
  obtain ⟨a,ha⟩ := hc
  have hd : 180 ∣ Nat.card (centralizer ({c} : Set X)) := by
    rw [Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv e c).toEquiv,←ha]
    exact scalar_centralizer_card_multiple a
  let q : centralizer ({c} : Set X) →* centralizer ({f c} : Set G) :=
    (f.comp (centralizer ({c} : Set X)).subtype).codRestrict _ (by
      intro x
      apply mem_centralizer_singleton_iff.mpr
      change f x * f c = f c * f x
      simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp x.property))
  exact hd.trans (card_dvd_of_injective q (fun x y he => Subtype.ext (hf (congrArg Subtype.val he))))

end Theory.GroupTheory.QuasithinM23
