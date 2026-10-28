module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixScalarResidual
public import Theory.GroupTheory.PPerfectCentralKernelImage
public import Theory.GroupTheory.PResidual.FiniteLocalPair
public import Theory.GroupTheory.PCoreImage

/-!
# The actual scalar residual on an abelian commutator layer

For any actual intermediate K≤I≤KT, an action killing [O2(I),I] sends
O2(I) to its center. The literal two-perfect scalar residual X therefore
has abelian action of exponent three, and its original K-core kernel acts
trivially. This does not assume that the whole two-core acts trivially.

Source: the scalar-action reduction in Aschbacher--Smith12.7.19, p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The unchanged scalar residual has an actual cubic action once the
commutator layer acts trivially; its original kernel is retained and killed. -/
theorem original_tripleSix_scalar_layer_action
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (I : Subgroup G) (hKI : K ≤ I) (hIM : I ≤ K ⊔ (T : Subgroup G))
    {A : Type*} [Group A] (ρ : I →* A)
    (hP : ⁅pCore 2 I,(⊤ : Subgroup I)⁆ ≤ ρ.ker) :
    let X := tripleSixScalarResidual K
    ∃ hXI : X ≤ I,
      (∀ x y : X, Commute (ρ (inclusion hXI x)) (ρ (inclusion hXI y))) ∧
      (∀ x : X, ρ (inclusion hXI x)^3=1) ∧
      (∀ x : X, (x : G) ∈ K.pCoreIn 2 → ρ (inclusion hXI x)=1) := by
  let X := tripleSixScalarResidual K
  have hXK : X ≤ K := map_subtype_le _
  have hXI : X ≤ I := hXK.trans hKI
  let f : X →* Atlas.Codes.HexEvenAutomorphisms :=
    a.groupEquiv.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hXK))
  let r := ρ.comp (inclusion hXI)
  have hXp : IsPPerfect 2 X := by
    let Z := centralPreimage (pCore 2 K)
    let R := (pResidual 2 Z).map Z.subtype
    let e := R.equivMapOfInjective K.subtype K.subtype_injective
    exact (isPPerfect_embedded_pResidual_of_finite 2 Z).of_surjective e.toMonoidHom e.surjective
  have hkernel (x : X) : f x=1 ↔ (x : G) ∈ K.pCoreIn 2 := by
    constructor
    · intro hx
      have hq : QuotientGroup.mk' (pCore 2 K) (inclusion hXK x)=1 := by
        apply a.groupEquiv.injective
        exact hx.trans (map_one a.groupEquiv).symm
      exact mem_map_of_mem K.subtype ((QuotientGroup.eq_one_iff _).mp hq)
    · rintro ⟨k,hk,he⟩
      have he' : k=inclusion hXK x := Subtype.ext he
      change a.groupEquiv (QuotientGroup.mk' (pCore 2 K) (inclusion hXK x))=1
      have hh : QuotientGroup.mk' (pCore 2 K) (inclusion hXK x)=1 :=
        (QuotientGroup.eq_one_iff _).mpr (he' ▸ hk)
      rw [hh,map_one]
  have hp : IsPGroup 2 f.ker := by
    let j : f.ker →* K.pCoreIn 2 :=
      (X.subtype.comp f.ker.subtype).codRestrict _ (fun x => (hkernel x.val).mp x.property)
    apply (isPGroup_pCoreIn 2 K).of_injective j
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : K.pCoreIn 2 => (x : G)) he
  have hKQ : K.pCoreIn 2 ≤ I.pCoreIn 2 := pCoreIn_mono_of_normalizes hKI
    (hIM.trans (sup_le K.le_normalizer D.sylow_normalizes_component))
  have hc : ∀ x ∈ f.ker, ∀ y : X, Commute (r x) (r y) := by
    intro x hx y
    have hxQ : inclusion hXI x ∈ pCore 2 I := by
      obtain ⟨i,hi,he⟩ := hKQ ((hkernel x).mp hx)
      exact (show i=inclusion hXI x from Subtype.ext he) ▸ hi
    have hh := hP (commutator_mem_commutator hxQ (mem_top (inclusion hXI y)))
    change ρ ⁅inclusion hXI x,inclusion hXI y⁆=1 at hh
    rw [map_commutatorElement] at hh
    exact commutatorElement_eq_one_iff_mul_comm.mp hh
  have hcenter (x : X) : f x ∈ center Atlas.Codes.HexEvenAutomorphisms := by
    rw [← tripleSixScalarResidual_image D a]
    exact ⟨inclusion hXK x,x.property,rfl⟩
  have hcomm (x y : X) : Commute (f x) (f y) :=
    (mem_center_iff.mp (hcenter x) (f y)).symm
  have he (x : X) : f x^3=1 := by
    have hd := orderOf_dvd_natCard (⟨f x,hcenter x⟩ : center Atlas.Codes.HexEvenAutomorphisms)
    rw [Hexacode.even_center_card] at hd
    have hh := orderOf_dvd_iff_pow_eq_one.mp hd
    exact congrArg Subtype.val hh
  obtain ⟨hrc,hrp,hrk⟩ := MonoidHom.coprime_abelian_image_of_central_kernel_image
    hXp f r hp hc hcomm (by decide : Nat.Coprime 2 3) he
  exact ⟨hXI,hrc,hrp,fun x hx => hrk ((hkernel x).mpr hx)⟩

end CFSG.Quasithin.Chapter12.Section07
