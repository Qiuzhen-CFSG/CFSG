module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodeMultiplicity
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeRotation
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.GroupTheory.CoprimeQuotientSubgroups.ElementLift

/-!
# Odd rotations on the original code core section

The faithful F₄ multiplicity plane and its retained pure tensors prove
that the original order-five quotient rotation is fixed-point free on
P/U. The two-hexacode coordinates use the literal B/U inclusion and its
selected inverse conjugator, so this calculation applies to the original
sectionAction and its full covering kernel. Coprime lifting also produces
an actual residual cubic with the marked central image in 3.A6. Its
diagonal scalar action is fixed-point free and commutes with the pair action.

Source: Aschbacher--Smith 8.2.8(5--6), printed p.719,
refs/quasithin.pdf. Native ATLAS attribution: LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Atlas.Codes
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open HermitianSource Normalizer.SmallOvergroups
open MathieuCode.NormalizedShadowRows.CodeRotation
variable {G : Type*} [Group G]

theorem code_pair_quintic_fixedFree
    {R I V U : Subgroup G} {i : I}
    (hm : CodePairMultiplicityAction R I V U i)
    (hYP : R ⊔ I ≤ normalizer (I.pCoreIn 2 : Set G))
    (hYU : R ⊔ I ≤ normalizer (U : Set G))
    [(U.subgroupOf (I.pCoreIn 2)).Normal]
    (x : I) (hx : orderOf (QuotientGroup.mk' (pCore 2 I) x) = 5) :
    ∀ w, sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU
      (inclusion le_sup_right x) w = w → w = 1 := by
  obtain ⟨_,_,_,hBU,eB,eR,eP,μ,hμ,heP,hR,hpure⟩ := hm
  let := hBU
  let X := Fin 2 → hexacode
  let P := I.pCoreIn 2
  let f := sectionAction (R ⊔ I) P U hYP hYU
  let e : Multiplicative X ≃* (P ⧸ U.subgroupOf P) :=
    (LinearEquiv.finTwoArrow (ZMod 2) hexacode).toAddEquiv.toMultiplicative.trans
      ((MulEquiv.prodMultiplicative _ _).trans eP)
  let a : I →* MulAut (Multiplicative X) :=
    (MulAut.congr e.symm).toMonoidHom.comp (f.comp (inclusion le_sup_right))
  let ρ : Representation (ZMod 2) I X := {
    toFun g := (AddMonoidHom.toMultiplicative.symm (a g).toMonoidHom).toZModLinearMap 2
    map_one' := by apply LinearMap.ext; intro v; change (a 1 (Multiplicative.ofAdd v)).toAdd = v; rw [map_one]; rfl
    map_mul' g h := by apply LinearMap.ext; intro v; change (a (g*h) (Multiplicative.ofAdd v)).toAdd = (a g (a h (Multiplicative.ofAdd v))).toAdd; rw [map_mul]; rfl }
  have hρ (g : I) (v : X) :
      e (Multiplicative.ofAdd (ρ g v)) = f (inclusion le_sup_right g) (e (Multiplicative.ofAdd v)) := by
    change e (e.symm _) = _
    exact e.apply_symm_apply _
  have he (g : I) (c : Fin 2 → Hexacode.F) (v : hexacode) :
      ρ g (fun j => c j • v) = fun j => μ (QuotientGroup.mk' (pCore 2 I) g) c j • v := by
    apply Multiplicative.ofAdd.injective
    apply e.injective
    rw [hρ]
    exact hpure g c v
  have hf := pure_tensor_fixedFree ρ (μ.comp (QuotientGroup.mk' (pCore 2 I))) he x
    (quintic_plane_fixedFree μ hμ _ hx)
  intro w hw
  obtain ⟨v,rfl⟩ := e.surjective w
  have hv : ρ x v.toAdd = v.toAdd := by
    apply Multiplicative.ofAdd.injective
    apply e.injective
    exact (hρ x v.toAdd).trans hw
  have hz := hf v.toAdd hv
  have hv1 : v = 1 := hz
  rw [hv1,map_one]

/-- The quintic quotient produces an actual order-five actor in the
original pair, with no order lost through its full two-core kernel. -/
theorem code_pair_quintic_rotation [Finite G]
    {R I V U : Subgroup G} {i : I}
    (hm : CodePairMultiplicityAction R I V U i)
    (hD : Nonempty ((I ⧸ pCore 2 I) ≃* DihedralGroup 5)) :
    ∃ hYP : R ⊔ I ≤ normalizer (I.pCoreIn 2 : Set G),
      ∃ hYU : R ⊔ I ≤ normalizer (U : Set G),
        ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
          ∃ x : I, orderOf x = 5 ∧
            orderOf (QuotientGroup.mk' (pCore 2 I) x) = 5 ∧
            ∀ w, sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU
              (inclusion le_sup_right x) w = w → w = 1 := by
  obtain ⟨e⟩ := hD
  have hd : 5 ∣ Nat.card (I ⧸ pCore 2 I) := by
    rw [Nat.card_congr e.toEquiv,DihedralGroup.nat_card]
    decide
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := I) 5
    (hd.trans (card_quotient_dvd_card (pCore 2 I)))
  have hk : IsPGroup 2 (QuotientGroup.mk' (pCore 2 I)).ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hxq : orderOf (QuotientGroup.mk' (pCore 2 I) x) = 5 :=
    ((QuotientGroup.mk' (pCore 2 I)).orderOf_map_eq_of_coprime_of_isPGroup_ker
      hk x (by rw [hx]; decide)).trans hx
  have hm' := hm
  obtain ⟨hYP,hYU,hUP,_⟩ := hm'
  let := hUP
  exact ⟨hYP,hYU,hUP,x,hx,hxq,code_pair_quintic_fixedFree hm hYP hYU x hxq⟩

/-- Coprime lifting constructs an actual residual cubic, preserving its
central image in the genuine triple cover and its full diagonal action. -/
theorem code_pair_cubic_actor [Finite G]
    {R I V U : Subgroup G} {i : I}
    (hp : CodePairProductAction R I V U)
    (hn : CodePairNaturalAction R I V U i) :
    ∃ hYP : R ⊔ I ≤ normalizer (I.pCoreIn 2 : Set G),
      ∃ hYU : R ⊔ I ≤ normalizer (U : Set G),
        ∃ hUP : (U.subgroupOf (I.pCoreIn 2)).Normal, letI := hUP
          ∃ (eR : (R ⧸ pCore 2 R) ≃* HexEvenAutomorphisms) (z : R),
            orderOf z = 3 ∧ eR (QuotientGroup.mk' (pCore 2 R) z) = hexEvenZ ∧
            QuotientGroup.mk' (pCore 2 R) z ∈ center (R ⧸ pCore 2 R) ∧
            (∀ w, sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU
              (inclusion le_sup_left z) w = w → w = 1) ∧
            ∀ a : I, Commute
              (sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU (inclusion le_sup_left z))
              (sectionAction (R ⊔ I) (I.pCoreIn 2) U hYP hYU (inclusion le_sup_right a)) := by
  obtain ⟨hYP,hYU,hUP,hBU,eB,eR,eP,heP,hR⟩ := hn
  let := hUP
  let := hBU
  obtain ⟨_,_,_,hEl,hcard,hker,hcore,hRker,hIker,hRB,_,hB,eY,heY⟩ := hp
  let Y := R ⊔ I
  let P := I.pCoreIn 2
  let f := sectionAction Y P U hYP hYU
  let c : R →* HexEvenAutomorphisms := eR.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hc : Function.Surjective c := eR.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : c.ker = pCore 2 R := by
    rw [MonoidHom.ker_comp_of_injective _ _ eR.injective,QuotientGroup.ker_mk']
  have hcop : Nat.Coprime 3 (Nat.card c.ker) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := R)).exists_card_eq
    rw [hk,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨z,hzmark,hzpow⟩ := exists_prime_exponent_lift c hc hcop hexEvenZ
    (hexEvenZ_order ▸ pow_orderOf_eq_one hexEvenZ)
  have hz : orderOf z = 3 := Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hzpow)
    (by simpa only [hzmark,hexEvenZ_order] using orderOf_map_dvd c z)
  have hzc : hexEvenZ ∈ center HexEvenAutomorphisms := by
    rw [←Hexacode.even_kernel_eq_center,hexEvenCoordinate_kernel]
    exact mem_zpowers _
  refine ⟨hYP,hYU,hUP,eR,z,hz,hzmark,?_,?_,?_⟩
  · rw [mem_center_iff]
    intro r
    apply eR.injective
    simpa only [map_mul,show eR (QuotientGroup.mk' (pCore 2 R) z) = hexEvenZ from hzmark]
      using mem_center_iff.mp hzc (eR r)
  · intro w hw
    obtain ⟨⟨x,y⟩,rfl⟩ := eP.surjective w
    rw [hR] at hw
    change eP (Multiplicative.ofAdd (hexAction (c z).val x.toAdd),
      Multiplicative.ofAdd (hexAction (c z).val y.toAdd)) = eP (x,y) at hw
    rw [hzmark] at hw
    have hxy := eP.injective hw
    have hx : Hexacode.action hexZ x.toAdd = x.toAdd := congrArg (fun p => p.1.toAdd) hxy
    have hy : Hexacode.action hexZ y.toAdd = y.toAdd := congrArg (fun p => p.2.toAdd) hxy
    have hx1 : x = 1 := (Hexacode.scalar_fixed_iff x.toAdd).mp hx
    have hy1 : y = 1 := (Hexacode.scalar_fixed_iff y.toAdd).mp hy
    rw [hx1,hy1]
    exact eP.map_one
  · intro a
    let q := QuotientGroup.mk' (pCore 2 Y)
    have hrimg := heY z 1
    have haimg := heY 1 a
    simp only [map_one,mul_one,one_mul] at hrimg haimg
    have hcomm : Commute (q (inclusion le_sup_left z)) (q (inclusion le_sup_right a)) := by
      change _ * _ = _ * _
      apply eY.injective
      rw [map_mul,map_mul,hrimg,haimg]
      simp
    let fq := QuotientGroup.lift (pCore 2 Y) f (by rw [hker])
    exact hcomm.map fq


end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
