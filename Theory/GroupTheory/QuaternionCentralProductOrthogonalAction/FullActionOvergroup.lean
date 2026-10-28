module
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.CentralFactor
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter
public import Theory.GroupTheory.QuaternionCentralProductTransport
/-!
# Saturation of a full square-action subgroup

Let E be a quaternion central product, optionally expressed with a trivial
central direct factor. If E≤F≤M, E is normalized by M, and C_M(E)≤E, the
central-quotient action has kernel E. A full square-action image of F therefore
forces F=M. The orthogonal image is solvable and E is a two-group, so M is
solvable as well. The product coordinates need not respect conjugation.

Source: Aschbacher--Smith, 2.4.29, printed p.545, the equality M=M₁.
-/

@[expose] public section
open Subgroup
namespace Subgroup.QuaternionCentralProductData
variable {G Q D : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
  [Group D] [IsElementaryAbelian 2 D] [Subsingleton D]

theorem centralFactor_action_ker
    (E M : Subgroup G) (d : QuaternionCentralProductData Q) (e : E ≃* Q × D)
    (hEM : E ≤ M) (hMN : M ≤ normalizer (E : Set G))
    (hcent : M ⊓ centralizer (E : Set G) ≤ E) :
    ((d.centralFactorWreathAction e).comp
      (E.normalizerMonoidHom.comp (inclusion hMN))).ker = E.subgroupOf M := by
  let : Unique D := ⟨⟨1⟩,fun x=>Subsingleton.elim x 1⟩
  let eQ : E ≃* Q := e.trans (MulEquiv.prodUnique : Q × D ≃* Q)
  let de : QuaternionCentralProductData E := d.map eQ.symm
  let a : M →* MulAut E := E.normalizerMonoidHom.comp (inclusion hMN)
  let f := (d.centralFactorWreathAction e).comp a
  have hker : f.ker ≤ E.subgroupOf M := by
    intro m hm
    have ha : a m ∈ (quotientAut (center E)).ker := by
      rw [←d.centralFactorWreathAction_ker e]
      exact hm
    obtain ⟨p,hp⟩ := (de.quotientAut_eq_one_iff_inner (a m)).mp ha
    let pm : M := ⟨p,hEM p.property⟩
    have hpa : a pm = MulAut.conj p := by ext x; rfl
    have hk : a (pm⁻¹*m)=1 := by rw [map_mul,map_inv,hpa,hp,inv_mul_cancel]
    have hc : ((pm⁻¹*m:M):G) ∈ centralizer (E : Set G) := by
      intro y hy
      have hh := congrArg (fun b : MulAut E => (b ⟨y,hy⟩:G)) hk
      change (((pm⁻¹*m:M):G)*y*((pm⁻¹*m:M):G)⁻¹)=y at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    have hz := hcent ⟨(pm⁻¹*m).property,hc⟩
    have hh : (p:G)*((p:G)⁻¹*(m:G))∈E := E.mul_mem p.property hz
    change (m:G)∈E
    simpa only [mul_inv_cancel_left] using hh
  apply le_antisymm hker
  intro m hm
  change a m ∈ (d.centralFactorWreathAction e).ker
  rw [d.centralFactorWreathAction_ker]
  apply (de.quotientAut_eq_one_iff_inner (a m)).mpr
  exact ⟨⟨m,hm⟩,by ext x; rfl⟩

theorem eq_and_isSolvable_of_full_centralFactor_action
    (E F M : Subgroup G) (d : QuaternionCentralProductData Q) (e : E ≃* Q × D)
    (hEF : E ≤ F) (hFM : F ≤ M) (hMN : M ≤ normalizer (E : Set G))
    (hcent : M ⊓ centralizer (E : Set G) ≤ E)
    (hfull : ((d.centralFactorWreathAction e).comp
      (E.normalizerMonoidHom.comp (inclusion (hFM.trans hMN)))).range = ⊤) :
    F = M ∧ Group.IsSolvable M := by
  let : Unique D := ⟨⟨1⟩,fun x=>Subsingleton.elim x 1⟩
  let eQ : E ≃* Q := e.trans (MulEquiv.prodUnique : Q × D ≃* Q)
  let de : QuaternionCentralProductData E := d.map eQ.symm
  let a : M →* MulAut E := E.normalizerMonoidHom.comp (inclusion hMN)
  let f := (d.centralFactorWreathAction e).comp a
  have hEM : E ≤ M := hEF.trans hFM
  have hker : f.ker ≤ E.subgroupOf M :=
    (d.centralFactor_action_ker E M e hEM hMN hcent).le
  have hFs : Function.Surjective (f.comp (inclusion hFM)) :=
    MonoidHom.range_eq_top.mp hfull
  have heq : F=M := by
    apply le_antisymm hFM
    intro m hm
    obtain ⟨y,hy⟩ := hFs (f ⟨m,hm⟩)
    have hk : ((inclusion hFM y)⁻¹*⟨m,hm⟩:M) ∈ f.ker := by
      change f ((inclusion hFM y)⁻¹*⟨m,hm⟩)=1
      rw [map_mul,map_inv,show f (inclusion hFM y)=f ⟨m,hm⟩ from hy,inv_mul_cancel]
    have he : ((y:G)⁻¹*m)∈E := hker hk
    have hh := F.mul_mem y.property (hEF he)
    simpa only [mul_inv_cancel_left] using hh
  have h2 : IsPGroup 2 E := IsPGroup.of_card (n:=5) (by rw [de.card]; norm_num)
  let : Group.IsNilpotent E := h2.isNilpotent
  let : Group.IsSolvable BinaryFourPlus.Wreath := BinaryFourPlus.wreath_isSolvable
  have hs : Group.IsSolvable M := Group.isSolvable_of_ker_le_range
    (inclusion hEM) f (by rw [inclusion_range]; exact hker)
  exact ⟨heq,hs⟩

theorem card_eq_of_full_centralFactor_action
    (E F M : Subgroup G) (d : QuaternionCentralProductData Q) (e : E ≃* Q × D)
    (hEF : E ≤ F) (hFM : F ≤ M) (hMN : M ≤ normalizer (E : Set G))
    (hcent : M ⊓ centralizer (E : Set G) ≤ E)
    (hfull : ((d.centralFactorWreathAction e).comp
      (E.normalizerMonoidHom.comp (inclusion (hFM.trans hMN)))).range = ⊤) :
    Nat.card M = 2304 := by
  let f := (d.centralFactorWreathAction e).comp
    (E.normalizerMonoidHom.comp (inclusion hMN))
  have hEM : E ≤ M := hEF.trans hFM
  have hk : f.ker = E.subgroupOf M := d.centralFactor_action_ker E M e hEM hMN hcent
  have hs : Function.Surjective f := by
    have hh : Function.Surjective (f.comp (inclusion hFM)) := MonoidHom.range_eq_top.mp hfull
    exact Function.Surjective.of_comp hh
  have hcE : Nat.card E = 32 := by
    let : Unique D := ⟨⟨1⟩,fun x=>Subsingleton.elim x 1⟩
    exact (Nat.card_congr (e.trans (MulEquiv.prodUnique : Q × D ≃* Q)).toEquiv).trans d.card
  have hw : Nat.card BinaryFourPlus.Wreath = 72 :=
    (Nat.card_congr BinaryFourPlus.isometryEquivWreath.toEquiv).symm.trans BinaryFourPlus.card_isometrySubgroup
  have hh := f.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hs,
    Nat.card_congr (topEquiv : (⊤:Subgroup BinaryFourPlus.Wreath) ≃* BinaryFourPlus.Wreath).toEquiv,
    hw,hk,Nat.card_congr (subgroupOfEquivOfLe hEM).toEquiv,hcE] at hh
  exact hh.symm

end Subgroup.QuaternionCentralProductData
