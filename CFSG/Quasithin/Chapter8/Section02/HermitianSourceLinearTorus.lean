module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.LinearOddFixed
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceLinearRanks
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceLinearRanks

/-!
# The selected linear-two torus fixes exactly the central intersection

The native natural-sum calculation identifies C_V(y) for the original lift
in M intersect I. The two independently defined projection maps are retained:
the quotient determines its odd order, while conjugation on V determines the
automizer element. Transport through these literal maps gives the fixed
subgroup of the cyclic automizer torus, with no E.2.14 source premise.

The chosen Hermitian tensor consumer uses this to exclude every selected
PSL₂ family. This is the linear-two branch of E.2.14(9), not the remaining
Suzuki branch or the full field-four exclusion.
Source: Aschbacher–Smith E.2.14(9), printed pp.226–227, and 8.2.2(8),
printed p.715 (refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Matrix MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

/-- The original lift fixes precisely V intersect V^i. Its nontrivial odd
order is measured in the literal star quotient. -/
theorem selected_linear_odd_centralizer
    (s : Selected H T M V I k i S) (hk : 1 < k)
    (ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField k))
    (y : ↥(M ⊓ I))
    (ho : Odd (orderOf (selectedStarMap M I y)))
    (hne : selectedStarMap M I y ≠ 1) :
    V ⊓ centralizer ({y.val} : Set G) =
      V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  let e := ((QuotientGroup.quotientMulEquivOfEq s.core_eq).trans ξ).trans
    (Theory.PSL2.sl2QuotientEquiv (BinaryGaloisField k)).symm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (localCore M I))
  let R := S.mapSurjective (f := q)
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  obtain ⟨hMN,hVS,hMS⟩ := selected_linear_markings s ξ
  let x : I := ⟨y.val,y.property.2⟩
  have hx : q x = e (selectedStarMap M I y) := rfl
  have hodd : Odd (orderOf (q x)) := by
    rw [hx]
    change Odd (orderOf (e.toMonoidHom (selectedStarMap M I y)))
    rwa [orderOf_injective e.toMonoidHom e.injective]
  have hxne : q x ≠ 1 := by
    rw [hx]
    exact fun he => hne (e.map_eq_one_iff.mp he)
  have hc := s.twoConjugate.linear_pair_odd_centralizer hMN k (by omega)
    (GaloisField.card 2 k (by omega)) e R hVS hMS x hodd hxne
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  rw [←selected_intersection_image I V hVI i,←hc]
  apply le_antisymm
  · intro v hv
    refine ⟨⟨v,hVI hv.1⟩,⟨hv.1,?_⟩,rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (show Commute (⟨v,hVI hv.1⟩ : I) x from
        Subtype.ext ((mem_centralizer_singleton_iff.mp hv.2)))
  · rintro _ ⟨v,hv,rfl⟩
    exact ⟨hv.1,mem_centralizer_singleton_iff.mpr
      (congrArg I.subtype (mem_centralizer_singleton_iff.mp hv.2))⟩

/-- The actual selected cyclic torus has the source fixed subgroup, with
the E.2.14(9) premise discharged in the linear-two case. -/
theorem selected_linear_exists_torus_fixed
    (s : Selected H T M V I k i S) (hk : 1 < k)
    (ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField k)) :
    ∃ (y : ↥(M ⊓ I)) (x : Automizer V),
      x = (selectedActionMap M I V (s.normalizer_eq ▸ inf_le_right) y).val ∧
      orderOf y = 2^k-1 ∧ orderOf (selectedStarMap M I y) = 2^k-1 ∧
      x ∈ inducedAutomizer V (M ⊓ I) ∧ orderOf x = 2^k-1 ∧
      automizerFixedGroup V (zpowers x) =
        V ⊓ V.map (MulAut.conj i.val⁻¹).toMonoidHom := by
  obtain ⟨y,x,hxy,hy,hq,hx,ho⟩ := selected_exists_automizer_torus s hk
  have hodd : Odd (orderOf (selectedStarMap M I y)) := by
    rw [hq]
    exact Nat.Even.sub_odd (Nat.one_le_pow k 2 (by decide))
      (Nat.even_pow.mpr ⟨by decide,by omega⟩) odd_one
  have hne : selectedStarMap M I y ≠ 1 := by
    intro he
    rw [he,orderOf_one] at hq
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hk
    omega
  have hc := selected_linear_odd_centralizer s hk ξ y hodd hne
  have himage := selected_lift_action_image M I V (s.normalizer_eq ▸ inf_le_right) (zpowers y)
  rw [MonoidHom.map_zpowers,MonoidHom.map_zpowers] at himage
  have hnorm : (zpowers y).map (M ⊓ I).subtype ≤ normalizer (V : Set G) :=
    (map_subtype_le _).trans (s.normalizer_eq ▸ inf_le_right)
  have hfix := automizerFixedGroup_induced V ((zpowers y).map (M ⊓ I).subtype) hnorm
  rw [←himage] at hfix
  change automizerFixedGroup V (zpowers (selectedActionMap M I V _ y).val) = _ at hfix
  rw [←hxy,MonoidHom.map_zpowers] at hfix
  have hcz : centralizer (zpowers y.val : Set G) = centralizer ({y.val} : Set G) := by
    rw [zpowers_eq_closure,centralizer_closure]
  change automizerFixedGroup V (zpowers x) = V ⊓ centralizer (zpowers y.val : Set G) at hfix
  rw [hcz] at hfix
  exact ⟨y,x,hxy,hy,hq,hx,ho,hfix.trans hc⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
