module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixScalarLayerAction
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# Even and odd conjugation on the original scalar layer

The actual scalar residual is normalized by KT. Its unchanged quotient
kernel acts trivially on the abelian commutator layer. The prescribed full
hexacode chart therefore transports even centralization and odd inversion
to an actual cubic operator, which generates the entire residual image.

Source: the operators in Aschbacher--Smith12.7.19, printed p.846.
This owner uses the characteristic transport already present in the full
Chapter12 source cone, so the earlier isolated transport module is not imported.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original scalar lift acts cubically; the prescribed full chart gives
its exact even and odd conjugation, and its image generates all of X. -/
theorem original_tripleSix_scalar_layer_conjugation_at
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (I : Subgroup G) (hKI : K ≤ I) (hIM : I ≤ K ⊔ (T : Subgroup G))
    {A : Type*} [Group A] (ρ : I →* A)
    (hP : ⁅pCore 2 I,(⊤ : Subgroup I)⁆ ≤ ρ.ker)
    (f : I →* HexAutomorphisms)
    (hfk : ∀ k : K, f (inclusion hKI k)=
      (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) :
    let X := tripleSixScalarResidual K
    ∃ (hXI : X ≤ I) (c : X),
      f (inclusion hXI c)=hexZ ∧ ρ (inclusion hXI c)^3=1 ∧
      (∀ t : I, hexSign (f t)=1 → Commute (ρ t) (ρ (inclusion hXI c))) ∧
      (∀ t : I, hexSign (f t)=-1 →
        ρ t * ρ (inclusion hXI c) * (ρ t)⁻¹=(ρ (inclusion hXI c))⁻¹) ∧
      (ρ (inclusion hXI c)=1 → ∀ x : X, ρ (inclusion hXI x)=1) := by
  let X := tripleSixScalarResidual K
  have hXK : X ≤ K := map_subtype_le _
  obtain ⟨hXI,_,hcube,hkill⟩ := original_tripleSix_scalar_layer_action D a I hKI hIM ρ hP
  have hz : hexEvenZ ∈ center HexEvenAutomorphisms := by
    rw [←Hexacode.even_kernel_eq_center,hexEvenCoordinate_kernel]
    exact mem_zpowers _
  have hm := (tripleSixScalarResidual_image D a).symm ▸ hz
  obtain ⟨cK,hcx,hc⟩ := hm
  let c : X := ⟨cK.val,hcx⟩
  have hcK : c.val ∈ K := cK.property
  have hfc : f (inclusion hXI c)=hexZ :=
    (hfk ⟨c.val,hcK⟩).trans (congrArg Subtype.val hc)
  have hIX : I ≤ normalizer (X : Set G) := by
    let Z := centralPreimage (pCore 2 K)
    exact (hIM.trans (sup_le K.le_normalizer D.sylow_normalizes_component)).trans
      ((normalizer_le_normalizer_characteristic_image K Z).trans
        (normalizer_le_normalizer_characteristic_map K.subtype K.subtype_injective Z (pResidual 2 Z)))
  have hkernel (x : X) (hx : f (inclusion hXI x)=1) : (x : G) ∈ K.pCoreIn 2 := by
    have hh : a.groupEquiv (QuotientGroup.mk' (pCore 2 K) (inclusion hXK x))=1 := by
      apply Subtype.ext
      exact (hfk (inclusion hXK x)).symm.trans hx
    have hq : QuotientGroup.mk' (pCore 2 K) (inclusion hXK x)=1 := by
      apply a.groupEquiv.injective
      exact hh.trans (map_one a.groupEquiv).symm
    exact mem_map_of_mem K.subtype ((QuotientGroup.eq_one_iff _).mp hq)
  have hsame (x y : X) (hxy : f (inclusion hXI x)=f (inclusion hXI y)) :
      ρ (inclusion hXI x)=ρ (inclusion hXI y) := by
    have hh : f (inclusion hXI (x*y⁻¹))=1 := by
      rw [map_mul,map_inv,map_mul,map_inv,hxy,mul_inv_cancel]
    have hk := hkill (x*y⁻¹) (hkernel (x*y⁻¹) hh)
    rw [map_mul,map_inv,map_mul,map_inv] at hk
    exact mul_inv_eq_one.mp hk
  refine ⟨hXI,c,hfc,hcube c,?_,?_,?_⟩
  · intro t ht
    let d : X := ⟨t.val*c.val*t.val⁻¹,
      (mem_normalizer_iff.mp (hIX t.property) c.val).mp c.property⟩
    have hd : inclusion hXI d=t * inclusion hXI c * t⁻¹ := rfl
    have hf : f (inclusion hXI d)=f (inclusion hXI c) := by
      rw [hd,map_mul,map_mul,map_inv,hfc,hex_conjugation_even (f t) ht]
    have hh := hsame d c hf
    rw [hd,map_mul,map_mul,map_inv] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro t ht
    let d : X := ⟨t.val*c.val*t.val⁻¹,
      (mem_normalizer_iff.mp (hIX t.property) c.val).mp c.property⟩
    have hd : inclusion hXI d=t * inclusion hXI c * t⁻¹ := rfl
    have hf : f (inclusion hXI d)=f (inclusion hXI c⁻¹) := by
      rw [hd,map_mul,map_mul,map_inv,map_inv,map_inv,hfc,hex_conjugation_odd (f t) ht]
    have hh := hsame d c⁻¹ hf
    simpa only [hd,map_mul,map_inv] using hh
  · intro hrc x
    have hx : a.groupEquiv (QuotientGroup.mk' (pCore 2 K) (inclusion hXK x)) ∈
        zpowers hexEvenZ := by
      rw [←hexEvenCoordinate_kernel,Hexacode.even_kernel_eq_center,
        ←tripleSixScalarResidual_image D a]
      exact ⟨inclusion hXK x,x.property,rfl⟩
    obtain ⟨n,hn⟩ := hx
    have hf : f (inclusion hXI x)=f (inclusion hXI (c^n)) := by
      rw [map_zpow,map_zpow,hfc]
      exact (hfk (inclusion hXK x)).trans (congrArg Subtype.val hn).symm
    have hh := hsame x (c^n) hf
    simpa only [map_zpow,hrc,one_zpow] using hh

end CFSG.Quasithin.Chapter12.Section07
