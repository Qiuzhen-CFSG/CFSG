module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.CoreCenter
public import Theory.Mathieu.M24.Properties.Order

/-!
# The literal order-128 core inside every native Mathieu Sylow

The actual two-central centralizer has two-part 1024, so its Sylow is an
ambient Sylow. Its intrinsic normal self-centralizing core transports by
Sylow conjugacy to every ambient Sylow, preserving the entire core group.
This supplies a normal order-128 subgroup with center two; no extraspecial
or splitting conclusion is inferred from these numerical facts.
-/

public noncomputable section
open Subgroup
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA

public theorem exists_normal_selfCentralizing_core128 (S : Sylow 2 M24) :
    ∃ P : Subgroup M24, P≤(S : Subgroup M24) ∧
      (S : Subgroup M24)≤normalizer (P : Set M24) ∧ Nat.card P=128 ∧
      Nat.card (center P)=2 ∧ (S : Subgroup M24)⊓centralizer (P : Set M24)≤P ∧
      Nonempty (P≃*kernel) := by
  let R : Sylow 2 centralizer2A := Classical.choice inferInstance
  let R₀ := (R : Subgroup centralizer2A).map centralizer2A.subtype
  let P₀ := kernel.map centralizer2A.subtype
  have hRc : Nat.card R₀=1024 := by
    rw [card_map_of_injective centralizer2A.subtype_injective,R.card_eq_multiplicity,
      centralizer_card]
    decide +kernel
  let S₀ : Sylow 2 M24 := Sylow.ofCard R₀ (by rw [hRc,m24_order]; decide +kernel)
  have hP₀ : P₀≤(S₀ : Subgroup M24) :=
    map_mono (kernel_isTwoGroup.le_sylow_of_normal R)
  have hR₀ : (S₀ : Subgroup M24)≤centralizer2A := by
    rintro x ⟨r,_,rfl⟩
    exact r.property
  have hN₀ : (S₀ : Subgroup M24)≤normalizer (P₀ : Set M24) := by
    rintro x ⟨r,hr,rfl⟩
    exact kernel.le_normalizer_map centralizer2A.subtype
      (mem_map_of_mem _ (show r∈normalizer (kernel : Set centralizer2A) by
        rw [normalizer_eq_top]; exact mem_top _))
  have hC₀ : (S₀ : Subgroup M24)⊓centralizer (P₀ : Set M24)≤P₀ := by
    intro x hx
    have hxC : (⟨x,hR₀ hx.1⟩ : centralizer2A)∈centralizer (kernel : Set centralizer2A) := by
      intro y hy
      exact Subtype.ext (hx.2 y.val (mem_map_of_mem _ hy))
    exact mem_map_of_mem _ (kernel_selfCentralizing hxC)
  let e₀ := kernel.equivMapOfInjective centralizer2A.subtype centralizer2A.subtype_injective
  have hZ : Nat.card (center kernel)=2 := by
    have hle : Nat.card (center kernel)≤2 := by
      rw [kernel_eq_twoCore]
      exact core_center_card_le_two
    let : Nontrivial kernel := Finite.one_lt_card_iff_nontrivial.mp (by rw [kernel_card]; decide)
    let : Nontrivial (center kernel) := kernel_isTwoGroup.center_nontrivial
    exact Nat.le_antisymm hle (Nat.succ_le_of_lt
      (Finite.one_lt_card_iff_nontrivial.mpr inferInstance))
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M24 S₀ S
  have hRS : (S₀ : Subgroup M24).map (MulAut.conj g).toMonoidHom=(S : Subgroup M24) :=
    congrArg Sylow.toSubgroup hg
  let P := P₀.map (MulAut.conj g).toMonoidHom
  let e := P₀.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  have hPS : P≤(S : Subgroup M24) := (map_mono hP₀).trans_eq hRS
  have hSN : (S : Subgroup M24)≤normalizer (P : Set M24) := by
    rw [←hRS]
    exact (map_mono hN₀).trans (P₀.le_normalizer_map (MulAut.conj g).toMonoidHom)
  refine ⟨P,hPS,hSN,?_,?_,?_,⟨e.symm.trans e₀.symm⟩⟩
  · exact (Nat.card_congr (e.symm.trans e₀.symm).toEquiv).trans kernel_card
  · exact (Nat.card_congr (centerCongr (e.symm.trans e₀.symm)).toEquiv).trans hZ
  · intro x hx
    obtain ⟨r,hr,hrx⟩ := show x∈(S₀ : Subgroup M24).map (MulAut.conj g).toMonoidHom from hRS.symm ▸ hx.1
    have hrx' : (MulAut.conj g) r=x := hrx
    have hrC : r∈centralizer (P₀ : Set M24) := by
      intro y hy
      apply (MulAut.conj g).injective
      simpa only [map_mul,hrx'] using hx.2 ((MulAut.conj g) y) (mem_map_of_mem _ hy)
    exact mem_map.mpr ⟨r,hC₀ ⟨hr,hrC⟩,hrx⟩

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
