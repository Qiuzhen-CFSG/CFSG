module
public import Stellmacher.ElementaryAbelianMaxPair.CentralProduct
public import Stellmacher.ElementaryAbelianMaxPair.Normalizers
/-! # Geometry of marked elementary planes
Full elementary plane preimages identify the actual centralizer and normal
plane, and their common order gives the intrinsic two-member maximum family.
Source application: Aschbacher--Smith 2.5.7.
-/
public section
open Subgroup
namespace Stellmacher
variable {G Q:Type*} [Group G] [Group Q] [Finite G]
theorem maxFamily_pair_of_marked_preimages
    (f:G→*Q) (hf:Function.Surjective f) (P₀ P₁:Subgroup Q)
    [IsElementaryAbelian 2 (P₀.comap f)] [IsElementaryAbelian 2 (P₁.comap f)]
    (hcard:Nat.card P₀=Nat.card P₁) (hne:P₀≠P₁)
    (hcover:∀A:Subgroup Q,IsElementaryAbelian 2 A→A≤P₀∨A≤P₁) :
    elementaryAbelianMaxSubgroups (⊤:Subgroup G)={P₀.comap f,P₁.comap f} ∧
      P₀.comap f≠P₁.comap f := by
  have hker (P:Subgroup Q):f.ker≤P.comap f:=by
    intro a ha
    change f a∈P
    rw [show f a=1 from ha]
    exact P.one_mem
  have hsize:Nat.card (P₀.comap f)=Nat.card (P₁.comap f):=by
    rw [←IsElementaryAbelian.card_inf_ker_mul_card_map (P₀.comap f) f,
      ←IsElementaryAbelian.card_inf_ker_mul_card_map (P₁.comap f) f,
      inf_eq_right.mpr (hker P₀),inf_eq_right.mpr (hker P₁),
      map_comap_eq_self_of_surjective hf,map_comap_eq_self_of_surjective hf,hcard]
  constructor
  · apply maxFamily_eq_pair_of_cover ⊤ _ _ le_top le_top hsize
    intro A hA
    let :=hA.2.1
    have hm:IsElementaryAbelian 2 (A.map f):=IsElementaryAbelian.map f
    exact (hcover (A.map f) hm).imp map_le_iff_le_comap.mp map_le_iff_le_comap.mp
  · intro he
    apply hne
    have hm:=congrArg (Subgroup.map f) he
    simpa only [map_comap_eq_self_of_surjective hf] using hm
omit [Finite G] in
theorem maxFamily_pair_of_marked_image
    {E:Type*} [Group E] [Finite E]
    (f:E→*Q) (hf:Function.Surjective f) (i:E→*G) (hi:Function.Injective i)
    (P₀ P₁:Subgroup Q)
    [IsElementaryAbelian 2 (P₀.comap f)] [IsElementaryAbelian 2 (P₁.comap f)]
    (hcard:Nat.card P₀=Nat.card P₁) (hne:P₀≠P₁)
    (hcover:∀A:Subgroup Q,IsElementaryAbelian 2 A→A≤P₀∨A≤P₁) :
    elementaryAbelianMaxSubgroups i.range={(P₀.comap f).map i,(P₁.comap f).map i} ∧
      (P₀.comap f).map i≠(P₁.comap f).map i := by
  obtain ⟨hp,hn⟩:=maxFamily_pair_of_marked_preimages f hf P₀ P₁ hcard hne hcover
  have hm:=maxFamily_pair_map i hi ⊤ (P₀.comap f) (P₁.comap f) hp
  rw [←MonoidHom.range_eq_map] at hm
  exact ⟨hm,fun he=>hn (map_injective hi he)⟩
end Stellmacher
