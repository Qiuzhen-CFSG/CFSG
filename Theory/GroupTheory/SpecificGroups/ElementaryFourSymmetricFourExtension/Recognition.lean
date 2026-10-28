module

public import Theory.GroupTheory.SpecificGroups.ElementaryFourSymmetricFourExtension.Sylow
public import Theory.GroupTheory.SpecificGroups.ElementaryFourSymmetricFourExtension.Split
/-!
# Recognizing the index-two E₄ × S₄ extension

A group of order 192 with a normal E₄ × S₄ and Sylow two-group D₈ × D₈
is D₈ × S₄. The centralizer of the normal A₄ factor is D₈. The original
S₄ complement fixes a noncentral involution in its central E₄, so its
action on this D₈ is inner and has a canonical order-two lift. Correcting
the complement by that lift gives the direct product.

Source: Aschbacher--Smith F.5.4(3), printed p.301.
-/

public noncomputable section
open Subgroup
namespace ElementaryFourSymmetricFourExtension
variable {G : Type*} [Group G] [Finite G]

theorem exists_dihedral_product (E : Subgroup G) [E.Normal]
    (e : E ≃* Model) (hG : Nat.card G = 192)
    (R : Sylow 2 G) (eR : R ≃* DihedralGroup 4 × DihedralGroup 4) :
    Nonempty (G ≃* DihedralGroup 4 × S) := by
  classical
  let K := centralizer ((⁅E,E⁆ : Subgroup G) : Set G)
  obtain ⟨eK⟩ := centralizer_derived_dihedral E e hG R eR
  obtain ⟨hK,hSup⟩ := centralizer_derived_card_and_sup E e hG
  let v := leftEmbedding E e
  have hVK (x : V) : v x ∈ K := by
    intro y hy
    exact leftEmbedding_commutes E e x ⟨y,commutator_le_left E E hy⟩
  have hnon : ¬ ∀ x : V, (⟨v x,hVK x⟩ : K) ∈ center K := by
    intro hall
    apply central_factor_not_central E e R eR
    intro x
    let C := centralizer ({v x} : Set G)
    have hEC : E ≤ C := by
      intro y hy
      exact mem_centralizer_singleton_iff.mpr (leftEmbedding_commutes E e x ⟨y,hy⟩)
    have hKC : K ≤ C := by
      intro y hy
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp (hall x) (⟨y,hy⟩ : K)))
    have htop : (⊤ : Subgroup G) ≤ C := hSup ▸ sup_le hEC hKC
    apply mem_center_iff.mpr
    intro y
    exact mem_centralizer_singleton_iff.mp (htop (mem_top y))
  push Not at hnon
  obtain ⟨x,hx⟩ := hnon
  let s : K := ⟨v x,hVK x⟩
  have hs : s^2=1 := by
    apply Subtype.ext
    change v x ^2=1
    rw [←map_pow,show x^2=1 from (by decide : ∀ v : V, v^2=1) x,map_one]
  let d : S →* G := E.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inr V S))
  have hdis (h : S) (hh : d h ∈ K) : h=1 := by
    let z : K.subgroupOf E := ⟨e.symm (1,h),hh⟩
    have hz := (centralizer_derived_inside_equiv E e z).property
    change e (e.symm (1,h)) ∈ centralizer (commutator Model : Set Model) at hz
    rw [e.apply_symm_apply,centralizer_derived_model] at hz
    exact hz.2
  have hfix (h : S) : d h * (s : G) = (s : G) * d h :=
    leftEmbedding_commutes E e x (e.symm (1,h))
  have hcard : Nat.card G = Nat.card K * Nat.card S := by
    rw [hG,hK]
    norm_num [S,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  obtain ⟨eg⟩ := exists_product_of_normal_dihedral K eK d hdis s hs hx hfix hcard
  exact ⟨eg.trans (eK.prodCongr (MulEquiv.refl S))⟩

end ElementaryFourSymmetricFourExtension
