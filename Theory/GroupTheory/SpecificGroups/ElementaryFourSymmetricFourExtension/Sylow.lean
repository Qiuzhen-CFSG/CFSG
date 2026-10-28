module

public import Theory.GroupTheory.SpecificGroups.ElementaryFourSymmetricFourExtension.Derived
public import Theory.SpecificGroups.SymmetricFourSylow
public import Theory.GroupTheory.SpecificGroups.DihedralEightRecognition
/-!
# The dihedral centralizer forced by a D₈ × D₈ Sylow subgroup

An embedded E₄ × D₈ cannot have its first factor central in D₈ × D₈:
that factor would be the full center, which contains every commutator.
The second factor has a nontrivial commutator disjoint from the first.
Sylow containment transports this obstruction to an endpoint E₄ × S₄.
Its order-eight alternating-factor centralizer is consequently dihedral.

Source: Aschbacher--Smith F.5.4(3), printed p.301.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace ElementaryFourSymmetricFourExtension
local notation "D8" => DihedralGroup 4

private theorem dihedral_commutator_central : ∀ a b c : D8,
    c * ⁅a,b⁆ = ⁅a,b⁆ * c := by decide +kernel

private theorem product_commutator_central (a b : D8 × D8) :
    ⁅a,b⁆ ∈ center (D8 × D8) := by
  apply mem_center_iff.mpr
  intro c
  exact Prod.ext (dihedral_commutator_central a.1 b.1 c.1)
    (dihedral_commutator_central a.2 b.2 c.2)

private theorem product_center_card : Nat.card (center (D8 × D8)) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem no_central_four_embedding (f : V × D8 →* D8 × D8) (hf : Function.Injective f)
    (hc : ∀ v : V, f (v,1) ∈ center (D8 × D8)) : False := by
  let a : V →* D8 × D8 := f.comp (MonoidHom.inl V D8)
  have hai : Function.Injective a := fun x y h => congrArg Prod.fst (hf h)
  have haC : a.range ≤ center (D8 × D8) := by
    rintro x ⟨v,rfl⟩
    exact hc v
  have ha : a.range = center (D8 × D8) := eq_of_le_of_card_ge haC (by
    rw [←Nat.card_congr (MonoidHom.ofInjective hai).toEquiv,product_center_card]
    simp [V,Nat.card_eq_fintype_card])
  let r : D8 := .r 1
  let s : D8 := .sr 0
  have he : f (1,⁅r,s⁆) = ⁅f (1,r),f (1,s)⁆ := by
    simpa [commutatorElement_def] using map_commutatorElement f (1,r) (1,s)
  have hm : f (1,⁅r,s⁆) ∈ a.range := by
    rw [ha,he]
    exact product_commutator_central _ _
  obtain ⟨v,hv⟩ := hm
  have hv' : (v,1) = (1,⁅r,s⁆) := hf hv
  have hh : (1 : D8) = ⁅r,s⁆ := congrArg Prod.snd hv'
  have hn : (1 : D8) ≠ ⁅r,s⁆ := by decide
  exact hn hh

variable {G : Type*} [Group G] [Finite G]

theorem central_factor_not_central (E : Subgroup G) (e : E ≃* Model)
    (R : Sylow 2 G) (eR : R ≃* D8 × D8)
    (hc : ∀ v : V, (e.symm (v,1) : G) ∈ center G) : False := by
  let P : Sylow 2 S := Sylow.nonempty.some
  obtain ⟨eP⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four P
  let d : D8 →* S := (P : Subgroup S).subtype.comp eP.symm.toMonoidHom
  have hdi : Function.Injective d := (P : Subgroup S).subtype_injective.comp eP.symm.injective
  let j : V × D8 →* Model := (MonoidHom.id V).prodMap d
  have hji : Function.Injective j := by
    intro x y h
    change (x.1,d x.2) = (y.1,d y.2) at h
    exact Prod.ext (congrArg (fun p : V × S => p.1) h) (hdi (congrArg (fun p : V × S => p.2) h))
  let f : V × D8 →* G := E.subtype.comp (e.symm.toMonoidHom.comp j)
  have hfi : Function.Injective f := E.subtype_injective.comp (e.symm.injective.comp hji)
  have hp : IsPGroup 2 (V × D8) := IsPGroup.of_card (n := 5) (by
    norm_num [V,Nat.card_eq_fintype_card,DihedralGroup.card])
  obtain ⟨U,hU⟩ := (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_le_sylow
  let fU : V × D8 →* U := f.codRestrict U (fun x => hU ⟨x,rfl⟩)
  have hfU : Function.Injective fU := fun x y h => hfi (congrArg (fun t : U => (t : G)) h)
  let eu : U ≃* D8 × D8 := (U.equiv R).trans eR
  apply no_central_four_embedding (eu.toMonoidHom.comp fU) (eu.injective.comp hfU)
  intro v
  apply mem_center_iff.mpr
  intro y
  obtain ⟨y,rfl⟩ := eu.surjective y
  change eu y * eu (fU (v,1)) = eu (fU (v,1)) * eu y
  rw [←map_mul,←map_mul]
  apply congrArg eu
  apply Subtype.ext
  have hv := mem_center_iff.mp (hc v) (y : G)
  change (y:G) * (e.symm (v,d 1) : G) = (e.symm (v,d 1) : G) * (y:G)
  simpa only [map_one] using hv

def leftEmbedding (E : Subgroup G) (e : E ≃* Model) : V →* G :=
  E.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl V S))

omit [Finite G] in
theorem leftEmbedding_injective (E : Subgroup G) (e : E ≃* Model) :
    Function.Injective (leftEmbedding E e) := by
  intro x y h
  have hh : e.symm (x,1) = e.symm (y,1) := Subtype.ext h
  exact congrArg Prod.fst (e.symm.injective hh)

omit [Finite G] in
theorem leftEmbedding_commutes (E : Subgroup G) (e : E ≃* Model) (v : V) (y : E) :
    (y : G) * leftEmbedding E e v = leftEmbedding E e v * y := by
  change ((y * e.symm (v,1) : E) : G) = ((e.symm (v,1) * y : E) : G)
  apply congrArg Subtype.val
  apply e.injective
  simp only [map_mul,e.apply_symm_apply]
  exact Prod.ext (mul_comm _ _) (by simp)

theorem centralizer_derived_dihedral (E : Subgroup G) [E.Normal]
    (e : E ≃* Model) (hG : Nat.card G = 192)
    (R : Sylow 2 G) (eR : R ≃* D8 × D8) :
    Nonempty (centralizer ((⁅E,E⁆ : Subgroup G) : Set G) ≃* D8) := by
  let K := centralizer ((⁅E,E⁆ : Subgroup G) : Set G)
  obtain ⟨hK,hSup⟩ := centralizer_derived_card_and_sup E e hG
  let v := leftEmbedding E e
  have hv : Function.Injective v := leftEmbedding_injective E e
  have hVK : v.range ≤ K := by
    rintro x ⟨x,rfl⟩ y hy
    exact leftEmbedding_commutes E e x ⟨y,commutator_le_left E E hy⟩
  let W := v.range.subgroupOf K
  have hW : Nat.card W = 4 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVK).toEquiv,
      ←Nat.card_congr (MonoidHom.ofInjective hv).toEquiv]
    simp [V,Nat.card_eq_fintype_card]
  have hp : ∀ x : V, x^2 = 1 := by decide
  let : IsElementaryAbelian 2 v.range :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
        rintro ⟨x,y,rfl⟩
        apply Subtype.ext
        change v y ^ 2 = 1
        rw [←map_pow,hp,map_one]) }
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVK
  apply dihedral_eight_of_noncentral_elementary_four hK W hW
  intro hc
  apply central_factor_not_central E e R eR
  intro x
  let C := centralizer ({v x} : Set G)
  have hEC : E ≤ C := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (leftEmbedding_commutes E e x ⟨y,hy⟩)
  have hKC : K ≤ C := by
    intro y hy
    have hxW : (⟨v x,hVK ⟨x,rfl⟩⟩ : K) ∈ W := ⟨x,rfl⟩
    have hh := mem_center_iff.mp (hc hxW) (⟨y,hy⟩ : K)
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hh)
  have htop : (⊤ : Subgroup G) ≤ C := hSup ▸ sup_le hEC hKC
  apply mem_center_iff.mpr
  intro y
  exact mem_centralizer_singleton_iff.mp (htop (mem_top y))

end ElementaryFourSymmetricFourExtension
