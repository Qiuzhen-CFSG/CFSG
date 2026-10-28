module
public import Theory.SpecificGroups.Alternating.FiveTenMarking
public import Mathlib.GroupTheory.IndexNormal

/-!
# The full order-thirty overlap in C₃ × A₅

Every subgroup of order thirty contains the entire cubic factor and is its
product with an actual order-ten subgroup of A₅. A specified isomorphism of
two such subgroups extends to the whole central product, and the extension
is unique. In particular the cubic kernel is retained, not discarded by
passing to the A₅ quotient.
-/

public noncomputable section
namespace alternatingGroup.FiveLocalGeometry.CubicThirty
open Subgroup
local notation "A" => alternatingGroup (Fin 5)
abbrev Z := Multiplicative (ZMod 3)

private theorem cardZ : Nat.card Z = 3 := by
  simp [Z,Nat.card_eq_fintype_card,Fintype.card_multiplicative]
private theorem cardA : Nat.card A = 60 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]

private theorem no_thirty (D : Subgroup A) : Nat.card D ≠ 30 := by
  intro hc
  have hi : D.index = 2 := by
    have hh := D.card_mul_index
    rw [hc,cardA] at hh
    omega
  have hn : D.Normal := normal_of_index_eq_two hi
  rcases hn.eq_bot_or_eq_top with hd | hd
  · rw [hd,card_bot] at hc
    omega
  · rw [hd,card_top,cardA] at hc
    omega

/-- An actual subgroup of order thirty has the full cubic direct factor. -/
theorem subgroup_eq_product (U : Subgroup (Z × A)) (hU : Nat.card U = 30) :
    ∃ D : Subgroup A, Nat.card D=10 ∧ U = (⊤ : Subgroup Z).prod D := by
  let f : U →* A := (MonoidHom.snd Z A).comp U.subtype
  let k : f.ker →* Z := (MonoidHom.fst Z A).comp (U.subtype.comp f.ker.subtype)
  have hk : Function.Injective k := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext he (x.property.trans y.property.symm)
  have hcardk : Nat.card f.ker ∣ 3 := by
    have hr := (k.range).card_subgroup_dvd_card
    have he : Nat.card k.range = Nat.card f.ker :=
      Nat.card_congr (MonoidHom.ofInjective hk).toEquiv.symm
    rw [he] at hr
    simpa only [cardZ] using hr
  have hcard : Nat.card f.ker = 3 := by
    rcases (show Nat.Prime 3 by decide).eq_one_or_self_of_dvd _ hcardk with he | he
    · have hh := f.ker.card_mul_index
      rw [he,one_mul,index_ker,hU] at hh
      exact False.elim (no_thirty f.range hh)
    · exact he
  have hks : Function.Surjective k :=
    (Nat.bijective_iff_injective_and_card k).mpr ⟨hk,hcard.trans cardZ.symm⟩ |>.2
  have hz (z : Z) : (z,(1 : A)) ∈ U := by
    obtain ⟨x,hx⟩ := hks z
    have he : ((x : U) : Z × A) = (z,1) := Prod.ext hx x.property
    exact he ▸ (x : U).property
  let D := U.map (MonoidHom.snd Z A)
  have he : U = (⊤ : Subgroup Z).prod D := by
    apply le_antisymm
    · intro x hx
      exact ⟨mem_top _,mem_map_of_mem _ hx⟩
    · rintro ⟨z,a⟩ ⟨_,x,hx,hxa⟩
      have ha : (1,a) ∈ U := by
        have hh := U.mul_mem (U.inv_mem (hz x.1)) hx
        have hh' : (x.1,(1 : A))⁻¹ * x = (1,a) := by
          apply Prod.ext
          · exact inv_mul_cancel _
          · exact hxa
        exact hh' ▸ hh
      simpa using U.mul_mem (hz z) ha
  refine ⟨D,?_,he⟩
  have hc := Nat.card_congr ((⊤ : Subgroup Z).prodEquiv D).toEquiv
  rw [←he,hU,Nat.card_prod,card_top,cardZ] at hc
  omega

private def coordinates (D : Subgroup A) : (⊤ : Subgroup Z).prod D ≃* Z × D :=
  ((⊤ : Subgroup Z).prodEquiv D).trans (MulEquiv.prodCongr (topEquiv (G := Z)) (MulEquiv.refl D))

private theorem product_extension (D E : Subgroup A) (hD : Nat.card D=10) (hE : Nat.card E=10)
    (f : Z × D ≃* Z × E) :
    ∃ Φ : MulAut (Z × A), ∀ (z : Z) (d : D),
      Φ (z,(d : A)) = ((f (z,d)).1,((f (z,d)).2 : A)) := by
  have hz (z : Z) : (f (z,1)).2 = 1 := by
    apply (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 3 10)).mp
    constructor
    · have he : (z,(1 : D))^3=1 := by
        apply Prod.ext
        · change z^3=1
          simpa only [cardZ] using (pow_card_eq_one' (x := z))
        · exact one_pow _
      have hh := congrArg (fun x : Z × E => x.2) (congrArg f he)
      simpa only [map_pow,map_one,Prod.pow_snd,Prod.snd_one] using hh
    · exact hE ▸ pow_card_eq_one'
  have hd (d : D) : (f (1,d)).1 = 1 := by
    apply (pow_eq_one_iff_of_coprime (by decide : Nat.Coprime 10 3)).mp
    constructor
    · have he : ((1 : Z),d)^10=1 := by
        exact Prod.ext (one_pow _) (hD ▸ pow_card_eq_one')
      have hh := congrArg (fun x : Z × E => x.1) (congrArg f he)
      simpa only [map_pow,map_one,Prod.pow_fst,Prod.fst_one] using hh
    · simpa only [cardZ] using (pow_card_eq_one' (x := (f (1,d)).1))
  let z : Z →* Z := (MonoidHom.fst Z E).comp (f.toMonoidHom.comp (MonoidHom.inl Z D))
  let d : D →* E := (MonoidHom.snd Z E).comp (f.toMonoidHom.comp (MonoidHom.inr Z D))
  have hzI : Function.Injective z := by
    intro a b he
    exact congrArg Prod.fst (f.injective (Prod.ext he ((hz a).trans (hz b).symm)))
  have hdI : Function.Injective d := by
    intro a b he
    exact congrArg Prod.snd (f.injective (Prod.ext ((hd a).trans (hd b).symm) he))
  let zE : MulAut Z := MulEquiv.ofBijective z ((Nat.bijective_iff_injective_and_card z).mpr ⟨hzI,rfl⟩)
  let dE : D ≃* E := MulEquiv.ofBijective d
    ((Nat.bijective_iff_injective_and_card d).mpr ⟨hdI,hD.trans hE.symm⟩)
  obtain ⟨Φ,hΦ⟩ := TenAutomorphisms.equiv_extends D E hD hE dE
  refine ⟨MulEquiv.prodCongr zE Φ,?_⟩
  intro a b
  have he : (a,b) = (a,(1 : D))*((1 : Z),b) := by simp
  have hf : f (a,b) = (z a,d b) := by
    rw [he,map_mul]
    exact Prod.ext (by change (f (a,1)).1 * (f (1,b)).1 = z a; rw [hd,mul_one]; rfl)
      (by change (f (a,1)).2 * (f (1,b)).2 = d b; rw [hz,one_mul]; rfl)
  rw [hf]
  exact Prod.ext rfl (hΦ b)

/-- Every specified order-thirty marking extends to the same full C₃ × A₅. -/
theorem equiv_extends (U V : Subgroup (Z × A)) (hU : Nat.card U=30)
    (hV : Nat.card V=30) (f : U ≃* V) :
    ∃ Φ : MulAut (Z × A), ∀ x : U, Φ x = (f x : Z × A) := by
  obtain ⟨D,hD,hDU⟩ := subgroup_eq_product U hU
  obtain ⟨E,hE,hEV⟩ := subgroup_eq_product V hV
  let u := (MulEquiv.subgroupCongr hDU).trans (coordinates D)
  let v := (MulEquiv.subgroupCongr hEV).trans (coordinates E)
  obtain ⟨Φ,hΦ⟩ := product_extension D E hD hE (u.symm.trans (f.trans v))
  refine ⟨Φ,?_⟩
  intro x
  obtain ⟨⟨z,d⟩,rfl⟩ := u.symm.surjective x
  exact hΦ z d

/-- The extension is unique because the full cubic factor and an actual
D₁₀ already determine the automorphism of C₃ × A₅. -/
theorem equiv_ext {E : Type*} [Group E] (U : Subgroup (Z × A)) (hU : Nat.card U=30)
    (f g : Z × A ≃* E) (h : ∀ x : U, f x = g x) : f=g := by
  obtain ⟨D,hD,hDU⟩ := subgroup_eq_product U hU
  apply TenAutomorphisms.product_equiv_ext D hD f g
  intro z d
  exact h ⟨(z,d),hDU ▸ ⟨mem_top _,d.property⟩⟩

/-- Transport the full order-thirty extension to any two marked carriers. -/
theorem marked_equiv_extends {G H : Type*} [Group G] [Group H]
    (eG : G ≃* Z × A) (eH : H ≃* Z × A)
    (U : Subgroup G) (V : Subgroup H) (hU : Nat.card U=30) (hV : Nat.card V=30)
    (f : U ≃* V) : ∃ Φ : G ≃* H, ∀ x : U, Φ x = (f x : H) := by
  let a := eG.subgroupMap U
  let b := eH.subgroupMap V
  obtain ⟨Φ,hΦ⟩ := equiv_extends (U.map eG.toMonoidHom) (V.map eH.toMonoidHom)
    (by rw [card_map_of_injective eG.injective,hU])
    (by rw [card_map_of_injective eH.injective,hV]) (a.symm.trans (f.trans b))
  refine ⟨eG.trans (Φ.trans eH.symm),?_⟩
  intro x
  apply eH.injective
  change eH (eH.symm (Φ (eG x))) = _
  rw [eH.apply_symm_apply]
  have hh := hΦ (a x)
  change Φ (eG x) = eH (f (a.symm (a x))) at hh
  simpa only [a.symm_apply_apply] using hh

/-- Agreement on the actual order-thirty subgroup determines the whole
marked order-180 carrier. -/
theorem marked_equiv_ext {G H : Type*} [Group G] [Group H]
    (eG : G ≃* Z × A) (U : Subgroup G) (hU : Nat.card U=30)
    (f g : G ≃* H) (h : ∀ x : U, f x = g x) : f=g := by
  have he := equiv_ext (U.map eG.toMonoidHom)
    (by rw [card_map_of_injective eG.injective,hU])
    (eG.symm.trans f) (eG.symm.trans g) (by
      rintro ⟨_,x,hx,rfl⟩
      change f (eG.symm (eG x)) = g (eG.symm (eG x))
      rw [eG.symm_apply_apply]
      exact h ⟨x,hx⟩)
  apply MulEquiv.ext
  intro x
  have hh := congrArg (fun k : Z × A ≃* H => k (eG x)) he
  simpa only [MulEquiv.trans_apply,eG.symm_apply_apply] using hh

end alternatingGroup.FiveLocalGeometry.CubicThirty
