module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.JankoTwoOuterInvolution
public import Mathlib.GroupTheory.Complement

/-!
# A split complement and exact outer relations above the reduced J₂ pair

The fixed-point-free cubic in the actual second parabolic has a normal
cyclic image in its core quotient. Coprime normalizer lifting makes the
quotient map surjective on its normalizer. A core element normalizing the
cubic must centralize it, so the fixed-point-free action makes that map
injective. Thus this normalizer is an actual S₃ × S₃ complement to the
unchanged order-64 core.

The reduced endpoint is exactly the inverse image of S₃ × A₃ in the
previously constructed marked quotient coordinates. Inside the complement
we construct an outer involution x and a reduced cubic k with exact
relations [d,x] = [d,k] = 1 and k^x = k⁻¹. The cubic k centralizes the
whole reduced part of the complement. All quotient and reduced-inclusion
maps remain literal, and either endpoint orientation is allowed.

These relations do not yet place k and x in the source's chosen Borel or
prove that x fixes its marked z. Those markings and the order-12 product
remain necessary for Aut(J₂) parabolic recognition; no recognition is
inferred from this splitting or the orders.

Source: DGS, Groups and Graphs (1985), (15.3), pp.229–231. The source alpha
endpoint is the repository's second endpoint. The only finite calculations
here concern S₃; the J₂ cubic action is the previously checked ATLAS action.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
local notation "S3" => Equiv.Perm (Fin 3)
local notation "C3" => Multiplicative (ZMod 3)

private theorem cubic_line_normalizer {Y : Type*} [Group Y]
    (u : S3) (hu : u ^ 3 = 1) :
    normalizer (zpowers (u,(1 : Y)) : Set (S3 × Y)) = ⊤ := by
  apply top_unique
  intro x _
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  have hh : (MulAut.conj x) (u,1) = (x.1*u*x.1⁻¹,1) := by
    apply Prod.ext <;> simp [MulAut.conj_apply]
  change zpowers ((MulAut.conj x) (u,1)) = _
  rw [hh]
  rcases (show ∀ a b : S3, a^3=1 → b*a*b⁻¹=a ∨ b*a*b⁻¹=a⁻¹ by
    decide +kernel) u x.1 hu with he | he
  · rw [he]
  · rw [he]
    simpa using (zpowers_inv (g := (u,(1 : Y))))

private theorem normalizer_restriction_bijective
    {A Y : Type*} [Group A] [Finite A] [Group Y]
    (v : A →* Y) (hv : Function.Surjective v) (a : A) (ha : a^3=1)
    (hcop : Nat.Coprime 3 (Nat.card v.ker))
    (hfixed : ∀ x ∈ v.ker, a*x=x*a → x=1)
    (hN : normalizer ((zpowers a).map v : Set Y) = ⊤) :
    Function.Bijective (v.comp (normalizer (zpowers a : Set A)).subtype) := by
  let D := zpowers a
  have hD : IsPGroup 3 D :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one ha).isPGroup 3 _
  let : Fact (IsPGroup 3 D) := ⟨hD⟩
  have hDi := injective_comp_subtype_of_coprime_ker v hcop D hD
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hxv : v (x : A) = 1 := hx
    have hmem : (x : A)*a*(x : A)⁻¹ ∈ D :=
      (mem_normalizer_iff.mp x.property a).mp (mem_zpowers a)
    have hconj : (x : A)*a*(x : A)⁻¹ = a := by
      apply congrArg Subtype.val (hDi (a₁ := ⟨_,hmem⟩) (a₂ := ⟨a,mem_zpowers a⟩) ?_)
      change v ((x : A)*a*(x : A)⁻¹) = v a
      rw [map_mul,map_mul,map_inv,hxv]
      simp
    have hc : a*(x : A)=(x : A)*a := (mul_inv_eq_iff_eq_mul.mp hconj).symm
    exact Subtype.ext (hfixed x hxv hc)
  · intro y
    have hh : y ∈ (normalizer (D : Set A)).map v := by
      rw [←normalizer_map_eq_of_coprime_kernel 3 D v hv hcop,hN]
      trivial
    obtain ⟨x,hx,hxy⟩ := hh
    exact ⟨⟨x,hx⟩,hxy⟩

open SuzukiContainment GreenBook
open Sporadic.LeechRelated.J2.ExceptionalParabolics
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The normalizer is in the literal original second endpoint. -/
@[expose] def originalCubicNormalizer (h : HypothesisF11 L S) (j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1) :
    Subgroup (parabolic L S j) := normalizer (zpowers (originalCubic h j f) : Set _)

/-- The quotient map restricts to an isomorphism on the normalizer of the
fixed-point-free cubic. No complement to the original core is assumed. -/
theorem originalCubicNormalizer_quotient_bijective
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) :
    Function.Bijective ((QuotientGroup.mk' (pCore 2 (parabolic L S j))).comp
      (originalCubicNormalizer h j f).subtype) := by
  let := h.finite_parabolic j
  let P := parabolic L S j
  let a := originalCubic h j f
  let q := QuotientGroup.mk' (pCore 2 P)
  obtain ⟨d,c,_,hd⟩ := original_second_quotient_marked_of_ne h i j e f hne
  let v := d.toMonoidHom.comp q
  have hv : Function.Surjective v := d.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : v.ker = pCore 2 P := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
  have hcop : Nat.Coprime 3 (Nat.card v.ker) := by
    rw [hk,original_second_core_card h j f]
    decide
  let u := (reducedSecondQuotientEquiv j f (QuotientGroup.mk' _ (reducedCubic j f))).1
  have ha : v a = (u,1) := by
    have hh := hd (QuotientGroup.mk' _ (reducedCubic j f))
    rw [reducedCubic_second_coordinate,map_one] at hh
    have hm : coreQuotientMap h j (QuotientGroup.mk' _ (reducedCubic j f)) =
        q a := coreQuotientMap_mk h j (reducedCubic j f)
    rw [hm] at hh
    exact hh
  have hu : u ^ 3 = 1 := by
    have hh := congrArg (fun z => (v z).1) (originalCubic_cube h j f)
    change (v (a ^ 3)).1 = (v 1).1 at hh
    simpa [ha] using hh
  have hN : normalizer ((zpowers a).map v : Set (S3 × S3)) = ⊤ := by
    rw [MonoidHom.map_zpowers,ha]
    exact cubic_line_normalizer u hu
  have hvN := normalizer_restriction_bijective v hv a (originalCubic_cube h j f)
    hcop (fun x hx hc => originalCubic_core_fixed h j f x (hk ▸ hx) hc) hN
  constructor
  · intro x y hxy
    exact hvN.1 (congrArg d hxy)
  · intro y
    obtain ⟨x,hx⟩ := hvN.2 (d y)
    exact ⟨x,d.injective hx⟩

/-- The resulting equivalence is the original core quotient map itself. -/
@[expose] def originalCubicNormalizerEquiv
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) :
    originalCubicNormalizer h j f ≃*
      (parabolic L S j ⧸ pCore 2 (parabolic L S j)) :=
  MulEquiv.ofBijective _ (originalCubicNormalizer_quotient_bijective h i j e f hne)

@[simp] theorem originalCubicNormalizerEquiv_apply
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) (x : originalCubicNormalizer h j f) :
    originalCubicNormalizerEquiv h i j e f hne x =
      QuotientGroup.mk' (pCore 2 (parabolic L S j)) x.val := rfl

/-- The cubic normalizer is an actual complement to the unchanged original
order-64 core, not only a subgroup of the right order. -/
theorem originalCubicNormalizer_complement
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) :
    IsComplement' (originalCubicNormalizer h j f) (pCore 2 (parabolic L S j)) := by
  exact isComplement_subgroup_right_iff_bijective.mpr
    (originalCubicNormalizer_quotient_bijective h i j e f hne)

/-- The splitting subgroup has the full product-of-triples structure. -/
theorem originalCubicNormalizer_equiv
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) :
    Nonempty (originalCubicNormalizer h j f ≃* (S3 × S3)) := by
  obtain ⟨d⟩ := original_second_quotient_of_ne h i j e f hne
  exact ⟨(originalCubicNormalizerEquiv h i j e f hne).trans d⟩

private theorem cubic_embedding_range (c : C3 →* S3) (hc : Function.Injective c) :
    c.range = alternatingGroup (Fin 3) := by
  have hle : c.range ≤ alternatingGroup (Fin 3) := by
    rintro _ ⟨z,rfl⟩
    have hz : (c z)^3=1 := by
      rw [←map_pow,show z^3=1 from (by decide +kernel : ∀ z : C3, z^3=1) z,map_one]
    exact (show ∀ u : S3, u^3=1 → u ∈ alternatingGroup (Fin 3) by
      simp only [Equiv.Perm.mem_alternatingGroup]
      decide +kernel) _ hz
  apply eq_of_le_of_card_ge hle
  have hh := Nat.card_congr (MonoidHom.ofInjective hc).toEquiv
  have hC : Nat.card C3 = 3 := by rw [Nat.card_eq_fintype_card]; rfl
  rw [hC] at hh
  rw [←hh,nat_card_alternatingGroup,Nat.card_fin]
  decide

/-- In any of the constructed marked quotient coordinates, the actual reduced
endpoint is the inverse image of S₃ × A₃. This retains its original inclusion. -/
theorem original_second_quotient_reduced
    (h : HypothesisF11 L S) (j : Fin 2)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (d : (parabolic L S j ⧸ pCore 2 (parabolic L S j)) ≃* (S3 × S3))
    (c : C3 →* S3) (hc : Function.Injective c)
    (hd : ∀ z, d (coreQuotientMap h j z) =
      ((reducedSecondQuotientEquiv j f z).1,c (reducedSecondQuotientEquiv j f z).2))
    (x : parabolic L S j) :
    (d (QuotientGroup.mk' (pCore 2 (parabolic L S j)) x)).2 ∈
      alternatingGroup (Fin 3) ↔ (x : G) ∈ parabolic L (reducedSylow L S) j := by
  let P := parabolic L S j
  let R := parabolic L (reducedSylow L S) j
  let q := QuotientGroup.mk' (pCore 2 P)
  let r := QuotientGroup.mk' (pCore 2 R)
  let v := d.toMonoidHom.comp q
  let inc := Subgroup.inclusion (reduced_parabolic_le h j)
  have hi (z : R) : v (inc z) =
      ((reducedSecondQuotientEquiv j f (r z)).1,c (reducedSecondQuotientEquiv j f (r z)).2) := by
    have hh := hd (r z)
    have hm : coreQuotientMap h j (r z) = q (inc z) := coreQuotientMap_mk h j z
    rwa [hm] at hh
  have hk : v.ker ≤ R.subgroupOf P := by
    rw [MonoidHom.ker_comp_of_injective _ _ d.injective,QuotientGroup.ker_mk']
    intro z hz
    have hzG : (z : G) ∈ twoCore R := by
      rw [reduced_parabolic_core h j]
      exact mem_map_of_mem P.subtype hz
    obtain ⟨w,_,hw⟩ := hzG
    change (z : G) ∈ R
    rw [←hw]
    exact w.property
  change (v x).2 ∈ alternatingGroup (Fin 3) ↔ (x : G) ∈ R
  rw [←cubic_embedding_range c hc]
  constructor
  · rintro ⟨z,hz⟩
    let w := (reducedSecondQuotientEquiv j f).symm ((v x).1,z)
    obtain ⟨y,hy⟩ := QuotientGroup.mk'_surjective (pCore 2 R) w
    have hyv : v (inc y) = v x := by
      rw [hi,show r y = w from hy]
      simp only [w,MulEquiv.apply_symm_apply,hz,Prod.mk.eta]
    have hxy : x * (inc y)⁻¹ ∈ v.ker := by
      change v (x * (inc y)⁻¹)=1
      rw [map_mul,map_inv,hyv,mul_inv_cancel]
    have hh := (R.subgroupOf P).mul_mem (hk hxy) (show inc y ∈ R.subgroupOf P from y.property)
    exact (show x ∈ R.subgroupOf P from by simpa only [inv_mul_cancel_right] using hh)
  · intro hx
    let y : R := ⟨x,hx⟩
    change (v (inc y)).2 ∈ c.range
    rw [hi]
    exact ⟨_,rfl⟩

/-- Exact outer-generator relations inside the original second endpoint.
The cubic k lies in the literal reduced endpoint and centralizes the chosen
d. The outer involution centralizes d and inverts k in the group itself.
Placement in the source's full Borel and fixation of its marked z are further
obligations; they are not inferred from these relations. -/
theorem exists_original_outer_cubic_relations
    (h : HypothesisF11 L S) (i j : Fin 2)
    (e : parabolic L (reducedSylow L S) i ≃* HallJanko.j2Model.toMarking.P 0)
    (f : parabolic L (reducedSylow L S) j ≃* HallJanko.j2Model.toMarking.P 1)
    (hne : S ≠ reducedSylow L S) :
    ∃ k x : parabolic L S j,
      orderOf k = 3 ∧ (k : G) ∈ parabolic L (reducedSylow L S) j ∧
      x^2=1 ∧ (x : G) ∉ parabolic L (reducedSylow L S) j ∧
      originalCubic h j f * k = k * originalCubic h j f ∧
      originalCubic h j f * x = x * originalCubic h j f ∧
      x*k*x⁻¹=k⁻¹ ∧
      ∀ y : parabolic L S j, y ∈ originalCubicNormalizer h j f →
        (y : G) ∈ parabolic L (reducedSylow L S) j → k*y=y*k := by
  let P := parabolic L S j
  let N := originalCubicNormalizer h j f
  let q := QuotientGroup.mk' (pCore 2 P)
  obtain ⟨d,c,hci,hd⟩ := original_second_quotient_marked_of_ne h i j e f hne
  let g := (originalCubicNormalizerEquiv h i j e f hne).trans d
  have hg (n : N) : g n = d (q n.val) := rfl
  let a : N := ⟨originalCubic h j f,(zpowers _).le_normalizer (mem_zpowers _)⟩
  let u := (reducedSecondQuotientEquiv j f (QuotientGroup.mk' _ (reducedCubic j f))).1
  have ha : g a = (u,1) := by
    have hh := hd (QuotientGroup.mk' _ (reducedCubic j f))
    rw [reducedCubic_second_coordinate,map_one] at hh
    have hm : coreQuotientMap h j (QuotientGroup.mk' _ (reducedCubic j f)) =
        q a.val := coreQuotientMap_mk h j (reducedCubic j f)
    rwa [hg,←hm]
  let z : C3 := Multiplicative.ofAdd (1 : ZMod 3)
  have hz : z^3=1 := by decide +kernel
  have hzne : z≠1 := by decide +kernel
  have hc3 : (c z)^3=1 := by rw [←map_pow,hz,map_one]
  let k : N := g.symm (1,c z)
  let x : N := g.symm (1,Equiv.swap 0 1)
  have hgk : g k = (1,c z) := g.apply_symm_apply _
  have hgx : g x = (1,Equiv.swap 0 1) := g.apply_symm_apply _
  have hk3 : k^3=1 := by
    apply g.injective
    rw [map_pow,hgk,map_one]
    exact Prod.ext (by simp) hc3
  have hkne : k≠1 := by
    intro hh
    have he := congrArg (fun n => (g n).2) hh
    rw [hgk,map_one] at he
    exact hzne (hci (he.trans c.map_one.symm))
  have hx2 : x^2=1 := by
    apply g.injective
    rw [map_pow,hgx,map_one]
    simp [pow_two]
  have hkR : (k.val : G) ∈ parabolic L (reducedSylow L S) j := by
    apply (original_second_quotient_reduced h j f d c hci hd k.val).mp
    change (g k).2 ∈ alternatingGroup (Fin 3)
    rw [hgk,←cubic_embedding_range c hci]
    exact ⟨z,rfl⟩
  have hxR : (x.val : G) ∉ parabolic L (reducedSylow L S) j := by
    intro hh
    have he := (original_second_quotient_reduced h j f d c hci hd x.val).mpr hh
    change (g x).2 ∈ alternatingGroup (Fin 3) at he
    rw [hgx] at he
    exact (by simp only [Equiv.Perm.mem_alternatingGroup]; decide : Equiv.swap (0 : Fin 3) 1 ∉ alternatingGroup (Fin 3)) he
  have hak : a*k=k*a := by
    apply g.injective
    rw [map_mul,map_mul,ha,hgk]
    exact Prod.ext (by simp) (by simp)
  have hax : a*x=x*a := by
    apply g.injective
    rw [map_mul,map_mul,ha,hgx]
    exact Prod.ext (by simp) (by simp)
  have hxk : x*k*x⁻¹=k⁻¹ := by
    apply g.injective
    rw [map_mul,map_mul,map_inv,map_inv,hgx,hgk]
    apply Prod.ext (by simp)
    exact (show ∀ v : S3, v^3=1 →
      Equiv.swap 0 1*v*(Equiv.swap 0 1)⁻¹=v⁻¹ by decide +kernel) _ hc3
  refine ⟨k.val,x.val,orderOf_eq_prime (congrArg Subtype.val hk3)
    (fun hh => hkne (Subtype.ext hh)),hkR,congrArg Subtype.val hx2,hxR,
    congrArg Subtype.val hak,congrArg Subtype.val hax,congrArg Subtype.val hxk,?_⟩
  intro y hyN hyR
  let yN : N := ⟨y,hyN⟩
  have hyalt := (original_second_quotient_reduced h j f d c hci hd y).mpr hyR
  change (g yN).2 ∈ alternatingGroup (Fin 3) at hyalt
  have hh : k*yN=yN*k := by
    apply g.injective
    rw [map_mul,map_mul,hgk]
    apply Prod.ext (by simp)
    exact (show ∀ u v : S3, u^3=1 → v ∈ alternatingGroup (Fin 3) → u*v=v*u by
      simp only [Equiv.Perm.mem_alternatingGroup]
      decide +kernel) _ _ hc3 hyalt
  exact congrArg Subtype.val hh

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension.JankoTwo
